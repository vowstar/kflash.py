#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from __future__ import (division, print_function)

import sys
import time
import zlib
import copy
import struct
import binascii
import hashlib
import argparse
import math
import zipfile, tempfile, backports.tempfile
import json
import re
import os


class KFlash:
    print_callback = None

    def __init__(self, print_callback = None):
        self.killProcess = False
        self.loader = None
        self.print_callback = print_callback

    @staticmethod
    def log(*args, **kwargs):
        if KFlash.print_callback:
            # pylint: disable=not-callable
            KFlash.print_callback(*args, **kwargs)
            # pylint: enable=not-callable
        else:
            print(*args, **kwargs)

    def process(self, terminal=True, dev="", baudrate=1500000, board=None, sram = False, file="", callback=None, noansi=False, terminal_auto_size=False, terminal_size=(50, 1), slow_mode = False, addr=None, length=None):
        self.killProcess = False
        BASH_TIPS = dict(NORMAL='\033[0m',BOLD='\033[1m',DIM='\033[2m',UNDERLINE='\033[4m',
                            DEFAULT='\033[0m', RED='\033[31m', YELLOW='\033[33m', GREEN='\033[32m',
                            BG_DEFAULT='\033[49m', BG_WHITE='\033[107m')

        ERROR_MSG   = BASH_TIPS['RED']+BASH_TIPS['BOLD']+'[ERROR]'+BASH_TIPS['NORMAL']
        WARN_MSG    = BASH_TIPS['YELLOW']+BASH_TIPS['BOLD']+'[WARN]'+BASH_TIPS['NORMAL']
        INFO_MSG    = BASH_TIPS['GREEN']+BASH_TIPS['BOLD']+'[INFO]'+BASH_TIPS['NORMAL']

        VID_LIST_FOR_AUTO_LOOKUP = "(1A86)|(0403)|(067B)|(10C4)|(C251)|(0403)"
        #                            WCH    FTDI    PL     CL    DAP   OPENEC
        ISP_RECEIVE_TIMEOUT = 0.5

        MAX_RETRY_TIMES = 10

        ISP_FLASH_SECTOR_SIZE = 4096
        ISP_FLASH_DATA_FRAME_SIZE = ISP_FLASH_SECTOR_SIZE * 16

        def tuple2str(t):
            ret = ""
            for i in t:
                ret += i+" "
            return ret

        def raise_exception(exception):
            if self.loader:
                try:
                    self.loader._port.close()
                except Exception:
                    pass
            raise exception

        try:
            from enum import Enum
        except ImportError:
            err = (ERROR_MSG,'enum34 must be installed, run '+BASH_TIPS['GREEN']+'`' + ('pip', 'pip3')[sys.version_info > (3, 0)] + ' install enum34`',BASH_TIPS['DEFAULT'])
            err = tuple2str(err)
            raise Exception(err)
        try:
            import serial
            import serial.tools.list_ports
        except ImportError:
            err = (ERROR_MSG,'PySerial must be installed, run '+BASH_TIPS['GREEN']+'`' + ('pip', 'pip3')[sys.version_info > (3, 0)] + ' install pyserial`',BASH_TIPS['DEFAULT'])
            err = tuple2str(err)
            raise Exception(err)

        class TimeoutError(Exception): pass

        class ProgramFileFormat(Enum):
            FMT_BINARY = 0
            FMT_ELF = 1
            FMT_KFPKG = 2

        # AES is from: https://github.com/ricmoo/pyaes, Copyright by Richard Moore
        class AES:
            '''Encapsulates the AES block cipher.
            You generally should not need this. Use the AESModeOfOperation classes
            below instead.'''
            @staticmethod
            def _compact_word(word):
                return (word[0] << 24) | (word[1] << 16) | (word[2] << 8) | word[3]

            # Number of rounds by keysize
            number_of_rounds = {16: 10, 24: 12, 32: 14}

            # Round constant words
            rcon = [ 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91 ]

            # S-box and Inverse S-box (S is for Substitution)
            S = [ 0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76, 0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0, 0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15, 0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75, 0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84, 0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf, 0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8, 0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2, 0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73, 0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb, 0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79, 0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08, 0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a, 0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e, 0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf, 0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16 ]
            Si =[ 0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb, 0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb, 0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e, 0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25, 0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92, 0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84, 0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06, 0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b, 0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73, 0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e, 0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b, 0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4, 0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f, 0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef, 0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61, 0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d ]

            # Transformations for encryption
            T1 = [ 0xc66363a5, 0xf87c7c84, 0xee777799, 0xf67b7b8d, 0xfff2f20d, 0xd66b6bbd, 0xde6f6fb1, 0x91c5c554, 0x60303050, 0x02010103, 0xce6767a9, 0x562b2b7d, 0xe7fefe19, 0xb5d7d762, 0x4dababe6, 0xec76769a, 0x8fcaca45, 0x1f82829d, 0x89c9c940, 0xfa7d7d87, 0xeffafa15, 0xb25959eb, 0x8e4747c9, 0xfbf0f00b, 0x41adadec, 0xb3d4d467, 0x5fa2a2fd, 0x45afafea, 0x239c9cbf, 0x53a4a4f7, 0xe4727296, 0x9bc0c05b, 0x75b7b7c2, 0xe1fdfd1c, 0x3d9393ae, 0x4c26266a, 0x6c36365a, 0x7e3f3f41, 0xf5f7f702, 0x83cccc4f, 0x6834345c, 0x51a5a5f4, 0xd1e5e534, 0xf9f1f108, 0xe2717193, 0xabd8d873, 0x62313153, 0x2a15153f, 0x0804040c, 0x95c7c752, 0x46232365, 0x9dc3c35e, 0x30181828, 0x379696a1, 0x0a05050f, 0x2f9a9ab5, 0x0e070709, 0x24121236, 0x1b80809b, 0xdfe2e23d, 0xcdebeb26, 0x4e272769, 0x7fb2b2cd, 0xea75759f, 0x1209091b, 0x1d83839e, 0x582c2c74, 0x341a1a2e, 0x361b1b2d, 0xdc6e6eb2, 0xb45a5aee, 0x5ba0a0fb, 0xa45252f6, 0x763b3b4d, 0xb7d6d661, 0x7db3b3ce, 0x5229297b, 0xdde3e33e, 0x5e2f2f71, 0x13848497, 0xa65353f5, 0xb9d1d168, 0x00000000, 0xc1eded2c, 0x40202060, 0xe3fcfc1f, 0x79b1b1c8, 0xb65b5bed, 0xd46a6abe, 0x8dcbcb46, 0x67bebed9, 0x7239394b, 0x944a4ade, 0x984c4cd4, 0xb05858e8, 0x85cfcf4a, 0xbbd0d06b, 0xc5efef2a, 0x4faaaae5, 0xedfbfb16, 0x864343c5, 0x9a4d4dd7, 0x66333355, 0x11858594, 0x8a4545cf, 0xe9f9f910, 0x04020206, 0xfe7f7f81, 0xa05050f0, 0x783c3c44, 0x259f9fba, 0x4ba8a8e3, 0xa25151f3, 0x5da3a3fe, 0x804040c0, 0x058f8f8a, 0x3f9292ad, 0x219d9dbc, 0x70383848, 0xf1f5f504, 0x63bcbcdf, 0x77b6b6c1, 0xafdada75, 0x42212163, 0x20101030, 0xe5ffff1a, 0xfdf3f30e, 0xbfd2d26d, 0x81cdcd4c, 0x180c0c14, 0x26131335, 0xc3ecec2f, 0xbe5f5fe1, 0x359797a2, 0x884444cc, 0x2e171739, 0x93c4c457, 0x55a7a7f2, 0xfc7e7e82, 0x7a3d3d47, 0xc86464ac, 0xba5d5de7, 0x3219192b, 0xe6737395, 0xc06060a0, 0x19818198, 0x9e4f4fd1, 0xa3dcdc7f, 0x44222266, 0x542a2a7e, 0x3b9090ab, 0x0b888883, 0x8c4646ca, 0xc7eeee29, 0x6bb8b8d3, 0x2814143c, 0xa7dede79, 0xbc5e5ee2, 0x160b0b1d, 0xaddbdb76, 0xdbe0e03b, 0x64323256, 0x743a3a4e, 0x140a0a1e, 0x924949db, 0x0c06060a, 0x4824246c, 0xb85c5ce4, 0x9fc2c25d, 0xbdd3d36e, 0x43acacef, 0xc46262a6, 0x399191a8, 0x319595a4, 0xd3e4e437, 0xf279798b, 0xd5e7e732, 0x8bc8c843, 0x6e373759, 0xda6d6db7, 0x018d8d8c, 0xb1d5d564, 0x9c4e4ed2, 0x49a9a9e0, 0xd86c6cb4, 0xac5656fa, 0xf3f4f407, 0xcfeaea25, 0xca6565af, 0xf47a7a8e, 0x47aeaee9, 0x10080818, 0x6fbabad5, 0xf0787888, 0x4a25256f, 0x5c2e2e72, 0x381c1c24, 0x57a6a6f1, 0x73b4b4c7, 0x97c6c651, 0xcbe8e823, 0xa1dddd7c, 0xe874749c, 0x3e1f1f21, 0x964b4bdd, 0x61bdbddc, 0x0d8b8b86, 0x0f8a8a85, 0xe0707090, 0x7c3e3e42, 0x71b5b5c4, 0xcc6666aa, 0x904848d8, 0x06030305, 0xf7f6f601, 0x1c0e0e12, 0xc26161a3, 0x6a35355f, 0xae5757f9, 0x69b9b9d0, 0x17868691, 0x99c1c158, 0x3a1d1d27, 0x279e9eb9, 0xd9e1e138, 0xebf8f813, 0x2b9898b3, 0x22111133, 0xd26969bb, 0xa9d9d970, 0x078e8e89, 0x339494a7, 0x2d9b9bb6, 0x3c1e1e22, 0x15878792, 0xc9e9e920, 0x87cece49, 0xaa5555ff, 0x50282878, 0xa5dfdf7a, 0x038c8c8f, 0x59a1a1f8, 0x09898980, 0x1a0d0d17, 0x65bfbfda, 0xd7e6e631, 0x844242c6, 0xd06868b8, 0x824141c3, 0x299999b0, 0x5a2d2d77, 0x1e0f0f11, 0x7bb0b0cb, 0xa85454fc, 0x6dbbbbd6, 0x2c16163a ]
            T2 = [ 0xa5c66363, 0x84f87c7c, 0x99ee7777, 0x8df67b7b, 0x0dfff2f2, 0xbdd66b6b, 0xb1de6f6f, 0x5491c5c5, 0x50603030, 0x03020101, 0xa9ce6767, 0x7d562b2b, 0x19e7fefe, 0x62b5d7d7, 0xe64dabab, 0x9aec7676, 0x458fcaca, 0x9d1f8282, 0x4089c9c9, 0x87fa7d7d, 0x15effafa, 0xebb25959, 0xc98e4747, 0x0bfbf0f0, 0xec41adad, 0x67b3d4d4, 0xfd5fa2a2, 0xea45afaf, 0xbf239c9c, 0xf753a4a4, 0x96e47272, 0x5b9bc0c0, 0xc275b7b7, 0x1ce1fdfd, 0xae3d9393, 0x6a4c2626, 0x5a6c3636, 0x417e3f3f, 0x02f5f7f7, 0x4f83cccc, 0x5c683434, 0xf451a5a5, 0x34d1e5e5, 0x08f9f1f1, 0x93e27171, 0x73abd8d8, 0x53623131, 0x3f2a1515, 0x0c080404, 0x5295c7c7, 0x65462323, 0x5e9dc3c3, 0x28301818, 0xa1379696, 0x0f0a0505, 0xb52f9a9a, 0x090e0707, 0x36241212, 0x9b1b8080, 0x3ddfe2e2, 0x26cdebeb, 0x694e2727, 0xcd7fb2b2, 0x9fea7575, 0x1b120909, 0x9e1d8383, 0x74582c2c, 0x2e341a1a, 0x2d361b1b, 0xb2dc6e6e, 0xeeb45a5a, 0xfb5ba0a0, 0xf6a45252, 0x4d763b3b, 0x61b7d6d6, 0xce7db3b3, 0x7b522929, 0x3edde3e3, 0x715e2f2f, 0x97138484, 0xf5a65353, 0x68b9d1d1, 0x00000000, 0x2cc1eded, 0x60402020, 0x1fe3fcfc, 0xc879b1b1, 0xedb65b5b, 0xbed46a6a, 0x468dcbcb, 0xd967bebe, 0x4b723939, 0xde944a4a, 0xd4984c4c, 0xe8b05858, 0x4a85cfcf, 0x6bbbd0d0, 0x2ac5efef, 0xe54faaaa, 0x16edfbfb, 0xc5864343, 0xd79a4d4d, 0x55663333, 0x94118585, 0xcf8a4545, 0x10e9f9f9, 0x06040202, 0x81fe7f7f, 0xf0a05050, 0x44783c3c, 0xba259f9f, 0xe34ba8a8, 0xf3a25151, 0xfe5da3a3, 0xc0804040, 0x8a058f8f, 0xad3f9292, 0xbc219d9d, 0x48703838, 0x04f1f5f5, 0xdf63bcbc, 0xc177b6b6, 0x75afdada, 0x63422121, 0x30201010, 0x1ae5ffff, 0x0efdf3f3, 0x6dbfd2d2, 0x4c81cdcd, 0x14180c0c, 0x35261313, 0x2fc3ecec, 0xe1be5f5f, 0xa2359797, 0xcc884444, 0x392e1717, 0x5793c4c4, 0xf255a7a7, 0x82fc7e7e, 0x477a3d3d, 0xacc86464, 0xe7ba5d5d, 0x2b321919, 0x95e67373, 0xa0c06060, 0x98198181, 0xd19e4f4f, 0x7fa3dcdc, 0x66442222, 0x7e542a2a, 0xab3b9090, 0x830b8888, 0xca8c4646, 0x29c7eeee, 0xd36bb8b8, 0x3c281414, 0x79a7dede, 0xe2bc5e5e, 0x1d160b0b, 0x76addbdb, 0x3bdbe0e0, 0x56643232, 0x4e743a3a, 0x1e140a0a, 0xdb924949, 0x0a0c0606, 0x6c482424, 0xe4b85c5c, 0x5d9fc2c2, 0x6ebdd3d3, 0xef43acac, 0xa6c46262, 0xa8399191, 0xa4319595, 0x37d3e4e4, 0x8bf27979, 0x32d5e7e7, 0x438bc8c8, 0x596e3737, 0xb7da6d6d, 0x8c018d8d, 0x64b1d5d5, 0xd29c4e4e, 0xe049a9a9, 0xb4d86c6c, 0xfaac5656, 0x07f3f4f4, 0x25cfeaea, 0xafca6565, 0x8ef47a7a, 0xe947aeae, 0x18100808, 0xd56fbaba, 0x88f07878, 0x6f4a2525, 0x725c2e2e, 0x24381c1c, 0xf157a6a6, 0xc773b4b4, 0x5197c6c6, 0x23cbe8e8, 0x7ca1dddd, 0x9ce87474, 0x213e1f1f, 0xdd964b4b, 0xdc61bdbd, 0x860d8b8b, 0x850f8a8a, 0x90e07070, 0x427c3e3e, 0xc471b5b5, 0xaacc6666, 0xd8904848, 0x05060303, 0x01f7f6f6, 0x121c0e0e, 0xa3c26161, 0x5f6a3535, 0xf9ae5757, 0xd069b9b9, 0x91178686, 0x5899c1c1, 0x273a1d1d, 0xb9279e9e, 0x38d9e1e1, 0x13ebf8f8, 0xb32b9898, 0x33221111, 0xbbd26969, 0x70a9d9d9, 0x89078e8e, 0xa7339494, 0xb62d9b9b, 0x223c1e1e, 0x92158787, 0x20c9e9e9, 0x4987cece, 0xffaa5555, 0x78502828, 0x7aa5dfdf, 0x8f038c8c, 0xf859a1a1, 0x80098989, 0x171a0d0d, 0xda65bfbf, 0x31d7e6e6, 0xc6844242, 0xb8d06868, 0xc3824141, 0xb0299999, 0x775a2d2d, 0x111e0f0f, 0xcb7bb0b0, 0xfca85454, 0xd66dbbbb, 0x3a2c1616 ]
            T3 = [ 0x63a5c663, 0x7c84f87c, 0x7799ee77, 0x7b8df67b, 0xf20dfff2, 0x6bbdd66b, 0x6fb1de6f, 0xc55491c5, 0x30506030, 0x01030201, 0x67a9ce67, 0x2b7d562b, 0xfe19e7fe, 0xd762b5d7, 0xabe64dab, 0x769aec76, 0xca458fca, 0x829d1f82, 0xc94089c9, 0x7d87fa7d, 0xfa15effa, 0x59ebb259, 0x47c98e47, 0xf00bfbf0, 0xadec41ad, 0xd467b3d4, 0xa2fd5fa2, 0xafea45af, 0x9cbf239c, 0xa4f753a4, 0x7296e472, 0xc05b9bc0, 0xb7c275b7, 0xfd1ce1fd, 0x93ae3d93, 0x266a4c26, 0x365a6c36, 0x3f417e3f, 0xf702f5f7, 0xcc4f83cc, 0x345c6834, 0xa5f451a5, 0xe534d1e5, 0xf108f9f1, 0x7193e271, 0xd873abd8, 0x31536231, 0x153f2a15, 0x040c0804, 0xc75295c7, 0x23654623, 0xc35e9dc3, 0x18283018, 0x96a13796, 0x050f0a05, 0x9ab52f9a, 0x07090e07, 0x12362412, 0x809b1b80, 0xe23ddfe2, 0xeb26cdeb, 0x27694e27, 0xb2cd7fb2, 0x759fea75, 0x091b1209, 0x839e1d83, 0x2c74582c, 0x1a2e341a, 0x1b2d361b, 0x6eb2dc6e, 0x5aeeb45a, 0xa0fb5ba0, 0x52f6a452, 0x3b4d763b, 0xd661b7d6, 0xb3ce7db3, 0x297b5229, 0xe33edde3, 0x2f715e2f, 0x84971384, 0x53f5a653, 0xd168b9d1, 0x00000000, 0xed2cc1ed, 0x20604020, 0xfc1fe3fc, 0xb1c879b1, 0x5bedb65b, 0x6abed46a, 0xcb468dcb, 0xbed967be, 0x394b7239, 0x4ade944a, 0x4cd4984c, 0x58e8b058, 0xcf4a85cf, 0xd06bbbd0, 0xef2ac5ef, 0xaae54faa, 0xfb16edfb, 0x43c58643, 0x4dd79a4d, 0x33556633, 0x85941185, 0x45cf8a45, 0xf910e9f9, 0x02060402, 0x7f81fe7f, 0x50f0a050, 0x3c44783c, 0x9fba259f, 0xa8e34ba8, 0x51f3a251, 0xa3fe5da3, 0x40c08040, 0x8f8a058f, 0x92ad3f92, 0x9dbc219d, 0x38487038, 0xf504f1f5, 0xbcdf63bc, 0xb6c177b6, 0xda75afda, 0x21634221, 0x10302010, 0xff1ae5ff, 0xf30efdf3, 0xd26dbfd2, 0xcd4c81cd, 0x0c14180c, 0x13352613, 0xec2fc3ec, 0x5fe1be5f, 0x97a23597, 0x44cc8844, 0x17392e17, 0xc45793c4, 0xa7f255a7, 0x7e82fc7e, 0x3d477a3d, 0x64acc864, 0x5de7ba5d, 0x192b3219, 0x7395e673, 0x60a0c060, 0x81981981, 0x4fd19e4f, 0xdc7fa3dc, 0x22664422, 0x2a7e542a, 0x90ab3b90, 0x88830b88, 0x46ca8c46, 0xee29c7ee, 0xb8d36bb8, 0x143c2814, 0xde79a7de, 0x5ee2bc5e, 0x0b1d160b, 0xdb76addb, 0xe03bdbe0, 0x32566432, 0x3a4e743a, 0x0a1e140a, 0x49db9249, 0x060a0c06, 0x246c4824, 0x5ce4b85c, 0xc25d9fc2, 0xd36ebdd3, 0xacef43ac, 0x62a6c462, 0x91a83991, 0x95a43195, 0xe437d3e4, 0x798bf279, 0xe732d5e7, 0xc8438bc8, 0x37596e37, 0x6db7da6d, 0x8d8c018d, 0xd564b1d5, 0x4ed29c4e, 0xa9e049a9, 0x6cb4d86c, 0x56faac56, 0xf407f3f4, 0xea25cfea, 0x65afca65, 0x7a8ef47a, 0xaee947ae, 0x08181008, 0xbad56fba, 0x7888f078, 0x256f4a25, 0x2e725c2e, 0x1c24381c, 0xa6f157a6, 0xb4c773b4, 0xc65197c6, 0xe823cbe8, 0xdd7ca1dd, 0x749ce874, 0x1f213e1f, 0x4bdd964b, 0xbddc61bd, 0x8b860d8b, 0x8a850f8a, 0x7090e070, 0x3e427c3e, 0xb5c471b5, 0x66aacc66, 0x48d89048, 0x03050603, 0xf601f7f6, 0x0e121c0e, 0x61a3c261, 0x355f6a35, 0x57f9ae57, 0xb9d069b9, 0x86911786, 0xc15899c1, 0x1d273a1d, 0x9eb9279e, 0xe138d9e1, 0xf813ebf8, 0x98b32b98, 0x11332211, 0x69bbd269, 0xd970a9d9, 0x8e89078e, 0x94a73394, 0x9bb62d9b, 0x1e223c1e, 0x87921587, 0xe920c9e9, 0xce4987ce, 0x55ffaa55, 0x28785028, 0xdf7aa5df, 0x8c8f038c, 0xa1f859a1, 0x89800989, 0x0d171a0d, 0xbfda65bf, 0xe631d7e6, 0x42c68442, 0x68b8d068, 0x41c38241, 0x99b02999, 0x2d775a2d, 0x0f111e0f, 0xb0cb7bb0, 0x54fca854, 0xbbd66dbb, 0x163a2c16 ]
            T4 = [ 0x6363a5c6, 0x7c7c84f8, 0x777799ee, 0x7b7b8df6, 0xf2f20dff, 0x6b6bbdd6, 0x6f6fb1de, 0xc5c55491, 0x30305060, 0x01010302, 0x6767a9ce, 0x2b2b7d56, 0xfefe19e7, 0xd7d762b5, 0xababe64d, 0x76769aec, 0xcaca458f, 0x82829d1f, 0xc9c94089, 0x7d7d87fa, 0xfafa15ef, 0x5959ebb2, 0x4747c98e, 0xf0f00bfb, 0xadadec41, 0xd4d467b3, 0xa2a2fd5f, 0xafafea45, 0x9c9cbf23, 0xa4a4f753, 0x727296e4, 0xc0c05b9b, 0xb7b7c275, 0xfdfd1ce1, 0x9393ae3d, 0x26266a4c, 0x36365a6c, 0x3f3f417e, 0xf7f702f5, 0xcccc4f83, 0x34345c68, 0xa5a5f451, 0xe5e534d1, 0xf1f108f9, 0x717193e2, 0xd8d873ab, 0x31315362, 0x15153f2a, 0x04040c08, 0xc7c75295, 0x23236546, 0xc3c35e9d, 0x18182830, 0x9696a137, 0x05050f0a, 0x9a9ab52f, 0x0707090e, 0x12123624, 0x80809b1b, 0xe2e23ddf, 0xebeb26cd, 0x2727694e, 0xb2b2cd7f, 0x75759fea, 0x09091b12, 0x83839e1d, 0x2c2c7458, 0x1a1a2e34, 0x1b1b2d36, 0x6e6eb2dc, 0x5a5aeeb4, 0xa0a0fb5b, 0x5252f6a4, 0x3b3b4d76, 0xd6d661b7, 0xb3b3ce7d, 0x29297b52, 0xe3e33edd, 0x2f2f715e, 0x84849713, 0x5353f5a6, 0xd1d168b9, 0x00000000, 0xeded2cc1, 0x20206040, 0xfcfc1fe3, 0xb1b1c879, 0x5b5bedb6, 0x6a6abed4, 0xcbcb468d, 0xbebed967, 0x39394b72, 0x4a4ade94, 0x4c4cd498, 0x5858e8b0, 0xcfcf4a85, 0xd0d06bbb, 0xefef2ac5, 0xaaaae54f, 0xfbfb16ed, 0x4343c586, 0x4d4dd79a, 0x33335566, 0x85859411, 0x4545cf8a, 0xf9f910e9, 0x02020604, 0x7f7f81fe, 0x5050f0a0, 0x3c3c4478, 0x9f9fba25, 0xa8a8e34b, 0x5151f3a2, 0xa3a3fe5d, 0x4040c080, 0x8f8f8a05, 0x9292ad3f, 0x9d9dbc21, 0x38384870, 0xf5f504f1, 0xbcbcdf63, 0xb6b6c177, 0xdada75af, 0x21216342, 0x10103020, 0xffff1ae5, 0xf3f30efd, 0xd2d26dbf, 0xcdcd4c81, 0x0c0c1418, 0x13133526, 0xecec2fc3, 0x5f5fe1be, 0x9797a235, 0x4444cc88, 0x1717392e, 0xc4c45793, 0xa7a7f255, 0x7e7e82fc, 0x3d3d477a, 0x6464acc8, 0x5d5de7ba, 0x19192b32, 0x737395e6, 0x6060a0c0, 0x81819819, 0x4f4fd19e, 0xdcdc7fa3, 0x22226644, 0x2a2a7e54, 0x9090ab3b, 0x8888830b, 0x4646ca8c, 0xeeee29c7, 0xb8b8d36b, 0x14143c28, 0xdede79a7, 0x5e5ee2bc, 0x0b0b1d16, 0xdbdb76ad, 0xe0e03bdb, 0x32325664, 0x3a3a4e74, 0x0a0a1e14, 0x4949db92, 0x06060a0c, 0x24246c48, 0x5c5ce4b8, 0xc2c25d9f, 0xd3d36ebd, 0xacacef43, 0x6262a6c4, 0x9191a839, 0x9595a431, 0xe4e437d3, 0x79798bf2, 0xe7e732d5, 0xc8c8438b, 0x3737596e, 0x6d6db7da, 0x8d8d8c01, 0xd5d564b1, 0x4e4ed29c, 0xa9a9e049, 0x6c6cb4d8, 0x5656faac, 0xf4f407f3, 0xeaea25cf, 0x6565afca, 0x7a7a8ef4, 0xaeaee947, 0x08081810, 0xbabad56f, 0x787888f0, 0x25256f4a, 0x2e2e725c, 0x1c1c2438, 0xa6a6f157, 0xb4b4c773, 0xc6c65197, 0xe8e823cb, 0xdddd7ca1, 0x74749ce8, 0x1f1f213e, 0x4b4bdd96, 0xbdbddc61, 0x8b8b860d, 0x8a8a850f, 0x707090e0, 0x3e3e427c, 0xb5b5c471, 0x6666aacc, 0x4848d890, 0x03030506, 0xf6f601f7, 0x0e0e121c, 0x6161a3c2, 0x35355f6a, 0x5757f9ae, 0xb9b9d069, 0x86869117, 0xc1c15899, 0x1d1d273a, 0x9e9eb927, 0xe1e138d9, 0xf8f813eb, 0x9898b32b, 0x11113322, 0x6969bbd2, 0xd9d970a9, 0x8e8e8907, 0x9494a733, 0x9b9bb62d, 0x1e1e223c, 0x87879215, 0xe9e920c9, 0xcece4987, 0x5555ffaa, 0x28287850, 0xdfdf7aa5, 0x8c8c8f03, 0xa1a1f859, 0x89898009, 0x0d0d171a, 0xbfbfda65, 0xe6e631d7, 0x4242c684, 0x6868b8d0, 0x4141c382, 0x9999b029, 0x2d2d775a, 0x0f0f111e, 0xb0b0cb7b, 0x5454fca8, 0xbbbbd66d, 0x16163a2c ]

            # Transformations for decryption
            T5 = [ 0x51f4a750, 0x7e416553, 0x1a17a4c3, 0x3a275e96, 0x3bab6bcb, 0x1f9d45f1, 0xacfa58ab, 0x4be30393, 0x2030fa55, 0xad766df6, 0x88cc7691, 0xf5024c25, 0x4fe5d7fc, 0xc52acbd7, 0x26354480, 0xb562a38f, 0xdeb15a49, 0x25ba1b67, 0x45ea0e98, 0x5dfec0e1, 0xc32f7502, 0x814cf012, 0x8d4697a3, 0x6bd3f9c6, 0x038f5fe7, 0x15929c95, 0xbf6d7aeb, 0x955259da, 0xd4be832d, 0x587421d3, 0x49e06929, 0x8ec9c844, 0x75c2896a, 0xf48e7978, 0x99583e6b, 0x27b971dd, 0xbee14fb6, 0xf088ad17, 0xc920ac66, 0x7dce3ab4, 0x63df4a18, 0xe51a3182, 0x97513360, 0x62537f45, 0xb16477e0, 0xbb6bae84, 0xfe81a01c, 0xf9082b94, 0x70486858, 0x8f45fd19, 0x94de6c87, 0x527bf8b7, 0xab73d323, 0x724b02e2, 0xe31f8f57, 0x6655ab2a, 0xb2eb2807, 0x2fb5c203, 0x86c57b9a, 0xd33708a5, 0x302887f2, 0x23bfa5b2, 0x02036aba, 0xed16825c, 0x8acf1c2b, 0xa779b492, 0xf307f2f0, 0x4e69e2a1, 0x65daf4cd, 0x0605bed5, 0xd134621f, 0xc4a6fe8a, 0x342e539d, 0xa2f355a0, 0x058ae132, 0xa4f6eb75, 0x0b83ec39, 0x4060efaa, 0x5e719f06, 0xbd6e1051, 0x3e218af9, 0x96dd063d, 0xdd3e05ae, 0x4de6bd46, 0x91548db5, 0x71c45d05, 0x0406d46f, 0x605015ff, 0x1998fb24, 0xd6bde997, 0x894043cc, 0x67d99e77, 0xb0e842bd, 0x07898b88, 0xe7195b38, 0x79c8eedb, 0xa17c0a47, 0x7c420fe9, 0xf8841ec9, 0x00000000, 0x09808683, 0x322bed48, 0x1e1170ac, 0x6c5a724e, 0xfd0efffb, 0x0f853856, 0x3daed51e, 0x362d3927, 0x0a0fd964, 0x685ca621, 0x9b5b54d1, 0x24362e3a, 0x0c0a67b1, 0x9357e70f, 0xb4ee96d2, 0x1b9b919e, 0x80c0c54f, 0x61dc20a2, 0x5a774b69, 0x1c121a16, 0xe293ba0a, 0xc0a02ae5, 0x3c22e043, 0x121b171d, 0x0e090d0b, 0xf28bc7ad, 0x2db6a8b9, 0x141ea9c8, 0x57f11985, 0xaf75074c, 0xee99ddbb, 0xa37f60fd, 0xf701269f, 0x5c72f5bc, 0x44663bc5, 0x5bfb7e34, 0x8b432976, 0xcb23c6dc, 0xb6edfc68, 0xb8e4f163, 0xd731dcca, 0x42638510, 0x13972240, 0x84c61120, 0x854a247d, 0xd2bb3df8, 0xaef93211, 0xc729a16d, 0x1d9e2f4b, 0xdcb230f3, 0x0d8652ec, 0x77c1e3d0, 0x2bb3166c, 0xa970b999, 0x119448fa, 0x47e96422, 0xa8fc8cc4, 0xa0f03f1a, 0x567d2cd8, 0x223390ef, 0x87494ec7, 0xd938d1c1, 0x8ccaa2fe, 0x98d40b36, 0xa6f581cf, 0xa57ade28, 0xdab78e26, 0x3fadbfa4, 0x2c3a9de4, 0x5078920d, 0x6a5fcc9b, 0x547e4662, 0xf68d13c2, 0x90d8b8e8, 0x2e39f75e, 0x82c3aff5, 0x9f5d80be, 0x69d0937c, 0x6fd52da9, 0xcf2512b3, 0xc8ac993b, 0x10187da7, 0xe89c636e, 0xdb3bbb7b, 0xcd267809, 0x6e5918f4, 0xec9ab701, 0x834f9aa8, 0xe6956e65, 0xaaffe67e, 0x21bccf08, 0xef15e8e6, 0xbae79bd9, 0x4a6f36ce, 0xea9f09d4, 0x29b07cd6, 0x31a4b2af, 0x2a3f2331, 0xc6a59430, 0x35a266c0, 0x744ebc37, 0xfc82caa6, 0xe090d0b0, 0x33a7d815, 0xf104984a, 0x41ecdaf7, 0x7fcd500e, 0x1791f62f, 0x764dd68d, 0x43efb04d, 0xccaa4d54, 0xe49604df, 0x9ed1b5e3, 0x4c6a881b, 0xc12c1fb8, 0x4665517f, 0x9d5eea04, 0x018c355d, 0xfa877473, 0xfb0b412e, 0xb3671d5a, 0x92dbd252, 0xe9105633, 0x6dd64713, 0x9ad7618c, 0x37a10c7a, 0x59f8148e, 0xeb133c89, 0xcea927ee, 0xb761c935, 0xe11ce5ed, 0x7a47b13c, 0x9cd2df59, 0x55f2733f, 0x1814ce79, 0x73c737bf, 0x53f7cdea, 0x5ffdaa5b, 0xdf3d6f14, 0x7844db86, 0xcaaff381, 0xb968c43e, 0x3824342c, 0xc2a3405f, 0x161dc372, 0xbce2250c, 0x283c498b, 0xff0d9541, 0x39a80171, 0x080cb3de, 0xd8b4e49c, 0x6456c190, 0x7bcb8461, 0xd532b670, 0x486c5c74, 0xd0b85742 ]
            T6 = [ 0x5051f4a7, 0x537e4165, 0xc31a17a4, 0x963a275e, 0xcb3bab6b, 0xf11f9d45, 0xabacfa58, 0x934be303, 0x552030fa, 0xf6ad766d, 0x9188cc76, 0x25f5024c, 0xfc4fe5d7, 0xd7c52acb, 0x80263544, 0x8fb562a3, 0x49deb15a, 0x6725ba1b, 0x9845ea0e, 0xe15dfec0, 0x02c32f75, 0x12814cf0, 0xa38d4697, 0xc66bd3f9, 0xe7038f5f, 0x9515929c, 0xebbf6d7a, 0xda955259, 0x2dd4be83, 0xd3587421, 0x2949e069, 0x448ec9c8, 0x6a75c289, 0x78f48e79, 0x6b99583e, 0xdd27b971, 0xb6bee14f, 0x17f088ad, 0x66c920ac, 0xb47dce3a, 0x1863df4a, 0x82e51a31, 0x60975133, 0x4562537f, 0xe0b16477, 0x84bb6bae, 0x1cfe81a0, 0x94f9082b, 0x58704868, 0x198f45fd, 0x8794de6c, 0xb7527bf8, 0x23ab73d3, 0xe2724b02, 0x57e31f8f, 0x2a6655ab, 0x07b2eb28, 0x032fb5c2, 0x9a86c57b, 0xa5d33708, 0xf2302887, 0xb223bfa5, 0xba02036a, 0x5ced1682, 0x2b8acf1c, 0x92a779b4, 0xf0f307f2, 0xa14e69e2, 0xcd65daf4, 0xd50605be, 0x1fd13462, 0x8ac4a6fe, 0x9d342e53, 0xa0a2f355, 0x32058ae1, 0x75a4f6eb, 0x390b83ec, 0xaa4060ef, 0x065e719f, 0x51bd6e10, 0xf93e218a, 0x3d96dd06, 0xaedd3e05, 0x464de6bd, 0xb591548d, 0x0571c45d, 0x6f0406d4, 0xff605015, 0x241998fb, 0x97d6bde9, 0xcc894043, 0x7767d99e, 0xbdb0e842, 0x8807898b, 0x38e7195b, 0xdb79c8ee, 0x47a17c0a, 0xe97c420f, 0xc9f8841e, 0x00000000, 0x83098086, 0x48322bed, 0xac1e1170, 0x4e6c5a72, 0xfbfd0eff, 0x560f8538, 0x1e3daed5, 0x27362d39, 0x640a0fd9, 0x21685ca6, 0xd19b5b54, 0x3a24362e, 0xb10c0a67, 0x0f9357e7, 0xd2b4ee96, 0x9e1b9b91, 0x4f80c0c5, 0xa261dc20, 0x695a774b, 0x161c121a, 0x0ae293ba, 0xe5c0a02a, 0x433c22e0, 0x1d121b17, 0x0b0e090d, 0xadf28bc7, 0xb92db6a8, 0xc8141ea9, 0x8557f119, 0x4caf7507, 0xbbee99dd, 0xfda37f60, 0x9ff70126, 0xbc5c72f5, 0xc544663b, 0x345bfb7e, 0x768b4329, 0xdccb23c6, 0x68b6edfc, 0x63b8e4f1, 0xcad731dc, 0x10426385, 0x40139722, 0x2084c611, 0x7d854a24, 0xf8d2bb3d, 0x11aef932, 0x6dc729a1, 0x4b1d9e2f, 0xf3dcb230, 0xec0d8652, 0xd077c1e3, 0x6c2bb316, 0x99a970b9, 0xfa119448, 0x2247e964, 0xc4a8fc8c, 0x1aa0f03f, 0xd8567d2c, 0xef223390, 0xc787494e, 0xc1d938d1, 0xfe8ccaa2, 0x3698d40b, 0xcfa6f581, 0x28a57ade, 0x26dab78e, 0xa43fadbf, 0xe42c3a9d, 0x0d507892, 0x9b6a5fcc, 0x62547e46, 0xc2f68d13, 0xe890d8b8, 0x5e2e39f7, 0xf582c3af, 0xbe9f5d80, 0x7c69d093, 0xa96fd52d, 0xb3cf2512, 0x3bc8ac99, 0xa710187d, 0x6ee89c63, 0x7bdb3bbb, 0x09cd2678, 0xf46e5918, 0x01ec9ab7, 0xa8834f9a, 0x65e6956e, 0x7eaaffe6, 0x0821bccf, 0xe6ef15e8, 0xd9bae79b, 0xce4a6f36, 0xd4ea9f09, 0xd629b07c, 0xaf31a4b2, 0x312a3f23, 0x30c6a594, 0xc035a266, 0x37744ebc, 0xa6fc82ca, 0xb0e090d0, 0x1533a7d8, 0x4af10498, 0xf741ecda, 0x0e7fcd50, 0x2f1791f6, 0x8d764dd6, 0x4d43efb0, 0x54ccaa4d, 0xdfe49604, 0xe39ed1b5, 0x1b4c6a88, 0xb8c12c1f, 0x7f466551, 0x049d5eea, 0x5d018c35, 0x73fa8774, 0x2efb0b41, 0x5ab3671d, 0x5292dbd2, 0x33e91056, 0x136dd647, 0x8c9ad761, 0x7a37a10c, 0x8e59f814, 0x89eb133c, 0xeecea927, 0x35b761c9, 0xede11ce5, 0x3c7a47b1, 0x599cd2df, 0x3f55f273, 0x791814ce, 0xbf73c737, 0xea53f7cd, 0x5b5ffdaa, 0x14df3d6f, 0x867844db, 0x81caaff3, 0x3eb968c4, 0x2c382434, 0x5fc2a340, 0x72161dc3, 0x0cbce225, 0x8b283c49, 0x41ff0d95, 0x7139a801, 0xde080cb3, 0x9cd8b4e4, 0x906456c1, 0x617bcb84, 0x70d532b6, 0x74486c5c, 0x42d0b857 ]
            T7 = [ 0xa75051f4, 0x65537e41, 0xa4c31a17, 0x5e963a27, 0x6bcb3bab, 0x45f11f9d, 0x58abacfa, 0x03934be3, 0xfa552030, 0x6df6ad76, 0x769188cc, 0x4c25f502, 0xd7fc4fe5, 0xcbd7c52a, 0x44802635, 0xa38fb562, 0x5a49deb1, 0x1b6725ba, 0x0e9845ea, 0xc0e15dfe, 0x7502c32f, 0xf012814c, 0x97a38d46, 0xf9c66bd3, 0x5fe7038f, 0x9c951592, 0x7aebbf6d, 0x59da9552, 0x832dd4be, 0x21d35874, 0x692949e0, 0xc8448ec9, 0x896a75c2, 0x7978f48e, 0x3e6b9958, 0x71dd27b9, 0x4fb6bee1, 0xad17f088, 0xac66c920, 0x3ab47dce, 0x4a1863df, 0x3182e51a, 0x33609751, 0x7f456253, 0x77e0b164, 0xae84bb6b, 0xa01cfe81, 0x2b94f908, 0x68587048, 0xfd198f45, 0x6c8794de, 0xf8b7527b, 0xd323ab73, 0x02e2724b, 0x8f57e31f, 0xab2a6655, 0x2807b2eb, 0xc2032fb5, 0x7b9a86c5, 0x08a5d337, 0x87f23028, 0xa5b223bf, 0x6aba0203, 0x825ced16, 0x1c2b8acf, 0xb492a779, 0xf2f0f307, 0xe2a14e69, 0xf4cd65da, 0xbed50605, 0x621fd134, 0xfe8ac4a6, 0x539d342e, 0x55a0a2f3, 0xe132058a, 0xeb75a4f6, 0xec390b83, 0xefaa4060, 0x9f065e71, 0x1051bd6e, 0x8af93e21, 0x063d96dd, 0x05aedd3e, 0xbd464de6, 0x8db59154, 0x5d0571c4, 0xd46f0406, 0x15ff6050, 0xfb241998, 0xe997d6bd, 0x43cc8940, 0x9e7767d9, 0x42bdb0e8, 0x8b880789, 0x5b38e719, 0xeedb79c8, 0x0a47a17c, 0x0fe97c42, 0x1ec9f884, 0x00000000, 0x86830980, 0xed48322b, 0x70ac1e11, 0x724e6c5a, 0xfffbfd0e, 0x38560f85, 0xd51e3dae, 0x3927362d, 0xd9640a0f, 0xa621685c, 0x54d19b5b, 0x2e3a2436, 0x67b10c0a, 0xe70f9357, 0x96d2b4ee, 0x919e1b9b, 0xc54f80c0, 0x20a261dc, 0x4b695a77, 0x1a161c12, 0xba0ae293, 0x2ae5c0a0, 0xe0433c22, 0x171d121b, 0x0d0b0e09, 0xc7adf28b, 0xa8b92db6, 0xa9c8141e, 0x198557f1, 0x074caf75, 0xddbbee99, 0x60fda37f, 0x269ff701, 0xf5bc5c72, 0x3bc54466, 0x7e345bfb, 0x29768b43, 0xc6dccb23, 0xfc68b6ed, 0xf163b8e4, 0xdccad731, 0x85104263, 0x22401397, 0x112084c6, 0x247d854a, 0x3df8d2bb, 0x3211aef9, 0xa16dc729, 0x2f4b1d9e, 0x30f3dcb2, 0x52ec0d86, 0xe3d077c1, 0x166c2bb3, 0xb999a970, 0x48fa1194, 0x642247e9, 0x8cc4a8fc, 0x3f1aa0f0, 0x2cd8567d, 0x90ef2233, 0x4ec78749, 0xd1c1d938, 0xa2fe8cca, 0x0b3698d4, 0x81cfa6f5, 0xde28a57a, 0x8e26dab7, 0xbfa43fad, 0x9de42c3a, 0x920d5078, 0xcc9b6a5f, 0x4662547e, 0x13c2f68d, 0xb8e890d8, 0xf75e2e39, 0xaff582c3, 0x80be9f5d, 0x937c69d0, 0x2da96fd5, 0x12b3cf25, 0x993bc8ac, 0x7da71018, 0x636ee89c, 0xbb7bdb3b, 0x7809cd26, 0x18f46e59, 0xb701ec9a, 0x9aa8834f, 0x6e65e695, 0xe67eaaff, 0xcf0821bc, 0xe8e6ef15, 0x9bd9bae7, 0x36ce4a6f, 0x09d4ea9f, 0x7cd629b0, 0xb2af31a4, 0x23312a3f, 0x9430c6a5, 0x66c035a2, 0xbc37744e, 0xcaa6fc82, 0xd0b0e090, 0xd81533a7, 0x984af104, 0xdaf741ec, 0x500e7fcd, 0xf62f1791, 0xd68d764d, 0xb04d43ef, 0x4d54ccaa, 0x04dfe496, 0xb5e39ed1, 0x881b4c6a, 0x1fb8c12c, 0x517f4665, 0xea049d5e, 0x355d018c, 0x7473fa87, 0x412efb0b, 0x1d5ab367, 0xd25292db, 0x5633e910, 0x47136dd6, 0x618c9ad7, 0x0c7a37a1, 0x148e59f8, 0x3c89eb13, 0x27eecea9, 0xc935b761, 0xe5ede11c, 0xb13c7a47, 0xdf599cd2, 0x733f55f2, 0xce791814, 0x37bf73c7, 0xcdea53f7, 0xaa5b5ffd, 0x6f14df3d, 0xdb867844, 0xf381caaf, 0xc43eb968, 0x342c3824, 0x405fc2a3, 0xc372161d, 0x250cbce2, 0x498b283c, 0x9541ff0d, 0x017139a8, 0xb3de080c, 0xe49cd8b4, 0xc1906456, 0x84617bcb, 0xb670d532, 0x5c74486c, 0x5742d0b8 ]
            T8 = [ 0xf4a75051, 0x4165537e, 0x17a4c31a, 0x275e963a, 0xab6bcb3b, 0x9d45f11f, 0xfa58abac, 0xe303934b, 0x30fa5520, 0x766df6ad, 0xcc769188, 0x024c25f5, 0xe5d7fc4f, 0x2acbd7c5, 0x35448026, 0x62a38fb5, 0xb15a49de, 0xba1b6725, 0xea0e9845, 0xfec0e15d, 0x2f7502c3, 0x4cf01281, 0x4697a38d, 0xd3f9c66b, 0x8f5fe703, 0x929c9515, 0x6d7aebbf, 0x5259da95, 0xbe832dd4, 0x7421d358, 0xe0692949, 0xc9c8448e, 0xc2896a75, 0x8e7978f4, 0x583e6b99, 0xb971dd27, 0xe14fb6be, 0x88ad17f0, 0x20ac66c9, 0xce3ab47d, 0xdf4a1863, 0x1a3182e5, 0x51336097, 0x537f4562, 0x6477e0b1, 0x6bae84bb, 0x81a01cfe, 0x082b94f9, 0x48685870, 0x45fd198f, 0xde6c8794, 0x7bf8b752, 0x73d323ab, 0x4b02e272, 0x1f8f57e3, 0x55ab2a66, 0xeb2807b2, 0xb5c2032f, 0xc57b9a86, 0x3708a5d3, 0x2887f230, 0xbfa5b223, 0x036aba02, 0x16825ced, 0xcf1c2b8a, 0x79b492a7, 0x07f2f0f3, 0x69e2a14e, 0xdaf4cd65, 0x05bed506, 0x34621fd1, 0xa6fe8ac4, 0x2e539d34, 0xf355a0a2, 0x8ae13205, 0xf6eb75a4, 0x83ec390b, 0x60efaa40, 0x719f065e, 0x6e1051bd, 0x218af93e, 0xdd063d96, 0x3e05aedd, 0xe6bd464d, 0x548db591, 0xc45d0571, 0x06d46f04, 0x5015ff60, 0x98fb2419, 0xbde997d6, 0x4043cc89, 0xd99e7767, 0xe842bdb0, 0x898b8807, 0x195b38e7, 0xc8eedb79, 0x7c0a47a1, 0x420fe97c, 0x841ec9f8, 0x00000000, 0x80868309, 0x2bed4832, 0x1170ac1e, 0x5a724e6c, 0x0efffbfd, 0x8538560f, 0xaed51e3d, 0x2d392736, 0x0fd9640a, 0x5ca62168, 0x5b54d19b, 0x362e3a24, 0x0a67b10c, 0x57e70f93, 0xee96d2b4, 0x9b919e1b, 0xc0c54f80, 0xdc20a261, 0x774b695a, 0x121a161c, 0x93ba0ae2, 0xa02ae5c0, 0x22e0433c, 0x1b171d12, 0x090d0b0e, 0x8bc7adf2, 0xb6a8b92d, 0x1ea9c814, 0xf1198557, 0x75074caf, 0x99ddbbee, 0x7f60fda3, 0x01269ff7, 0x72f5bc5c, 0x663bc544, 0xfb7e345b, 0x4329768b, 0x23c6dccb, 0xedfc68b6, 0xe4f163b8, 0x31dccad7, 0x63851042, 0x97224013, 0xc6112084, 0x4a247d85, 0xbb3df8d2, 0xf93211ae, 0x29a16dc7, 0x9e2f4b1d, 0xb230f3dc, 0x8652ec0d, 0xc1e3d077, 0xb3166c2b, 0x70b999a9, 0x9448fa11, 0xe9642247, 0xfc8cc4a8, 0xf03f1aa0, 0x7d2cd856, 0x3390ef22, 0x494ec787, 0x38d1c1d9, 0xcaa2fe8c, 0xd40b3698, 0xf581cfa6, 0x7ade28a5, 0xb78e26da, 0xadbfa43f, 0x3a9de42c, 0x78920d50, 0x5fcc9b6a, 0x7e466254, 0x8d13c2f6, 0xd8b8e890, 0x39f75e2e, 0xc3aff582, 0x5d80be9f, 0xd0937c69, 0xd52da96f, 0x2512b3cf, 0xac993bc8, 0x187da710, 0x9c636ee8, 0x3bbb7bdb, 0x267809cd, 0x5918f46e, 0x9ab701ec, 0x4f9aa883, 0x956e65e6, 0xffe67eaa, 0xbccf0821, 0x15e8e6ef, 0xe79bd9ba, 0x6f36ce4a, 0x9f09d4ea, 0xb07cd629, 0xa4b2af31, 0x3f23312a, 0xa59430c6, 0xa266c035, 0x4ebc3774, 0x82caa6fc, 0x90d0b0e0, 0xa7d81533, 0x04984af1, 0xecdaf741, 0xcd500e7f, 0x91f62f17, 0x4dd68d76, 0xefb04d43, 0xaa4d54cc, 0x9604dfe4, 0xd1b5e39e, 0x6a881b4c, 0x2c1fb8c1, 0x65517f46, 0x5eea049d, 0x8c355d01, 0x877473fa, 0x0b412efb, 0x671d5ab3, 0xdbd25292, 0x105633e9, 0xd647136d, 0xd7618c9a, 0xa10c7a37, 0xf8148e59, 0x133c89eb, 0xa927eece, 0x61c935b7, 0x1ce5ede1, 0x47b13c7a, 0xd2df599c, 0xf2733f55, 0x14ce7918, 0xc737bf73, 0xf7cdea53, 0xfdaa5b5f, 0x3d6f14df, 0x44db8678, 0xaff381ca, 0x68c43eb9, 0x24342c38, 0xa3405fc2, 0x1dc37216, 0xe2250cbc, 0x3c498b28, 0x0d9541ff, 0xa8017139, 0x0cb3de08, 0xb4e49cd8, 0x56c19064, 0xcb84617b, 0x32b670d5, 0x6c5c7448, 0xb85742d0 ]

            # Transformations for decryption key expansion
            U1 = [ 0x00000000, 0x0e090d0b, 0x1c121a16, 0x121b171d, 0x3824342c, 0x362d3927, 0x24362e3a, 0x2a3f2331, 0x70486858, 0x7e416553, 0x6c5a724e, 0x62537f45, 0x486c5c74, 0x4665517f, 0x547e4662, 0x5a774b69, 0xe090d0b0, 0xee99ddbb, 0xfc82caa6, 0xf28bc7ad, 0xd8b4e49c, 0xd6bde997, 0xc4a6fe8a, 0xcaaff381, 0x90d8b8e8, 0x9ed1b5e3, 0x8ccaa2fe, 0x82c3aff5, 0xa8fc8cc4, 0xa6f581cf, 0xb4ee96d2, 0xbae79bd9, 0xdb3bbb7b, 0xd532b670, 0xc729a16d, 0xc920ac66, 0xe31f8f57, 0xed16825c, 0xff0d9541, 0xf104984a, 0xab73d323, 0xa57ade28, 0xb761c935, 0xb968c43e, 0x9357e70f, 0x9d5eea04, 0x8f45fd19, 0x814cf012, 0x3bab6bcb, 0x35a266c0, 0x27b971dd, 0x29b07cd6, 0x038f5fe7, 0x0d8652ec, 0x1f9d45f1, 0x119448fa, 0x4be30393, 0x45ea0e98, 0x57f11985, 0x59f8148e, 0x73c737bf, 0x7dce3ab4, 0x6fd52da9, 0x61dc20a2, 0xad766df6, 0xa37f60fd, 0xb16477e0, 0xbf6d7aeb, 0x955259da, 0x9b5b54d1, 0x894043cc, 0x87494ec7, 0xdd3e05ae, 0xd33708a5, 0xc12c1fb8, 0xcf2512b3, 0xe51a3182, 0xeb133c89, 0xf9082b94, 0xf701269f, 0x4de6bd46, 0x43efb04d, 0x51f4a750, 0x5ffdaa5b, 0x75c2896a, 0x7bcb8461, 0x69d0937c, 0x67d99e77, 0x3daed51e, 0x33a7d815, 0x21bccf08, 0x2fb5c203, 0x058ae132, 0x0b83ec39, 0x1998fb24, 0x1791f62f, 0x764dd68d, 0x7844db86, 0x6a5fcc9b, 0x6456c190, 0x4e69e2a1, 0x4060efaa, 0x527bf8b7, 0x5c72f5bc, 0x0605bed5, 0x080cb3de, 0x1a17a4c3, 0x141ea9c8, 0x3e218af9, 0x302887f2, 0x223390ef, 0x2c3a9de4, 0x96dd063d, 0x98d40b36, 0x8acf1c2b, 0x84c61120, 0xaef93211, 0xa0f03f1a, 0xb2eb2807, 0xbce2250c, 0xe6956e65, 0xe89c636e, 0xfa877473, 0xf48e7978, 0xdeb15a49, 0xd0b85742, 0xc2a3405f, 0xccaa4d54, 0x41ecdaf7, 0x4fe5d7fc, 0x5dfec0e1, 0x53f7cdea, 0x79c8eedb, 0x77c1e3d0, 0x65daf4cd, 0x6bd3f9c6, 0x31a4b2af, 0x3fadbfa4, 0x2db6a8b9, 0x23bfa5b2, 0x09808683, 0x07898b88, 0x15929c95, 0x1b9b919e, 0xa17c0a47, 0xaf75074c, 0xbd6e1051, 0xb3671d5a, 0x99583e6b, 0x97513360, 0x854a247d, 0x8b432976, 0xd134621f, 0xdf3d6f14, 0xcd267809, 0xc32f7502, 0xe9105633, 0xe7195b38, 0xf5024c25, 0xfb0b412e, 0x9ad7618c, 0x94de6c87, 0x86c57b9a, 0x88cc7691, 0xa2f355a0, 0xacfa58ab, 0xbee14fb6, 0xb0e842bd, 0xea9f09d4, 0xe49604df, 0xf68d13c2, 0xf8841ec9, 0xd2bb3df8, 0xdcb230f3, 0xcea927ee, 0xc0a02ae5, 0x7a47b13c, 0x744ebc37, 0x6655ab2a, 0x685ca621, 0x42638510, 0x4c6a881b, 0x5e719f06, 0x5078920d, 0x0a0fd964, 0x0406d46f, 0x161dc372, 0x1814ce79, 0x322bed48, 0x3c22e043, 0x2e39f75e, 0x2030fa55, 0xec9ab701, 0xe293ba0a, 0xf088ad17, 0xfe81a01c, 0xd4be832d, 0xdab78e26, 0xc8ac993b, 0xc6a59430, 0x9cd2df59, 0x92dbd252, 0x80c0c54f, 0x8ec9c844, 0xa4f6eb75, 0xaaffe67e, 0xb8e4f163, 0xb6edfc68, 0x0c0a67b1, 0x02036aba, 0x10187da7, 0x1e1170ac, 0x342e539d, 0x3a275e96, 0x283c498b, 0x26354480, 0x7c420fe9, 0x724b02e2, 0x605015ff, 0x6e5918f4, 0x44663bc5, 0x4a6f36ce, 0x587421d3, 0x567d2cd8, 0x37a10c7a, 0x39a80171, 0x2bb3166c, 0x25ba1b67, 0x0f853856, 0x018c355d, 0x13972240, 0x1d9e2f4b, 0x47e96422, 0x49e06929, 0x5bfb7e34, 0x55f2733f, 0x7fcd500e, 0x71c45d05, 0x63df4a18, 0x6dd64713, 0xd731dcca, 0xd938d1c1, 0xcb23c6dc, 0xc52acbd7, 0xef15e8e6, 0xe11ce5ed, 0xf307f2f0, 0xfd0efffb, 0xa779b492, 0xa970b999, 0xbb6bae84, 0xb562a38f, 0x9f5d80be, 0x91548db5, 0x834f9aa8, 0x8d4697a3 ]
            U2 = [ 0x00000000, 0x0b0e090d, 0x161c121a, 0x1d121b17, 0x2c382434, 0x27362d39, 0x3a24362e, 0x312a3f23, 0x58704868, 0x537e4165, 0x4e6c5a72, 0x4562537f, 0x74486c5c, 0x7f466551, 0x62547e46, 0x695a774b, 0xb0e090d0, 0xbbee99dd, 0xa6fc82ca, 0xadf28bc7, 0x9cd8b4e4, 0x97d6bde9, 0x8ac4a6fe, 0x81caaff3, 0xe890d8b8, 0xe39ed1b5, 0xfe8ccaa2, 0xf582c3af, 0xc4a8fc8c, 0xcfa6f581, 0xd2b4ee96, 0xd9bae79b, 0x7bdb3bbb, 0x70d532b6, 0x6dc729a1, 0x66c920ac, 0x57e31f8f, 0x5ced1682, 0x41ff0d95, 0x4af10498, 0x23ab73d3, 0x28a57ade, 0x35b761c9, 0x3eb968c4, 0x0f9357e7, 0x049d5eea, 0x198f45fd, 0x12814cf0, 0xcb3bab6b, 0xc035a266, 0xdd27b971, 0xd629b07c, 0xe7038f5f, 0xec0d8652, 0xf11f9d45, 0xfa119448, 0x934be303, 0x9845ea0e, 0x8557f119, 0x8e59f814, 0xbf73c737, 0xb47dce3a, 0xa96fd52d, 0xa261dc20, 0xf6ad766d, 0xfda37f60, 0xe0b16477, 0xebbf6d7a, 0xda955259, 0xd19b5b54, 0xcc894043, 0xc787494e, 0xaedd3e05, 0xa5d33708, 0xb8c12c1f, 0xb3cf2512, 0x82e51a31, 0x89eb133c, 0x94f9082b, 0x9ff70126, 0x464de6bd, 0x4d43efb0, 0x5051f4a7, 0x5b5ffdaa, 0x6a75c289, 0x617bcb84, 0x7c69d093, 0x7767d99e, 0x1e3daed5, 0x1533a7d8, 0x0821bccf, 0x032fb5c2, 0x32058ae1, 0x390b83ec, 0x241998fb, 0x2f1791f6, 0x8d764dd6, 0x867844db, 0x9b6a5fcc, 0x906456c1, 0xa14e69e2, 0xaa4060ef, 0xb7527bf8, 0xbc5c72f5, 0xd50605be, 0xde080cb3, 0xc31a17a4, 0xc8141ea9, 0xf93e218a, 0xf2302887, 0xef223390, 0xe42c3a9d, 0x3d96dd06, 0x3698d40b, 0x2b8acf1c, 0x2084c611, 0x11aef932, 0x1aa0f03f, 0x07b2eb28, 0x0cbce225, 0x65e6956e, 0x6ee89c63, 0x73fa8774, 0x78f48e79, 0x49deb15a, 0x42d0b857, 0x5fc2a340, 0x54ccaa4d, 0xf741ecda, 0xfc4fe5d7, 0xe15dfec0, 0xea53f7cd, 0xdb79c8ee, 0xd077c1e3, 0xcd65daf4, 0xc66bd3f9, 0xaf31a4b2, 0xa43fadbf, 0xb92db6a8, 0xb223bfa5, 0x83098086, 0x8807898b, 0x9515929c, 0x9e1b9b91, 0x47a17c0a, 0x4caf7507, 0x51bd6e10, 0x5ab3671d, 0x6b99583e, 0x60975133, 0x7d854a24, 0x768b4329, 0x1fd13462, 0x14df3d6f, 0x09cd2678, 0x02c32f75, 0x33e91056, 0x38e7195b, 0x25f5024c, 0x2efb0b41, 0x8c9ad761, 0x8794de6c, 0x9a86c57b, 0x9188cc76, 0xa0a2f355, 0xabacfa58, 0xb6bee14f, 0xbdb0e842, 0xd4ea9f09, 0xdfe49604, 0xc2f68d13, 0xc9f8841e, 0xf8d2bb3d, 0xf3dcb230, 0xeecea927, 0xe5c0a02a, 0x3c7a47b1, 0x37744ebc, 0x2a6655ab, 0x21685ca6, 0x10426385, 0x1b4c6a88, 0x065e719f, 0x0d507892, 0x640a0fd9, 0x6f0406d4, 0x72161dc3, 0x791814ce, 0x48322bed, 0x433c22e0, 0x5e2e39f7, 0x552030fa, 0x01ec9ab7, 0x0ae293ba, 0x17f088ad, 0x1cfe81a0, 0x2dd4be83, 0x26dab78e, 0x3bc8ac99, 0x30c6a594, 0x599cd2df, 0x5292dbd2, 0x4f80c0c5, 0x448ec9c8, 0x75a4f6eb, 0x7eaaffe6, 0x63b8e4f1, 0x68b6edfc, 0xb10c0a67, 0xba02036a, 0xa710187d, 0xac1e1170, 0x9d342e53, 0x963a275e, 0x8b283c49, 0x80263544, 0xe97c420f, 0xe2724b02, 0xff605015, 0xf46e5918, 0xc544663b, 0xce4a6f36, 0xd3587421, 0xd8567d2c, 0x7a37a10c, 0x7139a801, 0x6c2bb316, 0x6725ba1b, 0x560f8538, 0x5d018c35, 0x40139722, 0x4b1d9e2f, 0x2247e964, 0x2949e069, 0x345bfb7e, 0x3f55f273, 0x0e7fcd50, 0x0571c45d, 0x1863df4a, 0x136dd647, 0xcad731dc, 0xc1d938d1, 0xdccb23c6, 0xd7c52acb, 0xe6ef15e8, 0xede11ce5, 0xf0f307f2, 0xfbfd0eff, 0x92a779b4, 0x99a970b9, 0x84bb6bae, 0x8fb562a3, 0xbe9f5d80, 0xb591548d, 0xa8834f9a, 0xa38d4697 ]
            U3 = [ 0x00000000, 0x0d0b0e09, 0x1a161c12, 0x171d121b, 0x342c3824, 0x3927362d, 0x2e3a2436, 0x23312a3f, 0x68587048, 0x65537e41, 0x724e6c5a, 0x7f456253, 0x5c74486c, 0x517f4665, 0x4662547e, 0x4b695a77, 0xd0b0e090, 0xddbbee99, 0xcaa6fc82, 0xc7adf28b, 0xe49cd8b4, 0xe997d6bd, 0xfe8ac4a6, 0xf381caaf, 0xb8e890d8, 0xb5e39ed1, 0xa2fe8cca, 0xaff582c3, 0x8cc4a8fc, 0x81cfa6f5, 0x96d2b4ee, 0x9bd9bae7, 0xbb7bdb3b, 0xb670d532, 0xa16dc729, 0xac66c920, 0x8f57e31f, 0x825ced16, 0x9541ff0d, 0x984af104, 0xd323ab73, 0xde28a57a, 0xc935b761, 0xc43eb968, 0xe70f9357, 0xea049d5e, 0xfd198f45, 0xf012814c, 0x6bcb3bab, 0x66c035a2, 0x71dd27b9, 0x7cd629b0, 0x5fe7038f, 0x52ec0d86, 0x45f11f9d, 0x48fa1194, 0x03934be3, 0x0e9845ea, 0x198557f1, 0x148e59f8, 0x37bf73c7, 0x3ab47dce, 0x2da96fd5, 0x20a261dc, 0x6df6ad76, 0x60fda37f, 0x77e0b164, 0x7aebbf6d, 0x59da9552, 0x54d19b5b, 0x43cc8940, 0x4ec78749, 0x05aedd3e, 0x08a5d337, 0x1fb8c12c, 0x12b3cf25, 0x3182e51a, 0x3c89eb13, 0x2b94f908, 0x269ff701, 0xbd464de6, 0xb04d43ef, 0xa75051f4, 0xaa5b5ffd, 0x896a75c2, 0x84617bcb, 0x937c69d0, 0x9e7767d9, 0xd51e3dae, 0xd81533a7, 0xcf0821bc, 0xc2032fb5, 0xe132058a, 0xec390b83, 0xfb241998, 0xf62f1791, 0xd68d764d, 0xdb867844, 0xcc9b6a5f, 0xc1906456, 0xe2a14e69, 0xefaa4060, 0xf8b7527b, 0xf5bc5c72, 0xbed50605, 0xb3de080c, 0xa4c31a17, 0xa9c8141e, 0x8af93e21, 0x87f23028, 0x90ef2233, 0x9de42c3a, 0x063d96dd, 0x0b3698d4, 0x1c2b8acf, 0x112084c6, 0x3211aef9, 0x3f1aa0f0, 0x2807b2eb, 0x250cbce2, 0x6e65e695, 0x636ee89c, 0x7473fa87, 0x7978f48e, 0x5a49deb1, 0x5742d0b8, 0x405fc2a3, 0x4d54ccaa, 0xdaf741ec, 0xd7fc4fe5, 0xc0e15dfe, 0xcdea53f7, 0xeedb79c8, 0xe3d077c1, 0xf4cd65da, 0xf9c66bd3, 0xb2af31a4, 0xbfa43fad, 0xa8b92db6, 0xa5b223bf, 0x86830980, 0x8b880789, 0x9c951592, 0x919e1b9b, 0x0a47a17c, 0x074caf75, 0x1051bd6e, 0x1d5ab367, 0x3e6b9958, 0x33609751, 0x247d854a, 0x29768b43, 0x621fd134, 0x6f14df3d, 0x7809cd26, 0x7502c32f, 0x5633e910, 0x5b38e719, 0x4c25f502, 0x412efb0b, 0x618c9ad7, 0x6c8794de, 0x7b9a86c5, 0x769188cc, 0x55a0a2f3, 0x58abacfa, 0x4fb6bee1, 0x42bdb0e8, 0x09d4ea9f, 0x04dfe496, 0x13c2f68d, 0x1ec9f884, 0x3df8d2bb, 0x30f3dcb2, 0x27eecea9, 0x2ae5c0a0, 0xb13c7a47, 0xbc37744e, 0xab2a6655, 0xa621685c, 0x85104263, 0x881b4c6a, 0x9f065e71, 0x920d5078, 0xd9640a0f, 0xd46f0406, 0xc372161d, 0xce791814, 0xed48322b, 0xe0433c22, 0xf75e2e39, 0xfa552030, 0xb701ec9a, 0xba0ae293, 0xad17f088, 0xa01cfe81, 0x832dd4be, 0x8e26dab7, 0x993bc8ac, 0x9430c6a5, 0xdf599cd2, 0xd25292db, 0xc54f80c0, 0xc8448ec9, 0xeb75a4f6, 0xe67eaaff, 0xf163b8e4, 0xfc68b6ed, 0x67b10c0a, 0x6aba0203, 0x7da71018, 0x70ac1e11, 0x539d342e, 0x5e963a27, 0x498b283c, 0x44802635, 0x0fe97c42, 0x02e2724b, 0x15ff6050, 0x18f46e59, 0x3bc54466, 0x36ce4a6f, 0x21d35874, 0x2cd8567d, 0x0c7a37a1, 0x017139a8, 0x166c2bb3, 0x1b6725ba, 0x38560f85, 0x355d018c, 0x22401397, 0x2f4b1d9e, 0x642247e9, 0x692949e0, 0x7e345bfb, 0x733f55f2, 0x500e7fcd, 0x5d0571c4, 0x4a1863df, 0x47136dd6, 0xdccad731, 0xd1c1d938, 0xc6dccb23, 0xcbd7c52a, 0xe8e6ef15, 0xe5ede11c, 0xf2f0f307, 0xfffbfd0e, 0xb492a779, 0xb999a970, 0xae84bb6b, 0xa38fb562, 0x80be9f5d, 0x8db59154, 0x9aa8834f, 0x97a38d46 ]
            U4 = [ 0x00000000, 0x090d0b0e, 0x121a161c, 0x1b171d12, 0x24342c38, 0x2d392736, 0x362e3a24, 0x3f23312a, 0x48685870, 0x4165537e, 0x5a724e6c, 0x537f4562, 0x6c5c7448, 0x65517f46, 0x7e466254, 0x774b695a, 0x90d0b0e0, 0x99ddbbee, 0x82caa6fc, 0x8bc7adf2, 0xb4e49cd8, 0xbde997d6, 0xa6fe8ac4, 0xaff381ca, 0xd8b8e890, 0xd1b5e39e, 0xcaa2fe8c, 0xc3aff582, 0xfc8cc4a8, 0xf581cfa6, 0xee96d2b4, 0xe79bd9ba, 0x3bbb7bdb, 0x32b670d5, 0x29a16dc7, 0x20ac66c9, 0x1f8f57e3, 0x16825ced, 0x0d9541ff, 0x04984af1, 0x73d323ab, 0x7ade28a5, 0x61c935b7, 0x68c43eb9, 0x57e70f93, 0x5eea049d, 0x45fd198f, 0x4cf01281, 0xab6bcb3b, 0xa266c035, 0xb971dd27, 0xb07cd629, 0x8f5fe703, 0x8652ec0d, 0x9d45f11f, 0x9448fa11, 0xe303934b, 0xea0e9845, 0xf1198557, 0xf8148e59, 0xc737bf73, 0xce3ab47d, 0xd52da96f, 0xdc20a261, 0x766df6ad, 0x7f60fda3, 0x6477e0b1, 0x6d7aebbf, 0x5259da95, 0x5b54d19b, 0x4043cc89, 0x494ec787, 0x3e05aedd, 0x3708a5d3, 0x2c1fb8c1, 0x2512b3cf, 0x1a3182e5, 0x133c89eb, 0x082b94f9, 0x01269ff7, 0xe6bd464d, 0xefb04d43, 0xf4a75051, 0xfdaa5b5f, 0xc2896a75, 0xcb84617b, 0xd0937c69, 0xd99e7767, 0xaed51e3d, 0xa7d81533, 0xbccf0821, 0xb5c2032f, 0x8ae13205, 0x83ec390b, 0x98fb2419, 0x91f62f17, 0x4dd68d76, 0x44db8678, 0x5fcc9b6a, 0x56c19064, 0x69e2a14e, 0x60efaa40, 0x7bf8b752, 0x72f5bc5c, 0x05bed506, 0x0cb3de08, 0x17a4c31a, 0x1ea9c814, 0x218af93e, 0x2887f230, 0x3390ef22, 0x3a9de42c, 0xdd063d96, 0xd40b3698, 0xcf1c2b8a, 0xc6112084, 0xf93211ae, 0xf03f1aa0, 0xeb2807b2, 0xe2250cbc, 0x956e65e6, 0x9c636ee8, 0x877473fa, 0x8e7978f4, 0xb15a49de, 0xb85742d0, 0xa3405fc2, 0xaa4d54cc, 0xecdaf741, 0xe5d7fc4f, 0xfec0e15d, 0xf7cdea53, 0xc8eedb79, 0xc1e3d077, 0xdaf4cd65, 0xd3f9c66b, 0xa4b2af31, 0xadbfa43f, 0xb6a8b92d, 0xbfa5b223, 0x80868309, 0x898b8807, 0x929c9515, 0x9b919e1b, 0x7c0a47a1, 0x75074caf, 0x6e1051bd, 0x671d5ab3, 0x583e6b99, 0x51336097, 0x4a247d85, 0x4329768b, 0x34621fd1, 0x3d6f14df, 0x267809cd, 0x2f7502c3, 0x105633e9, 0x195b38e7, 0x024c25f5, 0x0b412efb, 0xd7618c9a, 0xde6c8794, 0xc57b9a86, 0xcc769188, 0xf355a0a2, 0xfa58abac, 0xe14fb6be, 0xe842bdb0, 0x9f09d4ea, 0x9604dfe4, 0x8d13c2f6, 0x841ec9f8, 0xbb3df8d2, 0xb230f3dc, 0xa927eece, 0xa02ae5c0, 0x47b13c7a, 0x4ebc3774, 0x55ab2a66, 0x5ca62168, 0x63851042, 0x6a881b4c, 0x719f065e, 0x78920d50, 0x0fd9640a, 0x06d46f04, 0x1dc37216, 0x14ce7918, 0x2bed4832, 0x22e0433c, 0x39f75e2e, 0x30fa5520, 0x9ab701ec, 0x93ba0ae2, 0x88ad17f0, 0x81a01cfe, 0xbe832dd4, 0xb78e26da, 0xac993bc8, 0xa59430c6, 0xd2df599c, 0xdbd25292, 0xc0c54f80, 0xc9c8448e, 0xf6eb75a4, 0xffe67eaa, 0xe4f163b8, 0xedfc68b6, 0x0a67b10c, 0x036aba02, 0x187da710, 0x1170ac1e, 0x2e539d34, 0x275e963a, 0x3c498b28, 0x35448026, 0x420fe97c, 0x4b02e272, 0x5015ff60, 0x5918f46e, 0x663bc544, 0x6f36ce4a, 0x7421d358, 0x7d2cd856, 0xa10c7a37, 0xa8017139, 0xb3166c2b, 0xba1b6725, 0x8538560f, 0x8c355d01, 0x97224013, 0x9e2f4b1d, 0xe9642247, 0xe0692949, 0xfb7e345b, 0xf2733f55, 0xcd500e7f, 0xc45d0571, 0xdf4a1863, 0xd647136d, 0x31dccad7, 0x38d1c1d9, 0x23c6dccb, 0x2acbd7c5, 0x15e8e6ef, 0x1ce5ede1, 0x07f2f0f3, 0x0efffbfd, 0x79b492a7, 0x70b999a9, 0x6bae84bb, 0x62a38fb5, 0x5d80be9f, 0x548db591, 0x4f9aa883, 0x4697a38d ]

            def __init__(self, key):

                if len(key) not in (16, 24, 32):
                    raise_exception( ValueError('Invalid key size') )

                rounds = self.number_of_rounds[len(key)]

                # Encryption round keys
                self._Ke = [[0] * 4 for i in range(rounds + 1)]

                # Decryption round keys
                self._Kd = [[0] * 4 for i in range(rounds + 1)]

                round_key_count = (rounds + 1) * 4
                KC = len(key) // 4

                # Convert the key into ints
                tk = [ struct.unpack('>i', key[i:i + 4])[0] for i in range(0, len(key), 4) ]

                # Copy values into round key arrays
                for i in range(0, KC):
                    self._Ke[i // 4][i % 4] = tk[i]
                    self._Kd[rounds - (i // 4)][i % 4] = tk[i]

                # Key expansion (fips-197 section 5.2)
                rconpointer = 0
                t = KC
                while t < round_key_count:

                    tt = tk[KC - 1]
                    tk[0] ^= ((self.S[(tt >> 16) & 0xFF] << 24) ^
                              (self.S[(tt >>  8) & 0xFF] << 16) ^
                              (self.S[ tt        & 0xFF] <<  8) ^
                               self.S[(tt >> 24) & 0xFF]        ^
                              (self.rcon[rconpointer] << 24))
                    rconpointer += 1

                    if KC != 8:
                        for i in range(1, KC):
                            tk[i] ^= tk[i - 1]

                    # Key expansion for 256-bit keys is "slightly different" (fips-197)
                    else:
                        for i in range(1, KC // 2):
                            tk[i] ^= tk[i - 1]
                        tt = tk[KC // 2 - 1]

                        tk[KC // 2] ^= (self.S[ tt        & 0xFF]        ^
                                       (self.S[(tt >>  8) & 0xFF] <<  8) ^
                                       (self.S[(tt >> 16) & 0xFF] << 16) ^
                                       (self.S[(tt >> 24) & 0xFF] << 24))

                        for i in range(KC // 2 + 1, KC):
                            tk[i] ^= tk[i - 1]

                    # Copy values into round key arrays
                    j = 0
                    while j < KC and t < round_key_count:
                        self._Ke[t // 4][t % 4] = tk[j]
                        self._Kd[rounds - (t // 4)][t % 4] = tk[j]
                        j += 1
                        t += 1

                # Inverse-Cipher-ify the decryption round key (fips-197 section 5.3)
                for r in range(1, rounds):
                    for j in range(0, 4):
                        tt = self._Kd[r][j]
                        self._Kd[r][j] = (self.U1[(tt >> 24) & 0xFF] ^
                                          self.U2[(tt >> 16) & 0xFF] ^
                                          self.U3[(tt >>  8) & 0xFF] ^
                                          self.U4[ tt        & 0xFF])

            def encrypt(self, plaintext):
                'Encrypt a block of plain text using the AES block cipher.'

                if len(plaintext) != 16:
                    raise_exception( ValueError('wrong block length') )

                rounds = len(self._Ke) - 1
                (s1, s2, s3) = [1, 2, 3]
                a = [0, 0, 0, 0]

                # Convert plaintext to (ints ^ key)
                t = [(AES._compact_word(plaintext[4 * i:4 * i + 4]) ^ self._Ke[0][i]) for i in range(0, 4)]

                # Apply round transforms
                for r in range(1, rounds):
                    for i in range(0, 4):
                        a[i] = (self.T1[(t[ i          ] >> 24) & 0xFF] ^
                                self.T2[(t[(i + s1) % 4] >> 16) & 0xFF] ^
                                self.T3[(t[(i + s2) % 4] >>  8) & 0xFF] ^
                                self.T4[ t[(i + s3) % 4]        & 0xFF] ^
                                self._Ke[r][i])
                    t = copy.copy(a)

                # The last round is special
                result = [ ]
                for i in range(0, 4):
                    tt = self._Ke[rounds][i]
                    result.append((self.S[(t[ i           ] >> 24) & 0xFF] ^ (tt >> 24)) & 0xFF)
                    result.append((self.S[(t[(i + s1) % 4] >> 16) & 0xFF] ^ (tt >> 16)) & 0xFF)
                    result.append((self.S[(t[(i + s2) % 4] >>  8) & 0xFF] ^ (tt >>  8)) & 0xFF)
                    result.append((self.S[ t[(i + s3) % 4]        & 0xFF] ^  tt       ) & 0xFF)

                return result

            def decrypt(self, ciphertext):
                'Decrypt a block of cipher text using the AES block cipher.'

                if len(ciphertext) != 16:
                    raise_exception( ValueError('wrong block length') )

                rounds = len(self._Kd) - 1
                (s1, s2, s3) = [3, 2, 1]
                a = [0, 0, 0, 0]

                # Convert ciphertext to (ints ^ key)
                t = [(AES._compact_word(ciphertext[4 * i:4 * i + 4]) ^ self._Kd[0][i]) for i in range(0, 4)]

                # Apply round transforms
                for r in range(1, rounds):
                    for i in range(0, 4):
                        a[i] = (self.T5[(t[ i          ] >> 24) & 0xFF] ^
                                self.T6[(t[(i + s1) % 4] >> 16) & 0xFF] ^
                                self.T7[(t[(i + s2) % 4] >>  8) & 0xFF] ^
                                self.T8[ t[(i + s3) % 4]        & 0xFF] ^
                                self._Kd[r][i])
                    t = copy.copy(a)

                # The last round is special
                result = [ ]
                for i in range(0, 4):
                    tt = self._Kd[rounds][i]
                    result.append((self.Si[(t[ i          ] >> 24) & 0xFF] ^ (tt >> 24)) & 0xFF)
                    result.append((self.Si[(t[(i + s1) % 4] >> 16) & 0xFF] ^ (tt >> 16)) & 0xFF)
                    result.append((self.Si[(t[(i + s2) % 4] >>  8) & 0xFF] ^ (tt >>  8)) & 0xFF)
                    result.append((self.Si[ t[(i + s3) % 4]        & 0xFF] ^  tt       ) & 0xFF)

                return result

        class AES_128_CBC:

            def __init__(self, key, iv = None):
                self._aes = AES(key)
                if iv is None:
                    self._last_cipherblock = [ 0 ] * 16
                elif len(iv) != 16:
                    raise_exception( ValueError('initialization vector must be 16 bytes') )
                else:
                    self._last_cipherblock = iv


            def encrypt(self, plaintext):
                if len(plaintext) != 16:
                    raise_exception( ValueError('plaintext block must be 16 bytes') )

                precipherblock = [ (p ^ l) for (p, l) in zip(plaintext, self._last_cipherblock) ]
                self._last_cipherblock = self._aes.encrypt(precipherblock)

                return b''.join(map(lambda x: x.to_bytes(1, 'little'), self._last_cipherblock))

            def decrypt(self, ciphertext):
                if len(ciphertext) != 16:
                    raise_exception( ValueError('ciphertext block must be 16 bytes') )

                cipherblock = ciphertext
                plaintext = [ (p ^ l) for (p, l) in zip(self._aes.decrypt(cipherblock), self._last_cipherblock) ]
                self._last_cipherblock = cipherblock

                return b''.join(map(lambda x: x.to_bytes(1, 'little'), plaintext))

        ISP_PROG = '789cbd9b0d5813c7f6f06737d92c4150306250b00211a2d65a2a2a556f2da061d55a2f57aadcf6fa012e885aad22506a6fb912c8122352c48801c18a7815cbbff55aa9a6c58f8016d22f5b5b4bd1562b12be5410b044c40279cf641340dadef67d9fe7ffd2e7e7ec99397366e6cc99d9d9cdd6fb58dbf9f77f2210811eff8b0ff3f78f0ff3028230d3752442dad4d411f1bb97fa2b838860653011a20c21e629e711f395f309855241842a430946c9100b940b8885ca85c422e522e205e50bc462e562e245e58bc412e512e2afcabfe6ad892f24fde35dfc513842ed5780700252209c84140817400a840b2105c22948817011a440380d2910ee0029102e861408778414081f062910ee042910ee0c29103e1c52207c04a4802e18c6a4ac58275d2a4612f2649a642bd913ef1bd42121dcd05c6264f66654eb4dc489ea1d9b87b78c6c1fdd39f6e1133d45b547eb4b9a8fb79c6c3fdd59f6f07c4fc8add08645b797b42eed586e7ea57b556fddadc6863bb7efb5deef78607ed4ddd72bf7225ce4135c5de413bd5de4539e71917b058f944ff8db48f9c4a891f2297123e55eca51f209d9a3e4130f8d924ff96094dcab62b47cc237a3e5136f8d964fe9180df5c740fd31507f0cd41f03f53da0be07d4f780fa1e507f1cd41f07f5c741fd71507f3cd41f0ff5c743fdf1f1be5ed37ff67599ee983e8a649751a80da169630adbd0ee27e25ddca617458644d545915b8bb686c4d7c58ba28f4687c634c6885e3ffa7a68526392e3ba92758bd6df59eff866c99b8bfe79e79fc3371edfb864d3bd4dc3ff75fc5f4bb6dfdb4ec3d8d45e4a17da9b70557b2b5d691f62a4da473992961112b54c29a12710a3d41394a3685fc24dedab74a3fd88d16a3fe5685a4e48d572a5949e48b8ab272adde949c418f524e5187a3231563d5939967e92f0503fa9f4a0a7109eea294a4ffa29629cfa29e5387a2af1847aaaf209fa6962bcfa69e578094178c5232f7f3e62835d45f5f1f2a00e8e61c776214a016394fc9c34df3f1e85b9980d6d5e5b9e2f8a2414c1446a0afe8fba14ecea532baa9fac6a432eae3fc7f27a3fcb83a61fcae8fdd1876b4327460cce298a24a3f9ba10e98a696964dab6389f76bf16ad9044122040a50a5ad4bca47eb2c627fdb86624a753889196e322449dd0f272898844d4db4a854f4e9b577b2c3b5e4cea18883d355d21855442abcbb5e9cab45985aeb4c0cf68c9a665c78d7da63b357d5ab5324dca4074d24d4bd93b4d248cc9e12b6e11d7d6fe7c27eb2eb68ed25f80ffbd4c4a456049246ae7cb6f9adb50cabfb025baef9a7e569ccf43518f5fe7a2f6252d4b9b97d71f4f9fa68291754c4effe6aebe53eab55328e18429ba19d027aef26e1b2a4cd0cd826b8da6975aa85541c96c907696b4481c5d483faecdebc49ab4675548f09198708f4c3b2d469fab3d44dd96ef39bf1cf1a43654be45ab1193c14293c7c25eac7d79b57426ee9b5f0bdf826fab5f4e1b8a7c0d97b9ac9a9c7e94132bda5c6ab749a8dde16dc82bbebf47e5367de851caab7c8fd6775a7b54cef768a7c9dea3dd2fffb71e15c63edea313cbf91e894c7c0b543dee5150cc3983443a03e902f1dc308d653a41298dc8b40245eea66c93f8525a2345704cc07233c9bef13d3ab24079b760d3b8acdc8ed49452750dd9a02f851201e878ec10a1804433595a632425222460af3b10824f29686f8b40f2c602c48e72c0d714457ff0cee111357d3186ff3f2d7c9695f7f5de851c33a6f08cfa0139076c99defabeefc8024d93bd95397f3793bb17ce01cb17d2cffc49db9fe957c6bdd22c98232297b6af08114c4e471ef43054543bc7f14ed01c55539080a9427e3d8b1e2ee95cde925ebf0a56c871cd4955daec74c2f562f2f434a3106932b28d050b821936bb49b46d3afb52103147383fb820327f98101dc9387231adf2139457b1884bcde3b50f5cb46a1f6c126a2924b0e76ba9142a3b23cf04298df358451085f33d1c8588cb78f7eef2fc2385de8c29bbe951f2f43803d424b156ef1cd30b5b2c1e74a7a548cdc20d47c9cc1176056dd383e6eea61e6c7f99c1de4af2ec44fdc0b5e985a05fd58b33585b4edf40708e69958f2caddd0591de0c31e148069bda441e8d1445d725846c2bda46be59b721e4d5a257a3a25253ec3d499e6e7a21a5afc3e01ee319a51549d1a886329d2c458f5253f646118cef3cb705ef2e98b4249fa67ab57d5d23947276fb15229f36776bbbba46b0910fc97c3ae711cb4989bdb7dc2fc04cd2f7484e24a87c6079ee60871ef47ec17aa6350ffb40afe79661469c5fc3a25b5ff57cfbf0fb4e51abcfed1fda4b545335d3eab5628294385e26b58e4850142b514bd1ecfab44a1ae5ddbe13b928ba24da717de3b6d0378fbe29faa733ee3b1d46b21a33f2e366d69279a96b67aa8ad26febd318a580fc494612c28a7c995307d91b71befcabe6d41689c89fb4db1480cd6d0d02d094bcae4644d536d0bc454ae8429295340c97a8e5561d292a0891a8d2d1dc9fd81f6984b5cfd0ed41925835c2da737fd2d2b5243bc6fc9855ab8df10d8ebc0df7206c454bab100bc786e488b2f2b92a11c33234c2bdecb6f64f4b17d293d35937b36351ac365d8a665aed708c56b45bc4d2d54e6cebd1e15a510a05d723d9a6a38ea661d43d3c72d35873bb960a83fd87ccf3d6b3c314048b96094ca32bef63dbda26399a54c85fe1fe7690ae7a5e92a24b06eb3cc28cf8323355a64d5df7b7384c416ded076fdd679ed20f94b1ebbb105f62b9799f395f9ea74f2dd7e8b5a272919231b9563f285aab558f4673a1bf22e8afc9bdb253abf6b3caa391865182a6bf8875aa76d18a8244264975e3bba1a73f615fa211c594958b19c930f0cafe26078748f6ef14f8e83219401506c9c80ee11477b8839c501c83fa342bac1eced61d052fb58bd86166472d8d68d33873ad7d8c78641c2306dd309aa5aa49f0149457ff54016d11be69a130c314f74832c30db5ee77a49665ca9c0e91630a7fa327ba2668d721f2653d85d736faed5e1d7c7fd23187207bc99c4125e34ffabb7fcef9e17ba39e3a463153dcd903d84a87fe1073deda16071ec42d412b411586348510e216cb64de2baa43a59e91f8fa7cf37307f3d369c48a6a1047a7557559948d387e97e91bd772a2d32dd57ac27572edc974476e6aba8ec2f78e984a510b590fed7f911aeb138bd72c8dea227d1414ac8f9571d3da5d5c442d333b673f9cdb73a1b6aa7e1ad6eca98bc42b7f5cdcd4ce690f67f69caf2fabbdd05cd582eff693d377b0d35d746e56cb13a126e86fafac83938b2fd448aba19033e3aac8cc60d39a90583135273505dfc7f3ee06bb967070eb42124a6114e13a8f8842a270e06ed664b0dfcde07cd45a8cb4525f14083bcfdc1ccf601c919e158422352579596a0a94b71523474a0fca25badc798482ca1863cc9d4729b6e5e75ee47556c6252ad2ebe18e990c7708a152e108f7d4c85788506900f44020ab9038201749c4f220ed683fa47593a302b47fdff99c8290b463548f24f10191ffbd9ae0769ed9771495368e26bc695961758f23bd17cdd4a5f9d13df9353a82cb38a32b46d55932afae1ecacf3456f4cb4e35c104524f867987ee0ad78e96a3927db2c2d3c377cda3e470ca293ced647233f61d053f61cf4ae876b244cd6e28861da57d44f23276ad9e4c759306e2b316a3ef5696e5e406eb4588e81d8d2deea44b748959b917ed1e804827d93bc5227cc21375fab5e073ddd25a6c69aaaa37828dd60bb5740a4d2c647799c91255a0e393615a3112785062ab57bfd515ccb3eec9b96a88a21c7c5fa261cebba849a6f1b37a8bf8087da0648ab6900975d121eb8bd6931be6720ae8756fc45c8e9f4f899a1642ff9c9ea067ea645eb0a7e99250d93e712c483e34924da091323490464e5aca4528d9e78766ef9379c10ee067da7fba4fbbcf087ed48bbca086ac5084b42214824f0f3a38f168d3d78e9788bc84a775ca50d909b0f421ac0abf0adab4bfaa0fd7805d4d3453f7d23ca55fde85dec0060b179bafa6537e2e66fcb16fb4b48b906d2826f1293b3f62191a4d97e976d28172e4540671c285e2f95c9645c8077b126adc2946a41b4493d336e5dc1ca7fe38b38e93f61296aa9b48d28dc8e66727d6ad44b707ecee82db2fd6c4e76f898e11b061b4e3ac38518fcf43fe148b6bff3c29c81f7b49b21746bc3790f6423ebaf9f30493c03b1324fb8424b147e2e60771b2378498a4f41b755142a738c40732fef1b1427f7bcb7cabf4f093d6567359b17147ecd47a525714a3077b73f7ce2fff3949e8afc17ed8f17331ed1fbf7ba1bfcc6b0251b72524a12881dc56b77e2ae70d73371566ae9b61eb8a8793f638bbb24d391b5617a729d3a5aa03e9f9619effe8cebf91e9f4636a0a965658a5c5fd527e8e1b32e7f7eaed922f6acdafec9766a01bf99f19ec92029dcbffa6bf6c198278eb5dd65f1a83e55f96f5972762b9eb6ffde51c96dbfed65f9e83e59b39fde547b06cc8d1eb45f3c3aebf929c949f730ac6d3b5bd3beb46e6973fa4a6f0f9f9399528392959daaab7cbd5685b52a5c12e35a0b8a44bfd65661495f44d7f194504275deb2f732388a498fe325f2290eeb1c4f497ce00f9a125aabf5c0172bb25aabf7c19c8b59623fde53120975b8ef49727829c6239d45fce818c2c87facb73b0dce7db5f7e04cb3dbe03a3c272adf7c0b8b05cee6d2d87ab14ebe80809d365a93ca5a5b7906c7331698f0163d9e018c0350af0baed4b96e276b13f7755e128b7da1e52f265d50d6b1b058b86d4f8bcdb3a739e11d668aaa9b04983e3074b03f183a581f8c1d240fc60e9b1f8b15a5d5cf33e1f1d8f595df198d5158f595df198552cf151b58cf7db72bbdf92a5aec7f81cec3bbbe7ace3fdfec6397b5dbe4747fa2df3117ba4df361fa1fc9c262761eb7c84c6f4b78663f36ffd128ecc97f5fd3d81c83cd25f8623f3fdfe321c991ff497e1c8fcb8bf8c8fcce7fa4bf9487caebf9c8fc459fde57c24ceea2fe723b1f79c5de623adf7945de623bdbbbf9c8fd4eefe723e5293fbcb4f61f961727f391fa9dbfabdc8ef03cefd32bf0f389f0a76e514b6771fed960f7d3832ba2852a9082636b78fff504bef26d95bc522fc36c583f6b5dc60d8da2638df95ea9a50a0518e7ca5c959ae6d81cc55949ce56ccacbc86ce2146ded86cbf6772b7c4ce113af67cd0dbd5da2894b86fe6bf2861eefffc9333c680add66d8c6a681f592cdaf97fe1d33fc80064799b62ba9e75296e715bc5606f2ade33335f0ab646972d2010dc4c0781c79dd5997b20abeb5c5fbea739a0abc526e7ea6b7cb3856a16e3bd8bc99c8d75f754e83773a0ec7d1086bfd9f161aec25389e14b0d7f16d9dd314acc29112487758cc7c4caed69acd23b45d743bac9d9beff211b00ae7053f66f3fa4f7cf4e092409ab05cb7da499656f331b20ae68fc02b9de377809f08eb08fe326fc0fa948b66ebfc9f0df9b5f5b3172a4f0db67e3664b0f5b3a1380f97e11628c25aa38a8f1e5c36b8e5f7aa5eb646cd5bcc40cb1b8d0badba3da1bf6eb9a7eac0632df7840e6eb96788f5962a5fabf5bfbc30685c5fb8f13d59f41be3fadcfbf1712db25bb7f671de05b78ad72bb2cd6079e3c5ee337c1ed6b820add0f2f3f3176640678a71d3997719db2e2dc751278f1b883afb1e9d62e134b8c789563f153cb64b3f5e76bdaaba7f9f1e52ebf3db7cc485731aeb5e7d65131f514b398dfdeec947ea8b560b9ca66029bf57350c92f16e75cb3020e3fdea161f7536bb8baf64daf4af2ff5d099093d8552b495664b6fe6b5cc2fbfcd1bb88b74665a7b77c4761f99a1cf66d8167c3ae3fd10cb0ef8018f7733422328c56654488815ad060995426e4641c3032b7711128a3a969a82f7089f5a785e109a45ce97340ceb6c86e752825186128af024b7cb57ba4497c393badcaf24d13875b9d2455fbe0272788eb49cf0b5bf51d5c348f632b94c01736ea747048324495d024e44d1f935c5e85c066e8da3717bc97aacf91d7395b93e44f39a2150085e5ee0cc100aa845646698529b1ed9c6b4019e7be0691e9e883a462d705fe0b980af8bade3fae732085f6c83a33fd6138acded96fbd61db0a1d8cfee15269cf70a3f5aec1bbc5fe2ddf2f95e4a61bfdede265654f3fd08e3325835ed4328345fc3fefac8330c9f6ef36ba428338393072c33a381b1639fc2b341371e59c1ea73199a637c8ea58bcfc9af6150ab9ecf333cb0e7d1c435039fb7dd6ccf33a2cf6c7acf775af3c2f36b02d1016871ce3233196cd7bf6f2f8b45d576fd0e7b9e0e551828bc9bd7d9adaad129bd5881df4be09c9e797845898fe19cedb57c0eee0d27cfd749519401e75b7ec2f967996b069c1e7b4192681e41f9e64bdd109e490f9847ce56e2b18c4397f46ded379bb17c7d357e665a6900b9899771eb665cde689769a2039737585b662aa16cbcedba1aae57d7f3d7508f38a7b78fc988b88cec2f0885d20823ad237c795b1d067b14571aec9a3583340fdee435cfce8373d0af349b06695aaedb3595bf61b36b90e6ea1fec9ae306695aef6836a9b574e079eb6778468115d8beba262d962271ec49e0415e27c7cff2c5d3cb7405ac18560cf699f64117620f36427eb0aa609e52ae317aaecfbbe8b0295567bf271fc870654cfb9bfa3ca37a6b1c621af4a49b24a29a80475524a11a9e5632b373d81c23f2e068949a322aeaea222a23f1c7bd21016a33e26819aa8159e26bc88a08155f8b9b825b9b9d933b8f90b33146b4631ee19b9ac25102a3d922789642697e0b08ed0311d9d047c8655ecd28179ed26545b7541506fe579345cda24e8e295105ccba8ca8f92cdd85348cf37c56d08588f96314d3eaa7d64284b5a7c6a48e32a7cc59768af459eb316612f218351d6d9a19b0d68f087e9bf0c3cfcf21eb3d222a91f6f5ae11f952230aec1a01777edbbaf729db9b1b79863607e135b498a98b56fa6a1b2887c5c6972e82c746e4eb18844b475dc43e94797539c9fc6814665cc128e5f894b4c2b8027c09a715871517614710781af1133afecd68b22ac617bf61c96af5a04611f6f5df768774d3f67b951b3b37c7334a765cef909a42b86aa514296af169e61628b5921d4a31ab73a3b539309b136136777c2a3d9e2b2875406913e721e5446df34424f391105a8714b2748754702157f6d1a74876f62a928820476d243d84a7501917207a881cbef5e1f0fba4af353e6b7d38fe6d1477037ab6d3870b89ae8ba4a2a05f2acd0293d6ad77507b2e8fb7e73eb4bd13d0de875751b041ab265430b3ae87e90f1015aaa53a90a805e6e526b69c9a22f854a91ac7cc91d2041f95cca8b44f5d39e70505ec1c777722209626f09b000ff503cbd58b14936b2cc961c79e4270f545de1dd9311ac9fe8de38da2048cd9f2d1956afd97e11e6a1152fab29dd5c8434d21a5c283a310bbae0169dd6852993d755fde3bd7f48263b428803a8d384a86e00c6318e805b780ef87719800fa01bdc875e8ef85ecdf5202da773b25dc152ea1117986d2074d55b39da791b54dbea5571b48bea5bc772866eabedc2f2414220f346687e646b865989ea8e9fb75af93f5b82f020505fd390677f75dd631cc713815c4265c451eb403b6bd038fa279d02812f5010e506b81031e45214d771bf89ecb51013be02ffcbea977063ef3b0fb1bac7e53de1be8816022855cadb53b0c7fc673dffcca737c9b4d0f0bd821ade534fc372f6dfc2d2f71777ecb4b037d5cf9989f62fea49f36fdca4f846b1e231376d8f64179eb5e566054aa0e30822a57ee0c3ca150100946742d4bd4a294175c9888e024128a9f4f6edee06316d6221d291ab040dffeb3160cd7062cecee1eb0d054ff672d1cacb65be018510bb670587808c9a80fe06c62b8cfeb6582def82bbfa587f7435e4783c77379a0372e82c15ae3ef0d686dffcaae55f998a59b7707749eff92d7d916d71b211bd581f01dea6a04dea3459d9258daeb6acdd5d5fc9bd2c4ac12d5d59b8950a7ed807402ec72c20987d9fdc2e17a1a2d7d4e81775d997fd7776ded230a0e287c41ebe9a20f14de8ab6dad5ff5389e5da9b25d98a49582ec9513c85e577f314cf60f9dd038a19583ee61969b5f25cd757158c4cd5a13ac41cded1a1aa6664f0afec28a1b2adef4bb9ac8649ab52aaf07b50d9441aadf8c2ee7db887879ed95785df1bfb4114c93d2ff2e39c887f5b3907a385fbcaf8fa409a44a718092d3dd71b78ea2ed69888acfe3a837fdb078d46fceff3cdd6eb3bd67f5bf8b7b5f81e00e37d69213fde67bb3e81f166720a37ec95b203783cedffd9e3b9d15a3aabeb824c45a8deb58ee21af3948140bd33cd7d71fab2f40688e41c4686ec51a42effbd28f269c67134595570c11f39721c1f49c7d21825aa8b94a14e14128d67cfb61ecedaad600bd8126f8570e5a351023b78c10518e74381a203ea531a7b0c211247477e04451c86541b617ddf32c2875a990971e38663e6e0a77ccc64e333deb181e8f3a2fea8a6e593819aab8f0cd44ce9fda39aab2b066a1a0e0dd4dcd2c34733cc9161d0fa3ac86be4c0334dcdd8d4d1b673c0e1eed4b27d0521fcb943d459a63ba99aaa4a556b98df6bdd36de8f8fa6fba4675b23c79287e320b1772006fea8b6e1d440edf1fba09f8d71dfb41afea8d6ea9303b50c7b609dd6bd5cfdc7b52cc7076aadcec2f767ef1bad069819c1dc4f265741f97bb6fbf37e1c1dae1c678b0efebe89634c50457062db35deb3606ebc65250f86fba41f4de7d7cef60360e79a0951ed0d832caf2eb69d47f7febf5bbea9033bdf9904d49d0603fe5da9a87649e7d2f6e52daf34afaa4fafc7df0d9468a6ee9ca6d23a2217c930446a332a5444cbeffc92ded53d628efa5150999a8daf4745ea7c158dc615f869d8847c24112332ede830f42db784f31089b1876f68a56252a93da39a107c463c8b98bbbffbe14a3d444f7d8dfb6975aa948f9fa694ee34386dc32948d402b1933e353d559df95f67849f89bfdee3a3f1fddfd585fd16b465a20e94a3e8d66be913e055788cc2fedcbecbea4f0d33b9caead14adea3c5d8a39584755517f31eadc886270635f8d43c9cf767d62f51d8d630bbada6373ddc38f4e7edc1fdc4e74598e31322bb05e3eb93abc4cc0e169fb4d2c0ca01c51969173a93431197b2d2a0f61ca9de5ad7d3de97c9e6e139d8c2f0b99fe0b6792bb15bffac15fc5b8bd467134403fe6ac9fec512fe7a097f39324d25718428d859a1726d1ef80d266443d106fc2b4c918a4dd889b4423cd78e087f09e5912ec45156a7d50961aee7682610e7f3a8826ff481ea8f5a7b2324343d4dd920a9ecb2a4a6a48552e854d6a1508fefa5f0d486bf33e8cefa20ab77a652defb80a27a67dc32cc8a5bd41e287640f837a800a12f51a2e24fc562c5921651cf619a4069b354d0dad3251cc33e6126f12eaba53e238ee6b421b4259f86f3cd1734e9b9d8432d45a952a5d6fdcbaf74b29462e4beb822b68266cd4d08bc3fdcf3f2c0b808051ed5b60893aea96f54b49e16a26c5aa29e8f8eead8fd8d6854b3273cf33aa0f37b65ef09d16dbd67b37b7da5a1ffbbb6f69bef886f3b443ea309985188ec6f1c28c50d83f5d4e08c9f48f01d1f7f0157b8d21a3da83c127ff97659984f51085f95af6e43b5ffa88be4ef32251c7eb7e31d2a566c6effcfe134a31b12182954445fcbca5737ddd7eea305157bc6316c6c4da8548ad74ef112adce0fe1d5f3725c51fbd196afead33b3f6ffeb67679cf2b0f5775ae695fdbb2a1f9b57a58559aa9aa12d893d38c39109b1c58fc0ce2f2080aa1707a0aad81d542f8824f3b8bc9cc88c329dde8e81651426374e8faa3eb451beade0cf967d13fc9b7ea36866c2ada1403fd2c08d2645436c11df93edc9d6f1404e1af140aca5f3ee619acc9b875059f91c6541c8888311c5248283c5fdb6f0a9897501a331f11be3ef4caac34261a5db0a609a88ec651c9aa8a9126e2657d1ab3170916aa9080f9047a59da2427040bff8d42c4a5b1dd90ff215a230e58df0d96be43c4a422ab857a2498df09d6ae65ad11aedc454c60c78ad19866d87db4303faac45e650465d04a170a346dd486e4b1a56fcd27d85c27949ce47d50ffc022603b1b1117314b9f1be4fd6ac506fcdd4b6eb9c4f9170bb7897bd57b63456caf3420a91b3937cda1f706b36b2204f8cbbfed3b21022d89bdc1b1679c74c41cb19c30b5ecea2908ba916f3e1790f42e4199acda9b6209ac6d4983bdaa27b1f78c5301e84e21be3104242d24b675611d53b4be17eb8ce8031e81ceae7c628ee6494261c09e3465d08db0775f33795077ec9ebcf9f91f79d274a0f88ed58b8c0aa5857e678d1e01f36f54240ab15e810fadfa9f20427ee36decbf0b344e3ba17e35d4173729efc213afe5d629ed684660da23baa7dd07e93ba296ded7cfbd13083e33adfbbe45e72746b2238de7a57248655de775383d449fc7b1a046d5676cfdff01fa7f09faffd3fbe7ac39a9f40f78eed22a2b111e4f110d7b93027a40e1147a40ddc83ce40b1e3efb87a3dc5f7c1dffcebfdd68f2a4ae1604498609898a57b54d0cc4e16fc79024f3174bc5a68148924e714012a75d27ff38a288fa82a0d67caab422a9f4cd6ea49c5cfad6bb04fee68dfd3903056f60f39d48767d820056c38dc4dee5d0a7cd107d4fc375f0da1f382c5b7668a58e786f142f24e6e6e32fef92f530df3f628d3aab86a1788e7a31c146271173761e0896e4389144b664b42349ecf9815b83bfe49c08fa5779eb5975104f357cdd17f50263354a335622ab978c0dbc978c669b975c19d39ea66f772c84d35659c3c71aebd9fbafc7a56ed6f7524ef814254a38bae5b7d739a18889da5c9b7505bf93d15241425785a8beedf2c1faa2482d152674c3bf665d3698b6c5893af9f74d60adb7edf2f63b6db596cfc4f0b471d0d411c3ef665a8ef2b2e67c1f28c25f36a6934a05ff16c73717f6eda7acb163a073ade97f706abd47ef532ac4f014e08064cf74ed83a7985a31039b1dd2a657ede5bfc44d3fa05160bbcfd74a27805de17cad56e8d52b9d046562cd1ea77539b73cc35a6f7a86f5fe88f75e7c3a9009b3e179c0013f3def69435ec33a0c69b0bf2ee2fc11ffec46e015760c6b5bb53ea6df861dda21d980dfd01c42f84e44c1de2c6a81362bf9d3073c9b3b6d6e7fbecffafe90464eac67038ceb8433cc7a8f842a77b6bdc7ee91d0279c4d631b609d6fff45425d766ed0dbcfcb252a627e3edc77d8263d1a38ff96aa217e2b6934b59e12c21a7a5414d361c027a4c9d63777371fa6c6f8c4401bbff0efa06e76e1b60b82598f06a46ce298820aef63b2420a755bbf77a11856dd8434a1ecdb35a837a2579f2fa508dc9ffc1a3ad8e4d2d0a7612ae03451eecc8e36a35c389f20a7db7aade8b2736f84c9b5ba07e79c708e31b0a468248b4e8d64134f3994c69e42991993d5995f0730a79073c6493571d799615f372249d70c94cde4658d7b9b604ad31b90e053112a1535208a96a588087c970da0cde87c4e26c3de3792da083f743efdf88ed93b04871d50efe86c0799d73ae4ead0fa68273d57773ec779e7ca2a25d831dbec74e1f7a5d88ef4415f6acac99c52ba120580df9c33dcbe2eadd2a3cc9dd3d4d98dd9a16c6795b52763de962ce8b2f42e2fdd518d04171d50e90ef0c06859ca3a64d2892c01746d5099ae2c077a9e602425d09732e8cbdc1d1deeb83771eea009bd697dd4b13c80ae21ad9a3bc77c25097d60498ee81f5b7a134a96f27d6a843e3d5725e9328fc0fd3a9cd5d427430dd8efbd5542194887413afc36e4120d282f94bd0fb9201d06e910c3fe62244be9c220fc7e283303fb68dcdb1eb91491afe35069134de4efe3e01c579d15b75f299fbdcff3a22b6d7a02b757a296742521e7bbb6f3c0e5512c7fa5beecc2e6b233757159932e0a8c341af385c02845e2b600ae3888a25253701ed184a5d4148e4e34088c7224b6ca626b69a04d7206e910bdd280d0bca8c4f8182fff377cfd9f99b9f18d295e8ab07983a4799bb742a12342686b4cec3f7cfda745af9ce81b3fc9ebb9413abf57e268fdbf0b125f5b17f55af4c69868aff5af25c46cdd9ab825c19abf34262a7ef36bb3bd7ce379bd3fd18f67b066a300a5a0ff85b470f87f2f6f9fc1a70f6da9c34c3e75b1a55eb674a22d7dd69606d9d2305bfa775bbace966eb1a53b86c8bb87c8b9b6b4d09696dbd24f6de9555b5a6b4b1d021f975d6cb2bb2d7d76881c34445e30440e1b22ff7d881c694bd7d9d23786c82943e41d43e4dd43e4dc2172e110f9d810f9c410f9a3217279e0e3fefc74887c79887c7588fc66ccd6cd5ed82f515ba39f4a5abf15021a67a1ad515e5e387f694c42e2d6d7bca2a2a3b7c6c4c72314bf85cf0f4f88625ff5dab2d91afd20c7daf2998d9bd7446d1c2848b0e5bfb46e6b4c54f4a07c7f5b7ecca62d9bb7466d5d1f13ef352f6ae346ab31f84b78862f4f98c6a7f1fe4fafdd82db8d7a1dba086b737d3cd8797aedd6a84d3183ba81e26df51ed74328cad65e68e26b6cc2facd30a2adb1899b625e4b887f7a2b3fc4d7a33626c6c423db5f94cd4ed4b4dfabf77885a8009bfe745b3ac396ceb4a581b6714cfbadfec5a3785bfd785bfd785bfd785bfd787bfd676de92c5bfa8cbf2d7d86f797cd4e82cd4e82cd4e82cdcef161fcbcff6fa5f1db6212623679c5bcb13ec12b697dc23a2f7673748c976ff45447bb677723022001c1788484cf9f4014200268c00110038ec030c009749c81e1c008c005ed16b8423a12ea4b201d05a91b301aaea580fbf8dd680c3016f0003c8171c013c078c00bf0067c00193001f005fc0039301198044c069e04a6004f015381a7017fe019601a10004c076600338140e0596016301b9803fc05780e980b3c0f04415f83a19f2190ce83743ea40a484361ac0cb00058082c025e0016032f024b40e7af4018f0376029f8211cd297a06c19d8580e4480fc77e065e01590ff01ac005602ab206f35100944016b0016880662a07c2d100bac03d643de06e0556023b009780dd80c6c81f238602b100f24405e22f03a9004bc0133bc0def2bc03f81b78064e05f2ef9683b9002288154200d50411d0e4807d4606f07a001760219c02e2013781bc802f07fd9c01eff7ca405f6c2750eb00fd001b9401ed8da0fe40305c001e01de02050081c028a40ef30f06fe00870142886fc63c0bb4009f03fc07bc0fbc071e03fc009d0fb00380994021f02a720ff34a0073e023e06ca8033c059e01c701e3000e540057001b8087c025402558011f814f80cf81cf802f812b8047c057c0d5c06be8136bf05ae00df01d5c0f7400d7015b886b4e887f1f9e847f0fb75e006f0137013a885fab7803ac004d4030d4023d0043403b7813bc05da0056805ee016d403bd001dc077e063a0133f000e8021e02ddc023e017a007e805fa00cb78bcfe9f0cb36d044b6d69389f4cb0e7bf84ffa9fdd662b907f4008e572c1677c00f980ecc075e02a281044005ec05de03ce029f03578146a01320bfb35846023ec0342004580aac01b602a9c01ea0083809acb3e5edb7c9e5c057c075e00ef01070a8b65846031380694010b013b8fcbdc5520bec87eb25400950067c09fc0034030f0021e88c04bc8014c01f0802c28048603750086c014e00e5c02aa8b705d787ebe1355017980d2c02228137815dc03bc049e02ba01ee8015cae5a2c5380b1d72c96a9c05c2004e455c0ebc04ee0287016f80e680684a083004f6026f01d100644026f003b805ce018f011f000a805ea813bc03d7cfd03a4c023a00f98fa238c13780bc805de035efa912f2b87749ded1a97fb5f075d200cd8017c0b79f5400f1009f246e08debbcee5b836ce2f424e45f074437207e209d707da03cd7d6863dc520e46d8b3f1f5b2ab3a6cd0d10778d16cb0a600ff029e0d364b138355b2ccf0291c07bc03dc0ff36f4b705e4bba0d70af3d266b13c012c06f901e49f86bca5316b366f4ef0f6f6b605bba58fff4bb1fd21824483d7c1ffeddfff017f5d4bf3'
        ISP_PROG = binascii.unhexlify(ISP_PROG)
        ISP_PROG = zlib.decompress(ISP_PROG)

        def printProgressBar (iteration, total, prefix = '', suffix = '', filename = '', decimals = 1, length = 100, fill = '='):
            """
            Call in a loop to create terminal progress bar
            @params:
                iteration   - Required  : current iteration (Int)
                total       - Required  : total iterations (Int)
                prefix      - Optional  : prefix string (Str)
                suffix      - Optional  : suffix string (Str)
                decimals    - Optional  : positive number of decimals in percent complete (Int)
                length      - Optional  : character length of bar (Int)
                fill        - Optional  : bar fill character (Str)
            """
            percent = ("{0:." + str(decimals) + "f}").format(100 * (iteration / float(total)))
            filledLength = int(length * iteration // total)
            bar = fill * filledLength + '-' * (length - filledLength)
            KFlash.log('\r%s |%s| %s%% %s' % (prefix, bar, percent, suffix), end = '\r')
            # Print New Line on Complete
            if iteration == total:
                KFlash.log()
            if callback:
                fileTypeStr = filename
                if prefix == "Downloading ISP:":
                    fileTypeStr = "ISP"
                elif prefix == "Programming BIN:" and fileTypeStr == "":
                    fileTypeStr = "BIN"
                callback(fileTypeStr, iteration, total, suffix)

        def slip_reader(port):
            partial_packet = None
            in_escape = False

            while True:
                waiting = port.inWaiting()
                read_bytes = port.read(1 if waiting == 0 else waiting)
                if read_bytes == b'':
                    raise_exception( Exception("Timed out waiting for packet %s" % ("header" if partial_packet is None else "content")) )
                for b in read_bytes:

                    if type(b) is int:
                        b = bytes([b])  # python 2/3 compat

                    if partial_packet is None:  # waiting for packet header
                        if b == b'\xc0':
                            partial_packet = b""
                        else:
                            raise_exception( Exception('Invalid head of packet (%r)' % b) )
                    elif in_escape:  # part-way through escape sequence
                        in_escape = False
                        if b == b'\xdc':
                            partial_packet += b'\xc0'
                        elif b == b'\xdd':
                            partial_packet += b'\xdb'
                        else:
                            raise_exception( Exception('Invalid SLIP escape (%r%r)' % (b'\xdb', b)) )
                    elif b == b'\xdb':  # start of escape sequence
                        in_escape = True
                    elif b == b'\xc0':  # end of packet
                        yield partial_packet
                        partial_packet = None
                    else:  # normal byte in packet
                        partial_packet += b


        class ISPResponse:
            class ISPOperation(Enum):
                ISP_ECHO = 0xC1
                ISP_NOP = 0xC2
                ISP_MEMORY_WRITE = 0xC3
                ISP_MEMORY_READ = 0xC4
                ISP_MEMORY_BOOT = 0xC5
                ISP_DEBUG_INFO = 0xD1
                ISP_CHANGE_BAUDRATE = 0xc6

            class ErrorCode(Enum):
                ISP_RET_DEFAULT = 0
                ISP_RET_OK = 0xE0
                ISP_RET_BAD_DATA_LEN = 0xE1
                ISP_RET_BAD_DATA_CHECKSUM = 0xE2
                ISP_RET_INVALID_COMMAND = 0xE3

            @staticmethod
            def parse(data):
                # type: (bytes) -> (int, int, str)
                op = 0
                reason = 0
                text = ''
                if len(data) < 2:
                    return op, reason, "data null"

                if (sys.version_info > (3, 0)):
                    op = int(data[0])
                    reason = int(data[1])
                else:
                    op = ord(data[0])
                    reason = ord(data[1])

                try:
                    if ISPResponse.ISPOperation(op) == ISPResponse.ISPOperation.ISP_DEBUG_INFO:
                        text = data[2:].decode()
                except ValueError:
                    KFlash.log('Warning: recv unknown op', op)

                return (op, reason, text)


        class FlashModeResponse:
            class Operation(Enum):
                ISP_DEBUG_INFO = 0xD1
                ISP_NOP = 0xD2
                ISP_FLASH_ERASE = 0xD3
                ISP_FLASH_WRITE = 0xD4
                ISP_REBOOT = 0xD5
                ISP_UARTHS_BAUDRATE_SET = 0xD6
                ISP_FLASH_INIT = 0xD7
                ISP_FLASH_ERASE_NONBLOCKING = 0xD8
                ISP_FLASH_STATUS = 0xD9

            class ErrorCode(Enum):
                ISP_RET_DEFAULT = 0
                ISP_RET_OK = 0xE0
                ISP_RET_BAD_DATA_LEN = 0xE1
                ISP_RET_BAD_DATA_CHECKSUM = 0xE2
                ISP_RET_INVALID_COMMAND = 0xE3
                ISP_RET_BAD_INIT = 0xE4
                ISP_RET_BAD_ERASE = 0xE5
                ISP_RET_BAD_WRITE = 0xE6
                ISP_RET_FLASH_BUSY = 0xE7

            @staticmethod
            def parse(data):
                # type: (bytes) -> (int, int, str)
                op = 0
                reason = 0
                text = ''

                if (sys.version_info > (3, 0)):
                    op = int(data[0])
                    reason = int(data[1])
                else:
                    op = ord(data[0])
                    reason = ord(data[1])

                if FlashModeResponse.Operation(op) == FlashModeResponse.Operation.ISP_DEBUG_INFO:
                    text = data[2:].decode()
                reason_enum = FlashModeResponse.ErrorCode(reason)
                if (not text) or (text.strip() == ""):
                    if reason_enum == FlashModeResponse.ErrorCode.ISP_RET_OK:
                        text = None
                    elif reason_enum == FlashModeResponse.ErrorCode.ISP_RET_BAD_DATA_LEN:
                        text = "bad data len"
                    elif reason_enum == FlashModeResponse.ErrorCode.ISP_RET_BAD_DATA_CHECKSUM:
                        text = "bad data checksum"
                    elif reason_enum == FlashModeResponse.ErrorCode.ISP_RET_BAD_INIT:
                        text = "bad initialization"
                    elif reason_enum == FlashModeResponse.ErrorCode.ISP_RET_INVALID_COMMAND:
                        text = "invalid command"
                    elif reason_enum == FlashModeResponse.ErrorCode.ISP_RET_BAD_ERASE:
                        text = "bad flash erase"
                    elif reason_enum == FlashModeResponse.ErrorCode.ISP_RET_BAD_WRITE:
                        text = "bad flash write"
                    elif reason_enum == FlashModeResponse.ErrorCode.ISP_RET_FLASH_BUSY:
                        text = "flash is busy"
                    else:
                        text = "unknown error"
                return (op, reason, text)


        def chunks(l, n, address=None):
            """Yield successive n-sized chunks from l."""
            if address != None and (address % n != 0):
                l_offset = address % n
                l_first_size = n - l_offset
                yield l[0:l_first_size]
                l = l[l_first_size:len(l)]
                for i in range(0, len(l), n):
                    yield l[i:i + n]
            else:
                for i in range(0, len(l), n):
                    yield l[i:i + n]

        class TerminalSize:
            @staticmethod
            def getTerminalSize():
                import platform
                current_os = platform.system()
                tuple_xy=None
                if current_os == 'Windows':
                    tuple_xy = TerminalSize._getTerminalSize_windows()
                    if tuple_xy is None:
                        tuple_xy = TerminalSize._getTerminalSize_tput()
                        # needed for window's python in cygwin's xterm!
                if current_os == 'Linux' or current_os == 'Darwin' or  current_os.startswith('CYGWIN'):
                    tuple_xy = TerminalSize._getTerminalSize_linux()
                if tuple_xy is None:
                    # Use default value
                    tuple_xy = (80, 25)      # default value
                return tuple_xy

            @staticmethod
            def _getTerminalSize_windows():
                res=None
                try:
                    from ctypes import windll, create_string_buffer

                    # stdin handle is -10
                    # stdout handle is -11
                    # stderr handle is -12

                    h = windll.kernel32.GetStdHandle(-12)
                    csbi = create_string_buffer(22)
                    res = windll.kernel32.GetConsoleScreenBufferInfo(h, csbi)
                except:
                    return None
                if res:
                    import struct
                    (bufx, bufy, curx, cury, wattr,
                    left, top, right, bottom, maxx, maxy) = struct.unpack("hhhhHhhhhhh", csbi.raw)
                    sizex = right - left + 1
                    sizey = bottom - top + 1
                    return sizex, sizey
                else:
                    return None

            @staticmethod
            def _getTerminalSize_tput():
                # get terminal width
                # src: http://stackoverflow.com/questions/263890/how-do-i-find-the-width-height-of-a-terminal-window
                try:
                    import subprocess
                    proc=subprocess.Popen(["tput", "cols"],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
                    output=proc.communicate(input=None)
                    cols=int(output[0])
                    proc=subprocess.Popen(["tput", "lines"],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
                    output=proc.communicate(input=None)
                    rows=int(output[0])
                    return (cols,rows)
                except:
                    return None

            @staticmethod
            def _getTerminalSize_linux():
                def ioctl_GWINSZ(fd):
                    try:
                        import fcntl, termios, struct, os
                        cr = struct.unpack('hh', fcntl.ioctl(fd, termios.TIOCGWINSZ,'1234'))
                    except:
                        return None
                    return cr
                cr = ioctl_GWINSZ(0) or ioctl_GWINSZ(1) or ioctl_GWINSZ(2)
                if not cr:
                    try:
                        fd = os.open(os.ctermid(), os.O_RDONLY)
                        cr = ioctl_GWINSZ(fd)
                        os.close(fd)
                    except:
                        pass
                if not cr:
                    try:
                        cr = (os.environ['LINES'], os.environ['COLUMNS'])
                    except:
                        return None
                return int(cr[1]), int(cr[0])

            @staticmethod
            def get_terminal_size(fallback=(100, 24), terminal = False):
                try:
                    columns, rows = TerminalSize.getTerminalSize()
                    if not terminal:
                        if not terminal_auto_size:
                            columns, rows = terminal_size
                except:
                    columns, rows = fallback

                return columns, rows

        class MAIXLoader:
            def raise_exception(self, exception):
                raise_exception(exception)

            def change_baudrate(self, baudrate):
                KFlash.log(INFO_MSG,"Selected Baudrate: ", baudrate, BASH_TIPS['DEFAULT'])
                out = struct.pack('<III', 0, 4, baudrate)
                crc32_checksum = struct.pack('<I', binascii.crc32(out) & 0xFFFFFFFF)
                out = struct.pack('<HH', 0xd6, 0x00) + crc32_checksum + out
                self.write(out)
                time.sleep(0.05)
                self._port.baudrate = baudrate
                if args.Board == "goE":
                    if baudrate >= 4500000:
                        # OPENEC super baudrate
                        KFlash.log(INFO_MSG, "Enable OPENEC super baudrate!!!",  BASH_TIPS['DEFAULT'])
                        if baudrate == 4500000:
                            self._port.baudrate = 300
                        if baudrate == 6000000:
                            self._port.baudrate = 250
                        if baudrate == 7500000:
                            self._port.baudrate = 350

            def change_baudrate_stage0(self, baudrate):
                # Dangerous, here are dinosaur infested!!!!!
                # Don't touch this code unless you know what you are doing
                # Stage0 baudrate is fixed
                # Contributor: [@rgwan](https://github.com/rgwan)
                #              rgwan <dv.xw@qq.com>
                baudrate = 1500000
                if args.Board == "goE" or args.Board == "trainer":
                    KFlash.log(INFO_MSG,"Selected Stage0 Baudrate: ", baudrate, BASH_TIPS['DEFAULT'])
                    # This is for openec, contained ft2232, goE and trainer
                    KFlash.log(INFO_MSG,"FT2232 mode", BASH_TIPS['DEFAULT'])
                    baudrate_stage0 = int(baudrate * 38.6 / 38)
                    out = struct.pack('<III', 0, 4, baudrate_stage0)
                    crc32_checksum = struct.pack('<I', binascii.crc32(out) & 0xFFFFFFFF)
                    out = struct.pack('<HH', 0xc6, 0x00) + crc32_checksum + out
                    self.write(out)
                    time.sleep(0.05)
                    self._port.baudrate = baudrate

                    retry_count = 0
                    while 1:
                        self.checkKillExit()
                        retry_count = retry_count + 1
                        if retry_count > 3:
                            err = (ERROR_MSG,'Fast mode failed, please use slow mode by add parameter ' + BASH_TIPS['GREEN'] + '--Slow', BASH_TIPS['DEFAULT'])
                            err = tuple2str(err)
                            self.raise_exception( Exception(err) )
                        try:
                            self.greeting()
                            break
                        except TimeoutError:
                            pass
                elif args.Board == "dan" or args.Board == "bit" or args.Board == "kd233":
                    KFlash.log(INFO_MSG,"CH340 mode", BASH_TIPS['DEFAULT'])
                    # This is for CH340, contained dan, bit and kd233
                    baudrate_stage0 = int(baudrate * 38.4 / 38)
                    # CH340 can not use this method, test failed, take risks at your own risk
                else:
                    # This is for unknown board
                    KFlash.log(WARN_MSG,"Unknown mode", BASH_TIPS['DEFAULT'])

            def __init__(self, port='/dev/ttyUSB1', baudrate=115200):
                # configure the serial connections (the parameters differs on the device you are connecting to)
                self._port = serial.Serial(
                    port=port,
                    baudrate=baudrate,
                    parity=serial.PARITY_NONE,
                    stopbits=serial.STOPBITS_ONE,
                    bytesize=serial.EIGHTBITS,
                    timeout=0.1
                )
                KFlash.log(INFO_MSG, "Default baudrate is", baudrate, ", later it may be changed to the value you set.",  BASH_TIPS['DEFAULT'])

                self._port.isOpen()
                self._slip_reader = slip_reader(self._port)
                self._kill_process = False

            """ Read a SLIP packet from the serial port """

            def read(self):
                return next(self._slip_reader)

            """ Write bytes to the serial port while performing SLIP escaping """

            def write(self, packet):
                buf = b'\xc0' \
                      + (packet.replace(b'\xdb', b'\xdb\xdd').replace(b'\xc0', b'\xdb\xdc')) \
                      + b'\xc0'
                #KFlash.log('[WRITE]', binascii.hexlify(buf))
                return self._port.write(buf)

            def read_loop(self):
                #out = b''
                # while self._port.inWaiting() > 0:
                #     out += self._port.read(1)

                # KFlash.log(out)
                while 1:
                    sys.stdout.write('[RECV] raw data: ')
                    sys.stdout.write(binascii.hexlify(self._port.read(1)).decode())
                    sys.stdout.flush()

            def recv_one_return(self, timeout_s = None):
                timeout_init = time.time()
                data = b''
                if timeout_s == None:
                    timeout_s = ISP_RECEIVE_TIMEOUT
                # find start boarder
                #sys.stdout.write('[RECV one return] raw data: ')
                while 1:
                    if time.time() - timeout_init > timeout_s:
                        self.raise_exception( TimeoutError )
                    c = self._port.read(1)
                    #sys.stdout.write(binascii.hexlify(c).decode())
                    sys.stdout.flush()
                    if c == b'\xc0':
                        break

                in_escape = False
                while 1:
                    if time.time() - timeout_init > timeout_s:
                        self.raise_exception( TimeoutError )
                    c = self._port.read(1)
                    #sys.stdout.write(binascii.hexlify(c).decode())
                    sys.stdout.flush()
                    if c == b'\xc0':
                        break

                    elif in_escape:  # part-way through escape sequence
                        in_escape = False
                        if c == b'\xdc':
                            data += b'\xc0'
                        elif c == b'\xdd':
                            data += b'\xdb'
                        else:
                            self.raise_exception( Exception('Invalid SLIP escape (%r%r)' % (b'\xdb', c)) )
                    elif c == b'\xdb':  # start of escape sequence
                        in_escape = True

                    data += c

                #sys.stdout.write('\n')
                return data

            # kd233 or open-ec or new cmsis-dap
            def reset_to_isp_kd233(self):
                self._port.setDTR (False)
                self._port.setRTS (False)
                time.sleep(0.1)
                #KFlash.log('-- RESET to LOW, IO16 to HIGH --')
                # Pull reset down and keep 10ms
                self._port.setDTR (True)
                self._port.setRTS (False)
                time.sleep(0.1)
                #KFlash.log('-- IO16 to LOW, RESET to HIGH --')
                # Pull IO16 to low and release reset
                self._port.setRTS (True)
                self._port.setDTR (False)
                time.sleep(0.1)
            def reset_to_boot_kd233(self):
                self._port.setDTR (False)
                self._port.setRTS (False)
                time.sleep(0.1)
                #KFlash.log('-- RESET to LOW --')
                # Pull reset down and keep 10ms
                self._port.setDTR (True)
                self._port.setRTS (False)
                time.sleep(0.1)
                #KFlash.log('-- RESET to HIGH, BOOT --')
                # Pull IO16 to low and release reset
                self._port.setRTS (False)
                self._port.setDTR (False)
                time.sleep(0.1)

            #dan dock
            def reset_to_isp_dan(self):
                self._port.setDTR (False)
                self._port.setRTS (False)
                time.sleep(0.1)
                #KFlash.log('-- RESET to LOW, IO16 to HIGH --')
                # Pull reset down and keep 10ms
                self._port.setDTR (False)
                self._port.setRTS (True)
                time.sleep(0.1)
                #KFlash.log('-- IO16 to LOW, RESET to HIGH --')
                # Pull IO16 to low and release reset
                self._port.setRTS (False)
                self._port.setDTR (True)
                time.sleep(0.1)
            def reset_to_boot_dan(self):
                self._port.setDTR (False)
                self._port.setRTS (False)
                time.sleep(0.1)
                #KFlash.log('-- RESET to LOW --')
                # Pull reset down and keep 10ms
                self._port.setDTR (False)
                self._port.setRTS (True)
                time.sleep(0.1)
                #KFlash.log('-- RESET to HIGH, BOOT --')
                # Pull IO16 to low and release reset
                self._port.setRTS (False)
                self._port.setDTR (False)
                time.sleep(0.1)

            # maix goD for old cmsis-dap firmware
            def reset_to_isp_goD(self):
                self._port.setDTR (True)   ## output 0
                self._port.setRTS (True)
                time.sleep(0.1)
                #KFlash.log('-- RESET to LOW --')
                # Pull reset down and keep 10ms
                self._port.setRTS (False)
                self._port.setDTR (True)
                time.sleep(0.1)
                #KFlash.log('-- RESET to HIGH, BOOT --')
                # Pull IO16 to low and release reset
                self._port.setRTS (False)
                self._port.setDTR (True)
                time.sleep(0.1)
            def reset_to_boot_goD(self):
                self._port.setDTR (False)
                self._port.setRTS (False)
                time.sleep(0.1)
                #KFlash.log('-- RESET to LOW --')
                # Pull reset down and keep 10ms
                self._port.setRTS (False)
                self._port.setDTR (True)
                time.sleep(0.1)
                #KFlash.log('-- RESET to HIGH, BOOT --')
                # Pull IO16 to low and release reset
                self._port.setRTS (True)
                self._port.setDTR (True)
                time.sleep(0.1)

            # maix goE for openec or new cmsis-dap  firmware
            def reset_to_boot_maixgo(self):
                self._port.setDTR (False)
                self._port.setRTS (False)
                time.sleep(0.1)
                #KFlash.log('-- RESET to LOW --')
                # Pull reset down and keep 10ms
                self._port.setRTS (False)
                self._port.setDTR (True)
                time.sleep(0.1)
                #KFlash.log('-- RESET to HIGH, BOOT --')
                # Pull IO16 to low and release reset
                self._port.setRTS (False)
                self._port.setDTR (False)
                time.sleep(0.1)

            def greeting(self):
                self._port.write(b'\xc0\xc2\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc0')
                op, reason, text = ISPResponse.parse(self.recv_one_return())

                #KFlash.log('MAIX return op:', ISPResponse.ISPOperation(op).name, 'reason:', ISPResponse.ErrorCode(reason).name)


            def flash_greeting(self):
                retry_count = 0
                while 1:
                    self.checkKillExit()
                    try:
                        self._port.write(b'\xc0\xd2\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc0')
                    except Exception:
                        err = (ERROR_MSG,"The serial port has been disconnected, please try again, use slow mode, or reduce the baud rate.",BASH_TIPS['DEFAULT'])
                        err = tuple2str(err)
                        self.raise_exception( Exception(err) )
                    retry_count = retry_count + 1
                    try:
                        op, reason, text = FlashModeResponse.parse(self.recv_one_return())
                    except IndexError:
                        if retry_count > MAX_RETRY_TIMES:
                            err = (ERROR_MSG,"Failed to Connect to K210's Stub",BASH_TIPS['DEFAULT'])
                            err = tuple2str(err)
                            self.raise_exception( Exception(err) )
                        KFlash.log(WARN_MSG,"Index Error, retrying...",BASH_TIPS['DEFAULT'])
                        time.sleep(0.1)
                        continue
                    except TimeoutError:
                        if retry_count > MAX_RETRY_TIMES:
                            err = (ERROR_MSG,"Failed to Connect to K210's Stub",BASH_TIPS['DEFAULT'])
                            err = tuple2str(err)
                            self.raise_exception( Exception(err) )
                        KFlash.log(WARN_MSG,"Timeout Error, retrying...",BASH_TIPS['DEFAULT'])
                        time.sleep(0.1)
                        continue
                    except:
                        if retry_count > MAX_RETRY_TIMES:
                            err = (ERROR_MSG,"Failed to Connect to K210's Stub",BASH_TIPS['DEFAULT'])
                            err = tuple2str(err)
                            self.raise_exception( Exception(err) )
                        KFlash.log(WARN_MSG,"Unexcepted Error, retrying...",BASH_TIPS['DEFAULT'])
                        time.sleep(0.1)
                        continue
                    # KFlash.log('MAIX return op:', FlashModeResponse.Operation(op).name, 'reason:',
                    #      FlashModeResponse.ErrorCode(reason).name)
                    if FlashModeResponse.Operation(op) == FlashModeResponse.Operation.ISP_NOP and FlashModeResponse.ErrorCode(reason) == FlashModeResponse.ErrorCode.ISP_RET_OK:
                        KFlash.log(INFO_MSG,"Boot to Flashmode Successfully",BASH_TIPS['DEFAULT'])
                        self._port.flushInput()
                        self._port.flushOutput()
                        break
                    else:
                        if retry_count > MAX_RETRY_TIMES:
                            err = (ERROR_MSG,"Failed to Connect to K210's Stub",BASH_TIPS['DEFAULT'])
                            err = tuple2str(err)
                            self.raise_exception( Exception(err) )
                        KFlash.log(WARN_MSG,"Unexcepted Return recevied, retrying...",BASH_TIPS['DEFAULT'])
                        time.sleep(0.1)
                        continue

            def boot(self, address=0x80000000):
                KFlash.log(INFO_MSG,"Booting From " + hex(address),BASH_TIPS['DEFAULT'])

                out = struct.pack('<II', address, 0)

                crc32_checksum = struct.pack('<I', binascii.crc32(out) & 0xFFFFFFFF)

                out = struct.pack('<HH', 0xc5, 0x00) + crc32_checksum + out  # op: ISP_MEMORY_WRITE: 0xc3
                self.write(out)

            def recv_debug(self):
                ret = self.recv_one_return()
                if len(ret) < 2:
                    KFlash.log('-' * 30)
                    KFlash.log("receive data time out")
                    KFlash.log('-' * 30)
                    return False
                op, reason, text = ISPResponse.parse(ret)
                #KFlash.log('[RECV] op:', ISPResponse.ISPOperation(op).name, 'reason:', ISPResponse.ErrorCode(reason).name)
                if text:
                    KFlash.log('-' * 30)
                    KFlash.log(text)
                    KFlash.log('-' * 30)
                if ISPResponse.ErrorCode(reason) not in (ISPResponse.ErrorCode.ISP_RET_DEFAULT, ISPResponse.ErrorCode.ISP_RET_OK):
                    KFlash.log('Failed, retry, errcode=', hex(reason))
                    return False
                return True

            def flash_recv_debug(self):
                op, reason, text = FlashModeResponse.parse(self.recv_one_return())
                #KFlash.log('[Flash-RECV] op:', FlashModeResponse.Operation(op).name, 'reason:',
                #      FlashModeResponse.ErrorCode(reason).name)
                if text:
                    KFlash.log('-' * 30)
                    KFlash.log(text)
                    KFlash.log('-' * 30)

                if FlashModeResponse.ErrorCode(reason) not in (FlashModeResponse.ErrorCode.ISP_RET_OK, FlashModeResponse.ErrorCode.ISP_RET_OK):
                    KFlash.log('Failed, retry')
                    return False
                return True

            def init_flash(self, chip_type):
                chip_type = int(chip_type)
                KFlash.log(INFO_MSG,"Selected Flash: ",("In-Chip", "On-Board")[chip_type],BASH_TIPS['DEFAULT'])
                out = struct.pack('<II', chip_type, 0)
                crc32_checksum = struct.pack('<I', binascii.crc32(out) & 0xFFFFFFFF)
                out = struct.pack('<HH', 0xd7, 0x00) + crc32_checksum + out
                '''Retry when it have error'''
                retry_count = 0
                while 1:
                    self.checkKillExit()
                    sent = self.write(out)
                    retry_count = retry_count + 1
                    try:
                        op, reason, text = FlashModeResponse.parse(self.recv_one_return())
                    except IndexError:
                        if retry_count > MAX_RETRY_TIMES:
                            err = (ERROR_MSG,"Failed to initialize flash",BASH_TIPS['DEFAULT'])
                            err = tuple2str(err)
                            self.raise_exception( Exception(err) )
                        KFlash.log(WARN_MSG,"Index Error, retrying...",BASH_TIPS['DEFAULT'])
                        time.sleep(0.1)
                        continue
                    except TimeoutError:
                        if retry_count > MAX_RETRY_TIMES:
                            err = (ERROR_MSG,"Failed to initialize flash",BASH_TIPS['DEFAULT'])
                            err = tuple2str(err)
                            self.raise_exception( Exception(err) )
                        KFlash.log(WARN_MSG,"Timeout Error, retrying...",BASH_TIPS['DEFAULT'])
                        time.sleep(0.1)
                        continue
                    except:
                        if retry_count > MAX_RETRY_TIMES:
                            err = (ERROR_MSG,"Failed to initialize flash",BASH_TIPS['DEFAULT'])
                            err = tuple2str(err)
                            self.raise_exception( Exception(err) )
                        KFlash.log(WARN_MSG,"Unexcepted Error, retrying...",BASH_TIPS['DEFAULT'])
                        time.sleep(0.1)
                        continue
                    # KFlash.log('MAIX return op:', FlashModeResponse.Operation(op).name, 'reason:',
                    #      FlashModeResponse.ErrorCode(reason).name)
                    if FlashModeResponse.Operation(op) == FlashModeResponse.Operation.ISP_FLASH_INIT and FlashModeResponse.ErrorCode(reason) == FlashModeResponse.ErrorCode.ISP_RET_OK:
                        KFlash.log(INFO_MSG,"Initialization flash Successfully",BASH_TIPS['DEFAULT'])
                        break
                    else:
                        if retry_count > MAX_RETRY_TIMES:
                            err = (ERROR_MSG,"Failed to initialize flash",BASH_TIPS['DEFAULT'])
                            err = tuple2str(err)
                            self.raise_exception( Exception(err) )
                        KFlash.log(WARN_MSG,"Unexcepted Return recevied, retrying...",BASH_TIPS['DEFAULT'])
                        time.sleep(0.1)
                        continue

            def flash_dataframe(self, data, address=0x80000000):
                DATAFRAME_SIZE = 1024
                data_chunks = chunks(data, DATAFRAME_SIZE)
                #KFlash.log('[DEBUG] flash dataframe | data length:', len(data))
                total_len = len(data)
                write_len = 0
                time_start = time.time()
                for n, chunk in enumerate(data_chunks):
                    self.checkKillExit()
                    while 1:
                        self.checkKillExit()
                        #KFlash.log('[INFO] sending chunk', i, '@address', hex(address), 'chunklen', len(chunk))
                        out = struct.pack('<II', address, len(chunk))

                        crc32_checksum = struct.pack('<I', binascii.crc32(out + chunk) & 0xFFFFFFFF)

                        out = struct.pack('<HH', 0xc3, 0x00) + crc32_checksum + out + chunk  # op: ISP_MEMORY_WRITE: 0xc3
                        sent = self.write(out)
                        #KFlash.log('[INFO]', 'sent', sent, 'bytes', 'checksum', binascii.hexlify(crc32_checksum).decode())

                        address += len(chunk)

                        if self.recv_debug():
                            break

                    columns, lines = TerminalSize.get_terminal_size((100, 24), terminal)
                    time_delta = time.time() - time_start
                    speed = ''
                    chunk_len = len(chunk)
                    write_len = write_len + chunk_len
                    if (time_delta > 1):
                        speed = str(int(write_len / 1024.0 / time_delta)) + 'kiB/s'
                    printProgressBar(write_len, total_len, prefix = 'Downloading ISP:', suffix = speed, length = columns - 35)

            def dump_to_flash(self, data, address=0, size=None):
                '''
                typedef struct __attribute__((packed)) {
                    uint8_t op;
                    int32_t checksum; /* All the fields below are involved in the calculation of checksum */
                    uint32_t address;
                    uint32_t data_len;
                    uint8_t data_buf[1024];
                } isp_request_t;
                '''
                if size == None:
                    DATAFRAME_SIZE = ISP_FLASH_DATA_FRAME_SIZE
                    size = DATAFRAME_SIZE
                data_chunks = chunks(data, size)
                #KFlash.log('[DEBUG] flash dataframe | data length:', len(data))



                for n, chunk in enumerate(data_chunks):
                    #KFlash.log('[INFO] sending chunk', i, '@address', hex(address))
                    out = struct.pack('<II', address, len(chunk))

                    crc32_checksum = struct.pack('<I', binascii.crc32(out + chunk) & 0xFFFFFFFF)

                    out = struct.pack('<HH', 0xd4, 0x00) + crc32_checksum + out + chunk
                    #KFlash.log("[$$$$]", binascii.hexlify(out[:32]).decode())
                    retry_count = 0
                    while True:
                        try:
                            sent = self.write(out)
                            #KFlash.log('[INFO]', 'sent', sent, 'bytes', 'checksum', crc32_checksum)
                            self.flash_recv_debug()
                        except:
                            retry_count = retry_count + 1
                            if retry_count > MAX_RETRY_TIMES:
                                err = (ERROR_MSG,"Error Count Exceeded, Stop Trying",BASH_TIPS['DEFAULT'])
                                err = tuple2str(err)
                                self.raise_exception( Exception(err) )
                            continue
                        break
                    address += len(chunk)



            def flash_erase(self, erase_addr = 0, erase_len = 0):
                #KFlash.log('[DEBUG] erasing spi flash.')
                retry_count = 0
                last_message_is_debug = 0
                while 1:
                    self.checkKillExit()
                    if not last_message_is_debug:
                        # Write ISP_FLASH_ERASE_NONBLOCKING command
                        #self._port.write(b'\xc0\xd8\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc0')
                        out = struct.pack('<II', erase_addr, erase_len)

                        crc32_checksum = struct.pack('<I', binascii.crc32(out) & 0xFFFFFFFF)

                        out = struct.pack('<HH', 0xd8, 0x00) + crc32_checksum + out
                        sent = self.write(out)
                        #op, reason, text = FlashModeResponse.parse(self.recv_one_return(timeout_s=90))

                        retry_count = retry_count + 1
                    else:
                        last_message_is_debug = 0
                    try:
                        op, reason, text = FlashModeResponse.parse(self.recv_one_return(timeout_s=90))
                    except IndexError:
                        if retry_count > MAX_RETRY_TIMES:
                            err = (ERROR_MSG,"Failed to erase to K210's flash",BASH_TIPS['DEFAULT'])
                            err = tuple2str(err)
                            self.raise_exception( Exception(err) )
                        KFlash.log(WARN_MSG,"Index Error, retrying...",BASH_TIPS['DEFAULT'])
                        time.sleep(0.1)
                        continue
                    except TimeoutError:
                        if retry_count > MAX_RETRY_TIMES:
                            err = (ERROR_MSG,"Failed to erase to K210's flash",BASH_TIPS['DEFAULT'])
                            err = tuple2str(err)
                            self.raise_exception( Exception(err) )
                        KFlash.log(WARN_MSG,"Timeout Error, retrying...",BASH_TIPS['DEFAULT'])
                        time.sleep(0.1)
                        continue
                    except:
                        if retry_count > MAX_RETRY_TIMES:
                            err = (ERROR_MSG,"Failed to erase to K210's flash",BASH_TIPS['DEFAULT'])
                            err = tuple2str(err)
                            self.raise_exception( Exception(err) )
                        KFlash.log(WARN_MSG,"Unexcepted Error, retrying...",BASH_TIPS['DEFAULT'])
                        time.sleep(0.1)
                        continue
                    # KFlash.log('MAIX return op:', FlashModeResponse.Operation(op).name, 'reason:',
                    #      FlashModeResponse.ErrorCode(reason).name)
                    if FlashModeResponse.Operation(op) == FlashModeResponse.Operation.ISP_DEBUG_INFO:
                        KFlash.log(INFO_MSG,text,BASH_TIPS['DEFAULT'])
                        self._port.flushInput()
                        self._port.flushOutput()
                        last_message_is_debug = 1
                        continue
                    elif FlashModeResponse.Operation(op) == FlashModeResponse.Operation.ISP_FLASH_ERASE_NONBLOCKING and FlashModeResponse.ErrorCode(reason) == FlashModeResponse.ErrorCode.ISP_RET_OK:
                        KFlash.log(INFO_MSG,"Send Erase command Successfully, erasing ...",BASH_TIPS['DEFAULT'])
                        self._port.flushInput()
                        self._port.flushOutput()
                        break
                    elif FlashModeResponse.Operation(op) == FlashModeResponse.Operation.ISP_FLASH_ERASE_NONBLOCKING and FlashModeResponse.ErrorCode(reason) == FlashModeResponse.ErrorCode.ISP_RET_FLASH_BUSY:
                        KFlash.log(INFO_MSG,"Flash is busy, may be erasing ...",BASH_TIPS['DEFAULT'])
                        self._port.flushInput()
                        self._port.flushOutput()
                        time.sleep(5)
                        continue
                    else:
                        if retry_count > MAX_RETRY_TIMES:
                            err = (ERROR_MSG,"Failed to erase to K210's flash",BASH_TIPS['DEFAULT'])
                            err = tuple2str(err)
                            self.raise_exception( Exception(err) )
                        KFlash.log(WARN_MSG,"Unexcepted Return recevied, retrying...",BASH_TIPS['DEFAULT'])
                        time.sleep(0.1)
                        continue
                time.sleep(0.1)
                # Check and waiting erasing process
                retry_count = 0
                last_message_is_debug = 0
                while 1:
                    self.checkKillExit()
                    if not last_message_is_debug:
                        # Write ISP_FLASH_STATUS command
                        self._port.write(b'\xc0\xd9\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc0')
                        retry_count = retry_count + 1
                    else:
                        last_message_is_debug = 0
                    try:
                        op, reason, text = FlashModeResponse.parse(self.recv_one_return())
                    except IndexError:
                        if retry_count > MAX_RETRY_TIMES:
                            err = (ERROR_MSG,"Failed to communication with K210",BASH_TIPS['DEFAULT'])
                            err = tuple2str(err)
                            self.raise_exception( Exception(err) )
                        KFlash.log(WARN_MSG,"Index Error, retrying...",BASH_TIPS['DEFAULT'])
                        time.sleep(0.1)
                        continue
                    except TimeoutError:
                        if retry_count > MAX_RETRY_TIMES:
                            err = (ERROR_MSG,"Failed to communication with K210",BASH_TIPS['DEFAULT'])
                            err = tuple2str(err)
                            self.raise_exception( Exception(err) )
                        KFlash.log(WARN_MSG,"Timeout Error, retrying...",BASH_TIPS['DEFAULT'])
                        time.sleep(0.1)
                        continue
                    except:
                        if retry_count > MAX_RETRY_TIMES:
                            err = (ERROR_MSG,"Failed to communication with K210",BASH_TIPS['DEFAULT'])
                            err = tuple2str(err)
                            self.raise_exception( Exception(err) )
                        KFlash.log(WARN_MSG,"Unexcepted Error, retrying...",BASH_TIPS['DEFAULT'])
                        time.sleep(0.1)
                        continue
                    # KFlash.log('MAIX return op:', FlashModeResponse.Operation(op).name, 'reason:',
                    #      FlashModeResponse.ErrorCode(reason).name)
                    if FlashModeResponse.Operation(op) == FlashModeResponse.Operation.ISP_DEBUG_INFO:
                        KFlash.log(INFO_MSG,text,BASH_TIPS['DEFAULT'])
                        self._port.flushInput()
                        self._port.flushOutput()
                        last_message_is_debug = 1
                        continue
                    if FlashModeResponse.Operation(op) == FlashModeResponse.Operation.ISP_FLASH_STATUS and FlashModeResponse.ErrorCode(reason) == FlashModeResponse.ErrorCode.ISP_RET_OK:
                        KFlash.log(INFO_MSG,"Success, ISP stub tells us that the flash has been erased",BASH_TIPS['DEFAULT'])
                        self._port.flushInput()
                        self._port.flushOutput()
                        break
                    elif FlashModeResponse.Operation(op) == FlashModeResponse.Operation.ISP_FLASH_STATUS and FlashModeResponse.ErrorCode(reason) == FlashModeResponse.ErrorCode.ISP_RET_FLASH_BUSY:
                        KFlash.log(INFO_MSG,"Erasing flash ...",BASH_TIPS['DEFAULT'])
                        self._port.flushInput()
                        self._port.flushOutput()
                        retry_count = 0
                        time.sleep(5)
                        continue
                    else:
                        if retry_count > MAX_RETRY_TIMES:
                            err = (ERROR_MSG,"Failed to erase to K210's flash",BASH_TIPS['DEFAULT'])
                            err = tuple2str(err)
                            self.raise_exception( Exception(err) )
                        KFlash.log(WARN_MSG,"Unexcepted Return recevied, retrying...",BASH_TIPS['DEFAULT'])
                        time.sleep(0.1)
                        continue

            def install_flash_bootloader(self, data):
                # Download flash bootloader
                self.flash_dataframe(data, address=0x80000000)

            def load_elf_to_sram(self, f):
                try:
                    from elftools.elf.elffile import ELFFile
                    from elftools.elf.descriptions import describe_p_type
                except ImportError:
                    err = (ERROR_MSG,'pyelftools must be installed, run '+BASH_TIPS['GREEN']+'`' + ('pip', 'pip3')[sys.version_info > (3, 0)] + ' install pyelftools`',BASH_TIPS['DEFAULT'])
                    err = tuple2str(err)
                    self.raise_exception( Exception(err) )

                elffile = ELFFile(f)
                if elffile['e_entry'] != 0x80000000:
                    KFlash.log(WARN_MSG,"ELF entry is 0x%x instead of 0x80000000" % (elffile['e_entry']), BASH_TIPS['DEFAULT'])

                for segment in elffile.iter_segments():
                    t = describe_p_type(segment['p_type'])
                    KFlash.log(INFO_MSG, ("Program Header: Size: %d, Virtual Address: 0x%x, Type: %s" % (segment['p_filesz'], segment['p_vaddr'], t)), BASH_TIPS['DEFAULT'])
                    if not (segment['p_vaddr'] & 0x80000000):
                        continue
                    if segment['p_filesz']==0 or segment['p_vaddr']==0:
                        KFlash.log("Skipped")
                        continue
                    self.flash_dataframe(segment.data(), segment['p_vaddr'])

            def flash_firmware(self, firmware_bin, aes_key = None, address_offset = 0, sha256Prefix = True, filename = ""):
                # type: (bytes, bytes, int, bool) -> None
                # Don't remove above code!

                #KFlash.log('[DEBUG] flash_firmware DEBUG: aeskey=', aes_key)

                total_len = len(firmware_bin)
                data_chunks = None

                if sha256Prefix == True:
                    # Add header to the firmware
                    # Format: SHA256(after)(32bytes) + AES_CIPHER_FLAG (1byte) + firmware_size(4bytes) + firmware_data
                    aes_cipher_flag = b'\x01' if aes_key else b'\x00'

                    # Encryption
                    if aes_key:
                        enc = AES_128_CBC(aes_key, iv=b'\x00'*16).encrypt
                        padded = firmware_bin + b'\x00'*15 # zero pad
                        firmware_bin = b''.join([enc(padded[i*16:i*16+16]) for i in range(len(padded)//16)])

                    firmware_len = len(firmware_bin)

                    data = aes_cipher_flag + struct.pack('<I', firmware_len) + firmware_bin

                    sha256_hash = hashlib.sha256(data).digest()

                    firmware_with_header = data + sha256_hash

                    total_len = len(firmware_with_header)
                    # Slice download firmware
                    data_chunks = chunks(firmware_with_header, ISP_FLASH_DATA_FRAME_SIZE)  # 4kiB for a sector, 16kiB for dataframe
                else:
                    total_len = len(firmware_bin)
                    data_chunks = chunks(firmware_bin, ISP_FLASH_DATA_FRAME_SIZE, address = address_offset)

                time_start = time.time()
                write_len = 0
                for n, chunk in enumerate(data_chunks):
                    self.checkKillExit()

                    # Download a dataframe
                    #KFlash.log('[INFO]', 'Write firmware data piece')
                    chunk_len = len(chunk)
                    self.dump_to_flash(chunk, address= write_len + address_offset, size=chunk_len)
                    write_len += chunk_len
                    columns, lines = TerminalSize.get_terminal_size((100, 24), terminal)
                    time_delta = time.time() - time_start
                    speed = ''
                    if (time_delta > 1):
                        speed = str(int(write_len / 1024.0 / time_delta)) + 'kiB/s'
                    printProgressBar(write_len, total_len, prefix = 'Programming BIN:', filename=filename, suffix = speed, length = columns - 35)

            def kill(self):
                self._kill_process = True

            def checkKillExit(self):
                if self._kill_process:
                    self._port.close()
                    self._kill_process = False
                    raise Exception("Cancel")

        def open_terminal(reset):
            control_signal = '0' if reset else '1'
            control_signal_b = not reset
            import serial.tools.miniterm
            # For using the terminal with MaixPy the 'filter' option must be set to 'direct'
            # because some control characters are emited
            sys.argv = [sys.argv[0], _port, '115200', '--dtr='+control_signal, '--rts='+control_signal,  '--filter=direct', '--eol=LF']
            serial.tools.miniterm.main(default_port=_port, default_baudrate=115200, default_dtr=control_signal_b, default_rts=control_signal_b)
            sys.exit(0)

        boards_choices = ["kd233", "dan", "bit", "bit_mic", "goE", "goD", "maixduino", "trainer"]
        if terminal:
            parser = argparse.ArgumentParser()
            parser.add_argument("-p", "--port", help="COM Port", default="DEFAULT")
            parser.add_argument("-f", "--flash", help="SPI Flash type, 0 for SPI3, 1 for SPI0", default=1)
            parser.add_argument("-b", "--baudrate", type=int, help="UART baudrate for uploading firmware", default=115200)
            parser.add_argument("-l", "--bootloader", help="Bootloader bin path", required=False, default=None)
            parser.add_argument("-e", "--erase",required=False, help="Erase flash", default=False, action="store_true")
            parser.add_argument("-k", "--key", help="AES key in hex, if you need encrypt your firmware.", required=False, default=None)
            parser.add_argument("-v", "--version", help="Print version.", action='version', version='1.0.5')
            parser.add_argument("--verbose", help="Increase output verbosity", default=False, action="store_true")
            parser.add_argument("-t", "--terminal", help="Start a terminal after finish (Python miniterm)", default=False, action="store_true")
            parser.add_argument("-n", "--noansi", help="Do not use ANSI colors, recommended in Windows CMD", default=False, action="store_true")
            parser.add_argument("-s", "--sram", help="Download firmware to SRAM and boot", default=False, action="store_true")
            parser.add_argument("-B", "--Board",required=False, type=str, help="Select dev board", choices=boards_choices)
            parser.add_argument("-S", "--Slow",required=False, help="Slow download mode", default=False, action="store_true")
            parser.add_argument("-A", "--addr",required=False, help="flash addr", type=str, default="-1")
            parser.add_argument("-L", "--length",required=False, help="flash addr", type=str, default="-1")
            parser.add_argument("firmware", help="firmware bin path")
            args = parser.parse_args()
        else:
            args = argparse.Namespace()
            setattr(args, "port", "DEFAULT")
            setattr(args, "flash", 1)
            setattr(args, "baudrate", 115200)
            setattr(args, "bootloader", None)
            setattr(args, "key", None)
            setattr(args, "verbose", False)
            setattr(args, "terminal", False)
            setattr(args, "noansi", False)
            setattr(args, "sram", False)
            setattr(args, "Board", None)
            setattr(args, "Slow", False)
            setattr(args, "addr", -1)
            setattr(args, "length", -1)

        # udpate args for none terminal call
        if not terminal:
            args.port = dev
            args.baudrate = baudrate
            args.noansi = noansi
            args.sram = sram
            args.Board = board
            args.firmware = file
            args.Slow = slow_mode
            args.addr = addr
            args.length = length

        if args.Board == "maixduino" or args.Board == "bit_mic":
            args.Board = "goE"

        if (args.noansi == True):
            BASH_TIPS = dict(NORMAL='',BOLD='',DIM='',UNDERLINE='',
                                DEFAULT='', RED='', YELLOW='', GREEN='',
                                BG_DEFAULT='', BG_WHITE='')
            ERROR_MSG   = BASH_TIPS['RED']+BASH_TIPS['BOLD']+'[ERROR]'+BASH_TIPS['NORMAL']
            WARN_MSG    = BASH_TIPS['YELLOW']+BASH_TIPS['BOLD']+'[WARN]'+BASH_TIPS['NORMAL']
            INFO_MSG    = BASH_TIPS['GREEN']+BASH_TIPS['BOLD']+'[INFO]'+BASH_TIPS['NORMAL']
            KFlash.log(INFO_MSG,'ANSI colors not used',BASH_TIPS['DEFAULT'])

        manually_set_the_board = False
        if args.Board:
            manually_set_the_board = True

        if args.port == "DEFAULT":
            if args.Board == "goE":
                list_port_info = list(serial.tools.list_ports.grep("0403")) #Take the second one
                if len(list_port_info) == 0:
                    err = (ERROR_MSG,"No valid COM Port found in Auto Detect, Check Your Connection or Specify One by"+BASH_TIPS['GREEN']+'`--port/-p`',BASH_TIPS['DEFAULT'])
                    err = tuple2str(err)
                    raise_exception( Exception(err) )
                list_port_info.sort()
                if len(list_port_info) == 1:
                    _port = list_port_info[0].device
                elif len(list_port_info) > 1:
                    _port = list_port_info[1].device
                KFlash.log(INFO_MSG,"COM Port Auto Detected, Selected ", _port, BASH_TIPS['DEFAULT'])
            elif args.Board == "trainer":
                list_port_info = list(serial.tools.list_ports.grep("0403")) #Take the first one
                if(len(list_port_info)==0):
                    err = (ERROR_MSG,"No valid COM Port found in Auto Detect, Check Your Connection or Specify One by"+BASH_TIPS['GREEN']+'`--port/-p`',BASH_TIPS['DEFAULT'])
                    err = tuple2str(err)
                    raise_exception( Exception(err) )
                list_port_info.sort()
                _port = list_port_info[0].device
                KFlash.log(INFO_MSG,"COM Port Auto Detected, Selected ", _port, BASH_TIPS['DEFAULT'])
            else:
                try:
                    list_port_info = next(serial.tools.list_ports.grep(VID_LIST_FOR_AUTO_LOOKUP)) #Take the first one within the list
                    _port = list_port_info.device
                    KFlash.log(INFO_MSG,"COM Port Auto Detected, Selected ", _port, BASH_TIPS['DEFAULT'])
                except StopIteration:
                    err = (ERROR_MSG,"No valid COM Port found in Auto Detect, Check Your Connection or Specify One by"+BASH_TIPS['GREEN']+'`--port/-p`',BASH_TIPS['DEFAULT'])
                    err = tuple2str(err)
                    raise_exception( Exception(err) )
        else:
            _port = args.port
            KFlash.log(INFO_MSG,"COM Port Selected Manually: ", _port, BASH_TIPS['DEFAULT'])

        self.loader = MAIXLoader(port=_port, baudrate=115200)
        file_format = ProgramFileFormat.FMT_BINARY

        # 0. Check firmware or cmd
        cmds = ['erase']
        if not args.firmware in cmds:
            if not os.path.exists(args.firmware):
                err = (ERROR_MSG,'Unable to find the firmware at ', args.firmware, BASH_TIPS['DEFAULT'])
                err = tuple2str(err)
                raise_exception( Exception(err) )

            with open(args.firmware, 'rb') as f:
                file_header = f.read(4)
                #if file_header.startswith(bytes([0x50, 0x4B])):
                if file_header.startswith(b'\x50\x4B'):
                    if ".kfpkg" != os.path.splitext(args.firmware)[1]:
                        KFlash.log(INFO_MSG, 'Find a zip file, but not with ext .kfpkg:', args.firmware, BASH_TIPS['DEFAULT'])
                    else:
                        file_format = ProgramFileFormat.FMT_KFPKG

                #if file_header.startswith(bytes([0x7F, 0x45, 0x4C, 0x46])):
                if file_header.startswith(b'\x7f\x45\x4c\x46'):
                    file_format = ProgramFileFormat.FMT_ELF
                    if args.sram:
                        KFlash.log(INFO_MSG, 'Find an ELF file:', args.firmware, BASH_TIPS['DEFAULT'])
                    else:
                        err = (ERROR_MSG, 'This is an ELF file and cannot be programmed to flash directly:', args.firmware, BASH_TIPS['DEFAULT'] , '\r\nPlease retry:', args.firmware + '.bin', BASH_TIPS['DEFAULT'])
                        err = tuple2str(err)
                        raise_exception( Exception(err) )

        # 1. Greeting.
        KFlash.log(INFO_MSG,"Trying to Enter the ISP Mode...",BASH_TIPS['DEFAULT'])

        retry_count = 0

        while 1:
            self.checkKillExit()
            if not self.loader._port.isOpen():
                self.loader._port.open()
            try:
                retry_count = retry_count + 1
                if retry_count > 15:
                    err = (ERROR_MSG,"No valid Kendryte K210 found in Auto Detect, Check Your Connection or Specify One by"+BASH_TIPS['GREEN']+'`-p '+('/dev/ttyUSB0', 'COM3')[sys.platform == 'win32']+'`',BASH_TIPS['DEFAULT'])
                    err = tuple2str(err)
                    raise_exception( Exception(err) )
                if args.Board == "dan" or args.Board == "bit" or args.Board == "trainer":
                    try:
                        KFlash.log('.', end='')
                        self.loader.reset_to_isp_dan()
                        self.loader.greeting()
                        break
                    except TimeoutError:
                        pass
                elif args.Board == "kd233":
                    try:
                        KFlash.log('_', end='')
                        self.loader.reset_to_isp_kd233()
                        self.loader.greeting()
                        break
                    except TimeoutError:
                        pass
                elif args.Board == "goE":
                    try:
                        KFlash.log('*', end='')
                        self.loader.reset_to_isp_kd233()
                        self.loader.greeting()
                        break
                    except TimeoutError:
                        pass
                elif args.Board == "goD":
                    try:
                        KFlash.log('#', end='')
                        self.loader.reset_to_isp_goD()
                        self.loader.greeting()
                        break
                    except TimeoutError:
                        pass
                else:
                    try:
                        KFlash.log('.', end='')
                        self.loader.reset_to_isp_dan()
                        self.loader.greeting()
                        args.Board = "dan"
                        KFlash.log()
                        KFlash.log(INFO_MSG,"Automatically detected dan/bit/trainer",BASH_TIPS['DEFAULT'])
                        break
                    except TimeoutError:
                        if not self.loader._port.isOpen():
                            self.loader._port.open()
                        pass
                    try:
                        KFlash.log('_', end='')
                        self.loader.reset_to_isp_kd233()
                        self.loader.greeting()
                        args.Board = "kd233"
                        KFlash.log()
                        KFlash.log(INFO_MSG,"Automatically detected goE/kd233",BASH_TIPS['DEFAULT'])
                        break
                    except TimeoutError:
                        if not self.loader._port.isOpen():
                            self.loader._port.open()
                        pass
                    try:
                        KFlash.log('.', end='')
                        self.loader.reset_to_isp_goD()
                        self.loader.greeting()
                        args.Board = "goD"
                        KFlash.log()
                        KFlash.log(INFO_MSG,"Automatically detected goD",BASH_TIPS['DEFAULT'])
                        break
                    except TimeoutError:
                        if not self.loader._port.isOpen():
                            self.loader._port.open()
                        pass
                    try:
                        # Magic, just repeat, don't remove, it may unstable, don't know why.
                        KFlash.log('_', end='')
                        self.loader.reset_to_isp_kd233()
                        self.loader.greeting()
                        args.Board = "kd233"
                        KFlash.log()
                        KFlash.log(INFO_MSG,"Automatically detected goE/kd233",BASH_TIPS['DEFAULT'])
                        break
                    except TimeoutError:
                        if not self.loader._port.isOpen():
                            self.loader._port.open()
                        pass
            except Exception as e:
                KFlash.log()
                raise_exception( Exception("Greeting fail, check serial port ("+str(e)+")" ) )

        # Don't remove this line
        # Dangerous, here are dinosaur infested!!!!!
        ISP_RECEIVE_TIMEOUT = 3

        KFlash.log()
        KFlash.log(INFO_MSG,"Greeting Message Detected, Start Downloading ISP",BASH_TIPS['DEFAULT'])

        if manually_set_the_board and (not args.Slow):
            if (args.baudrate >= 1500000) or args.sram:
                self.loader.change_baudrate_stage0(args.baudrate)

        # 2. download bootloader and firmware
        if args.sram:
            with open(args.firmware, 'rb') as firmware_bin:
                if file_format == ProgramFileFormat.FMT_KFPKG:
                    err = (ERROR_MSG, "Unable to load kfpkg to SRAM")
                    err = tuple2str(err)
                    raise_exception( Exception(err) )
                elif file_format == ProgramFileFormat.FMT_ELF:
                    self.loader.load_elf_to_sram(firmware_bin)
                else:
                    self.loader.install_flash_bootloader(firmware_bin.read())
        else:
            # install bootloader at 0x80000000
            if args.bootloader:
                with open(args.bootloader, 'rb') as f:
                    isp_loader = f.read()
            else:
                isp_loader = ISP_PROG
            self.loader.install_flash_bootloader(isp_loader)

        # Boot the code from SRAM
        self.loader.boot()

        if args.sram:
            # Dangerous, here are dinosaur infested!!!!!
            # Don't touch this code unless you know what you are doing
            self.loader._port.baudrate = args.baudrate
            KFlash.log(INFO_MSG,"Boot user code from SRAM", BASH_TIPS['DEFAULT'])
            if(args.terminal == True):
                try:
                    self.loader._port.close()
                except Exception:
                    pass
                open_terminal(False)
            msg = "Burn SRAM OK"
            raise_exception( Exception(msg) )

        # Dangerous, here are dinosaur infested!!!!!
        # Don't touch this code unless you know what you are doing
        self.loader._port.baudrate = 115200

        KFlash.log(INFO_MSG,"Wait For 0.1 second for ISP to Boot", BASH_TIPS['DEFAULT'])

        time.sleep(0.1)

        self.loader.flash_greeting()

        if args.baudrate != 115200:
            self.loader.change_baudrate(args.baudrate)
            KFlash.log(INFO_MSG,"Baudrate changed, greeting with ISP again ... ", BASH_TIPS['DEFAULT'])
            self.loader.flash_greeting()

        self.loader.init_flash(args.flash)

        if args.erase:
            self.loader.flash_erase()

        if file_format == ProgramFileFormat.FMT_KFPKG:
            KFlash.log(INFO_MSG,"Extracting KFPKG ... ", BASH_TIPS['DEFAULT'])
            with tempfile.TemporaryDirectory() as tmpdir:
                try:
                    with zipfile.ZipFile(args.firmware) as zf:
                        zf.extractall(tmpdir)
                        if not os.path.exists(os.path.join(tmpdir, "flash-list.json")):
                            err = (ERROR_MSG,'Can not find flash-list.json in kfpkg root dir',BASH_TIPS['DEFAULT'])
                            err = tuple2str(err)
                            raise_exception( Exception(err) )
                except zipfile.BadZipFile:
                    err = (ERROR_MSG,'Unable to Decompress the kfpkg, your file might be corrupted.',BASH_TIPS['DEFAULT'])
                    err = tuple2str(err)
                    raise_exception( Exception(err) )

                fFlashList = open(os.path.join(tmpdir, 'flash-list.json'), "r")
                sFlashList = re.sub(r'"address": (.*),', r'"address": "\1",', fFlashList.read()) #Pack the Hex Number in json into str
                fFlashList.close()
                jsonFlashList = json.loads(sFlashList)
                for lBinFiles in jsonFlashList['files']:
                    self.checkKillExit()
                    KFlash.log(INFO_MSG,"Writing",lBinFiles['bin'],"into","0x%08x"%int(lBinFiles['address'], 0),BASH_TIPS['DEFAULT'])
                    with open(os.path.join(tmpdir, lBinFiles["bin"]), "rb") as firmware_bin:
                        self.loader.flash_firmware(firmware_bin.read(), None, int(lBinFiles['address'], 0), lBinFiles['sha256Prefix'], filename=lBinFiles['bin'])
        else:
            if args.firmware == "erase":
                if args.addr.lower().startswith("0x"):
                    addr = int(args.addr, base=16)
                else:
                    addr = int(args.addr)
                if args.length.lower() == "all":
                    addr = 0
                    length = 0
                    KFlash.log(INFO_MSG,"erase all")
                else:
                    if args.length.lower().startswith("0x"):
                        length = int(args.length, base=16)
                    else:
                        length = int(args.length)
                    KFlash.log(INFO_MSG,"erase '0x{:x}' - '0x{:x}' ({}B, {:.02}KiB, {:.02}MiB)".format(addr, addr+length, length, length/1024.0, length/1024.0/1024.0))
                if ((addr % 4096) != 0) or ((length % 4096) != 0) or addr < 0 or addr > 0x04000000 or length < 0 or length > 0x04000000 or (addr + length > 0x04000000):
                    err = (ERROR_MSG,"Erase arameter error. The address and length must be aligned to 4k, the sum of the address and length must be less than 64M, the address must be greater than or equal to 0, or equal to the string 'all', and the length must be greater than or equal to 0.")
                    err = tuple2str(err)
                    raise_exception( Exception(err) )
                self.loader.flash_erase(addr, length)
            else:
                with open(args.firmware, 'rb') as firmware_bin:
                    if args.key:
                        aes_key = binascii.a2b_hex(args.key)
                        if len(aes_key) != 16:
                            raise_exception( ValueError('AES key must by 16 bytes') )

                        self.loader.flash_firmware(firmware_bin.read(), aes_key=aes_key)
                    else:
                        self.loader.flash_firmware(firmware_bin.read())

        # 3. boot
        if args.Board == "dan" or args.Board == "bit" or args.Board == "trainer":
            self.loader.reset_to_boot_dan()
        elif args.Board == "kd233":
            self.loader.reset_to_boot_kd233()
        elif args.Board == "goE":
            self.loader.reset_to_boot_maixgo()
        elif args.Board == "goD":
            self.loader.reset_to_boot_goD()
        else:
            KFlash.log(WARN_MSG,"Board unknown !! please press reset to boot!!")

        KFlash.log(INFO_MSG,"Rebooting...", BASH_TIPS['DEFAULT'])
        try:
            self.loader._port.close()
        except Exception:
            pass

        if(args.terminal == True):
            open_terminal(True)

    def kill(self):
        if self.loader:
            self.loader.kill()
        self.killProcess = True

    def checkKillExit(self):
        if self.killProcess:
            if self.loader:
                self.loader._port.close()
            raise Exception("Cancel")


def main():
    kflash = KFlash()
    try:
        kflash.process()
    except Exception as e:
        if str(e) == "Burn SRAM OK":
            sys.exit(0)
        kflash.log(str(e))
        sys.exit(1)

if __name__ == '__main__':
    main()
