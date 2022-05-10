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

    def process(self, terminal=True, dev="", baudrate=1500000, board=None, sram = False, file="", callback=None, noansi=False, terminal_auto_size=False, terminal_size=(50, 1), slow_mode = False):
        self.killProcess = False
        BASH_TIPS = dict(NORMAL='\033[0m',BOLD='\033[1m',DIM='\033[2m',UNDERLINE='\033[4m',
                            DEFAULT='\033[0m', RED='\033[31m', YELLOW='\033[33m', GREEN='\033[32m',
                            BG_DEFAULT='\033[49m', BG_WHITE='\033[107m')

        ERROR_MSG   = BASH_TIPS['RED']+BASH_TIPS['BOLD']+'[ERROR]'+BASH_TIPS['NORMAL']
        WARN_MSG    = BASH_TIPS['YELLOW']+BASH_TIPS['BOLD']+'[WARN]'+BASH_TIPS['NORMAL']
        INFO_MSG    = BASH_TIPS['GREEN']+BASH_TIPS['BOLD']+'[INFO]'+BASH_TIPS['NORMAL']

        VID_LIST_FOR_AUTO_LOOKUP = "(1A86)|(0403)|(067B)|(10C4)|(C251)|(0403)"
        #                            WCH    FTDI    PL     CL    DAP   OPENEC
        ISP_RECEIVE_TIMEOUT = 1

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
                    result.append((self.Si[(t[ i           ] >> 24) & 0xFF] ^ (tt >> 24)) & 0xFF)
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

        ISP_PROG = '789ced7d0f7c5c45bdef9cfd7792fecbd2addd420bd976db6ea9b5a43434450b2e5a08decbbb8d9667b95e7da56c4ba89626362941c5eb86dd66517b69702be9a50885568a0a586c31708bba6825a83c5ba5122f97478ba95d54b481c66c4836bbeffb9b99f367cf9edd04c5cfbbefbd9b7ebe9d73667ebf99dffc66e637bf9973ce6c138b2a67beffe82b0a2bfc6b69a8a96969080061426d9783b1e4ed3ff4b5747ea42689741f1892808fe2019f1321e07321047c6e8480cf8310f0a908015f0542c0578910f04d4008f82622047c931002bec90801df148480af0a21d07d0364dbe3a869f1d6b0d58cf5bf00ac561002ab1d0881d54e84c06a174260b51b21b0da831058ad22045657200456572204564f4008ac9e8810583d0921b07a324260f51484c0ea2a8440d70390a9fd8aaff81fac801ebef32ddf1647b6655ef80d9ff22ee63be70db654b98235b168bd4f514e066bcf61c1e5b35970c51216acb9c211acfdb023b87c9d23b8e2d38e604dbb2b587b972bb8fc015770c5e3ae60cd339e60ed2f3cc1e5af7a822bdef0046b944af05782bf12fc95e09f08fe89e09f08fe89e09f0cfec9e09f0cfec9e0af027f15f8abc05f150a28ded0dc73bca105b3bda1454bbca1c0155343733f3c35b460ddd4d0a24f4f0d05daa785e6de352db4e08169a1458f4f0b059e991e9afb8be9a105af4e0f2d7a633af8cf05ffb9e03f17fce7827f26f867827f26f86782ff7cf09f0ffef3c17f3ef8abc15f0dfe6af057b7cc0bd49e9de7adf57914f405c51bf9a89b9d61a956e8869df11ebbbcc5fbaeda584d3b732e5194d89276c579b1e2885ddcee702e559cb1a5ed4e67ade28ad5b6bb9c9728eed825ed6ee732c5135bd6ee71d6296aacae5d752e572a62cbdb2b9c972a95b14bdb2b9def5526c4dedb3ec1f93e6562ec7ded139d2b9449b115ed939c9729936397b54f765eae4c895dde3ec5f97ea52af6fef62a15fa4904dabdea6ce59cc4ecf673d439cad4c49cf6a96a50f12582ed3e75ae322d31b77d9a3a4f7957625efbbbd4f9caf4c4fcf6e96a48f12742ed7e75813223b1a07d867aa1726ee2c2f673d585ca798985ede7a9ef566626dedd3e535da4cc4a2c6a9fa5be47393ff19ef6f3d5c5ca0589c5ed17a81729d5898bdaabd13f022d2c5083301fac6dc71852141fc69893ae1545698cd2782b9b960baee0698eae2ef4c984fabb60ed404e5cd7bf16ac19c835b1b0c35917cf25d57a4669b13a572ed981eb9ae339674865c13d69e6a4b884727bdfa64c5696a1206f87b50ca2a13c90a712439ebe04e5792a17dca3322aa3abab02e5f6b4f4dd90c9d9e7436341e4e5531db00b0e7650cd84294fba762e431e5f451edbb635f9b6a9ec4c73ead30574a80fdd53d9b8073de4265bc3693baba94cf42705fdc65c6e16e562ccb53b50ae2ba9ba992fe166c1f903d9a48afacf1dc8c64247b2bb132a8bdca13ae89ae7e76d089c6d5c5943b2b5b006efd950b896cae7facb24585f879ad3f9e266be63b374fa15c8bb2e3eaad14bf9a85f3b2197cb4e2fba7c3547729031276514e5ba857d4d4755c6e9509e4d7d476133c8b6507d9d7a7e8b657d170d64cff4af4d43de512efb2ec8dc7fff7f00af42f619ce507c94d2926e55e8b5bffa759df61ec4b9bda49b4a111eabd0e8fdb790cdbf6aaec177ff9b5436d501e939a19be856c8378cfac2e6b5bb201fecdcbee1e0f243c3c1da23c3e893c35d09eabb891fc4ba55eaafa4bf91c8dd54df38da7160b83be30f24bb42d4d7a3d41ea6fb14e91b7a7f23b89cf85ca3917bd569b165f161f49391ae6d8cfad501e725aedc196ff863c1f92ef4633685df3777cef44156d2f1d26d6946f2eeeef2b3991daa7e4df5f727683eeb7931d9554ffd91c5be5b989eecaaa3b134ccd39e284cdb9d407eb1e23823dffa5f68f93a9fb4e40bba82bca19be41da413276f5b51b72bbf7ec69bba86f3815ed3fb4ce257fb59dfcbe97e51d76393b4ba1e4ca469cc49ddfc789f6ca3ab055dc304de774807b8f7b903ec4cd8fb79d86e5fa14eaf7cd079497cf48c975d199cabe914f7cd0d1e514e7c54e8346ed269dca2d3c433853a8d97d169dc46a7f1123a559f2ed469fc6dead4dd097dd4713ed2298d435c17ea94ea1a6dd3ea5aa8d36d3b844ec34be5d87763acba31063c76633558bb2f17ac39047b70241b5c7e3c0b3d8f928d8b5d12cff9b7d1d8df7627c6e3f33e77e76ab475782c7e61f7fbf3c95e3f3bd896d1faef4fa9de5a9d63cb5c280363186d8cbae42cb6c501791d28c769d852614751561665c1a678b579251beb4e28d2466663fb130ce3d6019d6423b7ab5ef40b878857956497ea48f6aa7c5e821c0ee2c7358df5dcd2359922babed64c16fdae52a339081ab267fa7d1bcf236b9bff1a913fd928d16e9d2c723c2dcae8c17da61ec854453a28add9093915846ef251e0b73a9d640b6fc954d11ce9f3f8b95d3e9ce8e53c4196e17351df4e7550ab3fd1d15ce5435914173c9076505e723e2c69f7b5b6a3fc22afa8728eeb0f6b73b64f3de60876a4793c1f8fc236a74bcf79ffd54eff37b5139f2bd14ec22ff10afb6dd7563b85afc1e7e3edea14c8ac68fa840e7287a99dc08b6bf26b7287a1d799b28e44d3f7596aa370a5399df2e2eda4c5b5f13cb205f9ae11f9fecdda87cf5b2a7b27da48ea32a7cd815c57af8839f530b5d57c4b5b21de68ab13a74bb495e10723ffbd2af2a8873f0af961631d9101e842bfef74465e47beb8177392cafd27e844356898a790e77a4f214fd7b0e049394d3c2e0b8fcbc293153ca4f3fe3cd5c7e28317f9c2f0bdb23ed503db703cbbb7caf011c97f923e582e3887e6f5a8cb1972d1fc373a53e5756291e7d32eba778656f27ec7fb196870cd82730672628de0e76b04ea23943f641d9563e20fbcfc00b5914bb4fd3175586b5f2a9fec02da9cc65296caa0b58ac66fe3478f602e74d19a1a75736b760f73e130f990b1fdf5724cd17542fad4b8d6c7175dab0ef221a9bfd35c4e32a12e613e3ef8988a17c76bf9f4f4d0fa41f6e34c5e2f8b8f8d90181b716e6747684cf9f818624ae43cadefa7390feaef2ce2bbddca1765911999c2b2b88f8236f9583fe3f2e39e642c94c32ff2bb4fe6c7e312220e7645aceb5c59ac331cf005b2e40b081f92ca3895ebfb40bf51d73bb9ede3d74ee2a1be463c4c8b37c97fa7ea2aaaf7b48c4b96e5d4cbd2f9ccb6242a6d4854b596c3c7467159c5ba9a26e62a7359a6ba1ae573df0e759d6baeab496f51d565cf57a8236e93eb5b476df432ea23ba15a7b2a24d5d627cd4c8f13191c647eb2895d5d7a966c7d56ef1f1b59bb4692eda53c15871cb3193c198a9c098a9c098a9c49819c29819c2981984ff38887ab419b6a6c1119992e1b606f51a92f51a12edc0b60655d8867ad74832837e5c31302cae7b4dd7dda6eb367e1d5ce81a263b057b331c9c42d7f1b7c83f082e77911fe1d1ec5a12fd806c75247ada21ae993372fb698768df1a47c495211d3879de698c6de40d7e87b8f76bf78ab80f69f7d407489f19de062b4e0df23690765db6c1909057ea9ac677411d35ddec71601cbb6cf3aa73210e322d47dc7ed88b85e00bad1c89bca47accf2521ccd4ddca62c24f9c2ee82f9e54dd85af3fcf2fbb423e959f9964f8d6778bc670f33adbd1fd0e7a8d0cab7b43c0dfe938ec8f4cca45275d7eb34639c755accf750c41ec1aff9da88b7296f43c48beb94db325fba2cf325eae32a559f9d467d5ca23e227f842ee82e3e1279ae64dba891a919db76e67e964a36d72c5bca03ddd8d65ba32fa0f596ca3ba0d31a7db8d3833e3c5dbfbeaad725aea3eec8974e07f4eb6b7a196ccd0744ffc6b89b945981ba5e2ed26b3c91f8e98b455ad813a9c8c0674fad90692af2b958bf0ef7caf1d2efc17859286daf1a99909981fc2e15690dc4c3a4ad54231e4a4bd5416f343767b96e5fa4342fd779acfe94ac7b40b3ab465fe8a6fcd0067abb557d0de5b80d1eef3878561d12e3b2b08f15d2ec783e897bb93731447608fe4414652d7a67e45ef5d0db977bc7f7c621f7af8ae5de3100fb39db6c9bb47e46f324af0bfa90f0b9a36ef28793dd623ea07961f7dd21a6d957de86090f3bd8989136e5afd241fb5fa0835d63ebe0e881621dac3a853ee7a5b9dab6edcae7f72d9bfc4e20bf89563ed259f1dc15aea4f2e41e6b41dde4fe6356eca3339a634769df88ef2f9a7c05acc398752eefbb47cd6a76d046be5f413ec56e2e15be6f99396997daa1f9c8724eafc09c5e81b9bcd2d85392fb412bf6659309b7f02be07b88356a3ce7ec16eb56f8beccd7e167b165f0b30f3d2bf6c9e07f04a3696d8d65d9fb31d60e9437ad1d82b54744ded051b0d6853e0b3f6019fcf565aed12e37df1fccc8fef416ade7b4bdfba0f0f7b86d2ce1cf0f17ec6d69e5d51ca1b50ab511f433007dbb9cc1da694e94eb4c629da5edd14b7d8ff2fdb9feb503d6bd68d3de96a7d43a9febce49e3b015f39197513bf17dd09ace4525d6886f15c95c7b087942e615c7a96fd01e077408995770995dc94422cb9f7f2494dba9cff13d3b8f4a7b88527f3f1e94fafb2d7f8e5a28bb5a6acf9fe664be172edb3c722ff70947a90efeadb497f8e3ddb0997f6e62963e63dd83a436eb15ebbd64a68e87d2ef629827690e92ebcd007f8e44fb9f72dd69ee3b65f729fd6d7c5ff24992f3afd89bd4d7e794bfd8fb84cd1a4c737f84ec529d4a7b5b5446882da53242c88ffcc3408669ba2df5eccb3ecf94cb9c27977bbfc95f876f6e5b26f928bc4cafd49d6dd985cf49e6d31efc31e58cf7d8d51867c3e84348076a5ce83f2eee33e31ee3c39593cf36a6f135406fe68a996bba155a93efee5d13e6f3881f6b258f2b7f3031c8625f4f8c74dd827ed671d57ea2e7f5a078d463776f42d1eac2f7ede763bdd93b78c5ee5ee4d731c8928383cae1c420f7590ffb07e5fe3bf93a6e76308dfb0e5116ec759e8ff9477a874bcaa4c2c7eeb293ebd9af15cbd5f5d7cb25cbb3ca66f3eca4aaefe5f4ef854e539e6ecfbb1bb83c89427ee7fec4888c776ab2d27e854e6f4bab16d0da97dfccfa5e4c0f99c6becd3384768cadbb1cc115b39552cffc74fffc877cff50eee1c10fff297f36a3dd57197d3bba9c64176333b12dd6181fd5fab8f327b0213c5e8d9be3659fa17661bec14c951cd7edc5343d628c0c80a691e7ff85629a5e417356a3a9ff7c314d5ad0bca9d1a89f2ba6c9089abc46d3736b318dcafb934fa749dc524ce3177d2ea7cbd35a4c1312f9e834ea96629a3a41a3d7aba7a998a65e9435a4cb737331cd1a918f4e53ffa9629a4641f3675d9e8dc5346da2ac3ff3fd45e84aed17f6bd92fb91b437e86bcbb099fe04ab1bcce77d9ec1aa83991e8c23d8f9840b697ea4f568697923cd29d37a59dd696b9a43a6a559ddb3d6b42a999661751d9634554b53953a8f956f8a4cf3232d67e1d3d24248cb5ad23439eb903664c9b342a6d523addfc2a7a5ad41da494b9a5ba635222d65c9534b6b435ab4208df6c87db0974b13a7ad73922386b9ce79299f1f6ce7d47766ccc367d6e3b116bc20237c067754153ec8daa74826f299f7aa640fc39e3a15f64d5be316cc81b0cd7c3f58ec9746ee16fbd6224ecab5ddd8bb36caa83e28e2fc457bec7dc3e9219bf7130ed8f845ce225f18f69bfb43d23fa47d5e69d39d98a327f16700f03592777f941dc41c8225167fc7806cb3562f7acfc56aa3c55809b0be5c7a58e4c7fd8c49fa9c55824fe898b9fa5e4a67393dbd27925003c9ae1e9d47cee3aa9c9f0f3831cf39894e255daf61e46b25bbfc08614fe93937cd23075426e91f1d17fda152b2795d7dc7d3435206c54c63272fedaff336fd92b6f7c87d440ff2c8922e91163dbbbfbe86d64ee67e6df76c59faeafcbd1c4d16a38fb24966bf96da53ea3b0b9b28df1910cf1563f47e5099f634ed5d65d15f15c3b7f5b2c35d69a6f5551a9b44f7979643e39ae67753bd2dcfae2ceffe98dffb31b5874907a28f351a7d8c9e4d58ca28fd9c51aedbac6b04d2a5e83b1d5f74de786494bf1756a6ef207d949ecfc8fed6313e1eaca70f95d4c5107c5e0f7c5e0f64adc0fa6908b20e41d621fe3e9578fe9cd3758c7909fd6d86755ce3be467b0788d6f0a5fa6b704ea93495ef43505ab787f4bc326bee33e279aa8947fa6fb0991567bbd1c7570c0c9f6d74910cc35d37727db63a6f5c991d6b2cd29a27d2a17a04cf559f1e17cf1318ef827ef3f8ca4870bda7a36e66577767686536f8609a9d6d73d1bb6fc3dd213e76ef38bb5fad818ee9595ab6a5b3bec69e17eb0ff263eb5c6f497bacc21eab68d78ab1fafa5eb7b9af9f542227d33750fff641ef5d8dfc7dc66ab3fe459c7a01c535625d58a7aec43c7428c77d19f89e5867397d83d3f95a2bc9fd7d0ff7fd830be85941f4e3c5f4f5f6f40b39fd3fdad12741bffb6ee2e9cd1f4cf74adad4474bd3ce67b44f67d0b26b4bd32e63f49cc4a00d7fb834ed5534dfe60cdae83f94a6fd28d18e9ae4fdfbd2b43712ed8849de0f95a6bd8568332679af2a4ddb41b4674cf27eb034eddd447bc2246fb834ed4344fb0393bc9797a6fdaee6b37e41f85f7afeef2dcdf3acc5cfd5e5af2bcdf3a2c5ffd5f5535b9ae7b4c52fd6ebb3a434cfa0c55fd6ebf39ed23c1e8b1fadd7676199fe6ef1aff5fa84caf47b8bdfadd7676e99fe6ff1c7f5fa04ca8c038b9faed7e7fc32e3c1e2bfebf539afccb8b0f8f57a7dfc65c687c5dfd7ebe32b334ec0c3eceae32d335e882767539fc965c60df1646dea33a14cbf269e9336f5f194e9d7c493b2a98fd38e077d9ae8a3beab8ae8f5fdef72ef989bf77c936eaf5c2f9ce812f74cbbbf7b3ceffb14cd555c56fe8e02f7f5777784f233131edaafa1b96b52b2cbc37d4363fe520f17cf5f3d4f959ebf128ea279602eafbb8d7e355ad33cc06953367ad5684df300a765fcfb024db763ed87969fbf9b1d91d3e9db0ae76ff5719bfa7fbb4cfd59c9fe3c3743ef1cb415f3f494e6994f3ca9161b3f4129c9b38078a2cd763ab4f51544fbdc5c5ae7265f41b4cf274bd39a7c05d13e378dbf8f84378cbf8f446f187f1f49adb5d1b9bd2ee6737a1b3faba758179c967dac34ad49179c36bca634ad49179c366ae363f514eb42c86be36369b4263f44c8bbaa34ad8d9d9b5fcad7ea71d8da39417f75e9324c6d23e4b1f1b7345a93bf25f467e36f69b4261f4ae8cfc6dfd2686d7c2891ff65a5796c7c2821bf8ddfa5f1d8f850423fcbcab441b10f25eab3b4348f8d0f25ea53539ac7c68712f5b1f1bbf4be5fec4389fa5c58660c14fb50a23ef3cbf4ef627f48d42758a65f15fb43a23e367e97c663e30f89facc2acd63e30f89fa9c5ba66f16fb29a23ed3cbd883623f52d4c7c6efd2c74bb1df25ea5355c63ed8cd39549f4965c60ff10cd9d4a7b2cc5828f6bb447d6cfc02bd7d8c759cc8dfc62fd0dbc558c7cd377cadd2fe80bdbf25df1177989e27390afdb0aadf17deaf1a36ede38edb172bdc233ba0444ea5afd5fd8e35fc5bb2a5057e078fabbfb8c0ef08c5a18736cd1f801e6ed1e6912cd74380eb6c55695aaedf3e83367a4d69dabb35fb57adb79fc8ff43064f469b879dbec1417a265338b72e32adaf2df449d0cb79ad9fe7bdc8b4beb6a5edb03cd7d178c2e1d23cb0e1d32d368ff3b0cb4af3909d7cc3862775a9ce23fa21d5b98a9e4315d47931cfbfce4a8bbcab781d3c963a08fa5a7b7a9245299465b1697d6da297b64029a60d2f2ea4555db67207322ee8ffdd56da92720bfa05f6f436720bfa7985f489d2f47339fd1c2bbd6d3d396daadaa213fb7ace275a76be95b6643d05fd79f6f436720b7abf95de566e4e1b9e66d1a1db56ee055c1fe758694bca2de8a7d8d3dbc82de827eaf477abcee48b1e27d6b72e5f878775d3b7f11d83f9a5b7bc88eb3cf87a59817c7338bf6ac72fcb6305e5097a57317d627ce589fe51cee6ebcfd4b4f78ce81991f17c91dbe01ad8e051c306d7ffa6d806abaf6a36b89b64ddaf3a76f7faf93b46fc9b20fe2d4478919146f16da6b4e84223add192965a60a47559d25848a4c12e918d32f29ba7c5efeee5df1f98f30b1a69094b1a9b63a4f558d2c201238dde312828ef0291d6e334d19fafc5c972f226fa99461acfcb94963ad7c4a798f29b21f5e032c9ebd7e28acb08bfcb48b39611f589b47a57b20b7daa5775cafca66af19ca7202dec95f5b7f0a4a668f1c5e5b0c9469ab92ed189b28ea6ba8427687136faaa30d28af4e531f199f5e596f5779be471697136fa72186945fa12ef67caf70d8bdf872b3786f6b0c8ebe9698563487da2780cf51c2c1c4309e37d0e43c673645d6dd2a255527ea5382d35d948dbaf148e4b36491b5f96fc2618e3ae8759f2ab30d27a2d694c35d2d29634bd4d1cfabb3c46794ed9f72c723087160f1e65fc6d52fc0ea5d1266116792d5d51d82689fb6c7ccbafe96dd2b39d9e293f2cebefa6b31bcea0ef697e32d9697e8e028bba8db8b093bf63cac22e238e397ceea803748b8db8147f3fc05c1ffbefb52ddffbcd177d2db8d895a5eff5e9dbbe60c095db3bd9657ade1e90ef38d27e606a8ee9393c8bb0cc04d3f7a7ac8087d1b708e159bc9edaf77d9055eb9b9afd337fa74ffebbd177b9dd7516d1cc31d3ecb7cf27c0f5394d94bdb6afb0ec9e31caee1947d93d63949d9a64375ef64ea6f7f70f8deaefddff097d08f7fc8c8235fcbdad7fe17da847bca328dfb3e92d94df983bece5a732c7929fcb554e7eadbd9dd49f5627fcbf24ffe10584abdb32e7c5422bb5eba9f4bd265dbf80f817bafc3fd4c64989f7b8f5b55bc17b20b50339fe8c9cce7429dec7d7fb6db0f6aec2be4bfd7691b9af763afa4ea717615c66f9b8ace763f0c68271c9e3d40ddab8e463aebffa19f318a7f7a59a58e7023ef6fad7fea038edd87c9fbb86be45fa5e719a779ecf1da6b407298dde81d1de23a16fe6307ec5d8ef3ff194c64b7a1672dcff24c5f1f74976c29e1e773904ed8edf8978d146077b07389f1cef9abce78b72ab77972f77ed778acbad7edcbedcaadf8c5dae77baac6f728cfa7ed3a6bedf2851df97c651df29b2bedbc7a8ef5e9bfa3e58a2be2f8ca3beaaac6f7c8cfaeeb6a9ef3d25eafbb3b1cb8d7e41945b353a467d77dad43759a2be47c62e97dd2aca3d71a796afb85f9532f312e8dd267e368090b755d0adfdb2c1d740dfe83c5d9e8f7d5a969730f8a254de53639477b32c2f6ef03553794f8c51de27657951838f74b6ea3b639477a3d4c3a8c147f6e2e863639417117c47df32f8c896acfad618e5ad15f9af1a34f8aea77cf68f51dec745fe47df34f898827cf615f07595e4bf4ef2ffc9a41fe2df334efe6b25ffef4d7a22fe7bc7c9df20faead1d3067f27f1ef1a27ff3592ff3706ff1ee2df394efeab457f38fa8aa97c6a87ce71f2af94fc2f99ca27feede3e40f4bfe170dfe03c47fc738f95748fe5f9afa0dd53f3e4efee592ffe7a67145fcd171f2d74afe9f9ac6b372e6e4daec38f96b84ddd8f1a8bddd4b495b76f48861f7a28a2873c78ff432e91d01778a9d397962607ce5461788f155f550f972577dafb8dcaaa70bcb3d8672d7fe719cf59d2decd68efbc6a8ef1336f53d5458ee49aaef6fc759df73859dadea1aa3be8fd9d4f7d1c272fba9beaf8cb3be53859e77bc5aec4b85bdd2c69d284e8b4e91edf34a715a6a92485bf572711a9b28cb7bc9a6bc4a59deaf6dca5345bb54f5da94e71669ab7e65539e4bb6e70b36e539e41cf50b9bf2e4fa345ee04bc7c43ad565fb2ddd8a7d05df76d23a997c7e7f3dff6e24156b5c59f84d1dada112aafc7e38c3f62af42e4badf15df005194732d17e3bff3624c1df4775886f45552572bbea91df8f2af2fb5185bf4bcabfa38dba8c7cb0569e40674568f729f9ed30cf473b3ba4f03b54994f9977f98b9e0189efecc53a48d39da8b7fa78acd1f22de1fe7a45d45be5e71dd1f7b982b6fe312bad93be5350c5d998daf7096fe79d6afa0e9680b656a53c0fd3be81bd3c628c602ded92f27cbd9856e5dfacd1fbd6daf7b3be04ff2ea78abed5e5df17f27376c4fbd1f48e6edffacc9071964edc5c0767a9bea49f9b44df65d2f335f403fa0e81fab3f5fb66277f76a7af574f9bfb0c3f978feac6f9d3cc9c26ce728a8ff6dd94192e88b76ff382337db435207d974be776d29e35bdc34ddfbcd3fbdabc2f2ca6efde5d7c7fe2605dbfd81312cf0847f43d0c4f869e458e98f63046f43d0c6ef7c20ef96d88a29dc525ceb3aae1d7c2de717bf2552ed31c3a1b68259db993e5364e3bd3a8b787d74d3bf748d8c41e934de4672585f97daff87e2248b488a77113ab3f35babb8bafebab886eef9401d967d518ad770bfb480fef2332bddd9acefb4ba35ac1fbf54369e6afe3f6e19fad74e8fbfc7c277a075cd0d4df564c736a541b1f8246fd6c31cd718d6692a0e969b3d2041f22ddaf445b75e749ffe27cc69058973466787df8bb75e0a1ef3ca53c2d4575433f589a3ecd0aebd6d35c5247227db3ad8eda3299c27cea3715e7536fcaa7fe936575adebb1a7b158ee4e67705f5afb8edf7a364fc967ebbb135d8abe5774f268427e9b63c41ddb71e6edbed3486344d6e713e2bb12535bd2b7258fa52b6cf6696cecc71194715cda0f3e4e45fe0bb53313e4189c95a990e57dd45a9e45bfd75ad3857e434cd36fb243a974128d2abf41e3df3dd469dfa8e4824f8e4583f9f3e9348dfb09868cb005e76932aad7949751fd3b7b19fde397f1c038643c34060dfa01c69b43f4876e6963561adfcaa5d63ea5a7d17c62938f2fa154f26ff891def5e77c3eb9edcacff8b679c07be2b0395f91df897db29f953e27549e41417323e984cea2e0fd6101d9edf6b8beefa936b3c3fe8c9c37eed2e3939e1a76b86b50b709225d89938e351ba4ddc39ec2e664f2bace65bc8f6cf8beb476ded3a83c5b23ebec29cacb43e76fd1b91e7b279ecaf2333ccc793c4c79b04a2d8e9e2f50ff76ce8f93bd1f259dce842d8ab4f6f2e7a99426e691a8d3e0513ddcae618e9667e3650be672d37776da396eda797b7d9b33c35447fd6cb7057caee0f34adfddeaa05646f061a35ec17d2a2bf1add53bd846de71b7d13bd116fc5910978739b81ec6d506cc69d6b96d79e5747f43266bd57d71df0857fe679351ef1f3bd541fe4c5f972fe110fee71add2f23bfbdcf9bc9fd6dfad178c72893fda29ef70bd8a3387da02bbec9cb14f6897bff9f1e9f4573ab389fb33f1f740df0739df722e467821cbb3f41fe25ff1ee12bea04bebe4cad3dc3d7e4c74e6c13e7c677e2fafe2f27dd29c6d7fca9aa7b936eafc2e353ab7627dd61c6f7a8523bee49ba1b18df6f4a1dfdd724fc5cbe8792aac275b3d8d748adda85a9829ea9eca3351cd585cf5fb0153e3ab32a9ae6f6c147e739f1eb0770ddc0e3e979ae2867ed6ff99ee0b1a32342be14c9d72ef24ddce7c4dad29c2f9d1724f2dc63caf37a5996d607022cf84de31efea5a3a4ce134accaf721f78b62c23e6f7733f6d3bbf57e91c1e267ec7c41dd0be1579a4fcfad4ecaf5dcf443b99f3d1de755cfb7099771d8bd6f749b581e7e5535d323fe4e3514df9557fd159cfcf56e267378d5fc601edccdb21fd3b7c6d3ddaa1169d4f339edf1ae0ebdfb92467749464e6dffaf7aa8ab6e7b0578f33f62182e2db11de7fe93b12e8e70f857a0b6bfadf39feba310f957fa6fffed3f66d50ddf9b6eaa59d936b3a5f41d433c0fef27a9e7899ce3310f2d1994fae51a3aed51d64af41734a7b8ea3edcdf57932b9f2671e8c2d3bbdc3a1c922e729af699ee236acc85e8a3370e9fc0561dfc43e989893c4b99c0e41cbf81e148d313acf5fac8d8f8c529fa533b9c4f7c71ebe27181367078b7db0c695741eda283fff60b93c8757a487cd6739f7ed5287b47325faee53df2ca30bfbf38e139a2e3c5c175c2705e70d34b0c8e9f4e5fa33656e93e473fafdf299b2b07fdbb567cad4863eda1f107304ef0b222fb137639a3f789f30d2427a9ab8af13e780c8b8d2fde3e84f30366b45b907def172455c3d9d1d99b797a3417b6ffb19f4a54549f58053eeb38c8ab5df5d26bf3160f21bdb4d7e63b38ddff8c05fe457d6d533c4c1967f333da55856cd7eaffa33e69fd99075a226ebee2e313eff4fc80c9f65ce18f2fe9ebe6d80bc9e775eb7817758b73b4ed03b7a9075cadf4eb76f43e610c9ec1f4bbfc7cdefb9dabcbbf2b6ec8738ef363e5a640bc976cd3f22ed59a11d847d7f42d8c123263b78c462070b6dae6efbee5187cac86e7b26be4fda716dcf879f694e7bb9d2a730cec15fdbafcf3b25e7c8c27326698f87fba77c3f3e5549fe08b59dd81f8d735b7eb03e23f7849ab57d55b7f85e40f81dfc7cfe803ccfbcd72ff62942ae5c77e2c93fc2de5e4c677e88b9d0c3b4bc6205e7a0cb39e24575589c4f41eb4bd2d9ca514eb350bb064da73ac8cbeec9e44dfbe3a5cf2de4be9897fb357b5daedc19e6ade6fd4aeb4fecd802f15b38d1e9fabb17e26ccf51d086805925f64b4aeef5f1dfcfe3be4bd4387ff2e4fd7796d8dfd3cf0ca4df95b3febe12dfcb5ecccf4519a1b565acc7cf9218a374be8df67e2edf8bee48bf29bf65669153e9ab0abe650ef179aff02c0e1ed773be36178afc132cf66c174bdeddc1f76663cfeec7b547e1d73ddd54aea29dab13d3ce83badd7c4e95573c43aa8b0f635ecdede56b87d465f26c777ede3be7b95775697e8cb4438f68ba97bf6b22e8d321eddc9611714609e5cb64bee1e5e23eacddd759d29715957b8f6a918dd5624eee153edb8e9f6832608ce60af38a2e193baff045b04d3fd6ebf1252dbd414b7fcf99feaa5f14e6cb168d9d6fea42c8f883d2f9a6428579a6e68f9d6774ae68ef7ab4f11a537b379adabb4d6fefdd71d13f7c1d09d94f7a40db6be24b9bf832061ff5cb44421f533eb7876c67b7e11bbb4cfd25a0c97fdedbea8be2772f46d0bf15cdee76abf93cd91cb2efe25e415fcf8838fedb71f1aca64bff3c5ac75ef93ad61c4fd3f78531ed37e1fa773c2afa45d5c376befcdbd1837c4e6299438ea6cced466de6dc6ff475beaffd3675aded07193af56aededd674c4cf62166b954396f1e2b4ca60e9df8a99defcdb58f47b8fa6b32d0bcf1caedda79fc7bcb7d295a57df36eb542eeb927b89d4faab5a30567f59edcf1756e4fa5ddd76dcbb4ccf4d855b5a35a1eb05f0ae5c3f968bf9ba5d6703e3fecb0ff94f86d8d1faa150565ee4ff0f5de4c7adf41f816b93aa42d554fa32ff5eae783d1de3d3f1f69cda99ceed75bf2217d8bbea52a911cfaa2df9533d340ff53f8de3e64117538998f4ccd4c30d338bbf998e27e7bc49b91cf6cebe91c5d4143e7543da995eda2358d3893d69c7e888f1b67599a27d3cc36ef4385f50a3ea296f3adf2fcb7516bc46f5b625de3e2efc8edb9ff4dac2d5cfcfd9f3d27de907d03f3b262f9dd4b63be84af3272e6c0aaf633c7563d25da7cd5f3e679b3bb47a1760d88b4a3f7907cb03f0eda771263d67dd51916fd9c3fc49f375da9c92fee132bf97317be47c5f97f46fe6bd77c7eaed707fcbc8c677fc57d0091fe73fe1e82e00d1bfd13ed7a9f2ae3d5f71b6daf3afabea46625fd6505f41d6a85a45f618e2f3577f33d06e99bc8fc969bf97cb456f408fb29eabd6d196c872cbbe712bddd9e946b44ddaf89ce91f92d2d907bbb0a1f31301a64035a794bcce97c9f434febb948cf7f0fd2682fcbc87f5653ff89d7adfe96f56c3a71b69c97de5161fc370af7549d3edbb692ce5bcbd26f6e228f3cfac22be3df23d2de2119283cdffbd8fd7f2ae15f15f4599f9b4dc21c343c9e3eaa9565fa2da749915919da679d8cf962d0e74e21ac1e14bf63a2d11c986cd0ac1df0b98f213c71969fc758afefddbd5942d662df55fae8fa79ed62ef9b3f2f94bfb5c5bf4390367da078af5bfacd3789df891d4bbfda19eae4ff43fed7c9ff97fe708eea4adf888ce73935ad5b8a74771eff2d027adf89f1b3cdf9ef7979e5397cfc8cc4c9fc3cc03dc256f2fd2e492f7ef702fd48fe864c648236df0558c4c1bf33ad94e7a15658db4294133095237fa7a68bbeaf50af10bf99a0ff3e888947938d4d2a6ce363363407268bf74d78feacc46f798d046b6d7feb2aabfdce9ff6bb56913bd585e2bd20572e529131ae9b33d3b43313e57b43a3b4aea66f5722719aeb645cbd8cdbc5cfa71fe167bfbf26fc0ce215bf4147bf735b07bd86c56ff58a3c476262eea3fb61317ee91d2231a6931df47ce578ce59af32f91ed36892ff3e92e8a37dbbc46f20257b434c8ba3df602299a56f9193e70df2394fcf37a1fdd6b125bf9d323fc8a9e7d7a19ef797c88536f4cbdf3318e136ad467ff74adcd71ae751be3ddd862dba65ba6eed742aea0ed9f4bae35a96cde709d2915d1d7696d62d7c21537e3d467e053a1f976e5d7f8d7cf44d92f94c2afe4c4e8c03f37b3205e380db1b8c037a2f4cf31563f23784e91e79cee472a22ccde6d19997ba5fd6236c89f0d1a83d02b4172c79d90cc19bb6e7e563d8cf6da8fccd49d0f696a10de9b4a2aceb4d6585cf11fc3d65f8eb2cfc51333fb77ff4db9446df11cf884cfdd5d297a8fd7af2fab5e81bbc8f89dfe65c99e53e86b687d29590eb11ba16cf3eb47d39995e14c7d7590bb9cde0ef83d2fb29b23f8dc8f61fb68ce1117ace5ba2ed0bf6a062f23d587a6f99f220ddd07a551f6ba827dab02a667a5f925f67da98b43539ed1c597aaed9c5cf99ad9f4afb89f081c3e2bee71cba9767cf56e8ba295d5e85561e4fbfb7309de2f9ef4fd5893d797b9a1093bf0bc8f7e9ed69eab4dfb4e3bf4dc07fb3a6fffeb3d63dad0faedbdab2215073ebbc9a25cb36ddba287065c3074d771f6cda82c409186b5b3634fed3bc9a8bd77f62c1bc960b039799684aa51017631fd9b0aea569f37b03f35ac4fd38ca5b42945b377f6a7353db668437addbbc7ed386f5818d9b5b376cd9b2b5b995e7f3d90d5b9a0208af5eb765fd7bda366e010145b12deb0281002fb775eb96cd8175ebd76fd9d0d2c2584bb3885fddba2ef2a9407313cf0df78d32be7e53d30deb361909ad32feda9bb66c58b7de145f23e337dcdcdcb465dd968d1b5a021f5cb76913cf0c7fad4b447aebc5226ca9b9e8c6662a77dd2d1011badad8827c2eba71cbba9b3798c4602d92af908eb175b2bcabb66e8eb46e6c428db6346ebd79c3e6d6968bb6882adeb26ed3d60d2d4cfead93f9acbbb8145f21c3baa592be568697c870990ceb643d2eb693af85b548fe16c9df22f95b247f8bc6bf5c8697ca70498d0c97087dc97c5a653ead329f5699cf81db61f4f1f7a40c9f93e131199e94e16b321c92218b89d02bc319325c20c31a195e6db96fb0dc5f27c3eb651895e11d32dc25c33d327cce727f4c86bf96e190e59ec50bef2b2cf75ecbfd0ccb7d40de2f90e172cb7dd8727fb5e5bec1727f9de5fe7acbfd4d96fb66cbfdad96fb68bc509f7758ee3b2df7bb2cf7f1cabf4db87361f9f4ffecf6911b900d2dad1b37372e0ab434ddbca1f5265c865a026d5b9a28ea86a6a6d6c08deb3692056ddbd87a5360c3ad1b5b0391a6f51b02f3d62f0a3436055a9b02376edcbc3ef099a6ad5b02b76cd8bcbe69cbe209ecc6ad3093ad376d08446edad81cd8d812580f3338fbbfeceeff6f7677d205621cfcad42c6dedd20c24ea6000ec059cd98ebfd07981bf0002a50015402138089c024d04c06a600558097753acf413815fc3e84d310be0b988e6b3f30a3ba939d0b9c07cc046601e7031700d54000980dcc0182c05c601e301f08010b800b8185c0bb8145c07b80c5c045400db004b818580ad4029700cb803a60397029f05ee07dc00ae032e072e0fd4018b25e01393f80f083085722bc12e155a86b3d7035f021e0ef80bf07ae01fe1bf00fa0590534001f063e023dac46782dd2fe3bf2f828b006f7d701ff087c0cf7ff047c1cf804f03f10b716b81e5807dc004480f5c006a4df08340237011b11f749e053c026e0666033d0043423fdd3c016a0056845dc56e016a00db8152dfc19e0b3c0e780db80cf03ffecddcdbe00448176e0762006c4c1b30de80012c8ef0ee08bc097802f03db817f01ee047600f4ef2ee02b35bb5912d889ebaf0277035dc02ee05f91d73dc06ee05ee06bc07dc0fdc01ee001e041d0ed05f6015f071e02f623fe61e01bc037816f018f008f028f01df060e80ee71e03bc041e010f004e2bf0b74034f024f01ff061c069e06be077c1ff80190029e017e08fc083802fc187816e8019e037e02fc14f819f03cf03f819f03478163c02f50e62f811780e3c0af8017815ee0d7c0bfb3247ba97a37fb0fe8fd65e07f01af00278093e07f15f80dd0079c027e0b9c06d2c06bc0ef80df037f005e07fe08fc093803f4036f006f02678101e0cfc02090018680b780616004c802a3400ec8577303f011691a578b60aeb40bec5afaafe6be7cfe7aa013781a780d98767f3e1f063601bb8023403f306b4f3e7f35701b70003805cc78209fbf0688028780d780590fe6f30d401c7812781d08eccde7af05ee009e06fa81d67df9fcf31274cdbe2ec2b1b0a744dc1ecbf534e47735701b700038094c7a289f5f0eac073a81a781d78119fbf3f9954033b0e8e17cfeba47203f701daeef455c1ce101e01430e31ba83310050e01af01b3be89fa7d0bf54618079e045e07ee40dcd34000e807e622cfe7905f16707d0734b89ff128ca066e051e068e03158fe5f32b8066e05ee079200b2cf836ca01e2143e9ecfef048e0087707f0af01e001fb009b817780e1800e68286a1bc59c072e05aa019b803d807a48097812160d2419403ac043e0e3403db81878114f0323000780f810e58015c07b402db813dc0d3c071a01f98f404e88095c0c7815b819dc001e079e014b0e2bbd029703dd00adc01a49e4259c01030eddf40f734e4ff1eea0b6481daefa31e08b7236d13aeb7e3da7518e5fc08b43f409d536867c233a823d24f017311bf0f71a780b988bf1eb4b701bb80d78143c0cb88bff687900d584ff4c031c4571c010f701bca08231c40b8093289e1345b8eab39320cf2b0a1176d0034fc1a32038ffc3b74f5523e7fc5a68d8d9be17960e9ddb465f60476dd6f90ff09e47512ed83ebe75e45fd5e811c887b0450e45f54fe31c5f1bf01b9ee10f9'
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
                ISP_RET_BAD_INITIALIZATION = 0xE4
                ISP_RET_FLASH_BUSY = 0xE5

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

                return (op, reason, text)


        def chunks(l, n):
            """Yield successive n-sized chunks from l."""
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

            def recv_one_return(self):
                timeout_init = time.time()
                data = b''
                # find start boarder
                #sys.stdout.write('[RECV one return] raw data: ')
                while 1:
                    if time.time() - timeout_init > ISP_RECEIVE_TIMEOUT:
                        raise TimeoutError
                    c = self._port.read(1)
                    #sys.stdout.write(binascii.hexlify(c).decode())
                    sys.stdout.flush()
                    if c == b'\xc0':
                        break

                in_escape = False
                while 1:
                    if time.time() - timeout_init > ISP_RECEIVE_TIMEOUT:
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
                    self._port.write(b'\xc0\xd2\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc0')
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
                op, reason, text = ISPResponse.parse(self.recv_one_return())
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
                total_chunk = math.ceil(len(data)/DATAFRAME_SIZE)

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
                    if (time_delta > 1):
                        speed = str(int((n + 1) * DATAFRAME_SIZE / 1024.0 / time_delta)) + 'kiB/s'
                    printProgressBar(n+1, total_chunk, prefix = 'Downloading ISP:', suffix = speed, length = columns - 35)

            def dump_to_flash(self, data, address=0):
                '''
                typedef struct __attribute__((packed)) {
                    uint8_t op;
                    int32_t checksum; /* All the fields below are involved in the calculation of checksum */
                    uint32_t address;
                    uint32_t data_len;
                    uint8_t data_buf[1024];
                } isp_request_t;
                '''

                DATAFRAME_SIZE = ISP_FLASH_DATA_FRAME_SIZE
                data_chunks = chunks(data, DATAFRAME_SIZE)
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



            def flash_erase(self):
                #KFlash.log('[DEBUG] erasing spi flash.')
                # self._port.write(b'\xc0\xd3\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc0')
                # op, reason, text = FlashModeResponse.parse(self.recv_one_return())
                #KFlash.log('MAIX return op:', FlashModeResponse.Operation(op).name, 'reason:',
                #      FlashModeResponse.ErrorCode(reason).name)
                retry_count = 0
                while 1:
                    self.checkKillExit()
                    # Write ISP_FLASH_ERASE_NONBLOCKING command
                    self._port.write(b'\xc0\xd8\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc0')
                    retry_count = retry_count + 1
                    try:
                        op, reason, text = FlashModeResponse.parse(self.recv_one_return())
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
                    if FlashModeResponse.Operation(op) == FlashModeResponse.Operation.ISP_FLASH_ERASE_NONBLOCKING and FlashModeResponse.ErrorCode(reason) == FlashModeResponse.ErrorCode.ISP_RET_OK:
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
                # Check and waiting erasing process
                retry_count = 0
                while 1:
                    self.checkKillExit()
                    # Write ISP_FLASH_STATUS command
                    self._port.write(b'\xc0\xd9\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc0')
                    retry_count = retry_count + 1
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

                    total_chunk = math.ceil(len(firmware_with_header)/ISP_FLASH_DATA_FRAME_SIZE)
                    # Slice download firmware
                    data_chunks = chunks(firmware_with_header, ISP_FLASH_DATA_FRAME_SIZE)  # 4kiB for a sector, 16kiB for dataframe
                else:
                    total_chunk = math.ceil(len(firmware_bin)/ISP_FLASH_DATA_FRAME_SIZE)
                    data_chunks = chunks(firmware_bin, ISP_FLASH_DATA_FRAME_SIZE)

                time_start = time.time()
                for n, chunk in enumerate(data_chunks):
                    self.checkKillExit()
                    chunk = chunk.ljust(ISP_FLASH_DATA_FRAME_SIZE, b'\x00')  # align by size of dataframe

                    # Download a dataframe
                    #KFlash.log('[INFO]', 'Write firmware data piece')
                    self.dump_to_flash(chunk, address= n * ISP_FLASH_DATA_FRAME_SIZE + address_offset)
                    columns, lines = TerminalSize.get_terminal_size((100, 24), terminal)
                    time_delta = time.time() - time_start
                    speed = ''
                    if (time_delta > 1):
                        speed = str(int((n + 1) * ISP_FLASH_DATA_FRAME_SIZE / 1024.0 / time_delta)) + 'kiB/s'
                    printProgressBar(n+1, total_chunk, prefix = 'Programming BIN:', filename=filename, suffix = speed, length = columns - 35)

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

        # udpate args for none terminal call
        if not terminal:
            args.port = dev
            args.baudrate = baudrate
            args.noansi = noansi
            args.sram = sram
            args.Board = board
            args.firmware = file

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

        # 0. Check firmware
        try:
            firmware_bin = open(args.firmware, 'rb')
        except OSError:
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
                        pass
            except Exception as e:
                KFlash.log()
                raise_exception( Exception("Greeting fail, check serial port ("+str(e)+")" ) )

        # Don't remove this line
        # Dangerous, here are dinosaur infested!!!!!
        ISP_RECEIVE_TIMEOUT = 5

        KFlash.log()
        KFlash.log(INFO_MSG,"Greeting Message Detected, Start Downloading ISP",BASH_TIPS['DEFAULT'])

        if manually_set_the_board and (not args.Slow):
            if (args.baudrate >= 1500000) or args.sram:
                self.loader.change_baudrate_stage0(args.baudrate)

        # 2. download bootloader and firmware
        if args.sram:
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
            isp_loader = open(args.bootloader, 'rb').read() if args.bootloader else ISP_PROG
            self.loader.install_flash_bootloader(isp_loader)

        # Boot the code from SRAM
        self.loader.boot()

        if args.sram:
            # Dangerous, here are dinosaur infested!!!!!
            # Don't touch this code unless you know what you are doing
            self.loader._port.baudrate = args.baudrate
            KFlash.log(INFO_MSG,"Boot user code from SRAM", BASH_TIPS['DEFAULT'])
            if(args.terminal == True):
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
            firmware_bin.close()
            with backports.tempfile.TemporaryDirectory() as tmpdir:
                try:
                    with zipfile.ZipFile(args.firmware) as zf:
                        zf.extractall(tmpdir)
                except zipfile.error:
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
