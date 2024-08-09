// Code generated by 'ccgo stdio\gen.c -crt-import-path "" -export-defines "" -export-enums "" -export-externs X -export-fields F -export-structs "" -export-typedefs "" -header -hide _OSSwapInt16,_OSSwapInt32,_OSSwapInt64 -o stdio\stdio_windows_arm64.go -pkgname stdio', DO NOT EDIT.

package stdio

import (
	"math"
	"reflect"
	"sync/atomic"
	"unsafe"
)

var _ = math.Pi
var _ reflect.Kind
var _ atomic.Value
var _ unsafe.Pointer

const (
	BUFSIZ                                                 = 512
	DUMMYSTRUCTNAME                                        = 0
	DUMMYSTRUCTNAME1                                       = 0
	DUMMYSTRUCTNAME2                                       = 0
	DUMMYSTRUCTNAME3                                       = 0
	DUMMYSTRUCTNAME4                                       = 0
	DUMMYSTRUCTNAME5                                       = 0
	DUMMYUNIONNAME                                         = 0
	DUMMYUNIONNAME1                                        = 0
	DUMMYUNIONNAME2                                        = 0
	DUMMYUNIONNAME3                                        = 0
	DUMMYUNIONNAME4                                        = 0
	DUMMYUNIONNAME5                                        = 0
	DUMMYUNIONNAME6                                        = 0
	DUMMYUNIONNAME7                                        = 0
	DUMMYUNIONNAME8                                        = 0
	DUMMYUNIONNAME9                                        = 0
	EOF                                                    = -1
	FILENAME_MAX                                           = 260
	FOPEN_MAX                                              = 20
	MINGW_DDK_H                                            = 0
	MINGW_HAS_DDK_H                                        = 1
	MINGW_HAS_SECURE_API                                   = 1
	MINGW_SDK_INIT                                         = 0
	SEEK_CUR                                               = 1
	SEEK_END                                               = 2
	SEEK_SET                                               = 0
	STDERR_FILENO                                          = 2
	STDIN_FILENO                                           = 0
	STDOUT_FILENO                                          = 1
	SYS_OPEN                                               = 20
	TMP_MAX                                                = 32767
	TMP_MAX_S                                              = 32767
	UNALIGNED                                              = 0
	USE___UUIDOF                                           = 0
	WIN32                                                  = 1
	WIN64                                                  = 1
	WINNT                                                  = 1
	X_AGLOBAL                                              = 0
	X_ANONYMOUS_STRUCT                                     = 0
	X_ANONYMOUS_UNION                                      = 0
	X_ARGMAX                                               = 100
	X_ARM64_                                               = 1
	X_CONST_RETURN                                         = 0
	X_CRTNOALIAS                                           = 0
	X_CRTRESTRICT                                          = 0
	X_CRT_ALTERNATIVE_IMPORTED                             = 0
	X_CRT_DIRECTORY_DEFINED                                = 0
	X_CRT_INTERNAL_LOCAL_PRINTF_OPTIONS                    = 4
	X_CRT_INTERNAL_LOCAL_SCANF_OPTIONS                     = 2
	X_CRT_INTERNAL_PRINTF_LEGACY_MSVCRT_COMPATIBILITY      = 0x0008
	X_CRT_INTERNAL_PRINTF_LEGACY_THREE_DIGIT_EXPONENTS     = 0x0010
	X_CRT_INTERNAL_PRINTF_LEGACY_VSPRINTF_NULL_TERMINATION = 0x0001
	X_CRT_INTERNAL_PRINTF_LEGACY_WIDE_SPECIFIERS           = 0x0004
	X_CRT_INTERNAL_PRINTF_STANDARD_SNPRINTF_BEHAVIOR       = 0x0002
	X_CRT_INTERNAL_SCANF_LEGACY_MSVCRT_COMPATIBILITY       = 0x0004
	X_CRT_INTERNAL_SCANF_LEGACY_WIDE_SPECIFIERS            = 0x0002
	X_CRT_INTERNAL_SCANF_SECURECRT                         = 0x0001
	X_CRT_MANAGED_HEAP_DEPRECATE                           = 0
	X_CRT_PACKING                                          = 8
	X_CRT_PERROR_DEFINED                                   = 0
	X_CRT_SECURE_CPP_OVERLOAD_SECURE_NAMES                 = 0
	X_CRT_SECURE_CPP_OVERLOAD_SECURE_NAMES_MEMORY          = 0
	X_CRT_SECURE_CPP_OVERLOAD_STANDARD_NAMES               = 0
	X_CRT_SECURE_CPP_OVERLOAD_STANDARD_NAMES_COUNT         = 0
	X_CRT_SECURE_CPP_OVERLOAD_STANDARD_NAMES_MEMORY        = 0
	X_CRT_USE_WINAPI_FAMILY_DESKTOP_APP                    = 0
	X_CRT_WPERROR_DEFINED                                  = 0
	X_DLL                                                  = 0
	X_ERRCODE_DEFINED                                      = 0
	X_FILE_DEFINED                                         = 0
	X_FILE_OFFSET_BITS                                     = 64
	X_FILE_OFFSET_BITS_SET_FSEEKO                          = 0
	X_FILE_OFFSET_BITS_SET_FTELLO                          = 0
	X_FILE_OFFSET_BITS_SET_OFFT                            = 0
	X_FPOS_T_DEFINED                                       = 0
	X_INC_CORECRT                                          = 0
	X_INC_CRTDEFS_MACRO                                    = 0
	X_INC_MINGW_SECAPI                                     = 0
	X_INC_STDIO                                            = 0
	X_INC_STDIO_S                                          = 0
	X_INC_SWPRINTF_INL                                     = 0
	X_INC_VADEFS                                           = 0
	X_INC__MINGW_H                                         = 0
	X_INT128_DEFINED                                       = 0
	X_INTPTR_T_DEFINED                                     = 0
	X_IOB_ENTRIES                                          = 20
	X_IOFBF                                                = 0x0000
	X_IOLBF                                                = 0x0040
	X_IONBF                                                = 0x0004
	X_MT                                                   = 0
	X_M_ARM64                                              = 1
	X_NFILE                                                = 512
	X_NSTREAM_                                             = 512
	X_OFF64_T_DEFINED                                      = 0
	X_OFF_T_                                               = 0
	X_OFF_T_DEFINED                                        = 0
	X_OLD_P_OVERLAY                                        = 2
	X_PGLOBAL                                              = 0
	X_PTRDIFF_T_                                           = 0
	X_PTRDIFF_T_DEFINED                                    = 0
	X_P_DETACH                                             = 4
	X_P_NOWAIT                                             = 1
	X_P_NOWAITO                                            = 3
	X_P_OVERLAY                                            = 2
	X_P_WAIT                                               = 0
	X_P_tmpdir                                             = "\\"
	X_RSIZE_T_DEFINED                                      = 0
	X_SECURECRT_FILL_BUFFER_PATTERN                        = 0xFD
	X_SIZE_T_DEFINED                                       = 0
	X_SPAWNV_DEFINED                                       = 0
	X_SSIZE_T_DEFINED                                      = 0
	X_STDIO_CONFIG_DEFINED                                 = 0
	X_STDIO_DEFINED                                        = 0
	X_STDIO_S_DEFINED                                      = 0
	X_STDSTREAM_DEFINED                                    = 0
	X_SYS_OPEN                                             = 20
	X_TAGLC_ID_DEFINED                                     = 0
	X_THREADLOCALEINFO                                     = 0
	X_TIME32_T_DEFINED                                     = 0
	X_TIME64_T_DEFINED                                     = 0
	X_TIME_T_DEFINED                                       = 0
	X_TWO_DIGIT_EXPONENT                                   = 0x1
	X_UCRT                                                 = 0
	X_UINTPTR_T_DEFINED                                    = 0
	X_VA_LIST_DEFINED                                      = 0
	X_W64                                                  = 0
	X_WAIT_CHILD                                           = 0
	X_WAIT_GRANDCHILD                                      = 1
	X_WCHAR_T_DEFINED                                      = 0
	X_WCTYPE_T_DEFINED                                     = 0
	X_WIN32                                                = 1
	X_WIN32_WINNT                                          = 0x601
	X_WIN64                                                = 1
	X_WINT_T                                               = 0
	X_WSPAWN_DEFINED                                       = 0
	X_WSTDIO_DEFINED                                       = 0
	X_WSTDIO_S_DEFINED                                     = 0
)

type Ptrdiff_t = int64 /* <builtin>:3:26 */

type Size_t = uint64 /* <builtin>:9:23 */

type Wchar_t = uint16 /* <builtin>:15:24 */

type X__int128_t = struct {
	Flo int64
	Fhi int64
} /* <builtin>:21:43 */ // must match github.com/opentoys/sqlite/mathutil.Int128
type X__uint128_t = struct {
	Flo uint64
	Fhi uint64
} /* <builtin>:22:44 */ // must match github.com/opentoys/sqlite/mathutil.Int128

type X__builtin_va_list = uintptr /* <builtin>:46:14 */
type X__float128 = float64        /* <builtin>:47:21 */

type Va_list = X__builtin_va_list /* <builtin>:50:27 */

// *
// This file has no copyright assigned and is placed in the Public Domain.
// This file is part of the mingw-w64 runtime package.
// No warranty is given; refer to the file DISCLAIMER.PD within this package.

// *
// This file has no copyright assigned and is placed in the Public Domain.
// This file is part of the Wine project.
// No warranty is given; refer to the file DISCLAIMER.PD within this package.

// *
// This file has no copyright assigned and is placed in the Public Domain.
// This file is part of the mingw-w64 runtime package.
// No warranty is given; refer to the file DISCLAIMER.PD within this package.

// *
// This file has no copyright assigned and is placed in the Public Domain.
// This file is part of the mingw-w64 runtime package.
// No warranty is given; refer to the file DISCLAIMER.PD within this package.

// *
// This file has no copyright assigned and is placed in the Public Domain.
// This file is part of the mingw-w64 runtime package.
// No warranty is given; refer to the file DISCLAIMER.PD within this package.

// This macro holds an monotonic increasing value, which indicates
//    a specific fix/patch is present on trunk.  This value isn't related to
//    minor/major version-macros.  It is increased on demand, if a big
//    fix was applied to trunk.  This macro gets just increased on trunk.  For
//    other branches its value won't be modified.

// mingw.org's version macros: these make gcc to define
//    MINGW32_SUPPORTS_MT_EH and to use the _CRT_MT global
//    and the __mingwthr_key_dtor() function from the MinGW
//    CRT in its private gthr-win32.h header.

// Set VC specific compiler target macros.

// MS does not prefix symbols by underscores for 64-bit.
// As we have to support older gcc version, which are using underscores
//       as symbol prefix for x64, we have to check here for the user label
//       prefix defined by gcc.

// Special case nameless struct/union.

// MinGW-w64 has some additional C99 printf/scanf feature support.
//    So we add some helper macros to ease recognition of them.

// If _FORTIFY_SOURCE is enabled, some inline functions may use
//    __builtin_va_arg_pack().  GCC may report an error if the address
//    of such a function is used.  Set _FORTIFY_VA_ARG=0 in this case.

// Enable workaround for ABI incompatibility on affected platforms

// *
// This file has no copyright assigned and is placed in the Public Domain.
// This file is part of the mingw-w64 runtime package.
// No warranty is given; refer to the file DISCLAIMER.PD within this package.

// http://msdn.microsoft.com/en-us/library/ms175759%28v=VS.100%29.aspx
// Templates won't work in C, will break if secure API is not enabled, disabled

// https://blogs.msdn.com/b/sdl/archive/2010/02/16/vc-2010-and-memcpy.aspx?Redirected=true
// fallback on default implementation if we can't know the size of the destination

// Include _cygwin.h if we're building a Cygwin application.

// Target specific macro replacement for type "long".  In the Windows API,
//    the type long is always 32 bit, even if the target is 64 bit (LLP64).
//    On 64 bit Cygwin, the type long is 64 bit (LP64).  So, to get the right
//    sized definitions and declarations, all usage of type long in the Windows
//    headers have to be replaced by the below defined macro __LONG32.

// C/C++ specific language defines.

// Note the extern. This is needed to work around GCC's
// limitations in handling dllimport attribute.

// Attribute `nonnull' was valid as of gcc 3.3.  We don't use GCC's
//    variadiac macro facility, because variadic macros cause syntax
//    errors with  --traditional-cpp.

//  High byte is the major version, low byte is the minor.

// Allow both 0x1400 and 0xE00 to identify UCRT

// ===-------- vadefs.h ---------------------------------------------------===
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===-----------------------------------------------------------------------===

// Only include this if we are aiming for MSVC compatibility.
// *
// This file has no copyright assigned and is placed in the Public Domain.
// This file is part of the mingw-w64 runtime package.
// No warranty is given; refer to the file DISCLAIMER.PD within this package.

// *
// This file has no copyright assigned and is placed in the Public Domain.
// This file is part of the mingw-w64 runtime package.
// No warranty is given; refer to the file DISCLAIMER.PD within this package.

// for backward compatibility

type X__gnuc_va_list = X__builtin_va_list /* vadefs.h:24:29 */

type Ssize_t = int64 /* corecrt.h:45:35 */

type Rsize_t = Size_t /* corecrt.h:52:16 */

type Intptr_t = int64 /* corecrt.h:62:35 */

type Uintptr_t = uint64 /* corecrt.h:75:44 */

type Wint_t = uint16   /* corecrt.h:106:24 */
type Wctype_t = uint16 /* corecrt.h:107:24 */

type Errno_t = int32 /* corecrt.h:113:13 */

type X__time32_t = int32 /* corecrt.h:118:14 */

type X__time64_t = int64 /* corecrt.h:123:35 */

type Time_t = X__time64_t /* corecrt.h:138:20 */

type Threadlocaleinfostruct = struct {
	F_locale_pctype      uintptr
	F_locale_mb_cur_max  int32
	F_locale_lc_codepage uint32
} /* corecrt.h:430:1 */

type Pthreadlocinfo = uintptr /* corecrt.h:432:39 */
type Pthreadmbcinfo = uintptr /* corecrt.h:433:36 */

type Localeinfo_struct = struct {
	Flocinfo Pthreadlocinfo
	Fmbcinfo Pthreadmbcinfo
} /* corecrt.h:436:9 */

type X_locale_tstruct = Localeinfo_struct /* corecrt.h:439:3 */
type X_locale_t = uintptr                 /* corecrt.h:439:19 */

type TagLC_ID = struct {
	FwLanguage uint16
	FwCountry  uint16
	FwCodePage uint16
} /* corecrt.h:443:9 */

type LC_ID = TagLC_ID  /* corecrt.h:447:3 */
type LPLC_ID = uintptr /* corecrt.h:447:9 */

type Threadlocinfo = Threadlocaleinfostruct /* corecrt.h:482:3 */

type X_iobuf = struct{ F_Placeholder uintptr } /* stdio.h:33:3 */

type FILE = X_iobuf /* stdio.h:47:25 */

type X_off_t = int32 /* _mingw_off_t.h:5:16 */
type Off32_t = int32 /* _mingw_off_t.h:7:16 */

type X_off64_t = int64 /* _mingw_off_t.h:13:39 */
type Off64_t = int64   /* _mingw_off_t.h:15:39 */

type Off_t = Off64_t /* _mingw_off_t.h:24:17 */

type Fpos_t = int64 /* stdio.h:115:37 */

var _ int8 /* gen.c:2:13: */
