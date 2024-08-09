// Code generated by 'ccgo stdlib\gen.c -crt-import-path "" -export-defines "" -export-enums "" -export-externs X -export-fields F -export-structs "" -export-typedefs "" -header -hide _OSSwapInt16,_OSSwapInt32,_OSSwapInt64 -o stdlib\stdlib_windows_arm64.go -pkgname stdlib', DO NOT EDIT.

package stdlib

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
	CHAR_BIT                                        = 8
	CHAR_MAX                                        = 127
	CHAR_MIN                                        = -128
	DUMMYSTRUCTNAME                                 = 0
	DUMMYSTRUCTNAME1                                = 0
	DUMMYSTRUCTNAME2                                = 0
	DUMMYSTRUCTNAME3                                = 0
	DUMMYSTRUCTNAME4                                = 0
	DUMMYSTRUCTNAME5                                = 0
	DUMMYUNIONNAME                                  = 0
	DUMMYUNIONNAME1                                 = 0
	DUMMYUNIONNAME2                                 = 0
	DUMMYUNIONNAME3                                 = 0
	DUMMYUNIONNAME4                                 = 0
	DUMMYUNIONNAME5                                 = 0
	DUMMYUNIONNAME6                                 = 0
	DUMMYUNIONNAME7                                 = 0
	DUMMYUNIONNAME8                                 = 0
	DUMMYUNIONNAME9                                 = 0
	EXIT_FAILURE                                    = 1
	EXIT_SUCCESS                                    = 0
	INT_MAX                                         = 2147483647
	INT_MIN                                         = -2147483648
	LLONG_MAX                                       = 9223372036854775807
	LLONG_MIN                                       = -9223372036854775808
	LONG_LONG_MAX                                   = 9223372036854775807
	LONG_LONG_MIN                                   = -9223372036854775808
	LONG_MAX                                        = 2147483647
	LONG_MIN                                        = -2147483648
	MB_LEN_MAX                                      = 1
	MINGW_DDK_H                                     = 0
	MINGW_HAS_DDK_H                                 = 1
	MINGW_HAS_SECURE_API                            = 1
	MINGW_SDK_INIT                                  = 0
	RAND_MAX                                        = 0x7fff
	SCHAR_MAX                                       = 127
	SCHAR_MIN                                       = -128
	SHRT_MAX                                        = 32767
	SHRT_MIN                                        = -32768
	UCHAR_MAX                                       = 255
	UINT_MAX                                        = 4294967295
	ULLONG_MAX                                      = 18446744073709551615
	ULONG_LONG_MAX                                  = 18446744073709551615
	ULONG_MAX                                       = 4294967295
	UNALIGNED                                       = 0
	USE___UUIDOF                                    = 0
	USHRT_MAX                                       = 65535
	WIN32                                           = 1
	WIN64                                           = 1
	WINNT                                           = 1
	X_AGLOBAL                                       = 0
	X_ALLOCA_S_HEAP_MARKER                          = 0xDDDD
	X_ALLOCA_S_MARKER_SIZE                          = 16
	X_ALLOCA_S_STACK_MARKER                         = 0xCCCC
	X_ALLOCA_S_THRESHOLD                            = 1024
	X_ANONYMOUS_STRUCT                              = 0
	X_ANONYMOUS_UNION                               = 0
	X_ARGMAX                                        = 100
	X_ARM64_                                        = 1
	X_CALL_REPORTFAULT                              = 0x2
	X_CONST_RETURN                                  = 0
	X_CRTNOALIAS                                    = 0
	X_CRTRESTRICT                                   = 0
	X_CRT_ABS_DEFINED                               = 0
	X_CRT_ALGO_DEFINED                              = 0
	X_CRT_ALLOCATION_DEFINED                        = 0
	X_CRT_ALTERNATIVE_IMPORTED                      = 0
	X_CRT_ATOF_DEFINED                              = 0
	X_CRT_DOUBLE_DEC                                = 0
	X_CRT_ERRNO_DEFINED                             = 0
	X_CRT_MANAGED_HEAP_DEPRECATE                    = 0
	X_CRT_PACKING                                   = 8
	X_CRT_PERROR_DEFINED                            = 0
	X_CRT_SECURE_CPP_OVERLOAD_SECURE_NAMES          = 0
	X_CRT_SECURE_CPP_OVERLOAD_SECURE_NAMES_MEMORY   = 0
	X_CRT_SECURE_CPP_OVERLOAD_STANDARD_NAMES        = 0
	X_CRT_SECURE_CPP_OVERLOAD_STANDARD_NAMES_COUNT  = 0
	X_CRT_SECURE_CPP_OVERLOAD_STANDARD_NAMES_MEMORY = 0
	X_CRT_SWAB_DEFINED                              = 0
	X_CRT_SYSTEM_DEFINED                            = 0
	X_CRT_TERMINATE_DEFINED                         = 0
	X_CRT_USE_WINAPI_FAMILY_DESKTOP_APP             = 0
	X_CRT_WPERROR_DEFINED                           = 0
	X_CRT_WSYSTEM_DEFINED                           = 0
	X_CVTBUFSIZE                                    = 349
	X_DIV_T_DEFINED                                 = 0
	X_DLL                                           = 0
	X_ERRCODE_DEFINED                               = 0
	X_FILE_OFFSET_BITS                              = 64
	X_FREEA_INLINE                                  = 0
	X_FREEENTRY                                     = 0
	X_GCC_LIMITS_H_                                 = 0
	X_HEAPBADBEGIN                                  = -3
	X_HEAPBADNODE                                   = -4
	X_HEAPBADPTR                                    = -6
	X_HEAPEMPTY                                     = -1
	X_HEAPEND                                       = -5
	X_HEAPINFO_DEFINED                              = 0
	X_HEAPOK                                        = -2
	X_HEAP_MAXREQ                                   = 0xFFFFFFFFFFFFFFE0
	X_INC_CORECRT                                   = 0
	X_INC_CORECRT_WSTDLIB                           = 0
	X_INC_CRTDEFS                                   = 0
	X_INC_CRTDEFS_MACRO                             = 0
	X_INC_MINGW_SECAPI                              = 0
	X_INC_STDLIB                                    = 0
	X_INC_STDLIB_S                                  = 0
	X_INC_VADEFS                                    = 0
	X_INC__MINGW_H                                  = 0
	X_INT128_DEFINED                                = 0
	X_INTPTR_T_DEFINED                              = 0
	X_MALLOC_H_                                     = 0
	X_MAX_DIR                                       = 256
	X_MAX_DRIVE                                     = 3
	X_MAX_ENV                                       = 32767
	X_MAX_EXT                                       = 256
	X_MAX_FNAME                                     = 256
	X_MAX_PATH                                      = 260
	X_MAX_WAIT_MALLOC_CRT                           = 60000
	X_MT                                            = 0
	X_M_ARM64                                       = 1
	X_ONEXIT_T_DEFINED                              = 0
	X_OUT_TO_DEFAULT                                = 0
	X_OUT_TO_MSGBOX                                 = 2
	X_OUT_TO_STDERR                                 = 1
	X_PGLOBAL                                       = 0
	X_PTRDIFF_T_                                    = 0
	X_PTRDIFF_T_DEFINED                             = 0
	X_QSORT_S_DEFINED                               = 0
	X_REPORT_ERRMODE                                = 3
	X_RSIZE_T_DEFINED                               = 0
	X_SECURECRT_FILL_BUFFER_PATTERN                 = 0xFD
	X_SIZE_T_DEFINED                                = 0
	X_SSIZE_T_DEFINED                               = 0
	X_TAGLC_ID_DEFINED                              = 0
	X_THREADLOCALEINFO                              = 0
	X_TIME32_T_DEFINED                              = 0
	X_TIME64_T_DEFINED                              = 0
	X_TIME_T_DEFINED                                = 0
	X_UCRT                                          = 0
	X_UINTPTR_T_DEFINED                             = 0
	X_USEDENTRY                                     = 1
	X_VA_LIST_DEFINED                               = 0
	X_W64                                           = 0
	X_WCHAR_T_DEFINED                               = 0
	X_WCTYPE_T_DEFINED                              = 0
	X_WIN32                                         = 1
	X_WIN32_WINNT                                   = 0x601
	X_WIN64                                         = 1
	X_WINT_T                                        = 0
	X_WRITE_ABORT_MSG                               = 0x1
	X_WSTDLIBP_DEFINED                              = 0
	X_WSTDLIB_DEFINED                               = 0
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

//===---- limits.h - Standard header for integer sizes --------------------===* *
//  Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
//  See https://llvm.org/LICENSE.txt for license information.
//  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// \*===----------------------------------------------------------------------===

// The system's limits.h may, in turn, try to #include_next GCC's limits.h.
//    Avert this #include_next madness.

// System headers include a number of constants from POSIX in <limits.h>.
//    Include it if we're hosted.

// Many system headers try to "help us out" by defining these.  No really, we
//    know how big each datatype is.

// C90/99 5.2.4.2.1

// C2x 5.2.4.2.1
// FIXME: This is using the placeholder dates Clang produces for these macros
//    in C2x mode; switch to the correct values once they've been published.

// C99 5.2.4.2.1: Added long long.
//    C++11 18.3.3.2: same contents as the Standard C Library header <limits.h>.
//

// LONG_LONG_MIN/LONG_LONG_MAX/ULONG_LONG_MAX are a GNU extension.  It's too bad
//    that we don't have something like #pragma poison that could be used to
//    deprecate a macro - the code should just use LLONG_MAX and friends.
//

type X_onexit_t = uintptr /* stdlib.h:50:15 */

type X_div_t = struct {
	Fquot int32
	Frem  int32
} /* stdlib.h:60:11 */

type Div_t = X_div_t /* stdlib.h:63:5 */

type X_ldiv_t = struct {
	Fquot int32
	Frem  int32
} /* stdlib.h:65:11 */

type Ldiv_t = X_ldiv_t /* stdlib.h:68:5 */

type X_LDOUBLE = struct{ Fld [10]uint8 } /* stdlib.h:77:5 */

type X_CRT_DOUBLE = struct{ Fx float64 } /* stdlib.h:84:5 */

type X_CRT_FLOAT = struct{ Ff float32 } /* stdlib.h:88:5 */

type X_LONGDOUBLE = struct{ Fx float64 } /* stdlib.h:95:5 */

type X_LDBL12 = struct{ Fld12 [12]uint8 } /* stdlib.h:102:5 */

type X_purecall_handler = uintptr /* stdlib.h:143:16 */

type X_invalid_parameter_handler = uintptr /* stdlib.h:148:16 */

type Lldiv_t = struct {
	Fquot int64
	Frem  int64
} /* stdlib.h:724:61 */

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

// Return codes for _heapwalk()

// Values for _heapinfo.useflag

// The structure used to walk through the heap with _heapwalk.
type X_heapinfo = struct {
	F_pentry     uintptr
	F_size       Size_t
	F_useflag    int32
	F__ccgo_pad1 [4]byte
} /* malloc.h:46:11 */

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

// Return codes for _heapwalk()

// Values for _heapinfo.useflag

// The structure used to walk through the heap with _heapwalk.
type X_HEAPINFO = X_heapinfo /* malloc.h:50:5 */

var _ int8 /* gen.c:2:13: */
