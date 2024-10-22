// Code generated by 'ccgo limits\gen.c -crt-import-path "" -export-defines "" -export-enums "" -export-externs X -export-fields F -export-structs "" -export-typedefs "" -header -hide _OSSwapInt16,_OSSwapInt32,_OSSwapInt64 -o limits\limits_windows_arm64.go -pkgname limits', DO NOT EDIT.

package limits

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
	CHAR_BIT           = 8
	CHAR_MAX           = 127
	CHAR_MIN           = -128
	INT_MAX            = 2147483647
	INT_MIN            = -2147483648
	LLONG_MAX          = 9223372036854775807
	LLONG_MIN          = -9223372036854775808
	LONG_LONG_MAX      = 9223372036854775807
	LONG_LONG_MIN      = -9223372036854775808
	LONG_MAX           = 2147483647
	LONG_MIN           = -2147483648
	MB_LEN_MAX         = 1
	PATH_MAX           = 260
	SCHAR_MAX          = 127
	SCHAR_MIN          = -128
	SHRT_MAX           = 32767
	SHRT_MIN           = -32768
	UCHAR_MAX          = 255
	UINT_MAX           = 4294967295
	ULLONG_MAX         = 18446744073709551615
	ULONG_LONG_MAX     = 18446744073709551615
	ULONG_MAX          = 4294967295
	USHRT_MAX          = 65535
	WIN32              = 1
	WIN64              = 1
	WINNT              = 1
	X_FILE_OFFSET_BITS = 64
	X_GCC_LIMITS_H_    = 0
	X_VA_LIST_DEFINED  = 0
	X_WIN32            = 1
	X_WIN64            = 1
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

var _ int8 /* gen.c:2:13: */
