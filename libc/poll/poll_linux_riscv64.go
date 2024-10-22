// Code generated by 'ccgo poll/gen.c -crt-import-path "" -export-defines "" -export-enums "" -export-externs X -export-fields F -export-structs "" -export-typedefs "" -header -hide _OSSwapInt16,_OSSwapInt32,_OSSwapInt64 -o poll/poll_linux_riscv64.go -pkgname poll', DO NOT EDIT.

package poll

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
	POLLERR            = 0x008
	POLLHUP            = 0x010
	POLLIN             = 0x001
	POLLNVAL           = 0x020
	POLLOUT            = 0x004
	POLLPRI            = 0x002
	POLLRDBAND         = 0x080
	POLLRDNORM         = 0x040
	POLLWRBAND         = 0x200
	POLLWRNORM         = 0x100
	X_ATFILE_SOURCE    = 1
	X_DEFAULT_SOURCE   = 1
	X_FEATURES_H       = 1
	X_FILE_OFFSET_BITS = 64
	X_LP64             = 1
	X_POSIX_C_SOURCE   = 200809
	X_POSIX_SOURCE     = 1
	X_STDC_PREDEF_H    = 1
	X_SYS_CDEFS_H      = 1
	X_SYS_POLL_H       = 1
	Linux              = 1
	Unix               = 1
)

type Ptrdiff_t = int64 /* <builtin>:3:26 */

type Size_t = uint64 /* <builtin>:9:23 */

type Wchar_t = int32 /* <builtin>:15:24 */

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

// Compatibility definitions for System V `poll' interface.
//    Copyright (C) 1994-2021 Free Software Foundation, Inc.
//    This file is part of the GNU C Library.
//
//    The GNU C Library is free software; you can redistribute it and/or
//    modify it under the terms of the GNU Lesser General Public
//    License as published by the Free Software Foundation; either
//    version 2.1 of the License, or (at your option) any later version.
//
//    The GNU C Library is distributed in the hope that it will be useful,
//    but WITHOUT ANY WARRANTY; without even the implied warranty of
//    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
//    Lesser General Public License for more details.
//
//    You should have received a copy of the GNU Lesser General Public
//    License along with the GNU C Library; if not, see
//    <https://www.gnu.org/licenses/>.

// Copyright (C) 1991-2021 Free Software Foundation, Inc.
//    This file is part of the GNU C Library.
//
//    The GNU C Library is free software; you can redistribute it and/or
//    modify it under the terms of the GNU Lesser General Public
//    License as published by the Free Software Foundation; either
//    version 2.1 of the License, or (at your option) any later version.
//
//    The GNU C Library is distributed in the hope that it will be useful,
//    but WITHOUT ANY WARRANTY; without even the implied warranty of
//    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
//    Lesser General Public License for more details.
//
//    You should have received a copy of the GNU Lesser General Public
//    License along with the GNU C Library; if not, see
//    <https://www.gnu.org/licenses/>.

// These are defined by the user (or the compiler)
//    to specify the desired environment:
//
//    __STRICT_ANSI__	ISO Standard C.
//    _ISOC99_SOURCE	Extensions to ISO C89 from ISO C99.
//    _ISOC11_SOURCE	Extensions to ISO C99 from ISO C11.
//    _ISOC2X_SOURCE	Extensions to ISO C99 from ISO C2X.
//    __STDC_WANT_LIB_EXT2__
// 			Extensions to ISO C99 from TR 27431-2:2010.
//    __STDC_WANT_IEC_60559_BFP_EXT__
// 			Extensions to ISO C11 from TS 18661-1:2014.
//    __STDC_WANT_IEC_60559_FUNCS_EXT__
// 			Extensions to ISO C11 from TS 18661-4:2015.
//    __STDC_WANT_IEC_60559_TYPES_EXT__
// 			Extensions to ISO C11 from TS 18661-3:2015.
//    __STDC_WANT_IEC_60559_EXT__
// 			ISO C2X interfaces defined only in Annex F.
//
//    _POSIX_SOURCE	IEEE Std 1003.1.
//    _POSIX_C_SOURCE	If ==1, like _POSIX_SOURCE; if >=2 add IEEE Std 1003.2;
// 			if >=199309L, add IEEE Std 1003.1b-1993;
// 			if >=199506L, add IEEE Std 1003.1c-1995;
// 			if >=200112L, all of IEEE 1003.1-2004
// 			if >=200809L, all of IEEE 1003.1-2008
//    _XOPEN_SOURCE	Includes POSIX and XPG things.  Set to 500 if
// 			Single Unix conformance is wanted, to 600 for the
// 			sixth revision, to 700 for the seventh revision.
//    _XOPEN_SOURCE_EXTENDED XPG things and X/Open Unix extensions.
//    _LARGEFILE_SOURCE	Some more functions for correct standard I/O.
//    _LARGEFILE64_SOURCE	Additional functionality from LFS for large files.
//    _FILE_OFFSET_BITS=N	Select default filesystem interface.
//    _ATFILE_SOURCE	Additional *at interfaces.
//    _DYNAMIC_STACK_SIZE_SOURCE Select correct (but non compile-time constant)
// 			MINSIGSTKSZ, SIGSTKSZ and PTHREAD_STACK_MIN.
//    _GNU_SOURCE		All of the above, plus GNU extensions.
//    _DEFAULT_SOURCE	The default set of features (taking precedence over
// 			__STRICT_ANSI__).
//
//    _FORTIFY_SOURCE	Add security hardening to many library functions.
// 			Set to 1 or 2; 2 performs stricter checks than 1.
//
//    _REENTRANT, _THREAD_SAFE
// 			Obsolete; equivalent to _POSIX_C_SOURCE=199506L.
//
//    The `-ansi' switch to the GNU C compiler, and standards conformance
//    options such as `-std=c99', define __STRICT_ANSI__.  If none of
//    these are defined, or if _DEFAULT_SOURCE is defined, the default is
//    to have _POSIX_SOURCE set to one and _POSIX_C_SOURCE set to
//    200809L, as well as enabling miscellaneous functions from BSD and
//    SVID.  If more than one of these are defined, they accumulate.  For
//    example __STRICT_ANSI__, _POSIX_SOURCE and _POSIX_C_SOURCE together
//    give you ISO C, 1003.1, and 1003.2, but nothing else.
//
//    These are defined by this file and are used by the
//    header files to decide what to declare or define:
//
//    __GLIBC_USE (F)	Define things from feature set F.  This is defined
// 			to 1 or 0; the subsequent macros are either defined
// 			or undefined, and those tests should be moved to
// 			__GLIBC_USE.
//    __USE_ISOC11		Define ISO C11 things.
//    __USE_ISOC99		Define ISO C99 things.
//    __USE_ISOC95		Define ISO C90 AMD1 (C95) things.
//    __USE_ISOCXX11	Define ISO C++11 things.
//    __USE_POSIX		Define IEEE Std 1003.1 things.
//    __USE_POSIX2		Define IEEE Std 1003.2 things.
//    __USE_POSIX199309	Define IEEE Std 1003.1, and .1b things.
//    __USE_POSIX199506	Define IEEE Std 1003.1, .1b, .1c and .1i things.
//    __USE_XOPEN		Define XPG things.
//    __USE_XOPEN_EXTENDED	Define X/Open Unix things.
//    __USE_UNIX98		Define Single Unix V2 things.
//    __USE_XOPEN2K        Define XPG6 things.
//    __USE_XOPEN2KXSI     Define XPG6 XSI things.
//    __USE_XOPEN2K8       Define XPG7 things.
//    __USE_XOPEN2K8XSI    Define XPG7 XSI things.
//    __USE_LARGEFILE	Define correct standard I/O things.
//    __USE_LARGEFILE64	Define LFS things with separate names.
//    __USE_FILE_OFFSET64	Define 64bit interface as default.
//    __USE_MISC		Define things from 4.3BSD or System V Unix.
//    __USE_ATFILE		Define *at interfaces and AT_* constants for them.
//    __USE_DYNAMIC_STACK_SIZE Define correct (but non compile-time constant)
// 			MINSIGSTKSZ, SIGSTKSZ and PTHREAD_STACK_MIN.
//    __USE_GNU		Define GNU extensions.
//    __USE_FORTIFY_LEVEL	Additional security measures used, according to level.
//
//    The macros `__GNU_LIBRARY__', `__GLIBC__', and `__GLIBC_MINOR__' are
//    defined by this file unconditionally.  `__GNU_LIBRARY__' is provided
//    only for compatibility.  All new code should use the other symbols
//    to test for features.
//
//    All macros listed above as possibly being defined by this file are
//    explicitly undefined if they are not explicitly defined.
//    Feature-test macros that are not defined by the user or compiler
//    but are implied by the other feature-test macros defined (or by the
//    lack of any definitions) are defined by the file.
//
//    ISO C feature test macros depend on the definition of the macro
//    when an affected header is included, not when the first system
//    header is included, and so they are handled in
//    <bits/libc-header-start.h>, which does not have a multiple include
//    guard.  Feature test macros that can be handled from the first
//    system header included are handled here.

// Undefine everything, so we get a clean slate.

// Suppress kernel-name space pollution unless user expressedly asks
//    for it.

// Convenience macro to test the version of gcc.
//    Use like this:
//    #if __GNUC_PREREQ (2,8)
//    ... code requiring gcc 2.8 or later ...
//    #endif
//    Note: only works for GCC 2.0 and later, because __GNUC_MINOR__ was
//    added in 2.0.

// Similarly for clang.  Features added to GCC after version 4.2 may
//    or may not also be available in clang, and clang's definitions of
//    __GNUC(_MINOR)__ are fixed at 4 and 2 respectively.  Not all such
//    features can be queried via __has_extension/__has_feature.

// Whether to use feature set F.

// _BSD_SOURCE and _SVID_SOURCE are deprecated aliases for
//    _DEFAULT_SOURCE.  If _DEFAULT_SOURCE is present we do not
//    issue a warning; the expectation is that the source is being
//    transitioned to use the new macro.

// If _GNU_SOURCE was defined by the user, turn on all the other features.

// If nothing (other than _GNU_SOURCE and _DEFAULT_SOURCE) is defined,
//    define _DEFAULT_SOURCE.

// This is to enable the ISO C2X extension.

// This is to enable the ISO C11 extension.

// This is to enable the ISO C99 extension.

// This is to enable the ISO C90 Amendment 1:1995 extension.

// If none of the ANSI/POSIX macros are defined, or if _DEFAULT_SOURCE
//    is defined, use POSIX.1-2008 (or another version depending on
//    _XOPEN_SOURCE).

// Some C libraries once required _REENTRANT and/or _THREAD_SAFE to be
//    defined in all multithreaded code.  GNU libc has not required this
//    for many years.  We now treat them as compatibility synonyms for
//    _POSIX_C_SOURCE=199506L, which is the earliest level of POSIX with
//    comprehensive support for multithreaded code.  Using them never
//    lowers the selected level of POSIX conformance, only raises it.

// Features part to handle 64-bit time_t support.
//    Copyright (C) 2021 Free Software Foundation, Inc.
//    This file is part of the GNU C Library.
//
//    The GNU C Library is free software; you can redistribute it and/or
//    modify it under the terms of the GNU Lesser General Public
//    License as published by the Free Software Foundation; either
//    version 2.1 of the License, or (at your option) any later version.
//
//    The GNU C Library is distributed in the hope that it will be useful,
//    but WITHOUT ANY WARRANTY; without even the implied warranty of
//    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
//    Lesser General Public License for more details.
//
//    You should have received a copy of the GNU Lesser General Public
//    License along with the GNU C Library; if not, see
//    <https://www.gnu.org/licenses/>.

// We need to know the word size in order to check the time size.
// Determine the wordsize from the preprocessor defines.  RISC-V version.
//    Copyright (C) 2002-2021 Free Software Foundation, Inc.
//    This file is part of the GNU C Library.
//
//    The GNU C Library is free software; you can redistribute it and/or
//    modify it under the terms of the GNU Lesser General Public
//    License as published by the Free Software Foundation; either
//    version 2.1 of the License, or (at your option) any later version.
//
//    The GNU C Library is distributed in the hope that it will be useful,
//    but WITHOUT ANY WARRANTY; without even the implied warranty of
//    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
//    Lesser General Public License for more details.
//
//    You should have received a copy of the GNU Lesser General Public
//    License along with the GNU C Library.  If not, see
//    <https://www.gnu.org/licenses/>.

// Bit size of the time_t type at glibc build time, RISC-V case.
//    Copyright (C) 2020-2021 Free Software Foundation, Inc.
//    This file is part of the GNU C Library.
//
//    The GNU C Library is free software; you can redistribute it and/or
//    modify it under the terms of the GNU Lesser General Public
//    License as published by the Free Software Foundation; either
//    version 2.1 of the License, or (at your option) any later version.
//
//    The GNU C Library is distributed in the hope that it will be useful,
//    but WITHOUT ANY WARRANTY; without even the implied warranty of
//    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
//    Lesser General Public License for more details.
//
//    You should have received a copy of the GNU Lesser General Public
//    License along with the GNU C Library; if not, see
//    <https://www.gnu.org/licenses/>.

// Determine the wordsize from the preprocessor defines.  RISC-V version.
//    Copyright (C) 2002-2021 Free Software Foundation, Inc.
//    This file is part of the GNU C Library.
//
//    The GNU C Library is free software; you can redistribute it and/or
//    modify it under the terms of the GNU Lesser General Public
//    License as published by the Free Software Foundation; either
//    version 2.1 of the License, or (at your option) any later version.
//
//    The GNU C Library is distributed in the hope that it will be useful,
//    but WITHOUT ANY WARRANTY; without even the implied warranty of
//    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
//    Lesser General Public License for more details.
//
//    You should have received a copy of the GNU Lesser General Public
//    License along with the GNU C Library.  If not, see
//    <https://www.gnu.org/licenses/>.

// RV32 and RV64 both use 64-bit time_t

// The function 'gets' existed in C89, but is impossible to use
//    safely.  It has been removed from ISO C11 and ISO C++14.  Note: for
//    compatibility with various implementations of <cstdio>, this test
//    must consider only the value of __cplusplus when compiling C++.

// GNU formerly extended the scanf functions with modified format
//    specifiers %as, %aS, and %a[...] that allocate a buffer for the
//    input using malloc.  This extension conflicts with ISO C99, which
//    defines %a as a standalone format specifier that reads a floating-
//    point number; moreover, POSIX.1-2008 provides the same feature
//    using the modifier letter 'm' instead (%ms, %mS, %m[...]).
//
//    We now follow C99 unless GNU extensions are active and the compiler
//    is specifically in C89 or C++98 mode (strict or not).  For
//    instance, with GCC, -std=gnu11 will have C99-compliant scanf with
//    or without -D_GNU_SOURCE, but -std=c89 -D_GNU_SOURCE will have the
//    old extension.

// Get definitions of __STDC_* predefined macros, if the compiler has
//    not preincluded this header automatically.
// Copyright (C) 1991-2021 Free Software Foundation, Inc.
//    This file is part of the GNU C Library.
//
//    The GNU C Library is free software; you can redistribute it and/or
//    modify it under the terms of the GNU Lesser General Public
//    License as published by the Free Software Foundation; either
//    version 2.1 of the License, or (at your option) any later version.
//
//    The GNU C Library is distributed in the hope that it will be useful,
//    but WITHOUT ANY WARRANTY; without even the implied warranty of
//    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
//    Lesser General Public License for more details.
//
//    You should have received a copy of the GNU Lesser General Public
//    License along with the GNU C Library; if not, see
//    <https://www.gnu.org/licenses/>.

// This macro indicates that the installed library is the GNU C Library.
//    For historic reasons the value now is 6 and this will stay from now
//    on.  The use of this variable is deprecated.  Use __GLIBC__ and
//    __GLIBC_MINOR__ now (see below) when you want to test for a specific
//    GNU C library version and use the values in <gnu/lib-names.h> to get
//    the sonames of the shared libraries.

// Major and minor version number of the GNU C library package.  Use
//    these macros to test for features in specific releases.

// This is here only because every header file already includes this one.
// Copyright (C) 1992-2021 Free Software Foundation, Inc.
//    This file is part of the GNU C Library.
//
//    The GNU C Library is free software; you can redistribute it and/or
//    modify it under the terms of the GNU Lesser General Public
//    License as published by the Free Software Foundation; either
//    version 2.1 of the License, or (at your option) any later version.
//
//    The GNU C Library is distributed in the hope that it will be useful,
//    but WITHOUT ANY WARRANTY; without even the implied warranty of
//    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
//    Lesser General Public License for more details.
//
//    You should have received a copy of the GNU Lesser General Public
//    License along with the GNU C Library; if not, see
//    <https://www.gnu.org/licenses/>.

// We are almost always included from features.h.

// The GNU libc does not support any K&R compilers or the traditional mode
//    of ISO C compilers anymore.  Check for some of the combinations not
//    supported anymore.

// Some user header file might have defined this before.

// Compilers that lack __has_attribute may object to
//        #if defined __has_attribute && __has_attribute (...)
//    even though they do not need to evaluate the right-hand side of the &&.
//    Similarly for __has_builtin, etc.

// All functions, except those with callbacks or those that
//    synchronize memory, are leaf functions.

// GCC can always grok prototypes.  For C++ programs we add throw()
//    to help it optimize the function calls.  But this only works with
//    gcc 2.8.x and egcs.  For gcc 3.4 and up we even mark C functions
//    as non-throwing using a function attribute since programs can use
//    the -fexceptions options for C code as well.

// These two macros are not used in glibc anymore.  They are kept here
//    only because some other projects expect the macros to be defined.

// For these things, GCC behaves the ANSI way normally,
//    and the non-ANSI way under -traditional.

// This is not a typedef so `const __ptr_t' does the right thing.

// C++ needs to know that types and declarations are C, not C++.

// Fortify support.

// Use __builtin_dynamic_object_size at _FORTIFY_SOURCE=3 when available.

// Support for flexible arrays.
//    Headers that should use flexible arrays only if they're "real"
//    (e.g. only if they won't affect sizeof()) should test
//    #if __glibc_c99_flexarr_available.

// __asm__ ("xyz") is used throughout the headers to rename functions
//    at the assembly language level.  This is wrapped by the __REDIRECT
//    macro, in order to support compilers that can do this some other
//    way.  When compilers don't support asm-names at all, we have to do
//    preprocessor tricks instead (which don't have exactly the right
//    semantics, but it's the best we can do).
//
//    Example:
//    int __REDIRECT(setpgrp, (__pid_t pid, __pid_t pgrp), setpgid);

//
// #elif __SOME_OTHER_COMPILER__
//
// # define __REDIRECT(name, proto, alias) name proto; 	_Pragma("let " #name " = " #alias)

// GCC and clang have various useful declarations that can be made with
//    the '__attribute__' syntax.  All of the ways we use this do fine if
//    they are omitted for compilers that don't understand it.

// At some point during the gcc 2.96 development the `malloc' attribute
//    for functions was introduced.  We don't want to use it unconditionally
//    (although this would be possible) since it generates warnings.

// Tell the compiler which arguments to an allocation function
//    indicate the size of the allocation.

// At some point during the gcc 2.96 development the `pure' attribute
//    for functions was introduced.  We don't want to use it unconditionally
//    (although this would be possible) since it generates warnings.

// This declaration tells the compiler that the value is constant.

// At some point during the gcc 3.1 development the `used' attribute
//    for functions was introduced.  We don't want to use it unconditionally
//    (although this would be possible) since it generates warnings.

// Since version 3.2, gcc allows marking deprecated functions.

// Since version 4.5, gcc also allows one to specify the message printed
//    when a deprecated function is used.  clang claims to be gcc 4.2, but
//    may also support this feature.

// At some point during the gcc 2.8 development the `format_arg' attribute
//    for functions was introduced.  We don't want to use it unconditionally
//    (although this would be possible) since it generates warnings.
//    If several `format_arg' attributes are given for the same function, in
//    gcc-3.0 and older, all but the last one are ignored.  In newer gccs,
//    all designated arguments are considered.

// At some point during the gcc 2.97 development the `strfmon' format
//    attribute for functions was introduced.  We don't want to use it
//    unconditionally (although this would be possible) since it
//    generates warnings.

// The nonnull function attribute marks pointer parameters that
//    must not be NULL.

// The returns_nonnull function attribute marks the return type of the function
//    as always being non-null.

// If fortification mode, we warn about unused results of certain
//    function calls which can lead to problems.

// Forces a function to be always inlined.
// The Linux kernel defines __always_inline in stddef.h (283d7573), and
//    it conflicts with this definition.  Therefore undefine it first to
//    allow either header to be included first.

// Associate error messages with the source location of the call site rather
//    than with the source location inside the function.

// GCC 4.3 and above with -std=c99 or -std=gnu99 implements ISO C99
//    inline semantics, unless -fgnu89-inline is used.  Using __GNUC_STDC_INLINE__
//    or __GNUC_GNU_INLINE is not a good enough check for gcc because gcc versions
//    older than 4.3 may define these macros and still not guarantee GNU inlining
//    semantics.
//
//    clang++ identifies itself as gcc-4.2, but has support for GNU inlining
//    semantics, that can be checked for by using the __GNUC_STDC_INLINE_ and
//    __GNUC_GNU_INLINE__ macro definitions.

// GCC 4.3 and above allow passing all anonymous arguments of an
//    __extern_always_inline function to some other vararg function.

// It is possible to compile containing GCC extensions even if GCC is
//    run in pedantic mode if the uses are carefully marked using the
//    `__extension__' keyword.  But this is not generally available before
//    version 2.8.

// __restrict is known in EGCS 1.2 and above, and in clang.
//    It works also in C++ mode (outside of arrays), but only when spelled
//    as '__restrict', not 'restrict'.

// ISO C99 also allows to declare arrays as non-overlapping.  The syntax is
//      array_name[restrict]
//    GCC 3.1 and clang support this.
//    This syntax is not usable in C++ mode.

// Describes a char array whose address can safely be passed as the first
//    argument to strncpy and strncat, as the char array is not necessarily
//    a NUL-terminated string.

// Undefine (also defined in libc-symbols.h).
// Copies attributes from the declaration or type referenced by
//    the argument.

// The #ifndef lets Gnulib avoid including these on non-glibc
//    platforms, where the includes typically do not exist.
// Determine the wordsize from the preprocessor defines.  RISC-V version.
//    Copyright (C) 2002-2021 Free Software Foundation, Inc.
//    This file is part of the GNU C Library.
//
//    The GNU C Library is free software; you can redistribute it and/or
//    modify it under the terms of the GNU Lesser General Public
//    License as published by the Free Software Foundation; either
//    version 2.1 of the License, or (at your option) any later version.
//
//    The GNU C Library is distributed in the hope that it will be useful,
//    but WITHOUT ANY WARRANTY; without even the implied warranty of
//    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
//    Lesser General Public License for more details.
//
//    You should have received a copy of the GNU Lesser General Public
//    License along with the GNU C Library.  If not, see
//    <https://www.gnu.org/licenses/>.

// Properties of long double type.  ldbl-128 version.
//    Copyright (C) 2016-2021 Free Software Foundation, Inc.
//    This file is part of the GNU C Library.
//
//    The GNU C Library is free software; you can redistribute it and/or
//    modify it under the terms of the GNU Lesser General Public
//    License  published by the Free Software Foundation; either
//    version 2.1 of the License, or (at your option) any later version.
//
//    The GNU C Library is distributed in the hope that it will be useful,
//    but WITHOUT ANY WARRANTY; without even the implied warranty of
//    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
//    Lesser General Public License for more details.
//
//    You should have received a copy of the GNU Lesser General Public
//    License along with the GNU C Library; if not, see
//    <https://www.gnu.org/licenses/>.

// long double is distinct from double, so there is nothing to
//    define here.

// __glibc_macro_warning (MESSAGE) issues warning MESSAGE.  This is
//    intended for use in preprocessor macros.
//
//    Note: MESSAGE must be a _single_ string; concatenation of string
//    literals is not supported.

// Generic selection (ISO C11) is a C-only feature, available in GCC
//    since version 4.9.  Previous versions do not provide generic
//    selection, even though they might set __STDC_VERSION__ to 201112L,
//    when in -std=c11 mode.  Thus, we must check for !defined __GNUC__
//    when testing __STDC_VERSION__ for generic selection support.
//    On the other hand, Clang also defines __GNUC__, so a clang-specific
//    check is required to enable the use of generic selection.

// Designates a 1-based positional argument ref-index of pointer type
//    that can be used to access size-index elements of the pointed-to
//    array according to access mode, or at least one element when
//    size-index is not provided:
//      access (access-mode, <ref-index> [, <size-index>])

// Designates dealloc as a function to call to deallocate objects
//    allocated by the declared function.

// Specify that a function such as setjmp or vfork may return
//    twice.

// If we don't have __REDIRECT, prototypes will be missing if
//    __USE_FILE_OFFSET64 but not __USE_LARGEFILE[64].

// Decide whether we can define 'extern inline' functions in headers.

// This is here only because every header file already includes this one.
//    Get the definitions of all the appropriate `__stub_FUNCTION' symbols.
//    <gnu/stubs.h> contains `#define __stub_FUNCTION' when FUNCTION is a stub
//    that will always return failure (and set errno to ENOSYS).
// This file is automatically generated.
//    This file selects the right generated file of `__stub_FUNCTION' macros
//    based on the architecture being compiled for.

// Determine the wordsize from the preprocessor defines.  RISC-V version.
//    Copyright (C) 2002-2021 Free Software Foundation, Inc.
//    This file is part of the GNU C Library.
//
//    The GNU C Library is free software; you can redistribute it and/or
//    modify it under the terms of the GNU Lesser General Public
//    License as published by the Free Software Foundation; either
//    version 2.1 of the License, or (at your option) any later version.
//
//    The GNU C Library is distributed in the hope that it will be useful,
//    but WITHOUT ANY WARRANTY; without even the implied warranty of
//    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
//    Lesser General Public License for more details.
//
//    You should have received a copy of the GNU Lesser General Public
//    License along with the GNU C Library.  If not, see
//    <https://www.gnu.org/licenses/>.

// This file is automatically generated.
//    It defines a symbol `__stub_FUNCTION' for each function
//    in the C library which is a stub, meaning it will fail
//    every time called, usually setting errno to ENOSYS.

// Get the platform dependent bits of `poll'.
// Copyright (C) 1997-2021 Free Software Foundation, Inc.
//    This file is part of the GNU C Library.
//
//    The GNU C Library is free software; you can redistribute it and/or
//    modify it under the terms of the GNU Lesser General Public
//    License as published by the Free Software Foundation; either
//    version 2.1 of the License, or (at your option) any later version.
//
//    The GNU C Library is distributed in the hope that it will be useful,
//    but WITHOUT ANY WARRANTY; without even the implied warranty of
//    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
//    Lesser General Public License for more details.
//
//    You should have received a copy of the GNU Lesser General Public
//    License along with the GNU C Library; if not, see
//    <https://www.gnu.org/licenses/>.

// Event types that can be polled for.  These bits may be set in `events'
//    to indicate the interesting event types; they will appear in `revents'
//    to indicate the status of the file descriptor.

// These values are defined in XPG4.2.

// Event types always implicitly polled for.  These bits need not be set in
//    `events', but they will appear in `revents' to indicate the status of
//    the file descriptor.

// Type used for the number of file descriptors.
type Nfds_t = uint64 /* poll.h:33:27 */

// Data structure describing a polling request.
type Pollfd = struct {
	Ffd      int32
	Fevents  int16
	Frevents int16
} /* poll.h:36:1 */

// Define some inlines helping to catch common problems.

var _ uint8 /* gen.c:2:13: */
