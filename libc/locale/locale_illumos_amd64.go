// Code generated by 'ccgo locale/gen.c -crt-import-path "" -export-defines "" -export-enums "" -export-externs X -export-fields F -export-structs "" -export-typedefs "" -header -hide _OSSwapInt16,_OSSwapInt32,_OSSwapInt64 -ignore-unsupported-alignment -o locale/locale_illumos_amd64.go -pkgname locale', DO NOT EDIT.

package locale

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
	LC_ALL                          = 6   // locale_iso.h:102:1:
	LC_ALL_MASK                     = 63  // locale.h:80:1:
	LC_COLLATE                      = 3   // locale_iso.h:99:1:
	LC_COLLATE_MASK                 = 8   // locale.h:77:1:
	LC_CTYPE                        = 0   // locale_iso.h:96:1:
	LC_CTYPE_MASK                   = 1   // locale.h:74:1:
	LC_MESSAGES                     = 5   // locale_iso.h:101:1:
	LC_MESSAGES_MASK                = 32  // locale.h:79:1:
	LC_MONETARY                     = 4   // locale_iso.h:100:1:
	LC_MONETARY_MASK                = 16  // locale.h:78:1:
	LC_NUMERIC                      = 1   // locale_iso.h:97:1:
	LC_NUMERIC_MASK                 = 2   // locale.h:75:1:
	LC_TIME                         = 2   // locale_iso.h:98:1:
	LC_TIME_MASK                    = 4   // locale.h:76:1:
	TEXTDOMAINMAX                   = 256 // libintl.h:62:1:
	X_ALIGNMENT_REQUIRED            = 1   // isa_defs.h:262:1:
	X_BIT_FIELDS_LTOH               = 0   // isa_defs.h:245:1:
	X_BOOL_ALIGNMENT                = 1   // isa_defs.h:248:1:
	X_CHAR_ALIGNMENT                = 1   // isa_defs.h:249:1:
	X_CHAR_IS_SIGNED                = 0   // isa_defs.h:247:1:
	X_DMA_USES_PHYSADDR             = 0   // isa_defs.h:281:1:
	X_DONT_USE_1275_GENERIC_NAMES   = 0   // isa_defs.h:287:1:
	X_DOUBLE_ALIGNMENT              = 8   // isa_defs.h:256:1:
	X_DOUBLE_COMPLEX_ALIGNMENT      = 8   // isa_defs.h:257:1:
	X_DTRACE_VERSION                = 1   // feature_tests.h:490:1:
	X_FILE_OFFSET_BITS              = 64  // <builtin>:25:1:
	X_FIRMWARE_NEEDS_FDISK          = 0   // isa_defs.h:282:1:
	X_FLOAT_ALIGNMENT               = 4   // isa_defs.h:252:1:
	X_FLOAT_COMPLEX_ALIGNMENT       = 4   // isa_defs.h:253:1:
	X_HAVE_CPUID_INSN               = 0   // isa_defs.h:288:1:
	X_IEEE_754                      = 0   // isa_defs.h:246:1:
	X_INT_ALIGNMENT                 = 4   // isa_defs.h:251:1:
	X_ISO_CPP_14882_1998            = 0   // feature_tests.h:466:1:
	X_ISO_C_9899_1999               = 0   // feature_tests.h:472:1:
	X_ISO_C_9899_2011               = 0   // feature_tests.h:478:1:
	X_ISO_LOCALE_ISO_H              = 0   // locale_iso.h:47:1:
	X_LARGEFILE64_SOURCE            = 1   // feature_tests.h:231:1:
	X_LARGEFILE_SOURCE              = 1   // feature_tests.h:235:1:
	X_LIBINTL_H                     = 0   // libintl.h:30:1:
	X_LITTLE_ENDIAN                 = 0   // isa_defs.h:242:1:
	X_LOCALE_H                      = 0   // locale.h:39:1:
	X_LOCALE_T                      = 0   // locale.h:83:1:
	X_LONGLONG_TYPE                 = 0   // feature_tests.h:412:1:
	X_LONG_ALIGNMENT                = 8   // isa_defs.h:254:1:
	X_LONG_DOUBLE_ALIGNMENT         = 16  // isa_defs.h:258:1:
	X_LONG_DOUBLE_COMPLEX_ALIGNMENT = 16  // isa_defs.h:259:1:
	X_LONG_LONG_ALIGNMENT           = 8   // isa_defs.h:255:1:
	X_LONG_LONG_ALIGNMENT_32        = 4   // isa_defs.h:268:1:
	X_LONG_LONG_LTOH                = 0   // isa_defs.h:244:1:
	X_LP64                          = 1   // <predefined>:286:1:
	X_LastCategory                  = 5   // locale.h:62:1:
	X_MAX_ALIGNMENT                 = 16  // isa_defs.h:261:1:
	X_MULTI_DATAMODEL               = 0   // isa_defs.h:279:1:
	X_NORETURN_KYWD                 = 0   // feature_tests.h:448:1:
	X_POINTER_ALIGNMENT             = 8   // isa_defs.h:260:1:
	X_PSM_MODULES                   = 0   // isa_defs.h:284:1:
	X_RESTRICT_KYWD                 = 0   // feature_tests.h:435:1:
	X_RTC_CONFIG                    = 0   // isa_defs.h:285:1:
	X_SHORT_ALIGNMENT               = 2   // isa_defs.h:250:1:
	X_SOFT_HOSTID                   = 0   // isa_defs.h:286:1:
	X_STACK_GROWS_DOWNWARD          = 0   // isa_defs.h:243:1:
	X_STDC_C11                      = 0   // feature_tests.h:165:1:
	X_STDC_C99                      = 0   // feature_tests.h:169:1:
	X_SUNOS_VTOC_16                 = 0   // isa_defs.h:280:1:
	X_SYS_CCOMPILE_H                = 0   // ccompile.h:32:1:
	X_SYS_FEATURE_TESTS_H           = 0   // feature_tests.h:41:1:
	X_SYS_ISA_DEFS_H                = 0   // isa_defs.h:30:1:
	X_SYS_NULL_H                    = 0   // null.h:17:1:
	X_WCHAR_T                       = 0   // libintl.h:53:1:
	X_XOPEN_VERSION                 = 3   // feature_tests.h:392:1:
	Sun                             = 1   // <predefined>:172:1:
	Unix                            = 1   // <predefined>:175:1:
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

// CDDL HEADER START
//
// The contents of this file are subject to the terms of the
// Common Development and Distribution License, Version 1.0 only
// (the "License").  You may not use this file except in compliance
// with the License.
//
// You can obtain a copy of the license at usr/src/OPENSOLARIS.LICENSE
// or http://www.opensolaris.org/os/licensing.
// See the License for the specific language governing permissions
// and limitations under the License.
//
// When distributing Covered Code, include this CDDL HEADER in each
// file and include the License file at usr/src/OPENSOLARIS.LICENSE.
// If applicable, add the following below this CDDL HEADER, with the
// fields enclosed by brackets "[]" replaced with your own identifying
// information: Portions Copyright [yyyy] [name of copyright owner]
//
// CDDL HEADER END
// Copyright 2005 Sun Microsystems, Inc.  All rights reserved.
// Use is subject to license terms.

// Copyright 2014 Garrett D'Amore <garrett@damore.org>
//
// Portions of this file developed by Garrett D'Amore are licensed
// under the terms of the Common Development and Distribution License (CDDL)
// version 1.0 only.  The use of subsequent versions of the License are
// is specifically prohibited unless those terms are not in conflict with
// version 1.0 of the License.  You can find this license on-line at
// http://www.illumos.org/license/CDDL

// CDDL HEADER START
//
// The contents of this file are subject to the terms of the
// Common Development and Distribution License, Version 1.0 only
// (the "License").  You may not use this file except in compliance
// with the License.
//
// You can obtain a copy of the license at usr/src/OPENSOLARIS.LICENSE
// or http://www.opensolaris.org/os/licensing.
// See the License for the specific language governing permissions
// and limitations under the License.
//
// When distributing Covered Code, include this CDDL HEADER in each
// file and include the License file at usr/src/OPENSOLARIS.LICENSE.
// If applicable, add the following below this CDDL HEADER, with the
// fields enclosed by brackets "[]" replaced with your own identifying
// information: Portions Copyright [yyyy] [name of copyright owner]
//
// CDDL HEADER END
// Copyright 2014 Garrett D'Amore <garrett@damore.org>
// Copyright 2014 PALO, Richard.
//
// Copyright 2005 Sun Microsystems, Inc.  All rights reserved.
// Use is subject to license terms.

//	Copyright (c) 1988 AT&T
//	  All Rights Reserved

// An application should not include this header directly.  Instead it
// should be included only through the inclusion of other Sun headers.
//
// The contents of this header is limited to identifiers specified in the
// C Standard.  Any new identifiers specified in future amendments to the
// C Standard must be placed in this header.  If these new identifiers
// are required to also be in the C++ Standard "std" namespace, then for
// anything other than macro definitions, corresponding "using" directives
// must also be added to <locale.h>.

//  DO NOT EDIT THIS FILE.
//
//     It has been auto-edited by fixincludes from:
//
// 	"/usr/include/sys/feature_tests.h"
//
//     This had to be done to correct non-standard usages in the
//     original, manufacturer supplied header file.

// CDDL HEADER START
//
// The contents of this file are subject to the terms of the
// Common Development and Distribution License (the "License").
// You may not use this file except in compliance with the License.
//
// You can obtain a copy of the license at usr/src/OPENSOLARIS.LICENSE
// or http://www.opensolaris.org/os/licensing.
// See the License for the specific language governing permissions
// and limitations under the License.
//
// When distributing Covered Code, include this CDDL HEADER in each
// file and include the License file at usr/src/OPENSOLARIS.LICENSE.
// If applicable, add the following below this CDDL HEADER, with the
// fields enclosed by brackets "[]" replaced with your own identifying
// information: Portions Copyright [yyyy] [name of copyright owner]
//
// CDDL HEADER END

// Copyright 2013 Garrett D'Amore <garrett@damore.org>
// Copyright 2016 Joyent, Inc.
// Copyright 2022 Oxide Computer Company
//
// Copyright 2006 Sun Microsystems, Inc.  All rights reserved.
// Use is subject to license terms.

// CDDL HEADER START
//
// The contents of this file are subject to the terms of the
// Common Development and Distribution License, Version 1.0 only
// (the "License").  You may not use this file except in compliance
// with the License.
//
// You can obtain a copy of the license at usr/src/OPENSOLARIS.LICENSE
// or http://www.opensolaris.org/os/licensing.
// See the License for the specific language governing permissions
// and limitations under the License.
//
// When distributing Covered Code, include this CDDL HEADER in each
// file and include the License file at usr/src/OPENSOLARIS.LICENSE.
// If applicable, add the following below this CDDL HEADER, with the
// fields enclosed by brackets "[]" replaced with your own identifying
// information: Portions Copyright [yyyy] [name of copyright owner]
//
// CDDL HEADER END
// Copyright 2004 Sun Microsystems, Inc.  All rights reserved.
// Use is subject to license terms.
// Copyright 2015 EveryCity Ltd. All rights reserved.
// Copyright 2019 Joyent, Inc.

// This file contains definitions designed to enable different compilers
// to be used harmoniously on Solaris systems.

// Allow for version tests for compiler bugs and features.

// analogous to lint's PRINTFLIKEn

// Handle the kernel printf routines that can take '%b' too

// This one's pretty obvious -- the function never returns

// The function is 'extern inline' and expects GNU C89 behaviour, not C99
// behaviour.
//
// Should only be used on 'extern inline' definitions for GCC.

// The function has control flow such that it may return multiple times (in
// the manner of setjmp or vfork)

// This is an appropriate label for functions that do not
// modify their arguments, e.g. strlen()

// This is a stronger form of __pure__. Can be used for functions
// that do not modify their arguments and don't depend on global
// memory.

// This attribute, attached to a variable, means that the variable is meant to
// be possibly unused. GCC will not produce a warning for this variable.

// Shorthand versions for readability

// In release build, disable warnings about variables
// which are used only for debugging.

// CDDL HEADER START
//
// The contents of this file are subject to the terms of the
// Common Development and Distribution License (the "License").
// You may not use this file except in compliance with the License.
//
// You can obtain a copy of the license at usr/src/OPENSOLARIS.LICENSE
// or http://www.opensolaris.org/os/licensing.
// See the License for the specific language governing permissions
// and limitations under the License.
//
//
// When distributing Covered Code, include this CDDL HEADER in each
// file and include the License file at usr/src/OPENSOLARIS.LICENSE.
// If applicable, add the following below this CDDL HEADER, with the
// fields enclosed by brackets "[]" replaced with your own identifying
// information: Portions Copyright [yyyy] [name of copyright owner]
//
// CDDL HEADER END

// Copyright 2008 Sun Microsystems, Inc.  All rights reserved.
// Use is subject to license terms.
// Copyright 2016 Joyent, Inc.

// This header file serves to group a set of well known defines and to
// set these for each instruction set architecture.  These defines may
// be divided into two groups;  characteristics of the processor and
// implementation choices for Solaris on a processor.
//
// Processor Characteristics:
//
// _LITTLE_ENDIAN / _BIG_ENDIAN:
//	The natural byte order of the processor.  A pointer to an int points
//	to the least/most significant byte of that int.
//
// _STACK_GROWS_UPWARD / _STACK_GROWS_DOWNWARD:
//	The processor specific direction of stack growth.  A push onto the
//	stack increases/decreases the stack pointer, so it stores data at
//	successively higher/lower addresses.  (Stackless machines ignored
//	without regrets).
//
// _LONG_LONG_HTOL / _LONG_LONG_LTOH:
//	A pointer to a long long points to the most/least significant long
//	within that long long.
//
// _BIT_FIELDS_HTOL / _BIT_FIELDS_LTOH:
//	The C compiler assigns bit fields from the high/low to the low/high end
//	of an int (most to least significant vs. least to most significant).
//
// _IEEE_754:
//	The processor (or supported implementations of the processor)
//	supports the ieee-754 floating point standard.  No other floating
//	point standards are supported (or significant).  Any other supported
//	floating point formats are expected to be cased on the ISA processor
//	symbol.
//
// _CHAR_IS_UNSIGNED / _CHAR_IS_SIGNED:
//	The C Compiler implements objects of type `char' as `unsigned' or
//	`signed' respectively.  This is really an implementation choice of
//	the compiler writer, but it is specified in the ABI and tends to
//	be uniform across compilers for an instruction set architecture.
//	Hence, it has the properties of a processor characteristic.
//
// _CHAR_ALIGNMENT / _SHORT_ALIGNMENT / _INT_ALIGNMENT / _LONG_ALIGNMENT /
// _LONG_LONG_ALIGNMENT / _DOUBLE_ALIGNMENT / _LONG_DOUBLE_ALIGNMENT /
// _POINTER_ALIGNMENT / _FLOAT_ALIGNMENT:
//	The ABI defines alignment requirements of each of the primitive
//	object types.  Some, if not all, may be hardware requirements as
// 	well.  The values are expressed in "byte-alignment" units.
//
// _MAX_ALIGNMENT:
//	The most stringent alignment requirement as specified by the ABI.
//	Equal to the maximum of all the above _XXX_ALIGNMENT values.
//
// _MAX_ALIGNMENT_TYPE:
// 	The name of the C type that has the value descried in _MAX_ALIGNMENT.
//
// _ALIGNMENT_REQUIRED:
//	True or false (1 or 0) whether or not the hardware requires the ABI
//	alignment.
//
// _LONG_LONG_ALIGNMENT_32
//	The 32-bit ABI supported by a 64-bit kernel may have different
//	alignment requirements for primitive object types.  The value of this
//	identifier is expressed in "byte-alignment" units.
//
// _HAVE_CPUID_INSN
//	This indicates that the architecture supports the 'cpuid'
//	instruction as defined by Intel.  (Intel allows other vendors
//	to extend the instruction for their own purposes.)
//
//
// Implementation Choices:
//
// _ILP32 / _LP64:
//	This specifies the compiler data type implementation as specified in
//	the relevant ABI.  The choice between these is strongly influenced
//	by the underlying hardware, but is not absolutely tied to it.
//	Currently only two data type models are supported:
//
//	_ILP32:
//		Int/Long/Pointer are 32 bits.  This is the historical UNIX
//		and Solaris implementation.  Due to its historical standing,
//		this is the default case.
//
//	_LP64:
//		Long/Pointer are 64 bits, Int is 32 bits.  This is the chosen
//		implementation for 64-bit ABIs such as SPARC V9.
//
//	_I32LPx:
//		A compilation environment where 'int' is 32-bit, and
//		longs and pointers are simply the same size.
//
//	In all cases, Char is 8 bits and Short is 16 bits.
//
// _SUNOS_VTOC_8 / _SUNOS_VTOC_16 / _SVR4_VTOC_16:
//	This specifies the form of the disk VTOC (or label):
//
//	_SUNOS_VTOC_8:
//		This is a VTOC form which is upwardly compatible with the
//		SunOS 4.x disk label and allows 8 partitions per disk.
//
//	_SUNOS_VTOC_16:
//		In this format the incore vtoc image matches the ondisk
//		version.  It allows 16 slices per disk, and is not
//		compatible with the SunOS 4.x disk label.
//
//	Note that these are not the only two VTOC forms possible and
//	additional forms may be added.  One possible form would be the
//	SVr4 VTOC form.  The symbol for that is reserved now, although
//	it is not implemented.
//
//	_SVR4_VTOC_16:
//		This VTOC form is compatible with the System V Release 4
//		VTOC (as implemented on the SVr4 Intel and 3b ports) with
//		16 partitions per disk.
//
//
// _DMA_USES_PHYSADDR / _DMA_USES_VIRTADDR
//	This describes the type of addresses used by system DMA:
//
//	_DMA_USES_PHYSADDR:
//		This type of DMA, used in the x86 implementation,
//		requires physical addresses for DMA buffers.  The 24-bit
//		addresses used by some legacy boards is the source of the
//		"low-memory" (<16MB) requirement for some devices using DMA.
//
//	_DMA_USES_VIRTADDR:
//		This method of DMA allows the use of virtual addresses for
//		DMA transfers.
//
// _FIRMWARE_NEEDS_FDISK / _NO_FDISK_PRESENT
//      This indicates the presence/absence of an fdisk table.
//
//      _FIRMWARE_NEEDS_FDISK
//              The fdisk table is required by system firmware.  If present,
//              it allows a disk to be subdivided into multiple fdisk
//              partitions, each of which is equivalent to a separate,
//              virtual disk.  This enables the co-existence of multiple
//              operating systems on a shared hard disk.
//
//      _NO_FDISK_PRESENT
//              If the fdisk table is absent, it is assumed that the entire
//              media is allocated for a single operating system.
//
// _HAVE_TEM_FIRMWARE
//	Defined if this architecture has the (fallback) option of
//	using prom_* calls for doing I/O if a suitable kernel driver
//	is not available to do it.
//
// _DONT_USE_1275_GENERIC_NAMES
//		Controls whether or not device tree node names should
//		comply with the IEEE 1275 "Generic Names" Recommended
//		Practice. With _DONT_USE_GENERIC_NAMES, device-specific
//		names identifying the particular device will be used.
//
// __i386_COMPAT
//	This indicates whether the i386 ABI is supported as a *non-native*
//	mode for the platform.  When this symbol is defined:
//	-	32-bit xstat-style system calls are enabled
//	-	32-bit xmknod-style system calls are enabled
//	-	32-bit system calls use i386 sizes -and- alignments
//
//	Note that this is NOT defined for the i386 native environment!
//
// __x86
//	This is ONLY a synonym for defined(__i386) || defined(__amd64)
//	which is useful only insofar as these two architectures share
//	common attributes.  Analogous to __sparc.
//
// _PSM_MODULES
//	This indicates whether or not the implementation uses PSM
//	modules for processor support, reading /etc/mach from inside
//	the kernel to extract a list.
//
// _RTC_CONFIG
//	This indicates whether or not the implementation uses /etc/rtc_config
//	to configure the real-time clock in the kernel.
//
// _UNIX_KRTLD
//	This indicates that the implementation uses a dynamically
//	linked unix + krtld to form the core kernel image at boot
//	time, or (in the absence of this symbol) a prelinked kernel image.
//
// _OBP
//	This indicates the firmware interface is OBP.
//
// _SOFT_HOSTID
//	This indicates that the implementation obtains the hostid
//	from the file /etc/hostid, rather than from hardware.

// The following set of definitions characterize Solaris on AMD's
// 64-bit systems.

// Define the appropriate "processor characteristics"

// Different alignment constraints for the i386 ABI in compatibility mode

// Define the appropriate "implementation choices".

// The feature test macro __i386 is generic for all processors implementing
// the Intel 386 instruction set or a superset of it.  Specifically, this
// includes all members of the 386, 486, and Pentium family of processors.

// Values of _POSIX_C_SOURCE
//
//		undefined   not a POSIX compilation
//		1	    POSIX.1-1990 compilation
//		2	    POSIX.2-1992 compilation
//		199309L	    POSIX.1b-1993 compilation (Real Time)
//		199506L	    POSIX.1c-1995 compilation (POSIX Threads)
//		200112L	    POSIX.1-2001 compilation (Austin Group Revision)
//		200809L     POSIX.1-2008 compilation

// The feature test macros __XOPEN_OR_POSIX, _STRICT_STDC, _STRICT_SYMBOLS,
// and _STDC_C99 are Sun implementation specific macros created in order to
// compress common standards specified feature test macros for easier reading.
// These macros should not be used by the application developer as
// unexpected results may occur. Instead, the user should reference
// standards(7) for correct usage of the standards feature test macros.
//
// __XOPEN_OR_POSIX     Used in cases where a symbol is defined by both
//                      X/Open or POSIX or in the negative, when neither
//                      X/Open or POSIX defines a symbol.
//
// _STRICT_STDC         __STDC__ is specified by the C Standards and defined
//                      by the compiler. For Sun compilers the value of
//                      __STDC__ is either 1, 0, or not defined based on the
//                      compilation mode (see cc(1)). When the value of
//                      __STDC__ is 1 and in the absence of any other feature
//                      test macros, the namespace available to the application
//                      is limited to only those symbols defined by the C
//                      Standard. _STRICT_STDC provides a more readable means
//                      of identifying symbols defined by the standard, or in
//                      the negative, symbols that are extensions to the C
//                      Standard. See additional comments for GNU C differences.
//
// _STDC_C99            __STDC_VERSION__ is specified by the C standards and
//                      defined by the compiler and indicates the version of
//                      the C standard. A value of 199901L indicates a
//                      compiler that complies with ISO/IEC 9899:1999, other-
//                      wise known as the C99 standard.
//
// _STDC_C11		Like _STDC_C99 except that the value of __STDC_VERSION__
//                      is 201112L indicating a compiler that compiles with
//                      ISO/IEC 9899:2011, otherwise known as the C11 standard.
//
// _STRICT_SYMBOLS	Used in cases where symbol visibility is restricted
//                      by the standards, and the user has not explicitly
//                      relaxed the strictness via __EXTENSIONS__.

// ISO/IEC 9899:1990 and it's revisions, ISO/IEC 9899:1999 and ISO/IEC
// 99899:2011 specify the following predefined macro name:
//
// __STDC__	The integer constant 1, intended to indicate a conforming
//		implementation.
//
// Furthermore, a strictly conforming program shall use only those features
// of the language and library specified in these standards. A conforming
// implementation shall accept any strictly conforming program.
//
// Based on these requirements, Sun's C compiler defines __STDC__ to 1 for
// strictly conforming environments and __STDC__ to 0 for environments that
// use ANSI C semantics but allow extensions to the C standard. For non-ANSI
// C semantics, Sun's C compiler does not define __STDC__.
//
// The GNU C project interpretation is that __STDC__ should always be defined
// to 1 for compilation modes that accept ANSI C syntax regardless of whether
// or not extensions to the C standard are used. Violations of conforming
// behavior are conditionally flagged as warnings via the use of the
// -pedantic option. In addition to defining __STDC__ to 1, the GNU C
// compiler also defines __STRICT_ANSI__ as a means of specifying strictly
// conforming environments using the -ansi or -std=<standard> options.
//
// In the absence of any other compiler options, Sun and GNU set the value
// of __STDC__ as follows when using the following options:
//
//				Value of __STDC__  __STRICT_ANSI__
//
// cc -Xa (default)			0	      undefined
// cc -Xt (transitional)		0             undefined
// cc -Xc (strictly conforming)		1	      undefined
// cc -Xs (K&R C)		    undefined	      undefined
//
// gcc (default)			1	      undefined
// gcc -ansi, -std={c89, c99,...)	1               defined
// gcc -traditional (K&R)	    undefined	      undefined
//
// The default compilation modes for Sun C compilers versus GNU C compilers
// results in a differing value for __STDC__ which results in a more
// restricted namespace when using Sun compilers. To allow both GNU and Sun
// interpretations to peacefully co-exist, we use the following Sun
// implementation _STRICT_STDC_ macro:

// Compiler complies with ISO/IEC 9899:1999 or ISO/IEC 9989:2011

// Use strict symbol visibility.

// This is a variant of _STRICT_SYMBOLS that is meant to cover headers that are
// governed by POSIX, but have not been governed by ISO C. One can go two ways
// on what should happen if an application actively includes (not transitively)
// a header that isn't part of the ISO C spec, we opt to say that if someone has
// gone out of there way then they're doing it for a reason and that is an act
// of non-compliance and therefore it's not up to us to hide away every symbol.
//
// In general, prefer using _STRICT_SYMBOLS, but this is here in particular for
// cases where in the past we have only used a POSIX related check and we don't
// wish to make something stricter. Often applications are relying on the
// ability to, or more realistically unwittingly, have _STRICT_STDC declared and
// still use these interfaces.

// Large file interfaces:
//
//	_LARGEFILE_SOURCE
//		1		large file-related additions to POSIX
//				interfaces requested (fseeko, etc.)
//	_LARGEFILE64_SOURCE
//		1		transitional large-file-related interfaces
//				requested (seek64, stat64, etc.)
//
// The corresponding announcement macros are respectively:
//	_LFS_LARGEFILE
//	_LFS64_LARGEFILE
// (These are set in <unistd.h>.)
//
// Requesting _LARGEFILE64_SOURCE implies requesting _LARGEFILE_SOURCE as
// well.
//
// The large file interfaces are made visible regardless of the initial values
// of the feature test macros under certain circumstances:
//    -	If no explicit standards-conforming environment is requested (neither
//	of _POSIX_SOURCE nor _XOPEN_SOURCE is defined and the value of
//	__STDC__ does not imply standards conformance).
//    -	Extended system interfaces are explicitly requested (__EXTENSIONS__
//	is defined).
//    -	Access to in-kernel interfaces is requested (_KERNEL or _KMEMUSER is
//	defined).  (Note that this dependency is an artifact of the current
//	kernel implementation and may change in future releases.)

// Large file compilation environment control:
//
// The setting of _FILE_OFFSET_BITS controls the size of various file-related
// types and governs the mapping between file-related source function symbol
// names and the corresponding binary entry points.
//
// In the 32-bit environment, the default value is 32; if not set, set it to
// the default here, to simplify tests in other headers.
//
// In the 64-bit compilation environment, the only value allowed is 64.

// Use of _XOPEN_SOURCE
//
// The following X/Open specifications are supported:
//
// X/Open Portability Guide, Issue 3 (XPG3)
// X/Open CAE Specification, Issue 4 (XPG4)
// X/Open CAE Specification, Issue 4, Version 2 (XPG4v2)
// X/Open CAE Specification, Issue 5 (XPG5)
// Open Group Technical Standard, Issue 6 (XPG6), also referred to as
//    IEEE Std. 1003.1-2001 and ISO/IEC 9945:2002.
// Open Group Technical Standard, Issue 7 (XPG7), also referred to as
//    IEEE Std. 1003.1-2008 and ISO/IEC 9945:2009.
//
// XPG4v2 is also referred to as UNIX 95 (SUS or SUSv1).
// XPG5 is also referred to as UNIX 98 or the Single Unix Specification,
//     Version 2 (SUSv2)
// XPG6 is the result of a merge of the X/Open and POSIX specifications
//     and as such is also referred to as IEEE Std. 1003.1-2001 in
//     addition to UNIX 03 and SUSv3.
// XPG7 is also referred to as UNIX 08 and SUSv4.
//
// When writing a conforming X/Open application, as per the specification
// requirements, the appropriate feature test macros must be defined at
// compile time. These are as follows. For more info, see standards(7).
//
// Feature Test Macro				     Specification
// ------------------------------------------------  -------------
// _XOPEN_SOURCE                                         XPG3
// _XOPEN_SOURCE && _XOPEN_VERSION = 4                   XPG4
// _XOPEN_SOURCE && _XOPEN_SOURCE_EXTENDED = 1           XPG4v2
// _XOPEN_SOURCE = 500                                   XPG5
// _XOPEN_SOURCE = 600  (or POSIX_C_SOURCE=200112L)      XPG6
// _XOPEN_SOURCE = 700  (or POSIX_C_SOURCE=200809L)      XPG7
//
// In order to simplify the guards within the headers, the following
// implementation private test macros have been created. Applications
// must NOT use these private test macros as unexpected results will
// occur.
//
// Note that in general, the use of these private macros is cumulative.
// For example, the use of _XPG3 with no other restrictions on the X/Open
// namespace will make the symbols visible for XPG3 through XPG6
// compilation environments. The use of _XPG4_2 with no other X/Open
// namespace restrictions indicates that the symbols were introduced in
// XPG4v2 and are therefore visible for XPG4v2 through XPG6 compilation
// environments, but not for XPG3 or XPG4 compilation environments.
//
// _XPG3    X/Open Portability Guide, Issue 3 (XPG3)
// _XPG4    X/Open CAE Specification, Issue 4 (XPG4)
// _XPG4_2  X/Open CAE Specification, Issue 4, Version 2 (XPG4v2/UNIX 95/SUS)
// _XPG5    X/Open CAE Specification, Issue 5 (XPG5/UNIX 98/SUSv2)
// _XPG6    Open Group Technical Standard, Issue 6 (XPG6/UNIX 03/SUSv3)
// _XPG7    Open Group Technical Standard, Issue 7 (XPG7/UNIX 08/SUSv4)

// X/Open Portability Guide, Issue 3

// _XOPEN_VERSION is defined by the X/Open specifications and is not
// normally defined by the application, except in the case of an XPG4
// application.  On the implementation side, _XOPEN_VERSION defined with
// the value of 3 indicates an XPG3 application. _XOPEN_VERSION defined
// with the value of 4 indicates an XPG4 or XPG4v2 (UNIX 95) application.
// _XOPEN_VERSION  defined with a value of 500 indicates an XPG5 (UNIX 98)
// application and with a value of 600 indicates an XPG6 (UNIX 03)
// application and with a value of 700 indicates an XPG7 (UNIX 08).
// The appropriate version is determined by the use of the
// feature test macros described earlier.  The value of _XOPEN_VERSION
// defaults to 3 otherwise indicating support for XPG3 applications.

// ANSI C and ISO 9899:1990 say the type long long doesn't exist in strictly
// conforming environments.  ISO 9899:1999 says it does.
//
// The presence of _LONGLONG_TYPE says "long long exists" which is therefore
// defined in all but strictly conforming environments that disallow it.

// The following macro defines a value for the ISO C99 restrict
// keyword so that _RESTRICT_KYWD resolves to "restrict" if
// an ISO C99 compiler is used, "__restrict" for c++ and "" (null string)
// if any other compiler is used. This allows for the use of single
// prototype declarations regardless of compiler version.

// The following macro defines a value for the ISO C11 _Noreturn
// keyword so that _NORETURN_KYWD resolves to "_Noreturn" if
// an ISO C11 compiler is used and "" (null string) if any other
// compiler is used. This allows for the use of single prototype
// declarations regardless of compiler version.

// ISO/IEC 9899:2011 Annex K

// The following macro indicates header support for the ANSI C++
// standard.  The ISO/IEC designation for this is ISO/IEC FDIS 14882.

// The following macro indicates header support for the C99 standard,
// ISO/IEC 9899:1999, Programming Languages - C.

// The following macro indicates header support for the C11 standard,
// ISO/IEC 9899:2011, Programming Languages - C.

// The following macro indicates header support for the C11 standard,
// ISO/IEC 9899:2011 Annex K, Programming Languages - C.

// The following macro indicates header support for DTrace. The value is an
// integer that corresponds to the major version number for DTrace.

// This file and its contents are supplied under the terms of the
// Common Development and Distribution License ("CDDL"), version 1.0.
// You may only use this file in accordance with the terms of version
// 1.0 of the CDDL.
//
// A full copy of the text of the CDDL should have accompanied this
// source.  A copy of the CDDL is also available via the Internet at
// http://www.illumos.org/license/CDDL.

// Copyright 2014-2016 PALO, Richard.

//  DO NOT EDIT THIS FILE.
//
//     It has been auto-edited by fixincludes from:
//
// 	"/usr/include/sys/feature_tests.h"
//
//     This had to be done to correct non-standard usages in the
//     original, manufacturer supplied header file.

// CDDL HEADER START
//
// The contents of this file are subject to the terms of the
// Common Development and Distribution License (the "License").
// You may not use this file except in compliance with the License.
//
// You can obtain a copy of the license at usr/src/OPENSOLARIS.LICENSE
// or http://www.opensolaris.org/os/licensing.
// See the License for the specific language governing permissions
// and limitations under the License.
//
// When distributing Covered Code, include this CDDL HEADER in each
// file and include the License file at usr/src/OPENSOLARIS.LICENSE.
// If applicable, add the following below this CDDL HEADER, with the
// fields enclosed by brackets "[]" replaced with your own identifying
// information: Portions Copyright [yyyy] [name of copyright owner]
//
// CDDL HEADER END

// Copyright 2013 Garrett D'Amore <garrett@damore.org>
// Copyright 2016 Joyent, Inc.
// Copyright 2022 Oxide Computer Company
//
// Copyright 2006 Sun Microsystems, Inc.  All rights reserved.
// Use is subject to license terms.

// POSIX.1-2008 requires that the NULL macro be cast to type void *.

type Lconv = struct {
	Fdecimal_point     uintptr
	Fthousands_sep     uintptr
	Fgrouping          uintptr
	Fint_curr_symbol   uintptr
	Fcurrency_symbol   uintptr
	Fmon_decimal_point uintptr
	Fmon_thousands_sep uintptr
	Fmon_grouping      uintptr
	Fpositive_sign     uintptr
	Fnegative_sign     uintptr
	Fint_frac_digits   int8
	Ffrac_digits       int8
	Fp_cs_precedes     int8
	Fp_sep_by_space    int8
	Fn_cs_precedes     int8
	Fn_sep_by_space    int8
	Fp_sign_posn       int8
	Fn_sign_posn       int8
} /* locale_iso.h:60:1 */

// Allow global visibility for symbols defined in
// C++ "std" namespace in <iso/locale_iso.h>.

// These were added in POSIX 2008 as part of the newlocale() specification.

type Locale_t = uintptr /* locale.h:84:24 */

var _ int8 /* gen.c:2:13: */