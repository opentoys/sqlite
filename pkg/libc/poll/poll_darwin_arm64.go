// Code generated by 'ccgo poll/gen.c -crt-import-path "" -export-defines "" -export-enums "" -export-externs X -export-fields F -export-structs "" -export-typedefs "" -header -hide _OSSwapInt16,_OSSwapInt32,_OSSwapInt64 -ignore-unsupported-alignment -o poll/poll_darwin_arm64.go -pkgname poll', DO NOT EDIT.

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
	POLLATTRIB                             = 0x0400 // poll.h:81:1:
	POLLERR                                = 0x0008 // poll.h:89:1:
	POLLEXTEND                             = 0x0200 // poll.h:80:1:
	POLLHUP                                = 0x0010 // poll.h:90:1:
	POLLIN                                 = 0x0001 // poll.h:68:1:
	POLLNLINK                              = 0x0800 // poll.h:82:1:
	POLLNVAL                               = 0x0020 // poll.h:91:1:
	POLLOUT                                = 0x0004 // poll.h:70:1:
	POLLPRI                                = 0x0002 // poll.h:69:1:
	POLLRDBAND                             = 0x0080 // poll.h:73:1:
	POLLRDNORM                             = 0x0040 // poll.h:71:1:
	POLLSTANDARD                           = 511    // poll.h:93:1:
	POLLWRBAND                             = 0x0100 // poll.h:74:1:
	POLLWRITE                              = 0x1000 // poll.h:83:1:
	POLLWRNORM                             = 4      // poll.h:72:1:
	X_CDEFS_H_                             = 0      // cdefs.h:68:1:
	X_DARWIN_FEATURE_64_BIT_INODE          = 1      // cdefs.h:774:1:
	X_DARWIN_FEATURE_ONLY_64_BIT_INODE     = 1      // cdefs.h:784:1:
	X_DARWIN_FEATURE_ONLY_UNIX_CONFORMANCE = 1      // cdefs.h:800:1:
	X_DARWIN_FEATURE_ONLY_VERS_1050        = 1      // cdefs.h:792:1:
	X_DARWIN_FEATURE_UNIX_CONFORMANCE      = 3      // cdefs.h:808:1:
	X_FILE_OFFSET_BITS                     = 64     // <builtin>:25:1:
	X_LP64                                 = 1      // <predefined>:1:1:
	X_Nonnull                              = 0      // cdefs.h:268:1:
	X_Null_unspecified                     = 0      // cdefs.h:271:1:
	X_Nullable                             = 0      // cdefs.h:265:1:
	X_SYS_POLL_H_                          = 0      // poll.h:58:1:
)

type Ptrdiff_t = int64 /* <builtin>:3:26 */

type Size_t = uint64 /* <builtin>:9:23 */

type Wchar_t = int32 /* <builtin>:15:24 */

type X__int128_t = struct {
	Flo int64
	Fhi int64
} /* <builtin>:21:43 */ // must match github.com/opentoys/sqlite/pkg/mathutil.Int128
type X__uint128_t = struct {
	Flo uint64
	Fhi uint64
} /* <builtin>:22:44 */ // must match github.com/opentoys/sqlite/pkg/mathutil.Int128

type X__builtin_va_list = uintptr /* <builtin>:46:14 */
type X__float128 = float64        /* <builtin>:47:21 */

var X__darwin_check_fd_set_overflow uintptr /* <builtin>:146:5: */

// Copyright (c) 2004 Apple Computer, Inc. All rights reserved.
//
// @APPLE_LICENSE_HEADER_START@
//
// This file contains Original Code and/or Modifications of Original Code
// as defined in and that are subject to the Apple Public Source License
// Version 2.0 (the 'License'). You may not use this file except in
// compliance with the License. Please obtain a copy of the License at
// http://www.opensource.apple.com/apsl/ and read it before using this
// file.
//
// The Original Code and all software distributed under the License are
// distributed on an 'AS IS' basis, WITHOUT WARRANTY OF ANY KIND, EITHER
// EXPRESS OR IMPLIED, AND APPLE HEREBY DISCLAIMS ALL SUCH WARRANTIES,
// INCLUDING WITHOUT LIMITATION, ANY WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE, QUIET ENJOYMENT OR NON-INFRINGEMENT.
// Please see the License for the specific language governing rights and
// limitations under the License.
//
// @APPLE_LICENSE_HEADER_END@
// Copyright (c) 2000-2004 Apple Computer, Inc. All rights reserved.
//
// @APPLE_OSREFERENCE_LICENSE_HEADER_START@
//
// This file contains Original Code and/or Modifications of Original Code
// as defined in and that are subject to the Apple Public Source License
// Version 2.0 (the 'License'). You may not use this file except in
// compliance with the License. The rights granted to you under the License
// may not be used to create, or enable the creation or redistribution of,
// unlawful or unlicensed copies of an Apple operating system, or to
// circumvent, violate, or enable the circumvention or violation of, any
// terms of an Apple operating system software license agreement.
//
// Please obtain a copy of the License at
// http://www.opensource.apple.com/apsl/ and read it before using this file.
//
// The Original Code and all software distributed under the License are
// distributed on an 'AS IS' basis, WITHOUT WARRANTY OF ANY KIND, EITHER
// EXPRESS OR IMPLIED, AND APPLE HEREBY DISCLAIMS ALL SUCH WARRANTIES,
// INCLUDING WITHOUT LIMITATION, ANY WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE, QUIET ENJOYMENT OR NON-INFRINGEMENT.
// Please see the License for the specific language governing rights and
// limitations under the License.
//
// @APPLE_OSREFERENCE_LICENSE_HEADER_END@
// -
// Copyright (c) 1997 Peter Wemm <peter@freebsd.org>
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in the
//    documentation and/or other materials provided with the distribution.
// 3. The name of the author may not be used to endorse or promote products
//    derived from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
// FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
// DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
// OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
// HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
// LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
// OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
// SUCH DAMAGE.
//

// This file is intended to be compatible with the traditional poll.h.

// Requestable events.  If poll(2) finds any of these set, they are
// copied to revents on return.

// FreeBSD extensions: polling on a regular file might return one
// of these events (currently only supported on local filesystems).

// These events are set if they occur regardless of whether they were
// requested.

type Pollfd = struct {
	Ffd      int32
	Fevents  int16
	Frevents int16
} /* poll.h:96:1 */

type Nfds_t = uint32 /* poll.h:102:22 */

var _ int8 /* gen.c:2:13: */
