// Code generated by 'ccgo sys\stat\gen.c -crt-import-path "" -export-defines "" -export-enums "" -export-externs X -export-fields F -export-structs "" -export-typedefs "" -header -hide _OSSwapInt16,_OSSwapInt32,_OSSwapInt64 -o sys\stat\stat_windows_amd64.go -pkgname stat', DO NOT EDIT.

package stat

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
	F_OK                                            = 0
	MINGW_DDK_H                                     = 0
	MINGW_DDRAW_VERSION                             = 7
	MINGW_HAS_DDK_H                                 = 1
	MINGW_HAS_DDRAW_H                               = 1
	MINGW_HAS_SECURE_API                            = 1
	MINGW_SDK_INIT                                  = 0
	R_OK                                            = 4
	S_IEXEC                                         = 64
	S_IFBLK                                         = 12288
	S_IFCHR                                         = 8192
	S_IFDIR                                         = 16384
	S_IFIFO                                         = 4096
	S_IFMT                                          = 61440
	S_IFREG                                         = 32768
	S_IREAD                                         = 256
	S_IRGRP                                         = 32
	S_IROTH                                         = 4
	S_IRUSR                                         = 256
	S_IRWXG                                         = 56
	S_IRWXO                                         = 7
	S_IRWXU                                         = 448
	S_IWGRP                                         = 16
	S_IWOTH                                         = 2
	S_IWRITE                                        = 128
	S_IWUSR                                         = 128
	S_IXGRP                                         = 8
	S_IXOTH                                         = 1
	S_IXUSR                                         = 64
	UNALIGNED                                       = 0
	USE___UUIDOF                                    = 0
	WIN32                                           = 1
	WIN64                                           = 1
	WINNT                                           = 1
	W_OK                                            = 2
	X_OK                                            = 1
	X_AGLOBAL                                       = 0
	X_ANONYMOUS_STRUCT                              = 0
	X_ANONYMOUS_UNION                               = 0
	X_ARGMAX                                        = 100
	X_A_ARCH                                        = 0x20
	X_A_HIDDEN                                      = 0x02
	X_A_NORMAL                                      = 0x00
	X_A_RDONLY                                      = 0x01
	X_A_SUBDIR                                      = 0x10
	X_A_SYSTEM                                      = 0x04
	X_CONST_RETURN                                  = 0
	X_CRTNOALIAS                                    = 0
	X_CRTRESTRICT                                   = 0
	X_CRT_ALTERNATIVE_IMPORTED                      = 0
	X_CRT_DIRECTORY_DEFINED                         = 0
	X_CRT_MANAGED_HEAP_DEPRECATE                    = 0
	X_CRT_MEMORY_DEFINED                            = 0
	X_CRT_PACKING                                   = 8
	X_CRT_SECURE_CPP_OVERLOAD_SECURE_NAMES          = 0
	X_CRT_SECURE_CPP_OVERLOAD_SECURE_NAMES_MEMORY   = 0
	X_CRT_SECURE_CPP_OVERLOAD_STANDARD_NAMES        = 0
	X_CRT_SECURE_CPP_OVERLOAD_STANDARD_NAMES_COUNT  = 0
	X_CRT_SECURE_CPP_OVERLOAD_STANDARD_NAMES_MEMORY = 0
	X_DEV_T_DEFINED                                 = 0
	X_DLL                                           = 0
	X_ERRCODE_DEFINED                               = 0
	X_FILE_OFFSET_BITS                              = 64
	X_FILE_OFFSET_BITS_SET_LSEEK                    = 0
	X_FILE_OFFSET_BITS_SET_OFFT                     = 0
	X_FINDDATA_T_DEFINED                            = 0
	X_FSIZE_T_DEFINED                               = 0
	X_INC_CRTDEFS                                   = 0
	X_INC_CRTDEFS_MACRO                             = 0
	X_INC_MINGW_SECAPI                              = 0
	X_INC_STAT                                      = 0
	X_INC_STRING                                    = 0
	X_INC_STRING_S                                  = 0
	X_INC_TYPES                                     = 0
	X_INC_VADEFS                                    = 0
	X_INC__MINGW_H                                  = 0
	X_INO_T_DEFINED                                 = 0
	X_INT128_DEFINED                                = 0
	X_INTEGRAL_MAX_BITS                             = 64
	X_INTPTR_T_DEFINED                              = 0
	X_IO_H_                                         = 0
	X_MODE_T_                                       = 0
	X_MT                                            = 0
	X_M_AMD64                                       = 100
	X_M_X64                                         = 100
	X_NLSCMPERROR                                   = 2147483647
	X_NLSCMP_DEFINED                                = 0
	X_OFF64_T_DEFINED                               = 0
	X_OFF_T_                                        = 0
	X_OFF_T_DEFINED                                 = 0
	X_PGLOBAL                                       = 0
	X_PID_T_                                        = 0
	X_PTRDIFF_T_                                    = 0
	X_PTRDIFF_T_DEFINED                             = 0
	X_REENTRANT                                     = 1
	X_RSIZE_T_DEFINED                               = 0
	X_SECURECRT_FILL_BUFFER_PATTERN                 = 0xFD
	X_SIGSET_T_                                     = 0
	X_SIZE_T_DEFINED                                = 0
	X_SSIZE_T_DEFINED                               = 0
	X_STAT_DEFINED                                  = 0
	X_S_IEXEC                                       = 0x0040
	X_S_IFBLK                                       = 0x3000
	X_S_IFCHR                                       = 0x2000
	X_S_IFDIR                                       = 0x4000
	X_S_IFIFO                                       = 0x1000
	X_S_IFMT                                        = 0xF000
	X_S_IFREG                                       = 0x8000
	X_S_IREAD                                       = 0x0100
	X_S_IRUSR                                       = 256
	X_S_IRWXU                                       = 448
	X_S_IWRITE                                      = 0x0080
	X_S_IWUSR                                       = 128
	X_S_IXUSR                                       = 64
	X_TAGLC_ID_DEFINED                              = 0
	X_THREADLOCALEINFO                              = 0
	X_TIME32_T_DEFINED                              = 0
	X_TIME64_T_DEFINED                              = 0
	X_TIMESPEC_DEFINED                              = 0
	X_TIME_T_DEFINED                                = 0
	X_UINTPTR_T_DEFINED                             = 0
	X_VA_LIST_DEFINED                               = 0
	X_W64                                           = 0
	X_WCHAR_T_DEFINED                               = 0
	X_WCTYPE_T_DEFINED                              = 0
	X_WConst_return                                 = 0
	X_WFINDDATA_T_DEFINED                           = 0
	X_WIN32                                         = 1
	X_WIN32_WINNT                                   = 0x502
	X_WIN64                                         = 1
	X_WINT_T                                        = 0
	X_WIO_DEFINED                                   = 0
	X_WSTAT_DEFINED                                 = 0
	X_WSTRING_DEFINED                               = 0
	X_WSTRING_S_DEFINED                             = 0
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

// *
// This file has no copyright assigned and is placed in the Public Domain.
// This file is part of the mingw-w64 runtime package.
// No warranty is given; refer to the file DISCLAIMER.PD within this package.

// *
// This file has no copyright assigned and is placed in the Public Domain.
// This file is part of the mingw-w64 runtime package.
// No warranty is given; refer to the file DISCLAIMER.PD within this package.

type X__gnuc_va_list = X__builtin_va_list /* vadefs.h:24:29 */

type Ssize_t = int64 /* crtdefs.h:45:35 */

type Rsize_t = Size_t /* crtdefs.h:52:16 */

type Intptr_t = int64 /* crtdefs.h:62:35 */

type Uintptr_t = uint64 /* crtdefs.h:75:44 */

type Wint_t = uint16   /* crtdefs.h:106:24 */
type Wctype_t = uint16 /* crtdefs.h:107:24 */

type Errno_t = int32 /* crtdefs.h:113:13 */

type X__time32_t = int32 /* crtdefs.h:118:14 */

type X__time64_t = int64 /* crtdefs.h:123:35 */

type Time_t = X__time64_t /* crtdefs.h:138:20 */

type Threadlocaleinfostruct = struct {
	Frefcount      int32
	Flc_codepage   uint32
	Flc_collate_cp uint32
	Flc_handle     [6]uint32
	Flc_id         [6]LC_ID
	Flc_category   [6]struct {
		Flocale    uintptr
		Fwlocale   uintptr
		Frefcount  uintptr
		Fwrefcount uintptr
	}
	Flc_clike            int32
	Fmb_cur_max          int32
	Flconv_intl_refcount uintptr
	Flconv_num_refcount  uintptr
	Flconv_mon_refcount  uintptr
	Flconv               uintptr
	Fctype1_refcount     uintptr
	Fctype1              uintptr
	Fpctype              uintptr
	Fpclmap              uintptr
	Fpcumap              uintptr
	Flc_time_curr        uintptr
} /* crtdefs.h:422:1 */

type Pthreadlocinfo = uintptr /* crtdefs.h:424:39 */
type Pthreadmbcinfo = uintptr /* crtdefs.h:425:36 */

type Localeinfo_struct = struct {
	Flocinfo Pthreadlocinfo
	Fmbcinfo Pthreadmbcinfo
} /* crtdefs.h:428:9 */

type X_locale_tstruct = Localeinfo_struct /* crtdefs.h:431:3 */
type X_locale_t = uintptr                 /* crtdefs.h:431:19 */

type TagLC_ID = struct {
	FwLanguage uint16
	FwCountry  uint16
	FwCodePage uint16
} /* crtdefs.h:422:1 */

type LC_ID = TagLC_ID  /* crtdefs.h:439:3 */
type LPLC_ID = uintptr /* crtdefs.h:439:9 */

type Threadlocinfo = Threadlocaleinfostruct /* crtdefs.h:468:3 */
type X_fsize_t = uint32                     /* io.h:29:25 */

type X_finddata32_t = struct {
	Fattrib      uint32
	Ftime_create X__time32_t
	Ftime_access X__time32_t
	Ftime_write  X__time32_t
	Fsize        X_fsize_t
	Fname        [260]int8
} /* io.h:35:3 */

type X_finddata32i64_t = struct {
	Fattrib      uint32
	Ftime_create X__time32_t
	Ftime_access X__time32_t
	Ftime_write  X__time32_t
	Fsize        int64
	Fname        [260]int8
	F__ccgo_pad1 [4]byte
} /* io.h:44:3 */

type X_finddata64i32_t = struct {
	Fattrib      uint32
	F__ccgo_pad1 [4]byte
	Ftime_create X__time64_t
	Ftime_access X__time64_t
	Ftime_write  X__time64_t
	Fsize        X_fsize_t
	Fname        [260]int8
} /* io.h:53:3 */

type X__finddata64_t = struct {
	Fattrib      uint32
	F__ccgo_pad1 [4]byte
	Ftime_create X__time64_t
	Ftime_access X__time64_t
	Ftime_write  X__time64_t
	Fsize        int64
	Fname        [260]int8
	F__ccgo_pad2 [4]byte
} /* io.h:62:3 */

type X_wfinddata32_t = struct {
	Fattrib      uint32
	Ftime_create X__time32_t
	Ftime_access X__time32_t
	Ftime_write  X__time32_t
	Fsize        X_fsize_t
	Fname        [260]Wchar_t
} /* io.h:94:3 */

type X_wfinddata32i64_t = struct {
	Fattrib      uint32
	Ftime_create X__time32_t
	Ftime_access X__time32_t
	Ftime_write  X__time32_t
	Fsize        int64
	Fname        [260]Wchar_t
} /* io.h:103:3 */

type X_wfinddata64i32_t = struct {
	Fattrib      uint32
	F__ccgo_pad1 [4]byte
	Ftime_create X__time64_t
	Ftime_access X__time64_t
	Ftime_write  X__time64_t
	Fsize        X_fsize_t
	Fname        [260]Wchar_t
	F__ccgo_pad2 [4]byte
} /* io.h:112:3 */

type X_wfinddata64_t = struct {
	Fattrib      uint32
	F__ccgo_pad1 [4]byte
	Ftime_create X__time64_t
	Ftime_access X__time64_t
	Ftime_write  X__time64_t
	Fsize        int64
	Fname        [260]Wchar_t
} /* io.h:121:3 */

type X_off_t = int32 /* _mingw_off_t.h:5:16 */
type Off32_t = int32 /* _mingw_off_t.h:7:16 */

type X_off64_t = int64 /* _mingw_off_t.h:13:39 */
type Off64_t = int64   /* _mingw_off_t.h:15:39 */

type Off_t = Off64_t /* _mingw_off_t.h:24:17 */

// *
// This file has no copyright assigned and is placed in the Public Domain.
// This file is part of the mingw-w64 runtime package.
// No warranty is given; refer to the file DISCLAIMER.PD within this package.

// *
// This file has no copyright assigned and is placed in the Public Domain.
// This file is part of the mingw-w64 runtime package.
// No warranty is given; refer to the file DISCLAIMER.PD within this package.

type X_ino_t = uint16 /* types.h:43:24 */
type Ino_t = uint16   /* types.h:45:24 */

type X_dev_t = uint32 /* types.h:51:22 */
type Dev_t = uint32   /* types.h:53:22 */

type X_pid_t = int64 /* types.h:63:17 */

type Pid_t = X_pid_t /* types.h:68:16 */

type X_mode_t = uint16 /* types.h:74:24 */

type Mode_t = X_mode_t /* types.h:77:17 */

type Useconds_t = uint32 /* types.h:84:22 */

type Timespec = struct {
	Ftv_sec      Time_t
	Ftv_nsec     int32
	F__ccgo_pad1 [4]byte
} /* types.h:89:1 */

type Itimerspec = struct {
	Fit_interval struct {
		Ftv_sec      Time_t
		Ftv_nsec     int32
		F__ccgo_pad1 [4]byte
	}
	Fit_value struct {
		Ftv_sec      Time_t
		Ftv_nsec     int32
		F__ccgo_pad1 [4]byte
	}
} /* types.h:94:1 */

type X_sigset_t = uint64 /* types.h:104:28 */

type X_stat32 = struct {
	Fst_dev      X_dev_t
	Fst_ino      X_ino_t
	Fst_mode     uint16
	Fst_nlink    int16
	Fst_uid      int16
	Fst_gid      int16
	F__ccgo_pad1 [2]byte
	Fst_rdev     X_dev_t
	Fst_size     X_off_t
	Fst_atime    X__time32_t
	Fst_mtime    X__time32_t
	Fst_ctime    X__time32_t
} /* _mingw_stat64.h:28:3 */

type Stat = struct {
	Fst_dev      X_dev_t
	Fst_ino      X_ino_t
	Fst_mode     uint16
	Fst_nlink    int16
	Fst_uid      int16
	Fst_gid      int16
	F__ccgo_pad1 [2]byte
	Fst_rdev     X_dev_t
	Fst_size     X_off_t
	Fst_atime    Time_t
	Fst_mtime    Time_t
	Fst_ctime    Time_t
} /* _mingw_stat64.h:43:3 */

type X_stat32i64 = struct {
	Fst_dev      X_dev_t
	Fst_ino      X_ino_t
	Fst_mode     uint16
	Fst_nlink    int16
	Fst_uid      int16
	Fst_gid      int16
	F__ccgo_pad1 [2]byte
	Fst_rdev     X_dev_t
	F__ccgo_pad2 [4]byte
	Fst_size     int64
	Fst_atime    X__time32_t
	Fst_mtime    X__time32_t
	Fst_ctime    X__time32_t
	F__ccgo_pad3 [4]byte
} /* _mingw_stat64.h:58:3 */

type X_stat64i32 = struct {
	Fst_dev      X_dev_t
	Fst_ino      X_ino_t
	Fst_mode     uint16
	Fst_nlink    int16
	Fst_uid      int16
	Fst_gid      int16
	F__ccgo_pad1 [2]byte
	Fst_rdev     X_dev_t
	Fst_size     X_off_t
	Fst_atime    X__time64_t
	Fst_mtime    X__time64_t
	Fst_ctime    X__time64_t
} /* _mingw_stat64.h:72:3 */

type X_stat64 = struct {
	Fst_dev      X_dev_t
	Fst_ino      X_ino_t
	Fst_mode     uint16
	Fst_nlink    int16
	Fst_uid      int16
	Fst_gid      int16
	F__ccgo_pad1 [2]byte
	Fst_rdev     X_dev_t
	F__ccgo_pad2 [4]byte
	Fst_size     int64
	Fst_atime    X__time64_t
	Fst_mtime    X__time64_t
	Fst_ctime    X__time64_t
} /* _mingw_stat64.h:86:3 */

var _ int8 /* gen.c:2:13: */
