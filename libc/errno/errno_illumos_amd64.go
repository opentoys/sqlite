// Code generated by 'ccgo errno/gen.c -crt-import-path "" -export-defines "" -export-enums "" -export-externs X -export-fields F -export-structs "" -export-typedefs "" -header -hide _OSSwapInt16,_OSSwapInt32,_OSSwapInt64 -ignore-unsupported-alignment -o errno/errno_illumos_amd64.go -pkgname errno', DO NOT EDIT.

package errno

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
	E2BIG              = 7   // errno.h:57:1:
	EACCES             = 13  // errno.h:63:1:
	EADDRINUSE         = 125 // errno.h:173:1:
	EADDRNOTAVAIL      = 126 // errno.h:174:1:
	EADV               = 68  // errno.h:128:1:
	EAFNOSUPPORT       = 124 // errno.h:171:1:
	EAGAIN             = 11  // errno.h:61:1:
	EALREADY           = 149 // errno.h:193:1:
	EBADE              = 50  // errno.h:104:1:
	EBADF              = 9   // errno.h:59:1:
	EBADFD             = 81  // errno.h:143:1:
	EBADMSG            = 77  // errno.h:139:1:
	EBADR              = 51  // errno.h:105:1:
	EBADRQC            = 54  // errno.h:108:1:
	EBADSLT            = 55  // errno.h:109:1:
	EBFONT             = 57  // errno.h:112:1:
	EBUSY              = 16  // errno.h:66:1:
	ECANCELED          = 47  // errno.h:97:1:
	ECHILD             = 10  // errno.h:60:1:
	ECHRNG             = 37  // errno.h:87:1:
	ECOMM              = 70  // errno.h:131:1:
	ECONNABORTED       = 130 // errno.h:180:1:
	ECONNREFUSED       = 146 // errno.h:189:1:
	ECONNRESET         = 131 // errno.h:181:1:
	EDEADLK            = 45  // errno.h:95:1:
	EDEADLOCK          = 56  // errno.h:110:1:
	EDESTADDRREQ       = 96  // errno.h:163:1:
	EDOM               = 33  // errno.h:83:1:
	EDQUOT             = 49  // errno.h:101:1:
	EEXIST             = 17  // errno.h:67:1:
	EFAULT             = 14  // errno.h:64:1:
	EFBIG              = 27  // errno.h:77:1:
	EHOSTDOWN          = 147 // errno.h:190:1:
	EHOSTUNREACH       = 148 // errno.h:191:1:
	EIDRM              = 36  // errno.h:86:1:
	EILSEQ             = 88  // errno.h:152:1:
	EINPROGRESS        = 150 // errno.h:194:1:
	EINTR              = 4   // errno.h:54:1:
	EINVAL             = 22  // errno.h:72:1:
	EIO                = 5   // errno.h:55:1:
	EISCONN            = 133 // errno.h:183:1:
	EISDIR             = 21  // errno.h:71:1:
	EL2HLT             = 44  // errno.h:94:1:
	EL2NSYNC           = 38  // errno.h:88:1:
	EL3HLT             = 39  // errno.h:89:1:
	EL3RST             = 40  // errno.h:90:1:
	ELIBACC            = 83  // errno.h:147:1:
	ELIBBAD            = 84  // errno.h:148:1:
	ELIBEXEC           = 87  // errno.h:151:1:
	ELIBMAX            = 86  // errno.h:150:1:
	ELIBSCN            = 85  // errno.h:149:1:
	ELNRNG             = 41  // errno.h:91:1:
	ELOCKUNMAPPED      = 72  // errno.h:135:1:
	ELOOP              = 90  // errno.h:154:1:
	EMFILE             = 24  // errno.h:74:1:
	EMLINK             = 31  // errno.h:81:1:
	EMSGSIZE           = 97  // errno.h:164:1:
	EMULTIHOP          = 74  // errno.h:138:1:
	ENAMETOOLONG       = 78  // errno.h:140:1:
	ENETDOWN           = 127 // errno.h:176:1:
	ENETRESET          = 129 // errno.h:178:1:
	ENETUNREACH        = 128 // errno.h:177:1:
	ENFILE             = 23  // errno.h:73:1:
	ENOANO             = 53  // errno.h:107:1:
	ENOBUFS            = 132 // errno.h:182:1:
	ENOCSI             = 43  // errno.h:93:1:
	ENODATA            = 61  // errno.h:120:1:
	ENODEV             = 19  // errno.h:69:1:
	ENOENT             = 2   // errno.h:52:1:
	ENOEXEC            = 8   // errno.h:58:1:
	ENOLCK             = 46  // errno.h:96:1:
	ENOLINK            = 67  // errno.h:127:1:
	ENOMEM             = 12  // errno.h:62:1:
	ENOMSG             = 35  // errno.h:85:1:
	ENONET             = 64  // errno.h:124:1:
	ENOPKG             = 65  // errno.h:125:1:
	ENOPROTOOPT        = 99  // errno.h:166:1:
	ENOSPC             = 28  // errno.h:78:1:
	ENOSR              = 63  // errno.h:122:1:
	ENOSTR             = 60  // errno.h:119:1:
	ENOSYS             = 89  // errno.h:153:1:
	ENOTACTIVE         = 73  // errno.h:137:1:
	ENOTBLK            = 15  // errno.h:65:1:
	ENOTCONN           = 134 // errno.h:184:1:
	ENOTDIR            = 20  // errno.h:70:1:
	ENOTEMPTY          = 93  // errno.h:157:1:
	ENOTRECOVERABLE    = 59  // errno.h:116:1:
	ENOTSOCK           = 95  // errno.h:162:1:
	ENOTSUP            = 48  // errno.h:98:1:
	ENOTTY             = 25  // errno.h:75:1:
	ENOTUNIQ           = 80  // errno.h:142:1:
	ENXIO              = 6   // errno.h:56:1:
	EOPNOTSUPP         = 122 // errno.h:169:1:
	EOVERFLOW          = 79  // errno.h:141:1:
	EOWNERDEAD         = 58  // errno.h:115:1:
	EPERM              = 1   // errno.h:51:1:
	EPFNOSUPPORT       = 123 // errno.h:170:1:
	EPIPE              = 32  // errno.h:82:1:
	EPROTO             = 71  // errno.h:132:1:
	EPROTONOSUPPORT    = 120 // errno.h:167:1:
	EPROTOTYPE         = 98  // errno.h:165:1:
	ERANGE             = 34  // errno.h:84:1:
	EREMCHG            = 82  // errno.h:144:1:
	EREMOTE            = 66  // errno.h:126:1:
	ERESTART           = 91  // errno.h:155:1:
	EROFS              = 30  // errno.h:80:1:
	ESHUTDOWN          = 143 // errno.h:186:1:
	ESOCKTNOSUPPORT    = 121 // errno.h:168:1:
	ESPIPE             = 29  // errno.h:79:1:
	ESRCH              = 3   // errno.h:53:1:
	ESRMNT             = 69  // errno.h:129:1:
	ESTALE             = 151 // errno.h:197:1:
	ESTRPIPE           = 92  // errno.h:156:1:
	ETIME              = 62  // errno.h:121:1:
	ETIMEDOUT          = 145 // errno.h:188:1:
	ETOOMANYREFS       = 144 // errno.h:187:1:
	ETXTBSY            = 26  // errno.h:76:1:
	EUNATCH            = 42  // errno.h:92:1:
	EUSERS             = 94  // errno.h:158:1:
	EWOULDBLOCK        = 11  // errno.h:192:1:
	EXDEV              = 18  // errno.h:68:1:
	EXFULL             = 52  // errno.h:106:1:
	X_ERRNO_H          = 0   // errno.h:33:1:
	X_FILE_OFFSET_BITS = 64  // <builtin>:25:1:
	X_LP64             = 1   // <predefined>:286:1:
	X_SYS_ERRNO_H      = 0   // errno.h:41:1:
	Sun                = 1   // <predefined>:172:1:
	Unix               = 1   // <predefined>:175:1:
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
// ANSI C++ requires that errno be a macro

var _ int8 /* gen.c:2:13: */
