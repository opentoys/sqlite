// Code generated by 'ccgo -o vfs_linux_riscv64.go c/vfs.c -I../testdata/sqlite-amalgamation-3380500 -lgithub.com/opentoys/sqlite/lib -pkgname vfs -nocapi -export-externs X -D SQLITE_OS_UNIX -hide=vfsFullPathname -hide=vfsOpen -hide=vfsRead -hide=vfsAccess -hide=vfsFileSize -hide=vfsClose', DO NOT EDIT.

package vfs

import (
	"math"
	"reflect"
	"sync/atomic"
	"unsafe"

	"github.com/opentoys/sqlite/libc"
	"github.com/opentoys/sqlite/libc/sys/types"
	"github.com/opentoys/sqlite/lib"
)

var _ = math.Pi
var _ reflect.Kind
var _ atomic.Value
var _ unsafe.Pointer
var _ *libc.TLS
var _ types.Size_t

const (
	_PC_LINK_MAX           = 0
	_PC_MAX_CANON          = 1
	_PC_MAX_INPUT          = 2
	_PC_NAME_MAX           = 3
	_PC_PATH_MAX           = 4
	_PC_PIPE_BUF           = 5
	_PC_CHOWN_RESTRICTED   = 6
	_PC_NO_TRUNC           = 7
	_PC_VDISABLE           = 8
	_PC_SYNC_IO            = 9
	_PC_ASYNC_IO           = 10
	_PC_PRIO_IO            = 11
	_PC_SOCK_MAXBUF        = 12
	_PC_FILESIZEBITS       = 13
	_PC_REC_INCR_XFER_SIZE = 14
	_PC_REC_MAX_XFER_SIZE  = 15
	_PC_REC_MIN_XFER_SIZE  = 16
	_PC_REC_XFER_ALIGN     = 17
	_PC_ALLOC_SIZE_MIN     = 18
	_PC_SYMLINK_MAX        = 19
	_PC_2_SYMLINKS         = 20
)

const (
	_CS_PATH = 0

	_CS_V6_WIDTH_RESTRICTED_ENVS = 1

	_CS_GNU_LIBC_VERSION       = 2
	_CS_GNU_LIBPTHREAD_VERSION = 3

	_CS_V5_WIDTH_RESTRICTED_ENVS = 4

	_CS_V7_WIDTH_RESTRICTED_ENVS = 5

	_CS_LFS_CFLAGS      = 1000
	_CS_LFS_LDFLAGS     = 1001
	_CS_LFS_LIBS        = 1002
	_CS_LFS_LINTFLAGS   = 1003
	_CS_LFS64_CFLAGS    = 1004
	_CS_LFS64_LDFLAGS   = 1005
	_CS_LFS64_LIBS      = 1006
	_CS_LFS64_LINTFLAGS = 1007

	_CS_XBS5_ILP32_OFF32_CFLAGS     = 1100
	_CS_XBS5_ILP32_OFF32_LDFLAGS    = 1101
	_CS_XBS5_ILP32_OFF32_LIBS       = 1102
	_CS_XBS5_ILP32_OFF32_LINTFLAGS  = 1103
	_CS_XBS5_ILP32_OFFBIG_CFLAGS    = 1104
	_CS_XBS5_ILP32_OFFBIG_LDFLAGS   = 1105
	_CS_XBS5_ILP32_OFFBIG_LIBS      = 1106
	_CS_XBS5_ILP32_OFFBIG_LINTFLAGS = 1107
	_CS_XBS5_LP64_OFF64_CFLAGS      = 1108
	_CS_XBS5_LP64_OFF64_LDFLAGS     = 1109
	_CS_XBS5_LP64_OFF64_LIBS        = 1110
	_CS_XBS5_LP64_OFF64_LINTFLAGS   = 1111
	_CS_XBS5_LPBIG_OFFBIG_CFLAGS    = 1112
	_CS_XBS5_LPBIG_OFFBIG_LDFLAGS   = 1113
	_CS_XBS5_LPBIG_OFFBIG_LIBS      = 1114
	_CS_XBS5_LPBIG_OFFBIG_LINTFLAGS = 1115

	_CS_POSIX_V6_ILP32_OFF32_CFLAGS     = 1116
	_CS_POSIX_V6_ILP32_OFF32_LDFLAGS    = 1117
	_CS_POSIX_V6_ILP32_OFF32_LIBS       = 1118
	_CS_POSIX_V6_ILP32_OFF32_LINTFLAGS  = 1119
	_CS_POSIX_V6_ILP32_OFFBIG_CFLAGS    = 1120
	_CS_POSIX_V6_ILP32_OFFBIG_LDFLAGS   = 1121
	_CS_POSIX_V6_ILP32_OFFBIG_LIBS      = 1122
	_CS_POSIX_V6_ILP32_OFFBIG_LINTFLAGS = 1123
	_CS_POSIX_V6_LP64_OFF64_CFLAGS      = 1124
	_CS_POSIX_V6_LP64_OFF64_LDFLAGS     = 1125
	_CS_POSIX_V6_LP64_OFF64_LIBS        = 1126
	_CS_POSIX_V6_LP64_OFF64_LINTFLAGS   = 1127
	_CS_POSIX_V6_LPBIG_OFFBIG_CFLAGS    = 1128
	_CS_POSIX_V6_LPBIG_OFFBIG_LDFLAGS   = 1129
	_CS_POSIX_V6_LPBIG_OFFBIG_LIBS      = 1130
	_CS_POSIX_V6_LPBIG_OFFBIG_LINTFLAGS = 1131

	_CS_POSIX_V7_ILP32_OFF32_CFLAGS     = 1132
	_CS_POSIX_V7_ILP32_OFF32_LDFLAGS    = 1133
	_CS_POSIX_V7_ILP32_OFF32_LIBS       = 1134
	_CS_POSIX_V7_ILP32_OFF32_LINTFLAGS  = 1135
	_CS_POSIX_V7_ILP32_OFFBIG_CFLAGS    = 1136
	_CS_POSIX_V7_ILP32_OFFBIG_LDFLAGS   = 1137
	_CS_POSIX_V7_ILP32_OFFBIG_LIBS      = 1138
	_CS_POSIX_V7_ILP32_OFFBIG_LINTFLAGS = 1139
	_CS_POSIX_V7_LP64_OFF64_CFLAGS      = 1140
	_CS_POSIX_V7_LP64_OFF64_LDFLAGS     = 1141
	_CS_POSIX_V7_LP64_OFF64_LIBS        = 1142
	_CS_POSIX_V7_LP64_OFF64_LINTFLAGS   = 1143
	_CS_POSIX_V7_LPBIG_OFFBIG_CFLAGS    = 1144
	_CS_POSIX_V7_LPBIG_OFFBIG_LDFLAGS   = 1145
	_CS_POSIX_V7_LPBIG_OFFBIG_LIBS      = 1146
	_CS_POSIX_V7_LPBIG_OFFBIG_LINTFLAGS = 1147

	_CS_V6_ENV = 1148
	_CS_V7_ENV = 1149
)

const (
	_SC_ARG_MAX               = 0
	_SC_CHILD_MAX             = 1
	_SC_CLK_TCK               = 2
	_SC_NGROUPS_MAX           = 3
	_SC_OPEN_MAX              = 4
	_SC_STREAM_MAX            = 5
	_SC_TZNAME_MAX            = 6
	_SC_JOB_CONTROL           = 7
	_SC_SAVED_IDS             = 8
	_SC_REALTIME_SIGNALS      = 9
	_SC_PRIORITY_SCHEDULING   = 10
	_SC_TIMERS                = 11
	_SC_ASYNCHRONOUS_IO       = 12
	_SC_PRIORITIZED_IO        = 13
	_SC_SYNCHRONIZED_IO       = 14
	_SC_FSYNC                 = 15
	_SC_MAPPED_FILES          = 16
	_SC_MEMLOCK               = 17
	_SC_MEMLOCK_RANGE         = 18
	_SC_MEMORY_PROTECTION     = 19
	_SC_MESSAGE_PASSING       = 20
	_SC_SEMAPHORES            = 21
	_SC_SHARED_MEMORY_OBJECTS = 22
	_SC_AIO_LISTIO_MAX        = 23
	_SC_AIO_MAX               = 24
	_SC_AIO_PRIO_DELTA_MAX    = 25
	_SC_DELAYTIMER_MAX        = 26
	_SC_MQ_OPEN_MAX           = 27
	_SC_MQ_PRIO_MAX           = 28
	_SC_VERSION               = 29
	_SC_PAGESIZE              = 30
	_SC_RTSIG_MAX             = 31
	_SC_SEM_NSEMS_MAX         = 32
	_SC_SEM_VALUE_MAX         = 33
	_SC_SIGQUEUE_MAX          = 34
	_SC_TIMER_MAX             = 35

	_SC_BC_BASE_MAX        = 36
	_SC_BC_DIM_MAX         = 37
	_SC_BC_SCALE_MAX       = 38
	_SC_BC_STRING_MAX      = 39
	_SC_COLL_WEIGHTS_MAX   = 40
	_SC_EQUIV_CLASS_MAX    = 41
	_SC_EXPR_NEST_MAX      = 42
	_SC_LINE_MAX           = 43
	_SC_RE_DUP_MAX         = 44
	_SC_CHARCLASS_NAME_MAX = 45

	_SC_2_VERSION   = 46
	_SC_2_C_BIND    = 47
	_SC_2_C_DEV     = 48
	_SC_2_FORT_DEV  = 49
	_SC_2_FORT_RUN  = 50
	_SC_2_SW_DEV    = 51
	_SC_2_LOCALEDEF = 52

	_SC_PII                 = 53
	_SC_PII_XTI             = 54
	_SC_PII_SOCKET          = 55
	_SC_PII_INTERNET        = 56
	_SC_PII_OSI             = 57
	_SC_POLL                = 58
	_SC_SELECT              = 59
	_SC_UIO_MAXIOV          = 60
	_SC_IOV_MAX             = 60
	_SC_PII_INTERNET_STREAM = 61
	_SC_PII_INTERNET_DGRAM  = 62
	_SC_PII_OSI_COTS        = 63
	_SC_PII_OSI_CLTS        = 64
	_SC_PII_OSI_M           = 65
	_SC_T_IOV_MAX           = 66

	_SC_THREADS                      = 67
	_SC_THREAD_SAFE_FUNCTIONS        = 68
	_SC_GETGR_R_SIZE_MAX             = 69
	_SC_GETPW_R_SIZE_MAX             = 70
	_SC_LOGIN_NAME_MAX               = 71
	_SC_TTY_NAME_MAX                 = 72
	_SC_THREAD_DESTRUCTOR_ITERATIONS = 73
	_SC_THREAD_KEYS_MAX              = 74
	_SC_THREAD_STACK_MIN             = 75
	_SC_THREAD_THREADS_MAX           = 76
	_SC_THREAD_ATTR_STACKADDR        = 77
	_SC_THREAD_ATTR_STACKSIZE        = 78
	_SC_THREAD_PRIORITY_SCHEDULING   = 79
	_SC_THREAD_PRIO_INHERIT          = 80
	_SC_THREAD_PRIO_PROTECT          = 81
	_SC_THREAD_PROCESS_SHARED        = 82

	_SC_NPROCESSORS_CONF = 83
	_SC_NPROCESSORS_ONLN = 84
	_SC_PHYS_PAGES       = 85
	_SC_AVPHYS_PAGES     = 86
	_SC_ATEXIT_MAX       = 87
	_SC_PASS_MAX         = 88

	_SC_XOPEN_VERSION     = 89
	_SC_XOPEN_XCU_VERSION = 90
	_SC_XOPEN_UNIX        = 91
	_SC_XOPEN_CRYPT       = 92
	_SC_XOPEN_ENH_I18N    = 93
	_SC_XOPEN_SHM         = 94

	_SC_2_CHAR_TERM = 95
	_SC_2_C_VERSION = 96
	_SC_2_UPE       = 97

	_SC_XOPEN_XPG2 = 98
	_SC_XOPEN_XPG3 = 99
	_SC_XOPEN_XPG4 = 100

	_SC_CHAR_BIT   = 101
	_SC_CHAR_MAX   = 102
	_SC_CHAR_MIN   = 103
	_SC_INT_MAX    = 104
	_SC_INT_MIN    = 105
	_SC_LONG_BIT   = 106
	_SC_WORD_BIT   = 107
	_SC_MB_LEN_MAX = 108
	_SC_NZERO      = 109
	_SC_SSIZE_MAX  = 110
	_SC_SCHAR_MAX  = 111
	_SC_SCHAR_MIN  = 112
	_SC_SHRT_MAX   = 113
	_SC_SHRT_MIN   = 114
	_SC_UCHAR_MAX  = 115
	_SC_UINT_MAX   = 116
	_SC_ULONG_MAX  = 117
	_SC_USHRT_MAX  = 118

	_SC_NL_ARGMAX  = 119
	_SC_NL_LANGMAX = 120
	_SC_NL_MSGMAX  = 121
	_SC_NL_NMAX    = 122
	_SC_NL_SETMAX  = 123
	_SC_NL_TEXTMAX = 124

	_SC_XBS5_ILP32_OFF32  = 125
	_SC_XBS5_ILP32_OFFBIG = 126
	_SC_XBS5_LP64_OFF64   = 127
	_SC_XBS5_LPBIG_OFFBIG = 128

	_SC_XOPEN_LEGACY           = 129
	_SC_XOPEN_REALTIME         = 130
	_SC_XOPEN_REALTIME_THREADS = 131

	_SC_ADVISORY_INFO          = 132
	_SC_BARRIERS               = 133
	_SC_BASE                   = 134
	_SC_C_LANG_SUPPORT         = 135
	_SC_C_LANG_SUPPORT_R       = 136
	_SC_CLOCK_SELECTION        = 137
	_SC_CPUTIME                = 138
	_SC_THREAD_CPUTIME         = 139
	_SC_DEVICE_IO              = 140
	_SC_DEVICE_SPECIFIC        = 141
	_SC_DEVICE_SPECIFIC_R      = 142
	_SC_FD_MGMT                = 143
	_SC_FIFO                   = 144
	_SC_PIPE                   = 145
	_SC_FILE_ATTRIBUTES        = 146
	_SC_FILE_LOCKING           = 147
	_SC_FILE_SYSTEM            = 148
	_SC_MONOTONIC_CLOCK        = 149
	_SC_MULTI_PROCESS          = 150
	_SC_SINGLE_PROCESS         = 151
	_SC_NETWORKING             = 152
	_SC_READER_WRITER_LOCKS    = 153
	_SC_SPIN_LOCKS             = 154
	_SC_REGEXP                 = 155
	_SC_REGEX_VERSION          = 156
	_SC_SHELL                  = 157
	_SC_SIGNALS                = 158
	_SC_SPAWN                  = 159
	_SC_SPORADIC_SERVER        = 160
	_SC_THREAD_SPORADIC_SERVER = 161
	_SC_SYSTEM_DATABASE        = 162
	_SC_SYSTEM_DATABASE_R      = 163
	_SC_TIMEOUTS               = 164
	_SC_TYPED_MEMORY_OBJECTS   = 165
	_SC_USER_GROUPS            = 166
	_SC_USER_GROUPS_R          = 167
	_SC_2_PBS                  = 168
	_SC_2_PBS_ACCOUNTING       = 169
	_SC_2_PBS_LOCATE           = 170
	_SC_2_PBS_MESSAGE          = 171
	_SC_2_PBS_TRACK            = 172
	_SC_SYMLOOP_MAX            = 173
	_SC_STREAMS                = 174
	_SC_2_PBS_CHECKPOINT       = 175

	_SC_V6_ILP32_OFF32  = 176
	_SC_V6_ILP32_OFFBIG = 177
	_SC_V6_LP64_OFF64   = 178
	_SC_V6_LPBIG_OFFBIG = 179

	_SC_HOST_NAME_MAX      = 180
	_SC_TRACE              = 181
	_SC_TRACE_EVENT_FILTER = 182
	_SC_TRACE_INHERIT      = 183
	_SC_TRACE_LOG          = 184

	_SC_LEVEL1_ICACHE_SIZE     = 185
	_SC_LEVEL1_ICACHE_ASSOC    = 186
	_SC_LEVEL1_ICACHE_LINESIZE = 187
	_SC_LEVEL1_DCACHE_SIZE     = 188
	_SC_LEVEL1_DCACHE_ASSOC    = 189
	_SC_LEVEL1_DCACHE_LINESIZE = 190
	_SC_LEVEL2_CACHE_SIZE      = 191
	_SC_LEVEL2_CACHE_ASSOC     = 192
	_SC_LEVEL2_CACHE_LINESIZE  = 193
	_SC_LEVEL3_CACHE_SIZE      = 194
	_SC_LEVEL3_CACHE_ASSOC     = 195
	_SC_LEVEL3_CACHE_LINESIZE  = 196
	_SC_LEVEL4_CACHE_SIZE      = 197
	_SC_LEVEL4_CACHE_ASSOC     = 198
	_SC_LEVEL4_CACHE_LINESIZE  = 199

	_SC_IPV6        = 235
	_SC_RAW_SOCKETS = 236

	_SC_V7_ILP32_OFF32  = 237
	_SC_V7_ILP32_OFFBIG = 238
	_SC_V7_LP64_OFF64   = 239
	_SC_V7_LPBIG_OFFBIG = 240

	_SC_SS_REPL_MAX = 241

	_SC_TRACE_EVENT_NAME_MAX = 242
	_SC_TRACE_NAME_MAX       = 243
	_SC_TRACE_SYS_MAX        = 244
	_SC_TRACE_USER_EVENT_MAX = 245

	_SC_XOPEN_STREAMS = 246

	_SC_THREAD_ROBUST_PRIO_INHERIT = 247
	_SC_THREAD_ROBUST_PRIO_PROTECT = 248
)

const (
	SIGEV_SIGNAL = 0
	SIGEV_NONE   = 1
	SIGEV_THREAD = 2

	SIGEV_THREAD_ID = 4
)

const (
	SEGV_MAPERR  = 1
	SEGV_ACCERR  = 2
	SEGV_BNDERR  = 3
	SEGV_PKUERR  = 4
	SEGV_ACCADI  = 5
	SEGV_ADIDERR = 6
	SEGV_ADIPERR = 7
)

const (
	BUS_ADRALN    = 1
	BUS_ADRERR    = 2
	BUS_OBJERR    = 3
	BUS_MCEERR_AR = 4
	BUS_MCEERR_AO = 5
)

const (
	CLD_EXITED    = 1
	CLD_KILLED    = 2
	CLD_DUMPED    = 3
	CLD_TRAPPED   = 4
	CLD_STOPPED   = 5
	CLD_CONTINUED = 6
)

const (
	POLL_IN  = 1
	POLL_OUT = 2
	POLL_MSG = 3
	POLL_ERR = 4
	POLL_PRI = 5
	POLL_HUP = 6
)

const (
	SI_ASYNCNL  = -60
	SI_DETHREAD = -7

	SI_TKILL   = -6
	SI_SIGIO   = -5
	SI_ASYNCIO = -4
	SI_MESGQ   = -3
	SI_TIMER   = -2
	SI_QUEUE   = -1
	SI_USER    = 0
	SI_KERNEL  = 128
)

const (
	ILL_ILLOPC   = 1
	ILL_ILLOPN   = 2
	ILL_ILLADR   = 3
	ILL_ILLTRP   = 4
	ILL_PRVOPC   = 5
	ILL_PRVREG   = 6
	ILL_COPROC   = 7
	ILL_BADSTK   = 8
	ILL_BADIADDR = 9
)

const (
	FPE_INTDIV   = 1
	FPE_INTOVF   = 2
	FPE_FLTDIV   = 3
	FPE_FLTOVF   = 4
	FPE_FLTUND   = 5
	FPE_FLTRES   = 6
	FPE_FLTINV   = 7
	FPE_FLTSUB   = 8
	FPE_FLTUNK   = 14
	FPE_CONDTRAP = 15
)

const (
	SS_ONSTACK = 1
	SS_DISABLE = 2
)

type ptrdiff_t = int64

type size_t = uint64

type wchar_t = int32

type va_list = uintptr

type sqlite_int64 = int64
type sqlite_uint64 = uint64
type sqlite3_int64 = sqlite_int64
type sqlite3_uint64 = sqlite_uint64

type sqlite3_callback = uintptr

type sqlite3_file1 = struct{ pMethods uintptr }

type sqlite3_file = sqlite3_file1
type sqlite3_io_methods1 = struct {
	iVersion               int32
	_                      [4]byte
	xClose                 uintptr
	xRead                  uintptr
	xWrite                 uintptr
	xTruncate              uintptr
	xSync                  uintptr
	xFileSize              uintptr
	xLock                  uintptr
	xUnlock                uintptr
	xCheckReservedLock     uintptr
	xFileControl           uintptr
	xSectorSize            uintptr
	xDeviceCharacteristics uintptr
	xShmMap                uintptr
	xShmLock               uintptr
	xShmBarrier            uintptr
	xShmUnmap              uintptr
	xFetch                 uintptr
	xUnfetch               uintptr
}

type sqlite3_io_methods = sqlite3_io_methods1

type sqlite3_vfs1 = struct {
	iVersion          int32
	szOsFile          int32
	mxPathname        int32
	_                 [4]byte
	pNext             uintptr
	zName             uintptr
	pAppData          uintptr
	xOpen             uintptr
	xDelete           uintptr
	xAccess           uintptr
	xFullPathname     uintptr
	xDlOpen           uintptr
	xDlError          uintptr
	xDlSym            uintptr
	xDlClose          uintptr
	xRandomness       uintptr
	xSleep            uintptr
	xCurrentTime      uintptr
	xGetLastError     uintptr
	xCurrentTimeInt64 uintptr
	xSetSystemCall    uintptr
	xGetSystemCall    uintptr
	xNextSystemCall   uintptr
}

type sqlite3_vfs = sqlite3_vfs1
type sqlite3_syscall_ptr = uintptr

type sqlite3_mem_methods1 = struct {
	xMalloc   uintptr
	xFree     uintptr
	xRealloc  uintptr
	xSize     uintptr
	xRoundup  uintptr
	xInit     uintptr
	xShutdown uintptr
	pAppData  uintptr
}

type sqlite3_mem_methods = sqlite3_mem_methods1

type sqlite3_destructor_type = uintptr

type sqlite3_vtab1 = struct {
	pModule uintptr
	nRef    int32
	_       [4]byte
	zErrMsg uintptr
}

type sqlite3_vtab = sqlite3_vtab1
type sqlite3_index_info1 = struct {
	nConstraint      int32
	_                [4]byte
	aConstraint      uintptr
	nOrderBy         int32
	_                [4]byte
	aOrderBy         uintptr
	aConstraintUsage uintptr
	idxNum           int32
	_                [4]byte
	idxStr           uintptr
	needToFreeIdxStr int32
	orderByConsumed  int32
	estimatedCost    float64
	estimatedRows    sqlite3_int64
	idxFlags         int32
	_                [4]byte
	colUsed          sqlite3_uint64
}

type sqlite3_index_info = sqlite3_index_info1
type sqlite3_vtab_cursor1 = struct{ pVtab uintptr }

type sqlite3_vtab_cursor = sqlite3_vtab_cursor1
type sqlite3_module1 = struct {
	iVersion      int32
	_             [4]byte
	xCreate       uintptr
	xConnect      uintptr
	xBestIndex    uintptr
	xDisconnect   uintptr
	xDestroy      uintptr
	xOpen         uintptr
	xClose        uintptr
	xFilter       uintptr
	xNext         uintptr
	xEof          uintptr
	xColumn       uintptr
	xRowid        uintptr
	xUpdate       uintptr
	xBegin        uintptr
	xSync         uintptr
	xCommit       uintptr
	xRollback     uintptr
	xFindFunction uintptr
	xRename       uintptr
	xSavepoint    uintptr
	xRelease      uintptr
	xRollbackTo   uintptr
	xShadowName   uintptr
}

type sqlite3_module = sqlite3_module1

type sqlite3_index_constraint = struct {
	iColumn     int32
	op          uint8
	usable      uint8
	_           [2]byte
	iTermOffset int32
}

type sqlite3_index_orderby = struct {
	iColumn int32
	desc    uint8
	_       [3]byte
}

type sqlite3_index_constraint_usage = struct {
	argvIndex int32
	omit      uint8
	_         [3]byte
}

type sqlite3_mutex_methods1 = struct {
	xMutexInit    uintptr
	xMutexEnd     uintptr
	xMutexAlloc   uintptr
	xMutexFree    uintptr
	xMutexEnter   uintptr
	xMutexTry     uintptr
	xMutexLeave   uintptr
	xMutexHeld    uintptr
	xMutexNotheld uintptr
}

type sqlite3_mutex_methods = sqlite3_mutex_methods1

type sqlite3_pcache_page1 = struct {
	pBuf   uintptr
	pExtra uintptr
}

type sqlite3_pcache_page = sqlite3_pcache_page1

type sqlite3_pcache_methods21 = struct {
	iVersion   int32
	_          [4]byte
	pArg       uintptr
	xInit      uintptr
	xShutdown  uintptr
	xCreate    uintptr
	xCachesize uintptr
	xPagecount uintptr
	xFetch     uintptr
	xUnpin     uintptr
	xRekey     uintptr
	xTruncate  uintptr
	xDestroy   uintptr
	xShrink    uintptr
}

type sqlite3_pcache_methods2 = sqlite3_pcache_methods21

type sqlite3_pcache_methods1 = struct {
	pArg       uintptr
	xInit      uintptr
	xShutdown  uintptr
	xCreate    uintptr
	xCachesize uintptr
	xPagecount uintptr
	xFetch     uintptr
	xUnpin     uintptr
	xRekey     uintptr
	xTruncate  uintptr
	xDestroy   uintptr
}

type sqlite3_pcache_methods = sqlite3_pcache_methods1

type sqlite3_snapshot1 = struct{ hidden [48]uint8 }

type sqlite3_snapshot = sqlite3_snapshot1

type sqlite3_rtree_geometry1 = struct {
	pContext uintptr
	nParam   int32
	_        [4]byte
	aParam   uintptr
	pUser    uintptr
	xDelUser uintptr
}

type sqlite3_rtree_geometry = sqlite3_rtree_geometry1
type sqlite3_rtree_query_info1 = struct {
	pContext      uintptr
	nParam        int32
	_             [4]byte
	aParam        uintptr
	pUser         uintptr
	xDelUser      uintptr
	aCoord        uintptr
	anQueue       uintptr
	nCoord        int32
	iLevel        int32
	mxLevel       int32
	_             [4]byte
	iRowid        sqlite3_int64
	rParentScore  sqlite3_rtree_dbl
	eParentWithin int32
	eWithin       int32
	rScore        sqlite3_rtree_dbl
	apSqlParam    uintptr
}

type sqlite3_rtree_query_info = sqlite3_rtree_query_info1

type sqlite3_rtree_dbl = float64

type Fts5ExtensionApi1 = struct {
	iVersion           int32
	_                  [4]byte
	xUserData          uintptr
	xColumnCount       uintptr
	xRowCount          uintptr
	xColumnTotalSize   uintptr
	xTokenize          uintptr
	xPhraseCount       uintptr
	xPhraseSize        uintptr
	xInstCount         uintptr
	xInst              uintptr
	xRowid             uintptr
	xColumnText        uintptr
	xColumnSize        uintptr
	xQueryPhrase       uintptr
	xSetAuxdata        uintptr
	xGetAuxdata        uintptr
	xPhraseFirst       uintptr
	xPhraseNext        uintptr
	xPhraseFirstColumn uintptr
	xPhraseNextColumn  uintptr
}

type Fts5ExtensionApi = Fts5ExtensionApi1
type Fts5PhraseIter1 = struct {
	a uintptr
	b uintptr
}

type Fts5PhraseIter = Fts5PhraseIter1

type fts5_extension_function = uintptr
type fts5_tokenizer1 = struct {
	xCreate   uintptr
	xDelete   uintptr
	xTokenize uintptr
}

type fts5_tokenizer = fts5_tokenizer1

type fts5_api1 = struct {
	iVersion         int32
	_                [4]byte
	xCreateTokenizer uintptr
	xFindTokenizer   uintptr
	xCreateFunction  uintptr
}

type fts5_api = fts5_api1

type __locale_struct = struct {
	__locales       [13]uintptr
	__ctype_b       uintptr
	__ctype_tolower uintptr
	__ctype_toupper uintptr
	__names         [13]uintptr
}

type locale_t = uintptr

type u_char = uint8
type u_short = uint16
type u_int = uint32
type u_long = uint64
type quad_t = int64
type u_quad_t = uint64
type fsid_t = struct{ __val [2]int32 }
type loff_t = int64

type ino_t = uint64

type dev_t = uint64

type gid_t = uint32

type mode_t = uint32

type nlink_t = uint64

type uid_t = uint32

type off_t = int64

type pid_t = int32

type id_t = uint32

type ssize_t = int64

type daddr_t = int32
type caddr_t = uintptr

type key_t = int32

type clock_t = int64

type clockid_t = int32

type time_t = int64

type timer_t = uintptr

type ulong = uint64
type ushort = uint16
type uint = uint32

type int8_t = int8
type int16_t = int16
type int32_t = int32
type int64_t = int64

type u_int8_t = uint8
type u_int16_t = uint16
type u_int32_t = uint32
type u_int64_t = uint64

type register_t = int32

type sigset_t = struct{ __val [16]uint64 }

type timeval = struct {
	tv_sec  int64
	tv_usec int64
}

type timespec = struct {
	tv_sec  int64
	tv_nsec int64
}

type suseconds_t = int64

type fd_set = struct{ __fds_bits [16]int64 }

type fd_mask = int64

type blksize_t = int64

type blkcnt_t = int64
type fsblkcnt_t = uint64
type fsfilcnt_t = uint64

type __pthread_internal_list = struct {
	__prev uintptr
	__next uintptr
}

type __pthread_internal_slist = struct{ __next uintptr }

type __pthread_mutex_s = struct {
	__lock    int32
	__count   uint32
	__owner   int32
	__nusers  uint32
	__kind    int32
	__spins   int16
	__elision int16
	__list    struct {
		__prev uintptr
		__next uintptr
	}
}

type __pthread_rwlock_arch_t = struct {
	__readers       uint32
	__writers       uint32
	__wrphase_futex uint32
	__writers_futex uint32
	__pad3          uint32
	__pad4          uint32
	__cur_writer    int32
	__shared        int32
	__rwelision     int8
	__pad1          [7]uint8
	__pad2          uint64
	__flags         uint32
	_               [4]byte
}

type __pthread_cond_s = struct {
	__0            struct{ __wseq uint64 }
	__8            struct{ __g1_start uint64 }
	__g_refs       [2]uint32
	__g_size       [2]uint32
	__g1_orig_size uint32
	__wrefs        uint32
	__g_signals    [2]uint32
}

type pthread_t = uint64

type pthread_mutexattr_t = struct {
	_      [0]uint32
	__size [4]uint8
}

type pthread_condattr_t = struct {
	_      [0]uint32
	__size [4]uint8
}

type pthread_key_t = uint32

type pthread_once_t = int32

type pthread_attr_t1 = struct {
	_      [0]uint64
	__size [56]uint8
}

type pthread_attr_t = pthread_attr_t1

type pthread_mutex_t = struct{ __data __pthread_mutex_s }

type pthread_cond_t = struct{ __data __pthread_cond_s }

type pthread_rwlock_t = struct{ __data __pthread_rwlock_arch_t }

type pthread_rwlockattr_t = struct {
	_      [0]uint64
	__size [8]uint8
}

type pthread_spinlock_t = int32

type pthread_barrier_t = struct {
	_      [0]uint64
	__size [32]uint8
}

type pthread_barrierattr_t = struct {
	_      [0]uint32
	__size [4]uint8
}

type stat = struct {
	st_dev     uint64
	st_ino     uint64
	st_nlink   uint64
	st_mode    uint32
	st_uid     uint32
	st_gid     uint32
	__pad0     int32
	st_rdev    uint64
	st_size    int64
	st_blksize int64
	st_blocks  int64
	st_atim    struct {
		tv_sec  int64
		tv_nsec int64
	}
	st_mtim struct {
		tv_sec  int64
		tv_nsec int64
	}
	st_ctim struct {
		tv_sec  int64
		tv_nsec int64
	}
	__glibc_reserved [3]int64
}

type flock = struct {
	l_type   int16
	l_whence int16
	_        [4]byte
	l_start  int64
	l_len    int64
	l_pid    int32
	_        [4]byte
}

type sig_atomic_t = int32

type sigval = struct {
	_         [0]uint64
	sival_int int32
	_         [4]byte
}

type siginfo_t = struct {
	si_signo  int32
	si_errno  int32
	si_code   int32
	__pad0    int32
	_sifields struct {
		_    [0]uint64
		_pad [28]int32
	}
}

type sigval_t = sigval

type sigevent = struct {
	sigev_value struct {
		_         [0]uint64
		sival_int int32
		_         [4]byte
	}
	sigev_signo  int32
	sigev_notify int32
	_sigev_un    struct {
		_    [0]uint64
		_pad [12]int32
	}
}

type sigevent_t = sigevent

type sig_t = uintptr

type sigaction = struct {
	__sigaction_handler struct{ sa_handler uintptr }
	sa_mask             struct{ __val [16]uint64 }
	sa_flags            int32
	_                   [4]byte
	sa_restorer         uintptr
}

type _fpx_sw_bytes = struct {
	magic1            uint32
	extended_size     uint32
	xstate_bv         uint64
	xstate_size       uint32
	__glibc_reserved1 [7]uint32
}

type _fpreg = struct {
	significand [4]uint16
	exponent    uint16
}

type _fpxreg = struct {
	significand       [4]uint16
	exponent          uint16
	__glibc_reserved1 [3]uint16
}

type _xmmreg = struct{ element [4]uint32 }

type _fpstate = struct {
	cwd       uint16
	swd       uint16
	ftw       uint16
	fop       uint16
	rip       uint64
	rdp       uint64
	mxcsr     uint32
	mxcr_mask uint32
	_st       [8]struct {
		significand       [4]uint16
		exponent          uint16
		__glibc_reserved1 [3]uint16
	}
	_xmm              [16]struct{ element [4]uint32 }
	__glibc_reserved1 [24]uint32
}

type sigcontext = struct {
	r8          uint64
	r9          uint64
	r10         uint64
	r11         uint64
	r12         uint64
	r13         uint64
	r14         uint64
	r15         uint64
	rdi         uint64
	rsi         uint64
	rbp         uint64
	rbx         uint64
	rdx         uint64
	rax         uint64
	rcx         uint64
	rsp         uint64
	rip         uint64
	eflags      uint64
	cs          uint16
	gs          uint16
	fs          uint16
	__pad0      uint16
	err         uint64
	trapno      uint64
	oldmask     uint64
	cr2         uint64
	__184       struct{ fpstate uintptr }
	__reserved1 [8]uint64
}

type _xsave_hdr = struct {
	xstate_bv         uint64
	__glibc_reserved1 [2]uint64
	__glibc_reserved2 [5]uint64
}

type _ymmh_state = struct{ ymmh_space [64]uint32 }

type _xstate = struct {
	fpstate struct {
		cwd       uint16
		swd       uint16
		ftw       uint16
		fop       uint16
		rip       uint64
		rdp       uint64
		mxcsr     uint32
		mxcr_mask uint32
		_st       [8]struct {
			significand       [4]uint16
			exponent          uint16
			__glibc_reserved1 [3]uint16
		}
		_xmm              [16]struct{ element [4]uint32 }
		__glibc_reserved1 [24]uint32
	}
	xstate_hdr struct {
		xstate_bv         uint64
		__glibc_reserved1 [2]uint64
		__glibc_reserved2 [5]uint64
	}
	ymmh struct{ ymmh_space [64]uint32 }
}

type stack_t = struct {
	ss_sp    uintptr
	ss_flags int32
	_        [4]byte
	ss_size  size_t
}

type greg_t = int64

type gregset_t = [23]greg_t

type _libc_fpxreg = struct {
	significand       [4]uint16
	exponent          uint16
	__glibc_reserved1 [3]uint16
}

type _libc_xmmreg = struct{ element [4]uint32 }

type _libc_fpstate = struct {
	cwd       uint16
	swd       uint16
	ftw       uint16
	fop       uint16
	rip       uint64
	rdp       uint64
	mxcsr     uint32
	mxcr_mask uint32
	_st       [8]struct {
		significand       [4]uint16
		exponent          uint16
		__glibc_reserved1 [3]uint16
	}
	_xmm              [16]struct{ element [4]uint32 }
	__glibc_reserved1 [24]uint32
}

type fpregset_t = uintptr

type mcontext_t = struct {
	gregs       gregset_t
	fpregs      fpregset_t
	__reserved1 [8]uint64
}

type ucontext_t1 = struct {
	uc_flags     uint64
	uc_link      uintptr
	uc_stack     stack_t
	uc_mcontext  mcontext_t
	uc_sigmask   sigset_t
	__fpregs_mem struct {
		cwd       uint16
		swd       uint16
		ftw       uint16
		fop       uint16
		rip       uint64
		rdp       uint64
		mxcsr     uint32
		mxcr_mask uint32
		_st       [8]struct {
			significand       [4]uint16
			exponent          uint16
			__glibc_reserved1 [3]uint16
		}
		_xmm              [16]struct{ element [4]uint32 }
		__glibc_reserved1 [24]uint32
	}
	__ssp [4]uint64
}

type ucontext_t = ucontext_t1

type sigstack = struct {
	ss_sp      uintptr
	ss_onstack int32
	_          [4]byte
}

type useconds_t = uint32

type intptr_t = int64

type socklen_t = uint32

type tm = struct {
	tm_sec    int32
	tm_min    int32
	tm_hour   int32
	tm_mday   int32
	tm_mon    int32
	tm_year   int32
	tm_wday   int32
	tm_yday   int32
	tm_isdst  int32
	_         [4]byte
	tm_gmtoff int64
	tm_zone   uintptr
}

type itimerspec = struct {
	it_interval struct {
		tv_sec  int64
		tv_nsec int64
	}
	it_value struct {
		tv_sec  int64
		tv_nsec int64
	}
}

type VFSFile1 = struct {
	base        sqlite3_file
	fsFile      uintptr
	fd          int32
	_           [4]byte
	aBuffer     uintptr
	nBuffer     int32
	_           [4]byte
	iBufferOfst sqlite3_int64
}

type VFSFile = VFSFile1

func vfsDirectWrite(tls *libc.TLS, p uintptr, zBuf uintptr, iAmt int32, iOfst sqlite_int64) int32 {
	bp := tls.Alloc(16)
	defer tls.Free(16)

	var ofst off_t
	var nWrite size_t

	libc.X__builtin_printf(tls, ts, libc.VaList(bp, uintptr(unsafe.Pointer(&__func__)), 178))
	libc.X__builtin_abort(tls)
	ofst = libc.Xlseek(tls, (*VFSFile)(unsafe.Pointer(p)).fd, iOfst, 0)
	if ofst != iOfst {
		return 10 | int32(3)<<8
	}

	nWrite = size_t(libc.Xwrite(tls, (*VFSFile)(unsafe.Pointer(p)).fd, zBuf, uint64(iAmt)))
	if nWrite != size_t(iAmt) {
		return 10 | int32(3)<<8
	}

	return 0
}

var __func__ = *(*[15]uint8)(unsafe.Pointer(ts + 13))

func vfsFlushBuffer(tls *libc.TLS, p uintptr) int32 {
	bp := tls.Alloc(16)
	defer tls.Free(16)

	libc.X__builtin_printf(tls, ts, libc.VaList(bp, uintptr(unsafe.Pointer(&__func__1)), 198))
	libc.X__builtin_abort(tls)
	var rc int32 = 0
	if (*VFSFile)(unsafe.Pointer(p)).nBuffer != 0 {
		rc = vfsDirectWrite(tls, p, (*VFSFile)(unsafe.Pointer(p)).aBuffer, (*VFSFile)(unsafe.Pointer(p)).nBuffer, (*VFSFile)(unsafe.Pointer(p)).iBufferOfst)
		(*VFSFile)(unsafe.Pointer(p)).nBuffer = 0
	}
	return rc
}

var __func__1 = *(*[15]uint8)(unsafe.Pointer(ts + 28))

func vfsWrite(tls *libc.TLS, pFile uintptr, zBuf uintptr, iAmt int32, iOfst sqlite_int64) int32 {
	bp := tls.Alloc(16)
	defer tls.Free(16)

	libc.X__builtin_printf(tls, ts, libc.VaList(bp, uintptr(unsafe.Pointer(&__func__4)), 273))
	libc.X__builtin_abort(tls)
	var p uintptr = pFile

	if (*VFSFile)(unsafe.Pointer(p)).aBuffer != 0 {
		var z uintptr = zBuf
		var n int32 = iAmt
		var i sqlite3_int64 = iOfst

		for n > 0 {
			var nCopy int32

			if (*VFSFile)(unsafe.Pointer(p)).nBuffer == 8192 || (*VFSFile)(unsafe.Pointer(p)).iBufferOfst+sqlite3_int64((*VFSFile)(unsafe.Pointer(p)).nBuffer) != i {
				var rc int32 = vfsFlushBuffer(tls, p)
				if rc != 0 {
					return rc
				}
			}
			if (*VFSFile)(unsafe.Pointer(p)).nBuffer == 0 || (*VFSFile)(unsafe.Pointer(p)).iBufferOfst+sqlite3_int64((*VFSFile)(unsafe.Pointer(p)).nBuffer) == i {
			} else {
				libc.X__assert_fail(tls, ts+43, ts+89, uint32(294), uintptr(unsafe.Pointer(&__func__4)))
			}
			(*VFSFile)(unsafe.Pointer(p)).iBufferOfst = i - sqlite3_int64((*VFSFile)(unsafe.Pointer(p)).nBuffer)

			nCopy = 8192 - (*VFSFile)(unsafe.Pointer(p)).nBuffer
			if nCopy > n {
				nCopy = n
			}
			libc.Xmemcpy(tls, (*VFSFile)(unsafe.Pointer(p)).aBuffer+uintptr((*VFSFile)(unsafe.Pointer(p)).nBuffer), z, uint64(nCopy))
			*(*int32)(unsafe.Pointer(p + 32)) += nCopy

			n = n - nCopy
			i = i + sqlite3_int64(nCopy)
			z += uintptr(nCopy)
		}
	} else {
		return vfsDirectWrite(tls, p, zBuf, iAmt, iOfst)
	}

	return 0
}

var __func__4 = *(*[9]uint8)(unsafe.Pointer(ts + 97))

func vfsTruncate(tls *libc.TLS, pFile uintptr, size sqlite_int64) int32 {
	return 0
}

func vfsSync(tls *libc.TLS, pFile uintptr, flags int32) int32 {
	bp := tls.Alloc(16)
	defer tls.Free(16)

	libc.X__builtin_printf(tls, ts, libc.VaList(bp, uintptr(unsafe.Pointer(&__func__5)), 331))
	libc.X__builtin_abort(tls)
	var p uintptr = pFile
	var rc int32

	rc = vfsFlushBuffer(tls, p)
	if rc != 0 {
		return rc
	}

	rc = libc.Xfsync(tls, (*VFSFile)(unsafe.Pointer(p)).fd)
	return func() int32 {
		if rc == 0 {
			return 0
		}
		return 10 | int32(4)<<8
	}()
}

var __func__5 = *(*[8]uint8)(unsafe.Pointer(ts + 106))

func vfsLock(tls *libc.TLS, pFile uintptr, eLock int32) int32 {
	return 0
}

func vfsUnlock(tls *libc.TLS, pFile uintptr, eLock int32) int32 {
	return 0
}

func vfsCheckReservedLock(tls *libc.TLS, pFile uintptr, pResOut uintptr) int32 {
	*(*int32)(unsafe.Pointer(pResOut)) = 0
	return 0
}

func vfsFileControl(tls *libc.TLS, pFile uintptr, op int32, pArg uintptr) int32 {
	return 12
}

func vfsSectorSize(tls *libc.TLS, pFile uintptr) int32 {
	return 0
}

func vfsDeviceCharacteristics(tls *libc.TLS, pFile uintptr) int32 {
	return 0
}

func vfsDelete(tls *libc.TLS, pVfs uintptr, zPath uintptr, dirSync int32) int32 {
	bp := tls.Alloc(4129)
	defer tls.Free(4129)

	libc.X__builtin_printf(tls, ts, libc.VaList(bp, uintptr(unsafe.Pointer(&__func__8)), 473))
	libc.X__builtin_abort(tls)
	var rc int32

	rc = libc.Xunlink(tls, zPath)
	if rc != 0 && *(*int32)(unsafe.Pointer(libc.X__errno_location(tls))) == 2 {
		return 0
	}

	if rc == 0 && dirSync != 0 {
		var dfd int32
		var i int32

		sqlite3.Xsqlite3_snprintf(tls, 4096, bp+32, ts+114, libc.VaList(bp+16, zPath))
		*(*uint8)(unsafe.Pointer(bp + 32 + 4096)) = uint8(0)
		for i = int32(libc.Xstrlen(tls, bp+32)); i > 1 && int32(*(*uint8)(unsafe.Pointer(bp + 32 + uintptr(i)))) != '/'; i++ {
		}
		*(*uint8)(unsafe.Pointer(bp + 32 + uintptr(i))) = uint8(0)

		dfd = libc.Xopen(tls, bp+32, 00, libc.VaList(bp+24, 0))
		if dfd < 0 {
			rc = -1
		} else {
			rc = libc.Xfsync(tls, dfd)
			libc.Xclose(tls, dfd)
		}
	}
	return func() int32 {
		if rc == 0 {
			return 0
		}
		return 10 | int32(10)<<8
	}()
}

var __func__8 = *(*[10]uint8)(unsafe.Pointer(ts + 117))

func vfsDlOpen(tls *libc.TLS, pVfs uintptr, zPath uintptr) uintptr {
	return uintptr(0)
}

func vfsDlError(tls *libc.TLS, pVfs uintptr, nByte int32, zErrMsg uintptr) {
	sqlite3.Xsqlite3_snprintf(tls, nByte, zErrMsg, ts+127, 0)
	*(*uint8)(unsafe.Pointer(zErrMsg + uintptr(nByte-1))) = uint8(0)
}

func vfsDlSym(tls *libc.TLS, pVfs uintptr, pH uintptr, z uintptr) uintptr {
	return uintptr(0)
}

func vfsDlClose(tls *libc.TLS, pVfs uintptr, pHandle uintptr) {
	return
}

func vfsRandomness(tls *libc.TLS, pVfs uintptr, nByte int32, zByte uintptr) int32 {
	return 0
}

func vfsSleep(tls *libc.TLS, pVfs uintptr, nMicro int32) int32 {
	libc.Xsleep(tls, uint32(nMicro/1000000))
	libc.Xusleep(tls, uint32(nMicro%1000000))
	return nMicro
}

func vfsCurrentTime(tls *libc.TLS, pVfs uintptr, pTime uintptr) int32 {
	var t time_t = libc.Xtime(tls, uintptr(0))
	*(*float64)(unsafe.Pointer(pTime)) = float64(t)/86400.0 + 2440587.5
	return 0
}

func Xsqlite3_fsFS(tls *libc.TLS, zName uintptr, pAppData uintptr) uintptr {
	var p uintptr = sqlite3.Xsqlite3_malloc(tls, int32(unsafe.Sizeof(sqlite3_vfs{})))
	if !(p != 0) {
		return uintptr(0)
	}

	*(*sqlite3_vfs)(unsafe.Pointer(p)) = sqlite3_vfs{
		iVersion:   1,
		szOsFile:   int32(unsafe.Sizeof(VFSFile{})),
		mxPathname: 4096,
		zName:      zName,
		pAppData:   pAppData,
		xOpen: *(*uintptr)(unsafe.Pointer(&struct {
			f func(*libc.TLS, uintptr, uintptr, uintptr, int32, uintptr) int32
		}{vfsOpen})),
		xDelete: *(*uintptr)(unsafe.Pointer(&struct {
			f func(*libc.TLS, uintptr, uintptr, int32) int32
		}{vfsDelete})),
		xAccess: *(*uintptr)(unsafe.Pointer(&struct {
			f func(*libc.TLS, uintptr, uintptr, int32, uintptr) int32
		}{vfsAccess})),
		xFullPathname: *(*uintptr)(unsafe.Pointer(&struct {
			f func(*libc.TLS, uintptr, uintptr, int32, uintptr) int32
		}{vfsFullPathname})),
		xDlOpen: *(*uintptr)(unsafe.Pointer(&struct {
			f func(*libc.TLS, uintptr, uintptr) uintptr
		}{vfsDlOpen})),
		xDlError: *(*uintptr)(unsafe.Pointer(&struct {
			f func(*libc.TLS, uintptr, int32, uintptr)
		}{vfsDlError})),
		xDlSym: *(*uintptr)(unsafe.Pointer(&struct {
			f func(*libc.TLS, uintptr, uintptr, uintptr) uintptr
		}{vfsDlSym})),
		xDlClose: *(*uintptr)(unsafe.Pointer(&struct {
			f func(*libc.TLS, uintptr, uintptr)
		}{vfsDlClose})),
		xRandomness: *(*uintptr)(unsafe.Pointer(&struct {
			f func(*libc.TLS, uintptr, int32, uintptr) int32
		}{vfsRandomness})),
		xSleep: *(*uintptr)(unsafe.Pointer(&struct {
			f func(*libc.TLS, uintptr, int32) int32
		}{vfsSleep})),
		xCurrentTime: *(*uintptr)(unsafe.Pointer(&struct {
			f func(*libc.TLS, uintptr, uintptr) int32
		}{vfsCurrentTime}))}
	return p
}

var ts1 = "TODO %s:%i:\n\x00vfsDirectWrite\x00vfsFlushBuffer\x00p->nBuffer==0 || p->iBufferOfst+p->nBuffer==i\x00c/vfs.c\x00vfsWrite\x00vfsSync\x00%s\x00vfsDelete\x00Loadable extensions are not supported\x00"
var ts = (*reflect.StringHeader)(unsafe.Pointer(&ts1)).Data