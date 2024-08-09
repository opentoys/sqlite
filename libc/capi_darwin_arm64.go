// Code generated by 'go generate' - DO NOT EDIT.

package libc // import "github.com/opentoys/sqlite/libc"

var CAPI = map[string]struct{}{
	"_CurrentRuneLocale":               {},
	"_DefaultRuneLocale":               {},
	"_IO_putc":                         {},
	"_NSGetEnviron":                    {},
	"___errno_location":                {},
	"__assert_fail":                    {},
	"__assert_rtn":                     {},
	"__builtin___memcpy_chk":           {},
	"__builtin___memmove_chk":          {},
	"__builtin___memset_chk":           {},
	"__builtin___snprintf_chk":         {},
	"__builtin___sprintf_chk":          {},
	"__builtin___strcat_chk":           {},
	"__builtin___strcpy_chk":           {},
	"__builtin___strncpy_chk":          {},
	"__builtin___vsnprintf_chk":        {},
	"__builtin_abort":                  {},
	"__builtin_abs":                    {},
	"__builtin_add_overflowInt64":      {},
	"__builtin_add_overflowUint32":     {},
	"__builtin_add_overflowUint64":     {},
	"__builtin_bswap16":                {},
	"__builtin_bswap32":                {},
	"__builtin_bswap64":                {},
	"__builtin_bzero":                  {},
	"__builtin_clz":                    {},
	"__builtin_clzl":                   {},
	"__builtin_clzll":                  {},
	"__builtin_constant_p_impl":        {},
	"__builtin_copysign":               {},
	"__builtin_copysignf":              {},
	"__builtin_copysignl":              {},
	"__builtin_exit":                   {},
	"__builtin_expect":                 {},
	"__builtin_fabs":                   {},
	"__builtin_fabsf":                  {},
	"__builtin_fabsl":                  {},
	"__builtin_free":                   {},
	"__builtin_getentropy":             {},
	"__builtin_huge_val":               {},
	"__builtin_huge_valf":              {},
	"__builtin_inf":                    {},
	"__builtin_inff":                   {},
	"__builtin_infl":                   {},
	"__builtin_isnan":                  {},
	"__builtin_isunordered":            {},
	"__builtin_llabs":                  {},
	"__builtin_malloc":                 {},
	"__builtin_memcmp":                 {},
	"__builtin_memcpy":                 {},
	"__builtin_memset":                 {},
	"__builtin_mmap":                   {},
	"__builtin_mul_overflowInt64":      {},
	"__builtin_mul_overflowUint128":    {},
	"__builtin_mul_overflowUint64":     {},
	"__builtin_nan":                    {},
	"__builtin_nanf":                   {},
	"__builtin_nanl":                   {},
	"__builtin_object_size":            {},
	"__builtin_popcount":               {},
	"__builtin_popcountl":              {},
	"__builtin_prefetch":               {},
	"__builtin_printf":                 {},
	"__builtin_snprintf":               {},
	"__builtin_sprintf":                {},
	"__builtin_strchr":                 {},
	"__builtin_strcmp":                 {},
	"__builtin_strcpy":                 {},
	"__builtin_strlen":                 {},
	"__builtin_sub_overflowInt64":      {},
	"__builtin_trap":                   {},
	"__builtin_unreachable":            {},
	"__ccgo_dmesg":                     {},
	"__ccgo_getMutexType":              {},
	"__ccgo_in6addr_anyp":              {},
	"__ccgo_pthreadAttrGetDetachState": {},
	"__ccgo_pthreadMutexattrGettype":   {},
	"__ccgo_sqlite3_log":               {},
	"__cmsg_nxthdr":                    {},
	"__ctype_get_mb_cur_max":           {},
	"__darwin_check_fd_set_overflow":   {},
	"__darwin_fd_clr":                  {},
	"__darwin_fd_isset":                {},
	"__darwin_fd_set":                  {},
	"__env_rm_add":                     {},
	"__errno_location":                 {},
	"__error":                          {},
	"__floatscan":                      {},
	"__fpclassify":                     {},
	"__fpclassifyf":                    {},
	"__fpclassifyl":                    {},
	"__h_errno_location":               {},
	"__inet_aton":                      {},
	"__inline_isnand":                  {},
	"__inline_isnanf":                  {},
	"__inline_isnanl":                  {},
	"__intscan":                        {},
	"__isctype":                        {},
	"__isnan":                          {},
	"__isnanf":                         {},
	"__isnanl":                         {},
	"__isoc99_sscanf":                  {},
	"__istype":                         {},
	"__lookup_ipliteral":               {},
	"__lookup_name":                    {},
	"__lookup_serv":                    {},
	"__maskrune":                       {},
	"__mb_cur_max":                     {},
	"__putenv":                         {},
	"__shgetc":                         {},
	"__shlim":                          {},
	"__sincos_stret":                   {},
	"__sincosf_stret":                  {},
	"__sincospi_stret":                 {},
	"__sincospif_stret":                {},
	"__srget":                          {},
	"__stderrp":                        {},
	"__stdinp":                         {},
	"__stdoutp":                        {},
	"__strchrnul":                      {},
	"__strncasecmp_l":                  {},
	"__svfscanf":                       {},
	"__swbuf":                          {},
	"__sync_add_and_fetch_uint32":      {},
	"__sync_sub_and_fetch_uint32":      {},
	"__tolower":                        {},
	"__toread":                         {},
	"__toread_needs_stdio_exit":        {},
	"__toupper":                        {},
	"__uflow":                          {},
	"__wcwidth":                        {},
	"_exit":                            {},
	"_longjmp":                         {},
	"_obstack_begin":                   {},
	"_obstack_newchunk":                {},
	"_setjmp":                          {},
	"abort":                            {},
	"abs":                              {},
	"accept":                           {},
	"access":                           {},
	"acos":                             {},
	"acosh":                            {},
	"alarm":                            {},
	"arc4random_buf":                   {},
	"asin":                             {},
	"asinh":                            {},
	"atan":                             {},
	"atan2":                            {},
	"atanh":                            {},
	"atexit":                           {},
	"atof":                             {},
	"atoi":                             {},
	"atol":                             {},
	"bind":                             {},
	"bsearch":                          {},
	"bzero":                            {},
	"calloc":                           {},
	"ceil":                             {},
	"ceilf":                            {},
	"cfgetospeed":                      {},
	"cfsetispeed":                      {},
	"cfsetospeed":                      {},
	"chdir":                            {},
	"chflags":                          {},
	"chmod":                            {},
	"chown":                            {},
	"clock":                            {},
	"clock_gettime":                    {},
	"close":                            {},
	"closedir":                         {},
	"confstr":                          {},
	"connect":                          {},
	"copyfile":                         {},
	"copysign":                         {},
	"copysignf":                        {},
	"copysignl":                        {},
	"cos":                              {},
	"cosf":                             {},
	"cosh":                             {},
	"ctime":                            {},
	"ctime_r":                          {},
	"digittoint":                       {},
	"dlclose":                          {},
	"dlerror":                          {},
	"dlopen":                           {},
	"dlsym":                            {},
	"dup2":                             {},
	"endpwent":                         {},
	"environ":                          {},
	"exit":                             {},
	"exp":                              {},
	"fabs":                             {},
	"fabsf":                            {},
	"fabsl":                            {},
	"fchmod":                           {},
	"fchown":                           {},
	"fclose":                           {},
	"fcntl":                            {},
	"fcntl64":                          {},
	"fdopen":                           {},
	"ferror":                           {},
	"fflush":                           {},
	"fgetc":                            {},
	"fgets":                            {},
	"fileno":                           {},
	"flock":                            {},
	"floor":                            {},
	"fmod":                             {},
	"fmodl":                            {},
	"fopen":                            {},
	"fopen64":                          {},
	"fork":                             {},
	"fprintf":                          {},
	"fputc":                            {},
	"fputs":                            {},
	"fread":                            {},
	"free":                             {},
	"freeaddrinfo":                     {},
	"frexp":                            {},
	"fsctl":                            {},
	"fseek":                            {},
	"fstat":                            {},
	"fstat64":                          {},
	"fstatfs":                          {},
	"fsync":                            {},
	"ftell":                            {},
	"ftruncate":                        {},
	"fts_close":                        {},
	"fts_open":                         {},
	"fts_read":                         {},
	"futimes":                          {},
	"fwrite":                           {},
	"gai_strerror":                     {},
	"getaddrinfo":                      {},
	"getattrlist":                      {},
	"getc":                             {},
	"getcwd":                           {},
	"getegid":                          {},
	"getentropy":                       {},
	"getenv":                           {},
	"geteuid":                          {},
	"getgid":                           {},
	"getgrgid":                         {},
	"getgrgid_r":                       {},
	"getgrnam":                         {},
	"getgrnam_r":                       {},
	"gethostbyaddr":                    {},
	"gethostbyaddr_r":                  {},
	"gethostbyname":                    {},
	"gethostbyname2":                   {},
	"gethostbyname2_r":                 {},
	"gethostname":                      {},
	"gethostuuid":                      {},
	"getnameinfo":                      {},
	"getpeername":                      {},
	"getpid":                           {},
	"getprogname":                      {},
	"getpwnam":                         {},
	"getpwnam_r":                       {},
	"getpwuid":                         {},
	"getpwuid_r":                       {},
	"getresgid":                        {},
	"getresuid":                        {},
	"getrusage":                        {},
	"getservbyname":                    {},
	"getsockname":                      {},
	"getsockopt":                       {},
	"gettimeofday":                     {},
	"getuid":                           {},
	"gmtime_r":                         {},
	"h_errno":                          {},
	"htonl":                            {},
	"htons":                            {},
	"hypot":                            {},
	"inet_ntoa":                        {},
	"inet_ntop":                        {},
	"inet_pton":                        {},
	"initstate":                        {},
	"initstate_r":                      {},
	"ioctl":                            {},
	"isalnum":                          {},
	"isalpha":                          {},
	"isascii":                          {},
	"isatty":                           {},
	"isblank":                          {},
	"iscntrl":                          {},
	"isdigit":                          {},
	"isgraph":                          {},
	"ishexnumber":                      {},
	"isideogram":                       {},
	"islower":                          {},
	"isnan":                            {},
	"isnanf":                           {},
	"isnanl":                           {},
	"isnumber":                         {},
	"isphonogram":                      {},
	"isprint":                          {},
	"ispunct":                          {},
	"isrune":                           {},
	"issetugid":                        {},
	"isspace":                          {},
	"isspecial":                        {},
	"isupper":                          {},
	"iswalnum":                         {},
	"iswspace":                         {},
	"isxdigit":                         {},
	"kill":                             {},
	"ldexp":                            {},
	"link":                             {},
	"listen":                           {},
	"llabs":                            {},
	"localeconv":                       {},
	"localtime":                        {},
	"localtime_r":                      {},
	"log":                              {},
	"log10":                            {},
	"log2":                             {},
	"longjmp":                          {},
	"lrand48":                          {},
	"lseek":                            {},
	"lseek64":                          {},
	"lstat":                            {},
	"lstat64":                          {},
	"mach_absolute_time":               {},
	"mach_timebase_info":               {},
	"malloc":                           {},
	"mblen":                            {},
	"mbstowcs":                         {},
	"mbtowc":                           {},
	"memchr":                           {},
	"memcmp":                           {},
	"memcpy":                           {},
	"memmove":                          {},
	"memset":                           {},
	"mkdir":                            {},
	"mkfifo":                           {},
	"mknod":                            {},
	"mkostemp":                         {},
	"mkstemp":                          {},
	"mkstemp64":                        {},
	"mkstemps":                         {},
	"mkstemps64":                       {},
	"mktime":                           {},
	"mmap":                             {},
	"modf":                             {},
	"munmap":                           {},
	"nanf":                             {},
	"nl_langinfo":                      {},
	"ntohs":                            {},
	"obstack_free":                     {},
	"obstack_vprintf":                  {},
	"open":                             {},
	"opendir":                          {},
	"openpty":                          {},
	"pathconf":                         {},
	"pause":                            {},
	"pclose":                           {},
	"perror":                           {},
	"pipe":                             {},
	"poll":                             {},
	"popen":                            {},
	"posix_fadvise":                    {},
	"pow":                              {},
	"pread":                            {},
	"printf":                           {},
	"pselect":                          {},
	"pthread_attr_destroy":             {},
	"pthread_attr_getdetachstate":      {},
	"pthread_attr_init":                {},
	"pthread_attr_setdetachstate":      {},
	"pthread_attr_setscope":            {},
	"pthread_attr_setstacksize":        {},
	"pthread_cond_broadcast":           {},
	"pthread_cond_destroy":             {},
	"pthread_cond_init":                {},
	"pthread_cond_signal":              {},
	"pthread_cond_timedwait":           {},
	"pthread_cond_wait":                {},
	"pthread_create":                   {},
	"pthread_detach":                   {},
	"pthread_equal":                    {},
	"pthread_exit":                     {},
	"pthread_getspecific":              {},
	"pthread_join":                     {},
	"pthread_key_create":               {},
	"pthread_key_delete":               {},
	"pthread_mutex_destroy":            {},
	"pthread_mutex_init":               {},
	"pthread_mutex_lock":               {},
	"pthread_mutex_trylock":            {},
	"pthread_mutex_unlock":             {},
	"pthread_mutexattr_destroy":        {},
	"pthread_mutexattr_init":           {},
	"pthread_mutexattr_settype":        {},
	"pthread_self":                     {},
	"pthread_setspecific":              {},
	"putc":                             {},
	"putchar":                          {},
	"putenv":                           {},
	"puts":                             {},
	"pwrite":                           {},
	"qsort":                            {},
	"raise":                            {},
	"rand":                             {},
	"rand_r":                           {},
	"random":                           {},
	"random_r":                         {},
	"read":                             {},
	"readdir":                          {},
	"readlink":                         {},
	"readv":                            {},
	"realloc":                          {},
	"reallocarray":                     {},
	"realpath":                         {},
	"recv":                             {},
	"recvfrom":                         {},
	"recvmsg":                          {},
	"remove":                           {},
	"rename":                           {},
	"rewind":                           {},
	"rindex":                           {},
	"rint":                             {},
	"rmdir":                            {},
	"round":                            {},
	"scalbn":                           {},
	"scalbnl":                          {},
	"sched_yield":                      {},
	"select":                           {},
	"send":                             {},
	"sendmsg":                          {},
	"sendto":                           {},
	"setattrlist":                      {},
	"setbuf":                           {},
	"setenv":                           {},
	"setjmp":                           {},
	"setlocale":                        {},
	"setsid":                           {},
	"setsockopt":                       {},
	"setstate":                         {},
	"setvbuf":                          {},
	"shmat":                            {},
	"shmctl":                           {},
	"shmdt":                            {},
	"shutdown":                         {},
	"sigaction":                        {},
	"signal":                           {},
	"sin":                              {},
	"sinf":                             {},
	"sinh":                             {},
	"sleep":                            {},
	"snprintf":                         {},
	"socket":                           {},
	"sprintf":                          {},
	"sqrt":                             {},
	"srand48":                          {},
	"srandomdev":                       {},
	"sscanf":                           {},
	"stat":                             {},
	"stat64":                           {},
	"statfs":                           {},
	"stderr":                           {},
	"stdin":                            {},
	"stdout":                           {},
	"strcasecmp":                       {},
	"strcat":                           {},
	"strchr":                           {},
	"strcmp":                           {},
	"strcpy":                           {},
	"strcspn":                          {},
	"strdup":                           {},
	"strerror":                         {},
	"strerror_r":                       {},
	"strlcat":                          {},
	"strlcpy":                          {},
	"strlen":                           {},
	"strncasecmp":                      {},
	"strncat":                          {},
	"strncmp":                          {},
	"strncpy":                          {},
	"strnlen":                          {},
	"strpbrk":                          {},
	"strrchr":                          {},
	"strspn":                           {},
	"strstr":                           {},
	"strtod":                           {},
	"strtof":                           {},
	"strtoimax":                        {},
	"strtok":                           {},
	"strtol":                           {},
	"strtold":                          {},
	"strtoll":                          {},
	"strtoul":                          {},
	"strtoull":                         {},
	"strtoumax":                        {},
	"symlink":                          {},
	"sysconf":                          {},
	"system":                           {},
	"tan":                              {},
	"tanh":                             {},
	"tcgetattr":                        {},
	"tcsendbreak":                      {},
	"tcsetattr":                        {},
	"time":                             {},
	"tmpfile":                          {},
	"toascii":                          {},
	"tolower":                          {},
	"toupper":                          {},
	"trunc":                            {},
	"truncate":                         {},
	"tzset":                            {},
	"umask":                            {},
	"uname":                            {},
	"ungetc":                           {},
	"unlink":                           {},
	"unsetenv":                         {},
	"usleep":                           {},
	"utime":                            {},
	"utimes":                           {},
	"uuid_copy":                        {},
	"uuid_generate_random":             {},
	"uuid_parse":                       {},
	"uuid_unparse":                     {},
	"vasprintf":                        {},
	"vfprintf":                         {},
	"vprintf":                          {},
	"vsnprintf":                        {},
	"vsprintf":                         {},
	"waitpid":                          {},
	"wcschr":                           {},
	"wctomb":                           {},
	"wcwidth":                          {},
	"write":                            {},
	"writev":                           {},
	"zero_struct_address":              {},
}
