/* Runtime compatibility only: Lean 4.19 asks for its own executable through
   /proc/<own-pid>/exe. This environment exposes that information through
   /proc/self/exe. No other path, operation, or proof checker is changed. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
ssize_t readlink(const char *path, char *buf, size_t size) {
    static ssize_t (*real_readlink)(const char *, char *, size_t);
    if (!real_readlink) real_readlink = dlsym(RTLD_NEXT, "readlink");
    char own_exe[64];
    snprintf(own_exe, sizeof(own_exe), "/proc/%ld/exe", (long)getpid());
    return real_readlink(strcmp(path, own_exe) == 0 ? "/proc/self/exe" : path, buf, size);
}
