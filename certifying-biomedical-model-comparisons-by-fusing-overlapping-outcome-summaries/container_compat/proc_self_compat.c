#define _GNU_SOURCE
#include <dlfcn.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
/* The container's process identifier does not match its mounted proc tree.
   Resolve only this process's executable through the standard self alias.
   No proof checking or Lean library function is modified. */
ssize_t readlink(const char *path, char *buffer, size_t size) {
    static ssize_t (*real_readlink)(const char *, char *, size_t) = NULL;
    if (!real_readlink) real_readlink = dlsym(RTLD_NEXT, "readlink");
    char own[64];
    snprintf(own, sizeof(own), "/proc/%d/exe", (int)getpid());
    return real_readlink(strcmp(path, own) == 0 ? "/proc/self/exe" : path, buffer, size);
}
