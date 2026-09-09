/* Compatibility for a process namespace in which /proc/<getpid()>/exe is
 * absent but /proc/self/exe exists. Only the current executable lookup is
 * redirected. No Lean proof, kernel, declaration, or axiom is modified. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

ssize_t readlink(const char *path, char *buffer, size_t size) {
    static ssize_t (*original)(const char *, char *, size_t);
    if (!original) original = dlsym(RTLD_NEXT, "readlink");
    char own[64];
    snprintf(own, sizeof(own), "/proc/%d/exe", (int)getpid());
    return original(strcmp(path, own) == 0 ? "/proc/self/exe" : path,
                    buffer, size);
}
