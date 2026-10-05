/* Apply limits and a seccomp filter before executing one untrusted tool.
 * Bubblewrap supplies filesystem and namespace isolation. No subprocesses,
 * network sockets, namespace changes, tracing, or privileged kernel APIs. */
#define _GNU_SOURCE
#include <errno.h>
#include <linux/sched.h>
#include <seccomp.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <unistd.h>

static void die(const char *message) { perror(message); exit(125); }
static void limit(int which, rlim_t value) {
  struct rlimit setting = {value, value};
  if (setrlimit(which, &setting)) die("setrlimit");
}
int main(int argc, char **argv) {
  if (argc < 5) { fputs("sandbox-exec CPU MEMORY_MIB FILE_MIB COMMAND...\n", stderr); return 125; }
  limit(RLIMIT_CPU, strtoul(argv[1], NULL, 10));
  limit(RLIMIT_AS, (rlim_t)strtoul(argv[2], NULL, 10) * 1024 * 1024);
  limit(RLIMIT_FSIZE, (rlim_t)strtoul(argv[3], NULL, 10) * 1024 * 1024);
  limit(RLIMIT_CORE, 0);
  limit(RLIMIT_NOFILE, 128);
  limit(RLIMIT_NPROC, 256);
  if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0)) die("no_new_privs");
  scmp_filter_ctx filter = seccomp_init(SCMP_ACT_ALLOW);
  if (!filter) die("seccomp_init");
  const char *blocked[] = {
    "fork", "vfork", "socket", "socketpair", "connect", "bind", "listen",
    "accept", "accept4", "mount", "umount2", "pivot_root", "chroot",
    "unshare", "setns", "ptrace", "process_vm_readv", "process_vm_writev",
    "pidfd_getfd", "pidfd_send_signal", "pidfd_open", "kill", "tkill", "tgkill",
    "rt_sigqueueinfo", "rt_tgsigqueueinfo", "process_madvise", "process_mrelease",
    "bpf", "perf_event_open", "userfaultfd", "io_uring_setup",
    "io_uring_enter", "io_uring_register", "keyctl", "add_key", "request_key",
    "reboot", "kexec_load", "kexec_file_load", "init_module", "finit_module",
    "delete_module", "open_by_handle_at", "name_to_handle_at", "mknod", "mknodat"
  };
  for (size_t i = 0; i < sizeof(blocked) / sizeof(blocked[0]); i++) {
    int syscall = seccomp_syscall_resolve_name(blocked[i]);
    if (syscall != __NR_SCMP_ERROR &&
        seccomp_rule_add(filter, SCMP_ACT_ERRNO(EPERM), syscall, 0)) die("seccomp_rule_add");
  }
  /* glibc falls back to clone when clone3 returns ENOSYS. Permit threads,
     but not processes, so OCaml's runtime remains usable. */
  int clone3_call = seccomp_syscall_resolve_name("clone3");
  if (clone3_call != __NR_SCMP_ERROR &&
      seccomp_rule_add(filter, SCMP_ACT_ERRNO(ENOSYS), clone3_call, 0)) die("clone3 rule");
  if (seccomp_rule_add(filter, SCMP_ACT_ERRNO(EPERM), SCMP_SYS(clone), 1,
      SCMP_A0(SCMP_CMP_MASKED_EQ, CLONE_THREAD, 0))) die("clone rule");
  /* A child must not change its supervisor's limits. glibc uses pid=0
     when implementing getrlimit/setrlimit for the current process. */
  if (seccomp_rule_add(filter, SCMP_ACT_ERRNO(EPERM), SCMP_SYS(prlimit64), 1,
      SCMP_A0(SCMP_CMP_NE, 0))) die("prlimit rule");
  if (seccomp_load(filter)) die("seccomp_load");
  seccomp_release(filter);
  execvp(argv[4], argv + 4);
  die("execvp");
}
