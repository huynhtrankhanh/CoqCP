/* Installed from the statically linked compiler before it reads any input.
 * sandbox-exec must permit its first exec; this second filter closes that
 * remaining permission and prohibits loading or generating executable code. */
#define _GNU_SOURCE
#include <errno.h>
#include <seccomp.h>
#include <sys/mman.h>
#include <sys/shm.h>
#include <caml/fail.h>
#include <caml/mlvalues.h>

CAMLprim value coqcp_compile_lockdown(value unit) {
  (void)unit;
  scmp_filter_ctx filter = seccomp_init(SCMP_ACT_ALLOW);
  if (!filter) caml_failwith("Cannot create compiler lockdown filter");
  /* Include any runtime threads started during static initialization. */
  int error = seccomp_attr_set(filter, SCMP_FLTATR_CTL_TSYNC, 1);
  error |= seccomp_rule_add(filter, SCMP_ACT_ERRNO(EPERM), SCMP_SYS(execve), 0);
  error |= seccomp_rule_add(filter, SCMP_ACT_ERRNO(EPERM), SCMP_SYS(execveat), 0);
  error |= seccomp_rule_add(filter, SCMP_ACT_ERRNO(EPERM), SCMP_SYS(mmap), 1,
                          SCMP_A2(SCMP_CMP_MASKED_EQ, PROT_EXEC, PROT_EXEC));
  error |= seccomp_rule_add(filter, SCMP_ACT_ERRNO(EPERM), SCMP_SYS(mprotect), 1,
                          SCMP_A2(SCMP_CMP_MASKED_EQ, PROT_EXEC, PROT_EXEC));
  int pkey = seccomp_syscall_resolve_name("pkey_mprotect");
  if (pkey != __NR_SCMP_ERROR)
    error |= seccomp_rule_add(filter, SCMP_ACT_ERRNO(EPERM), pkey, 1,
                             SCMP_A2(SCMP_CMP_MASKED_EQ, PROT_EXEC, PROT_EXEC));
  error |= seccomp_rule_add(filter, SCMP_ACT_ERRNO(EPERM), SCMP_SYS(shmat), 1,
                          SCMP_A2(SCMP_CMP_MASKED_EQ, SHM_EXEC, SHM_EXEC));
  if (!error) error = seccomp_load(filter);
  seccomp_release(filter);
  if (error) caml_failwith("Cannot install compiler lockdown filter");
  return Val_unit;
}
