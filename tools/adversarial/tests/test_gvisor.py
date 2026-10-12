"""gVisor lifecycle and trust-boundary regressions."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from test_check import gate
import gvisor_backend
import gvisor_entry


class RuntimeIdentityTests(unittest.TestCase):
    def test_runtime_name_alone_does_not_authorize_plain_or_networked_container(self):
        profiles = [
            {"path": "/usr/bin/runc", "runtimeArgs": gvisor_backend.RUNTIME_ARGS},
            {"path": str(gvisor_backend.INSTALL / "runsc"),
             "runtimeArgs": ["--platform=systrap", "--network=host"]},
            {},
        ]
        for profile in profiles:
            with self.subTest(profile=profile), patch.object(
                    gvisor_backend, "query", return_value={gvisor_backend.RUNTIME: profile}):
                with self.assertRaisesRegex(gate.Rejected, "No safe condition for sandbox"):
                    gvisor_backend.identity(gate)

    def test_changed_sandbox_identity_rejects_a_frozen_runtime_before_startup(self):
        with patch.object(gvisor_backend, "identity", return_value={"image": "new"}), \
                patch.object(gvisor_backend.GvisorSandbox, "run") as execute:
            with self.assertRaisesRegex(gate.Rejected, "changed"):
                gate.make_sandbox(dict(gate.DEFAULT_LIMITS),
                                  runtime={"sandbox_identity": {"image": "old"}})
            execute.assert_not_called()

    def test_missing_marker_cannot_execute_any_tool(self):
        with patch.object(gvisor_entry.Path, "is_file", return_value=False), \
                patch.object(gvisor_entry.os, "execv") as execute:
            with self.assertRaisesRegex(RuntimeError, "marker missing"):
                gvisor_entry.main()
            execute.assert_not_called()


class GvisorLifecycleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        gate.ensure_built()

    def sandbox(self, **limits):
        return gate.make_sandbox(dict(gate.DEFAULT_LIMITS, **limits))

    def test_worker_and_child_both_inherit_socket_and_resource_restrictions(self):
        probe = """
import errno, resource, socket
assert resource.getrlimit(resource.RLIMIT_NOFILE) == (128, 128)
assert resource.getrlimit(resource.RLIMIT_NPROC) == (256, 256)
for family in (socket.AF_INET, socket.AF_INET6, socket.AF_UNIX, socket.AF_NETLINK):
    try:
        socket.socket(family, socket.SOCK_STREAM)
    except OSError as error:
        assert error.errno == errno.EPERM, error
    else:
        raise AssertionError('socket creation permitted')
"""
        driver = probe + f"""
import subprocess
subprocess.run(['/usr/bin/python3', '-I', '-c', {probe!r}], check=True)
print('isolated')
"""
        self.assertEqual(self.sandbox().run(["/usr/bin/python3", "-I", "-c", driver], [],
                                          compiler_worker=True), b"isolated\n")

    def test_readonly_devices_and_memory_backed_files_cannot_bypass_work_quota(self):
        probe = """
import errno, os, pathlib
pathlib.Path('/dev/null').write_bytes(b'usable')
for action in (lambda: pathlib.Path('/dev/bypass').write_bytes(b'x'),
               lambda: os.memfd_create('bypass')):
    try:
        action()
    except OSError as error:
        assert error.errno in (errno.EROFS, errno.EPERM, errno.EACCES), error
    else:
        raise AssertionError('unbounded memory-backed file permitted')
print('bounded')
"""
        self.assertEqual(self.sandbox(work_mib=4).run(
            ["/usr/bin/python3", "-I", "-c", probe], []), b"bounded\n")

    def test_timeout_removes_container_and_worker_descendants(self):
        sandbox = self.sandbox(wall_seconds=2)
        with tempfile.TemporaryDirectory() as temporary:
            name = "coqcp-" + Path(temporary).name.replace("_", "-")
            driver = """
import subprocess, time
subprocess.Popen(['/usr/bin/python3', '-I', '-c', 'import time; time.sleep(600)'])
time.sleep(600)
"""
            with patch.object(gvisor_backend.secrets, "token_hex", return_value=name[6:]):
                with self.assertRaisesRegex(gate.Rejected, "wall time"):
                    sandbox.run(["/usr/bin/python3", "-I", "-c", driver], [],
                                compiler_worker=True)
            inspect = subprocess.run(gvisor_backend.docker(gate) + ["inspect", name], env={},
                                     capture_output=True, timeout=10)
            self.assertNotEqual(inspect.returncode, 0)
            self.assertIn(b"no such", inspect.stderr.lower())


if __name__ == "__main__":
    unittest.main()
