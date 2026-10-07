"""Network isolation when an enclosing sandbox denies network namespaces."""
import errno
import sys
import tempfile
import unittest
from unittest.mock import patch
import test_check
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check as gate


class SeccompNetworkTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        gate.ensure_built()

    def sandbox(self):
        return gate.Sandbox(dict(gate.DEFAULT_LIMITS), network_isolation="seccomp")

    def test_worker_and_child_cannot_create_sockets(self):
        probe = """
import errno, socket
for family in [socket.AF_INET, socket.AF_INET6, socket.AF_UNIX, socket.AF_NETLINK]:
    try:
        socket.socket(family, socket.SOCK_STREAM)
    except OSError as error:
        assert error.errno == errno.EPERM, error
    else:
        raise AssertionError('Socket creation unexpectedly allowed')
"""
        source = probe + f"""
import subprocess
subprocess.run(['/usr/bin/python3', '-I', '-c', {probe!r}], check=True)
print('worker and child isolated')
"""
        self.assertEqual(self.sandbox().run(
            ["/usr/bin/python3", "-I", "-c", source], [], compiler_worker=True),
            b"worker and child isolated\n")

    def test_untrusted_tool_preserves_filesystem_and_process_isolation(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            (directory / 'secret').write_text('hidden')
            visible = directory / 'visible'
            visible.mkdir()
            (visible / 'immutable').write_text('trusted')
            source = f"""
import errno, os, pathlib, socket
assert not pathlib.Path({str(directory / 'secret')!r}).exists()
assert not pathlib.Path('/etc/passwd').exists()
for action in [socket.socket, os.fork,
               lambda: pathlib.Path('/trusted/immutable').write_text('changed')]:
    try:
        action()
    except OSError as error:
        assert error.errno in (errno.EPERM, errno.EROFS, errno.EACCES), error
    else:
        raise AssertionError('Isolation failed')
print('isolated')
"""
            self.assertEqual(self.sandbox().run(
                ['/usr/bin/python3', '-I', '-c', source], [(visible, '/trusted')]), b'isolated\n')
            self.assertEqual((visible / 'immutable').read_text(), 'trusted')

    def test_memory_backed_files_cannot_bypass_writable_space_limit(self):
        limits = dict(gate.DEFAULT_LIMITS, work_mib=4)
        source = """
import ctypes, errno, os, pathlib
pathlib.Path('/dev/null').write_bytes(b'usable')
for action in [lambda: pathlib.Path('/dev/quota-bypass').write_bytes(b'x'),
               lambda: os.memfd_create('quota-bypass')]:
    try:
        action()
    except OSError as error:
        assert error.errno in (errno.EPERM, errno.EROFS, errno.EACCES), error
    else:
        raise AssertionError('Unbounded memory-backed file creation was permitted')
libc = ctypes.CDLL(None, use_errno=True)
libseccomp = ctypes.CDLL('libseccomp.so.2')
libseccomp.seccomp_syscall_resolve_name.argtypes = [ctypes.c_char_p]
libseccomp.seccomp_syscall_resolve_name.restype = ctypes.c_int
memfd_secret = libseccomp.seccomp_syscall_resolve_name(b'memfd_secret')
if memfd_secret >= 0:
    ctypes.set_errno(0)
    assert libc.syscall(memfd_secret, 0) == -1 and ctypes.get_errno() == errno.EPERM
for action in [lambda: libc.shmget(0, 4096, 0o600),
               lambda: libc.msgget(0, 0o600),
               lambda: libc.semget(0, 1, 0o600)]:
    ctypes.set_errno(0)
    assert action() == -1 and ctypes.get_errno() == errno.EPERM
print('memory-backed files blocked')
"""
        sandbox = gate.Sandbox(limits, network_isolation="seccomp")
        self.assertEqual(sandbox.run(
            ["/usr/bin/python3", "-I", "-c", source], []),
            b"memory-backed files blocked\n")

    def test_worker_has_process_and_descriptor_limits(self):
        source = """
import resource
assert resource.getrlimit(resource.RLIMIT_NOFILE) == (128, 128)
assert resource.getrlimit(resource.RLIMIT_NPROC) == (256, 256)
print('worker bounded')
"""
        self.assertEqual(self.sandbox().run(
            ["/usr/bin/python3", "-I", "-c", source], [], compiler_worker=True),
            b"worker bounded\n")

    def test_unknown_mode_rejected(self):
        with self.assertRaises(gate.Rejected):
            gate.Sandbox(dict(gate.DEFAULT_LIMITS), network_isolation='disabled')

    def test_auto_uses_only_a_successfully_probed_fallback(self):
        with patch.object(gate.Sandbox, '_probe',
                          side_effect=[(False, 'network namespaces unavailable'), (True, '')]):
            sandbox = gate.Sandbox(dict(gate.DEFAULT_LIMITS))
        self.assertEqual(sandbox.network_isolation, 'seccomp')

    def test_no_safe_sandbox_fails_closed(self):
        with patch.object(gate.Sandbox, '_probe',
                          side_effect=[(False, 'namespace denied'), (False, 'filter denied')]):
            with self.assertRaisesRegex(gate.Rejected, 'No safe condition for sandbox'):
                gate.Sandbox(dict(gate.DEFAULT_LIMITS))


class SeccompAcceptanceTests(test_check.AcceptanceTests):
    @classmethod
    def setUpClass(cls):
        original = test_check.gate.Sandbox
        with patch.object(test_check.gate, 'Sandbox',
                          side_effect=lambda limits: original(limits, network_isolation='seccomp')):
            super().setUpClass()


if __name__ == '__main__':
    unittest.main()
