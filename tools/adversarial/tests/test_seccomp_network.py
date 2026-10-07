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

    def test_unknown_mode_rejected(self):
        with self.assertRaises(gate.Rejected):
            gate.Sandbox(dict(gate.DEFAULT_LIMITS), network_isolation='disabled')


class SeccompAcceptanceTests(test_check.AcceptanceTests):
    @classmethod
    def setUpClass(cls):
        original = test_check.gate.Sandbox
        with patch.object(test_check.gate, 'Sandbox',
                          side_effect=lambda limits: original(limits, network_isolation='seccomp')):
            super().setUpClass()


if __name__ == '__main__':
    unittest.main()
