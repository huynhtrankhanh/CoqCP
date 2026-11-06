"""Resource and containment tests for the untrusted source snapshot."""
import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

PATH = Path(__file__).resolve().parents[1] / 'check.py'
sys.path.insert(0, str(PATH.parent))
SPEC = importlib.util.spec_from_file_location('adversarial_source_snapshot_check', PATH)
gate = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = gate
SPEC.loader.exec_module(gate)


class SourceSnapshotTests(unittest.TestCase):
    def test_more_than_128_sources_are_accepted_and_sorted(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            submission, target = root / 'submission', root / 'snapshot'
            submission.mkdir()
            target.mkdir()
            (submission / 'Candidate.v').write_text('')
            for i in range(200):
                (submission / f'File{i}.v').write_text('')
            names = gate.snapshot_submission(submission, target, 2 * 1024**2)
            self.assertEqual(len(names), 201)
            self.assertEqual(names, sorted(names))
            self.assertEqual({path.name for path in target.iterdir()}, set(names))

    def test_empty_files_are_charged_to_the_work_budget(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            submission, target = root / 'submission', root / 'snapshot'
            submission.mkdir()
            target.mkdir()
            (submission / 'Candidate.v').write_text('')
            for i in range(20):
                (submission / f'File{i}.v').write_text('')
            with self.assertRaisesRegex(gate.Rejected, 'snapshot work budget'):
                gate.snapshot_submission(submission, target, 4 * gate.SNAPSHOT_BLOCK_BYTES)
            # The rejection happens during the scan, before copying the rest.
            self.assertLessEqual(len(list(target.iterdir())), 3)

    def test_byte_limit_still_applies(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            submission, target = root / 'submission', root / 'snapshot'
            submission.mkdir()
            target.mkdir()
            (submission / 'Candidate.v').write_text('x')
            (submission / 'Large.v').write_bytes(b'x' * gate.SOURCE_BYTES_LIMIT)
            with self.assertRaisesRegex(gate.Rejected, 'source size limit'):
                gate.snapshot_submission(submission, target, 32 * 1024**2)

    def test_symlink_and_non_source_entries_are_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            submission, target = root / 'submission', root / 'snapshot'
            submission.mkdir()
            target.mkdir()
            (submission / 'Candidate.v').symlink_to(root / 'outside.v')
            with self.assertRaises(OSError):
                gate.snapshot_submission(submission, target, 1024**2)
            (submission / 'Candidate.v').unlink()
            (submission / 'Candidate.v').write_text('')
            (submission / 'invalid.txt').write_text('')
            with self.assertRaises(gate.Rejected):
                gate.snapshot_submission(submission, target, 1024**2)

    def test_symlink_submission_directory_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            actual, target = root / 'actual', root / 'snapshot'
            actual.mkdir()
            target.mkdir()
            (actual / 'Candidate.v').write_text('candidate')
            linked = root / 'linked'
            linked.symlink_to(actual, target_is_directory=True)
            with self.assertRaises(OSError):
                gate.snapshot_submission(linked, target, 1024**2)
            self.assertEqual(list(target.iterdir()), [])

    def test_directory_swap_cannot_redirect_source_reads(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            submission, replacement = root / 'submission', root / 'replacement'
            target, moved = root / 'snapshot', root / 'moved'
            submission.mkdir()
            replacement.mkdir()
            target.mkdir()
            (submission / 'Candidate.v').write_text('original')
            (replacement / 'Candidate.v').write_text('replacement')
            original_scandir = gate.os.scandir

            def swap_then_scan(directory_fd):
                self.assertIsInstance(directory_fd, int)
                submission.rename(moved)
                submission.symlink_to(replacement, target_is_directory=True)
                return original_scandir(directory_fd)

            with mock.patch.object(gate.os, 'scandir', side_effect=swap_then_scan):
                names = gate.snapshot_submission(submission, target, 1024**2)
            self.assertEqual(names, ['Candidate.v'])
            self.assertEqual((target / 'Candidate.v').read_text(), 'original')


if __name__ == '__main__':
    unittest.main()
