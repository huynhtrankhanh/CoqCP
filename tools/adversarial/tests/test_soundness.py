"""Published proof-of-False regressions against the installed Rocq toolchain."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from test_check import gate

WITNESSES = Path(__file__).parent / "soundness"


class PublishedSoundnessTests(unittest.TestCase):
    def test_rejected_by_kernel(self):
        # Match the relevant diagnostic so missing dependencies or a broken
        # installation cannot masquerade as a successful security regression.
        cases = {
            "HigherOrderFixpoint": "Recursive definition of russell is ill-formed",
            "AuditBlindUniformArgs": "Recursive definition of russell is ill-formed",
            "AuditBlindNestedCofix": "Recursive definition of cycle is ill-formed",
            "AuditBlindSubtypeLetin": "Signature components for field T do not match",
            "AliasChainDeltaResolver": "Unable to unify",
        }
        with tempfile.TemporaryDirectory(prefix="rocq-soundness-") as temporary:
            for name, diagnostic in cases.items():
                with self.subTest(witness=name):
                    source = Path(temporary) / (name + ".v")
                    shutil.copyfile(WITNESSES / source.name, source)
                    result = subprocess.run([str(gate.TOOLCHAIN / "bin/rocq"), "compile", str(source)],
                                            capture_output=True, text=True, timeout=60)
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertIn(diagnostic, result.stderr)
                    self.assertFalse(source.with_suffix(".vo").exists())

    def test_functor_guard_flag_is_rejected_by_rocqchk(self):
        with tempfile.TemporaryDirectory(prefix="rocq-soundness-") as temporary:
            source = Path(temporary) / "GuardFlagThroughFunctor.v"
            shutil.copyfile(WITNESSES / source.name, source)
            subprocess.run([str(gate.TOOLCHAIN / "bin/rocq"), "compile", str(source)],
                           check=True, capture_output=True, timeout=60)
            for vm in ("no", "yes"):
                with self.subTest(vm=vm):
                    result = subprocess.run([str(gate.TOOLCHAIN / "bin/rocqchk"),
                                             "-silent", "-bytecode-compiler", vm,
                                             "-Q", temporary, "", source.stem],
                                            capture_output=True, text=True, timeout=60)
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertIn("IllFormedRecBody", result.stderr)
