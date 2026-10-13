"""Image archive reuse preserves identity and invalidates on recipe changes."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import runtime_image


class RuntimeImageTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.archive = Path(self.temporary.name) / "runtime.tar"
        self.commands = []
        self.image = "sha256:" + "a" * 64

    def command(self, argv, *, check):
        self.commands.append(argv)
        if "save" in argv:
            Path(argv[argv.index("--output") + 1]).write_bytes(b"trusted image archive")

    def provision(self):
        with patch.object(runtime_image.subprocess, "run", side_effect=self.command), \
                patch.object(runtime_image, "image_id", return_value=self.image):
            runtime_image.provision(self.archive)

    def test_second_run_restores_same_image_without_building(self):
        self.provision()
        record = json.loads(self.archive.with_suffix(".json").read_text())
        self.assertEqual(record["image"], self.image)
        self.commands.clear()
        self.provision()
        self.assertEqual(len(self.commands), 1)
        self.assertIn("load", self.commands[0])

    def test_archive_damage_and_metadata_damage_rebuild(self):
        self.provision()
        for damage in [lambda: self.archive.write_bytes(b"damaged"),
                       lambda: self.archive.with_suffix(".json").write_text("invalid")]:
            damage()
            self.commands.clear()
            self.provision()
            self.assertTrue(any("build" in command for command in self.commands))

    def test_recipe_edit_invalidates_archive(self):
        self.provision()
        self.commands.clear()
        original = runtime_image.digest
        with patch.object(runtime_image, "digest", side_effect=lambda path:
                          "0" * 64 if path.name == "Dockerfile.gvisor" else original(path)):
            self.provision()
        self.assertTrue(any("build" in command for command in self.commands))
        self.assertFalse(any("load" in command for command in self.commands))

    def test_loaded_image_must_match_recorded_immutable_id(self):
        self.provision()
        self.commands.clear()
        self.image = "sha256:" + "b" * 64
        self.provision()
        self.assertTrue(any("load" in command for command in self.commands))
        self.assertTrue(any("build" in command for command in self.commands))


if __name__ == "__main__":
    unittest.main()
