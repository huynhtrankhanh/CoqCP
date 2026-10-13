"""Reuse a trusted Docker image archive without changing its immutable ID."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

REPO = Path(__file__).resolve().parents[2]
IMAGE = "coqcp-gvisor:rocq-9.3.0"
DOCKER = ["docker", "--host=unix:///var/run/docker.sock"]


def digest(path):
    if path.is_symlink() or not path.is_file():
        raise ValueError("Runtime image cache must contain regular files")
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def image_id():
    return json.loads(subprocess.check_output(
        DOCKER + ["image", "inspect", IMAGE, "--format", "{{json .Id}}"], text=True))


def provision(archive=None):
    recipe = {str(path.relative_to(REPO)): digest(path) for path in
              [REPO / "tools/adversarial/Dockerfile.gvisor", Path(__file__),
               REPO / "tools/install-gvisor.sh"]}
    metadata = archive.with_suffix(".json") if archive else None
    if archive:
        try:
            if metadata.is_symlink() or metadata.stat().st_size > 1024 * 1024:
                raise ValueError("Runtime image metadata must be a regular file")
            record = json.loads(metadata.read_text())
            if (not isinstance(record, dict)
                    or set(record) != {"format", "recipe", "image", "archive_sha256"}
                    or type(record["format"]) is not int or record["format"] != 1
                    or not isinstance(record["image"], str)
                    or not re.fullmatch(r"sha256:[0-9a-f]{64}", record["image"])
                    or record["recipe"] != recipe
                    or record["archive_sha256"] != digest(archive)):
                raise ValueError("Runtime image cache changed")
            subprocess.run(DOCKER + ["load", "--input", str(archive)], check=True)
            if image_id() != record["image"]:
                raise ValueError("Restored runtime image identity changed")
            print("Restored runtime image " + record["image"], flush=True)
            return
        except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError):
            pass
    subprocess.run(DOCKER + ["build", "-f", str(REPO / "tools/adversarial/Dockerfile.gvisor"),
                            "-t", IMAGE, str(REPO / "tools/adversarial")], check=True)
    if archive:
        archive.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="image-", dir=archive.parent) as temporary:
            tar = Path(temporary) / "image.tar"
            subprocess.run(DOCKER + ["save", "--output", str(tar), IMAGE], check=True)
            record = {"format": 1, "recipe": recipe, "image": image_id(),
                      "archive_sha256": digest(tar)}
            tar.replace(archive)
            data = Path(temporary) / "metadata.json"
            data.write_text(json.dumps(record, sort_keys=True) + "\n")
            data.replace(metadata)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path)
    provision(parser.parse_args().archive)
