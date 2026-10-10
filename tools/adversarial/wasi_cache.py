"""Evaluator-owned compilation cache with recorded input/taint observations.

Cache contents are trusted infrastructure, just like the evaluator toolchain.
Only successful compilation artifacts are stored. Kernel acceptance is a
separate cache domain keyed by every checked artifact and the frozen contract.
"""
import base64
import hashlib
import json
import os
from pathlib import Path
import tempfile


def hash_bytes(data):
    return "directory" if data is None else hashlib.sha256(data).hexdigest()


def key(value):
    return hash_bytes(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def observation(path, files):
    """Include positive/negative lookups and directory membership, not just reads."""
    if path.startswith("stat:"):
        name = path[5:]
        if name in files and files[name] is not None:
            return "file-size:" + str(len(files[name]))
        return observation(name, files)
    if path.endswith("/"):
        prefix = path.rstrip("/") + "/"
        children = {}
        for name, data in files.items():
            if name.startswith(prefix):
                relative = name[len(prefix):]
                if relative:
                    child = relative.split("/")[0]
                    children[child] = "directory" if "/" in relative or data is None else "file"
        return key(sorted(children.items()))
    if path in files:
        if files[path] is None:
            return "directory"
        return "file:" + hash_bytes(files[path])
    prefix = path.rstrip("/") + "/"
    if any(name.startswith(prefix) for name in files):
        return "directory"
    if path in ("/", "/work", "/tmp"):
        return "directory"
    return "absent"


class Cache:
    def __init__(self, directory, read_regular, encoded, decoded, artifact_limit):
        self.directory = Path(directory) if directory else None
        self.read_regular, self.encoded, self.decoded = read_regular, encoded, decoded
        self.artifact_limit = artifact_limit
        self.hits = self.misses = 0

    def get(self, domain, base, files=None):
        if self.directory is None:
            self.misses += 1
            return None
        directory = self.directory / domain / base
        for path in sorted(directory.glob("*.json")):
            try:
                data = self.decoded(self.read_regular(path, self.artifact_limit * 4 // 3 + 1024**2), "cache entry")
                if set(data) != {"format", "base", "observed", "payload", "sha256"}:
                    continue
                if data["format"] != 1 or data["base"] != base:
                    continue
                if not isinstance(data["observed"], dict):
                    continue
                if files is not None and any(observation(name, files) != state
                                             for name, state in data["observed"].items()):
                    continue
                payload = base64.b64decode(data["payload"], validate=True)
                if len(payload) > self.artifact_limit or hash_bytes(payload) != data["sha256"]:
                    continue
                self.hits += 1
                return payload
            except Exception:
                continue  # Corruption is a cache miss, never an acceptance.
        self.misses += 1
        return None

    def put(self, domain, base, payload, observed=(), files=None):
        if self.directory is None:
            return
        relationships = {name: observation(name, files) for name in sorted(set(observed))} if files is not None else {}
        entry = dict(format=1, base=base, observed=relationships,
                     payload=base64.b64encode(payload).decode(), sha256=hash_bytes(payload))
        directory = self.directory / domain / base
        directory.mkdir(parents=True, exist_ok=True, mode=0o700)
        content = self.encoded(entry)
        with tempfile.NamedTemporaryFile(dir=directory, delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(content)
        try:
            os.replace(temporary, directory / (key(relationships) + ".json"))
        finally:
            temporary.unlink(missing_ok=True)
