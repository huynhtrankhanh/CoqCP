"""Evaluator-owned caches: complete input keys, verified blobs, atomic writes.

The directory is trusted state, like the toolchain and frozen bundles. Hashes
detect damage; they do not authenticate data supplied by an untrusted writer.
Never mount this directory inside a submission container.
"""
from contextlib import contextmanager
import fcntl
import hashlib
import os
from pathlib import Path
import stat
import tempfile


FORMAT = 1


class ResultCache:
    def __init__(self, gate, directory):
        self.gate = gate
        self.directory = Path(directory).absolute()
        self.counts = {kind: {"hits": 0, "misses": 0} for kind in ("compile", "kernel")}
        self._directory(self.directory)

    def _directory(self, path):
        if any(parent.is_symlink() for parent in path.parents):
            raise self.gate.Rejected("Cache paths must not contain symlinks")
        path.mkdir(mode=0o700, parents=True, exist_ok=True)
        info = path.lstat()
        if (not stat.S_ISDIR(info.st_mode) or info.st_uid != os.getuid()
                or stat.S_IMODE(info.st_mode) & 0o077):
            raise self.gate.Rejected("Cache directories must be private and evaluator-owned")
        return path

    def _read(self, path, limit):
        info = path.lstat()
        if (not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid()
                or stat.S_IMODE(info.st_mode) & 0o022):
            raise ValueError("Unsafe cache file")
        return self.gate.read_regular(path, limit)

    def key(self, kind, request):
        if kind not in self.counts:
            raise ValueError("Unknown cache operation")
        return hashlib.sha256(self.gate.encoded(
            {"format": FORMAT, "operation": kind, "request": request})).hexdigest()

    def _entry(self, kind, key):
        return self._directory(self.directory / kind / key[:2]) / (key + ".json")

    @contextmanager
    def lock(self, kind, request):
        key = self.key(kind, request)
        path = self._entry(kind, key).with_suffix(".lock")
        fd = os.open(path, os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
        with os.fdopen(fd, "a") as stream:
            info = os.fstat(stream.fileno())
            if (not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid()
                    or stat.S_IMODE(info.st_mode) & 0o077):
                raise self.gate.Rejected("Unsafe cache lock")
            fcntl.flock(stream, fcntl.LOCK_EX)
            yield key

    def _payload(self, kind, key, limit=1024 * 1024):
        envelope = self.gate.decoded(self._read(self._entry(kind, key), limit), "cache entry")
        if (not isinstance(envelope, dict)
                or set(envelope) != {"format", "key", "payload", "sha256"}
                or type(envelope["format"]) is not int or envelope["format"] != FORMAT
                or envelope["key"] != key
                or hashlib.sha256(self.gate.encoded(envelope["payload"])).hexdigest()
                    != envelope["sha256"]):
            raise ValueError("Damaged or mismatched cache entry")
        return envelope["payload"]

    def _write(self, path, data):
        self._directory(path.parent)
        fd, temporary = tempfile.mkstemp(prefix=".pending-", dir=path.parent)
        try:
            with os.fdopen(fd, "wb") as stream:
                stream.write(data)
                stream.flush()
                os.fsync(stream.fileno())
            os.replace(temporary, path)
        finally:
            Path(temporary).unlink(missing_ok=True)

    def _save(self, kind, key, payload):
        self._write(self._entry(kind, key), self.gate.encoded(
            {"format": FORMAT, "key": key, "payload": payload,
             "sha256": hashlib.sha256(self.gate.encoded(payload)).hexdigest()}))

    def compiled(self, key, expected, limit):
        try:
            payload = self._payload("compile", key)
            if (not isinstance(payload, dict) or set(payload) != {"artifacts"}
                    or not isinstance(payload["artifacts"], dict)
                    or set(payload["artifacts"]) != expected):
                raise ValueError("Unexpected cached artifact manifest")
            artifacts = {}
            for name, checksum in sorted(payload["artifacts"].items()):
                if (not isinstance(checksum, str) or len(checksum) != 64
                        or any(c not in "0123456789abcdef" for c in checksum)):
                    raise ValueError("Invalid cached artifact hash")
                data = self._read(self._directory(self.directory / "blobs" / checksum[:2])
                                  / checksum, limit - sum(map(len, artifacts.values())))
                if hashlib.sha256(data).hexdigest() != checksum:
                    raise ValueError("Damaged cached artifact")
                artifacts[name] = data
        except (OSError, ValueError, self.gate.Rejected):
            self.counts["compile"]["misses"] += 1
            return None
        self.counts["compile"]["hits"] += 1
        return artifacts

    def save_compiled(self, key, artifacts):
        hashes = {}
        for name, data in artifacts.items():
            checksum = hashlib.sha256(data).hexdigest()
            self._write(self._directory(self.directory / "blobs" / checksum[:2]) / checksum, data)
            hashes[name] = checksum
        self._save("compile", key, {"artifacts": hashes})

    def checked(self, key, allowed, status):
        try:
            report = self.gate.validate_kernel_report(self._payload("kernel", key), allowed, status)
        except (OSError, ValueError, self.gate.Rejected):
            self.counts["kernel"]["misses"] += 1
            return None
        self.counts["kernel"]["hits"] += 1
        return report

    def save_checked(self, key, report):
        self._save("kernel", key, report)

    def statistics(self):
        return {kind: dict(counts) for kind, counts in self.counts.items()}


def snapshot(gate, directory):
    """Bind all names, directories, permissions, and bytes visible in a mount."""
    result = {}
    for path in [directory, *sorted(directory.rglob("*"))]:
        info = path.lstat()
        name = str(path.relative_to(directory))
        mode = stat.S_IMODE(info.st_mode)
        if stat.S_ISDIR(info.st_mode):
            result[name] = {"directory": True, "mode": mode}
        elif stat.S_ISREG(info.st_mode):
            data = gate.read_regular(path, 64 * 1024**2)
            result[name] = {"sha256": hashlib.sha256(data).hexdigest(), "mode": mode}
        else:
            raise gate.Rejected("Cached inputs must be regular files or directories")
    return result
