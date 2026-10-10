"""An in-memory WASI preview1 filesystem. No guest path reaches the host OS.

Descriptors hold nodes, so renaming or unlinking a path cannot change an open
file's authority. Read-only authority follows the node, not its current name.
"""
import errno
import posixpath
import struct


class Node:
    def __init__(self, data=None, writable=False, region=None, input_path=None):
        self.data = None if data is None else bytearray(data) if writable else bytes(data)
        self.writable = writable
        self.region = region
        self.input_path = input_path


class Filesystem:
    def __init__(self, files, work_bytes, file_bytes, tmp_bytes=16 * 1024**2):
        self.nodes = {"/": Node()}
        self.quotas = {"/work": work_bytes, "/tmp": tmp_bytes}
        self.file_bytes = file_bytes
        self.descriptors = {0: [None, 0, False], 1: [None, 0, True], 2: [None, 0, True]}
        self.observed = set()
        for path, data in files.items():
            self.add(path, Node(data, input_path=path))
        for path in self.quotas:
            self.add(path, Node(writable=True, region=path))
        # A single virtual root grants access only to these memory nodes.
        self.descriptors[3] = [self.nodes["/"], 0, False]

    def add(self, path, node):
        self.nodes[path] = node
        parent = posixpath.dirname(path)
        while parent and parent not in self.nodes:
            self.nodes[parent] = Node()
            parent = posixpath.dirname(parent)

    def path(self, fd, name):
        node = self.descriptors.get(fd, [None])[0]
        if node is None or node.data is not None:
            raise OSError(errno.EBADF, "Not a directory descriptor")
        base = next((p for p, n in self.nodes.items() if n is node), None)
        if base is None:
            raise OSError(errno.ENOENT, "Directory was removed")
        if "\0" in name:
            raise OSError(errno.EINVAL, "NUL in path")
        # WASI paths are relative to the supplied directory capability.
        parts = name.split("/")
        depth = 0
        for part in parts:
            if part == "..":
                depth -= 1
                if depth < 0:
                    raise OSError(errno.EACCES, "Path escapes its capability")
            elif part not in ("", "."):
                depth += 1
        if name.startswith("/"):
            raise OSError(errno.EACCES, "Absolute WASI path")
        path = posixpath.normpath(posixpath.join(base, name))
        self.observed.add("stat:" + path)
        return path

    def get(self, path):
        if path not in self.nodes:
            raise OSError(errno.ENOENT, "No such virtual file")
        return self.nodes[path]

    def writable_parent(self, path):
        parent = self.get(posixpath.dirname(path))
        if parent.data is not None:
            raise OSError(errno.ENOTDIR, "Parent is a file")
        if not parent.writable:
            raise OSError(errno.EROFS, "Read-only virtual directory")
        return parent

    def resize(self, node, size):
        if not node.writable:
            raise OSError(errno.EROFS, "Read-only virtual file")
        if node.data is None:
            raise OSError(errno.EISDIR, "Directory")
        if size < 0 or size > self.file_bytes:
            raise OSError(errno.EFBIG, "File size quota exceeded")
        # Include unlinked files still held by open descriptors.
        live = set(self.nodes.values()) | {d[0] for d in self.descriptors.values()}
        usage = sum(len(n.data) for n in live if n and n.region == node.region and n.data is not None)
        if usage + size - len(node.data) > self.quotas[node.region]:
            raise OSError(errno.ENOSPC, "Workspace quota exceeded")
        if size < len(node.data):
            del node.data[size:]
        else:
            node.data.extend(bytes(size - len(node.data)))

    def open(self, path, oflags, rights, fdflags):
        writable = bool(rights & (1 << 6))  # FD_WRITE
        if path not in self.nodes:
            if not oflags & 1:  # CREAT
                raise OSError(errno.ENOENT, "No such virtual file")
            parent = self.writable_parent(path)
            # Node metadata counts against the workspace quota as well.
            if sum(n.region == parent.region for n in self.nodes.values()) >= 8192:
                raise OSError(errno.ENOSPC, "File count quota exceeded")
            self.nodes[path] = Node(b"", True, parent.region)
        elif oflags & 1 and oflags & 4:  # EXCL
            raise OSError(errno.EEXIST, "File exists")
        node = self.get(path)
        if oflags & 2 and node.data is not None:
            raise OSError(errno.ENOTDIR, "Not a directory")
        if writable and not node.writable:
            raise OSError(errno.EROFS, "Read-only input")
        if oflags & 8:
            self.resize(node, 0)
        fd = next((i for i in range(4, 128) if i not in self.descriptors), None)
        if fd is None:
            raise OSError(errno.EMFILE, "Descriptor quota exceeded")
        self.descriptors[fd] = [node, len(node.data or b"") if fdflags & 1 else 0, writable]
        return fd

    def stat(self, node):
        if node.input_path is not None:
            self.observed.add("stat:" + node.input_path)
        # WASI filestat: dev, ino, filetype, nlink, size, atim, mtim, ctim.
        return struct.pack("<QQB7xQQQQQ", 0, 0, 3 if node.data is None else 4,
                           1, len(node.data or b""), 0, 0, 0)

    def listing(self, path):
        self.observed.add(path + "/")
        prefix = path.rstrip("/") + "/"
        return sorted((p[len(prefix):], n) for p, n in self.nodes.items()
                      if p.startswith(prefix) and p != path and "/" not in p[len(prefix):])

    def mkdir(self, path):
        if path in self.nodes:
            raise OSError(errno.EEXIST, "File exists")
        parent = self.writable_parent(path)
        if sum(n.region == parent.region for n in self.nodes.values()) >= 8192:
            raise OSError(errno.ENOSPC, "File count quota exceeded")
        self.nodes[path] = Node(writable=True, region=parent.region)

    def unlink(self, path, directory=False):
        self.writable_parent(path)
        node = self.get(path)
        if not node.writable:
            raise OSError(errno.EROFS, "Read-only input")
        if directory != (node.data is None):
            raise OSError(errno.ENOTDIR if directory else errno.EISDIR, "Wrong file type")
        if directory and self.listing(path):
            raise OSError(errno.ENOTEMPTY, "Directory not empty")
        del self.nodes[path]

    def rename(self, old, new):
        self.writable_parent(old)
        parent = self.writable_parent(new)
        node = self.get(old)
        if not node.writable or node.region != parent.region:
            raise OSError(errno.EACCES, "Rename changes authority")
        if new in self.nodes:
            target = self.get(new)
            if not target.writable:
                raise OSError(errno.EROFS, "Read-only destination")
            if (target.data is None) != (node.data is None):
                raise OSError(errno.EINVAL, "Wrong destination type")
            if target.data is None and self.listing(new):
                raise OSError(errno.ENOTEMPTY, "Destination not empty")
        if new.startswith(old + "/"):
            raise OSError(errno.EINVAL, "Directory moved into itself")
        moved = [(p, n) for p, n in self.nodes.items() if p == old or p.startswith(old + "/")]
        for path, _ in moved:
            del self.nodes[path]
        for path, n in moved:
            self.nodes[new + path[len(old):]] = n
