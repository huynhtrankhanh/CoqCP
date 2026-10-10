#!/usr/bin/env python3
"""Trusted Wasmtime host. Guest I/O uses memory nodes, never host descriptors.

The coordinator supplies trusted modules and input snapshots. Each invocation
gets a fresh Store and filesystem. The Engine and compiled Modules can be reused
within a batch; no guest globals, heap, descriptors or writable files survive.
"""
import base64
import errno
import hashlib
import json
import os
from pathlib import Path
import resource
import struct
import sys
import time

import wasmtime
from wasi_fs import Filesystem


class GuestExit(Exception):
    def __init__(self, code):
        self.code = code


WASI_ERRNO = {errno.EACCES: 2, errno.EBADF: 8, errno.EEXIST: 20,
              errno.EFBIG: 22, errno.EINVAL: 28, errno.EIO: 29,
              errno.EISDIR: 31, errno.EMFILE: 33, errno.ENOENT: 44,
              errno.ENOSPC: 51, errno.ENOTDIR: 54, errno.ENOTEMPTY: 55,
              errno.ENOSYS: 52, errno.EPERM: 63, errno.EROFS: 69}


class Host:
    def __init__(self):
        config = wasmtime.Config()
        config.wasm_gc = False
        config.wasm_exceptions = True
        config.wasm_tail_call = True
        config.wasm_threads = False
        config.wasm_memory64 = False
        config.wasm_multi_memory = False  # C runtime and libc share one linear memory.
        config.wasm_stack_switching = False
        config.consume_fuel = True
        config.parallel_compilation = False
        config.cranelift_opt_level = "speed_and_size"
        config.target = "x86_64-unknown-linux-gnu"  # Cache portable x86-64 code, not host CPU extensions.
        config.max_wasm_stack = 2 * 1024**2
        # Keep reservations small so the process address-space limit accounts
        # for GC, Python, compiler code and virtual files as well as Wasm memory.
        config.memory_reservation = 16 * 1024**2
        config.memory_reservation_for_growth = 16 * 1024**2
        config.memory_guard_size = 0
        self.engine = wasmtime.Engine(config)
        self.modules = {}

    def precompile(self, source, destination):
        module = wasmtime.Module.from_file(self.engine, source)
        Path(destination).write_bytes(module.serialize())

    def execute(self, module_path, args, files, limits, directories=()):
        if module_path not in self.modules:
            if module_path.endswith(".cwasm"):
                # Only coordinator-owned runtime modules reach this branch.
                # Submitted source/artifact bytes are NEVER deserialized as code.
                self.modules[module_path] = wasmtime.Module.deserialize_file(self.engine, module_path)
            else:
                self.modules[module_path] = wasmtime.Module.from_file(self.engine, module_path)
        module = self.modules[module_path]
        fs = Filesystem(files, limits["work_mib"] * 1024**2,
                        limits["artifact_mib"] * 1024**2)
        for directory in directories:
            fs.mkdir(directory)
        output, errors = bytearray(), bytearray()
        encoded_args = [(arg + "\0").encode() for arg in args]
        environment = [value.encode() + b"\0" for value in [
            "HOME=/tmp", "TMPDIR=/tmp", "OCAMLRUNPARAM=b=0",
            "OCAMLPATH=/opt/rocq/9.3.0/lib",
            "OCAMLFIND_CONF=/opt/rocq/9.3.0/lib/findlib.conf",
            "ROCQRUNTIMELIB=/opt/rocq/9.3.0/lib/rocq-runtime"]]
        store = wasmtime.Store(self.engine)
        store.set_limits(memory_size=limits["memory_mib"] * 1024**2,
                         table_elements=100000, instances=1, tables=16, memories=4)
        store.set_fuel(limits.get("fuel", 5_000_000_000))
        linker = wasmtime.Linker(self.engine)

        def memory(caller):
            result = caller.get("memory")
            if not isinstance(result, wasmtime.Memory):
                raise RuntimeError("Guest does not export its WASI memory")
            return result

        def read(caller, offset, size):
            mem = memory(caller)
            if offset < 0 or size < 0 or offset + size > mem.data_len(caller):
                raise RuntimeError("Guest pointer outside linear memory")
            return bytes(mem.read(caller, offset, offset + size))

        def write(caller, offset, data):
            mem = memory(caller)
            if offset < 0 or offset + len(data) > mem.data_len(caller):
                raise RuntimeError("Guest pointer outside linear memory")
            mem.write(caller, data, offset)

        def put(caller, ptr, value, fmt="<I"):
            write(caller, ptr, struct.pack(fmt, value))

        def path(caller, fd, ptr, length):
            if length > 4096:
                raise OSError(errno.EINVAL, "Path too long")
            return fs.path(fd, read(caller, ptr, length).decode("utf-8", errors="strict"))

        def descriptor(fd):
            if fd not in fs.descriptors:
                raise OSError(errno.EBADF, "Unknown virtual descriptor")
            return fs.descriptors[fd]

        def vectors(caller, ptr, count):
            if count < 0 or count > 1024:
                raise OSError(errno.EINVAL, "Invalid iovec count")
            return list(struct.iter_unpack("<II", read(caller, ptr, count * 8)))

        def fd_write(caller, fd, ptr, count, result):
            desc = descriptor(fd)
            vecs = vectors(caller, ptr, count)
            total = sum(size for _, size in vecs)
            if fd in (1, 2):
                buffer = output if fd == 1 else errors
                if len(buffer) + total > limits["log_mib"] * 1024**2:
                    raise RuntimeError("Sandbox output limit exceeded")
                for offset, size in vecs:
                    buffer.extend(read(caller, offset, size))
            else:
                node, offset, writable = desc
                if not writable:
                    raise OSError(errno.EROFS, "Descriptor has no write authority")
                if node.data is None:
                    raise OSError(errno.EISDIR, "Directory")
                fs.resize(node, max(len(node.data), offset + total))
                for pointer, size in vecs:
                    node.data[offset:offset + size] = read(caller, pointer, size)
                    offset += size
                desc[1] = offset
            put(caller, result, total)
            return 0

        def fd_read(caller, fd, ptr, count, result):
            node, offset, _ = descriptor(fd)
            total = 0
            if node is not None:
                if node.input_path is not None:
                    fs.observed.add(node.input_path)
                if node.data is None:
                    raise OSError(errno.EISDIR, "Directory")
                for pointer, size in vectors(caller, ptr, count):
                    data = node.data[offset:offset + size]
                    write(caller, pointer, data)
                    offset += len(data)
                    total += len(data)
                fs.descriptors[fd][1] = offset
            put(caller, result, total)
            return 0

        def fd_pread(caller, fd, ptr, count, offset, result):
            desc = descriptor(fd)
            if desc[0] is None or desc[0].data is None or offset < 0:
                raise OSError(errno.EBADF, "Not a seekable file")
            previous = desc[1]
            desc[1] = offset
            try:
                return fd_read(caller, fd, ptr, count, result)
            finally:
                desc[1] = previous

        def fd_tell(caller, fd, result):
            desc = descriptor(fd)
            if desc[0] is None or desc[0].data is None:
                raise OSError(errno.EBADF, "Not a seekable file")
            put(caller, result, desc[1], "<Q")
            return 0

        def path_readlink(caller, fd, ptr, length, buffer, size, result):
            fs.get(path(caller, fd, ptr, length))
            raise OSError(errno.EINVAL, "Symlinks are unavailable")

        def poll_oneoff(*args):
            raise OSError(errno.ENOSYS, "Polling is unavailable")

        def fd_seek(caller, fd, offset, whence, result):
            desc = descriptor(fd)
            node = desc[0]
            if node is None or node.data is None:
                raise OSError(errno.EBADF, "Not a seekable file")
            if whence not in (0, 1, 2):
                raise OSError(errno.EINVAL, "Invalid whence")
            position = offset + (0 if whence == 0 else desc[1] if whence == 1 else len(node.data))
            if position < 0:
                raise OSError(errno.EINVAL, "Negative offset")
            desc[1] = position
            put(caller, result, position, "<Q")
            return 0

        def path_open(caller, fd, _lookup, ptr, length, oflags, rights, _inherit, flags, result):
            new = fs.open(path(caller, fd, ptr, length), oflags, rights, flags)
            put(caller, result, new)
            return 0

        def path_stat(caller, fd, _flags, ptr, length, result):
            write(caller, result, fs.stat(fs.get(path(caller, fd, ptr, length))))
            return 0

        def fd_stat(caller, fd, result):
            node = descriptor(fd)[0]
            if node is None:
                write(caller, result, struct.pack("<QQB7xQQQQQ", 0, 0, 2, 1, 0, 0, 0, 0))
            else:
                write(caller, result, fs.stat(node))
            return 0

        def fd_fdstat(caller, fd, result):
            node, _, writable = descriptor(fd)
            kind = 2 if node is None else 3 if node.data is None else 4
            rights = (1 << 1) | (1 << 2) | (1 << 21)  # read, seek, stat
            if writable:
                rights |= 1 << 6
            if kind == 3:
                rights = (1 << 29) - 1
            write(caller, result, struct.pack("<BxH4xQQ", kind, 0, rights, rights))
            return 0

        def fd_close(_caller, fd):
            descriptor(fd)
            del fs.descriptors[fd]
            return 0

        def prestat(caller, fd, result):
            if fd != 3 or fd not in fs.descriptors:
                raise OSError(errno.EBADF, "No preopen")
            write(caller, result, struct.pack("<B3xI", 0, 1))
            return 0

        def preopen_name(caller, fd, ptr, length):
            if fd != 3 or length < 1:
                raise OSError(errno.EBADF, "No preopen")
            write(caller, ptr, b"/")
            return 0

        def readdir(caller, fd, ptr, length, cookie, result):
            node = descriptor(fd)[0]
            name = next((p for p, n in fs.nodes.items() if n is node), None)
            if name is None or node.data is not None:
                raise OSError(errno.ENOTDIR, "Not a directory")
            data = bytearray()
            for index, (entry, child) in enumerate(fs.listing(name)):
                if index < cookie:
                    continue
                raw = entry.encode()
                data.extend(struct.pack("<QQIB3x", index + 1, 0, len(raw),
                                        3 if child.data is None else 4) + raw)
                if len(data) >= length:
                    break
            write(caller, ptr, data[:length])
            put(caller, result, min(length, len(data)))
            return 0

        def args_sizes(caller, count, size):
            put(caller, count, len(encoded_args))
            put(caller, size, sum(map(len, encoded_args)))
            return 0

        def args_get(caller, pointers, buffer):
            for index, arg in enumerate(encoded_args):
                put(caller, pointers + index * 4, buffer)
                write(caller, buffer, arg)
                buffer += len(arg)
            return 0

        def environ_sizes(caller, count, size):
            put(caller, count, len(environment))
            put(caller, size, sum(map(len, environment)))
            return 0

        def environ_get(caller, pointers, buffer):
            for index, value in enumerate(environment):
                put(caller, pointers + index * 4, buffer)
                write(caller, buffer, value)
                buffer += len(value)
            return 0

        def clock(caller, kind, _precision, ptr):
            clocks = {0: time.time_ns, 1: time.monotonic_ns,
                      2: time.process_time_ns, 3: time.thread_time_ns}
            if kind not in clocks:
                raise OSError(errno.EINVAL, "Clock not granted")
            put(caller, ptr, clocks[kind](), "<Q")
            return 0

        def random(caller, ptr, length):
            if length < 0 or length > 1024**2:
                raise OSError(errno.EINVAL, "Random request too large")
            write(caller, ptr, os.urandom(length))
            return 0

        def exit_guest(_caller, code):
            raise GuestExit(code)

        def mutate(caller, operation, fd, ptr, length):
            operation(path(caller, fd, ptr, length))
            return 0

        def rename(caller, old_fd, old_ptr, old_len, new_fd, new_ptr, new_len):
            fs.rename(path(caller, old_fd, old_ptr, old_len), path(caller, new_fd, new_ptr, new_len))
            return 0

        def set_size(_caller, fd, size):
            desc = descriptor(fd)
            if not desc[2]:
                raise OSError(errno.EROFS, "Descriptor has no write authority")
            fs.resize(desc[0], size)
            return 0

        handlers = {
            "args_sizes_get": args_sizes, "args_get": args_get,
            "environ_sizes_get": environ_sizes, "environ_get": environ_get,
            "clock_time_get": clock, "random_get": random, "proc_exit": exit_guest,
            "fd_write": fd_write, "fd_read": fd_read, "fd_seek": fd_seek,
            "fd_pread": fd_pread, "fd_tell": fd_tell, "poll_oneoff": poll_oneoff,
            "fd_close": fd_close, "fd_filestat_get": fd_stat, "fd_fdstat_get": fd_fdstat,
            "fd_prestat_get": prestat, "fd_prestat_dir_name": preopen_name,
            "fd_readdir": readdir, "path_open": path_open, "path_filestat_get": path_stat, "path_readlink": path_readlink,
            "path_create_directory": lambda c, f, p, n: mutate(c, fs.mkdir, f, p, n),
            "path_unlink_file": lambda c, f, p, n: mutate(c, fs.unlink, f, p, n),
            "path_remove_directory": lambda c, f, p, n: mutate(c, lambda p: fs.unlink(p, True), f, p, n),
            "path_rename": rename, "fd_filestat_set_size": set_size,
            "fd_sync": lambda c, fd: (descriptor(fd), 0)[1],
            "fd_datasync": lambda c, fd: (descriptor(fd), 0)[1],
            "fd_fdstat_set_flags": lambda c, fd, flags: (descriptor(fd), 0)[1],
            # No symlinks, sockets, process control or host descriptor imports.
        }
        for imp in module.imports:
            if imp.module != "wasi_snapshot_preview1" or imp.name not in handlers:
                raise RuntimeError(f"Unapproved guest import: {imp.module}.{imp.name}")
            handler = handlers[imp.name]

            def invoke(caller, *values, handler=handler):
                try:
                    return handler(caller, *values)
                except OSError as error:
                    return WASI_ERRNO.get(error.errno, 29)
                except UnicodeError:
                    return 28

            linker.define(store, imp.module, imp.name,
                          wasmtime.Func(store, imp.type, invoke, access_caller=True))
        try:
            instance = linker.instantiate(store, module)
            instance.exports(store)["_start"](store)
        except GuestExit as error:
            if error.code:
                raise RuntimeError(f"Guest exited {error.code}: " + errors.decode(errors="replace")) from error
        except Exception as error:
            raise RuntimeError(str(error) + "\n" + errors.decode(errors="replace")) from error
        finally:
            linker.close()
            store.close()
        return bytes(output), bytes(errors), fs


def main():
    # A framed JSON stream is the trusted coordinator protocol, never guest stdout.
    host = Host()
    if len(sys.argv) == 4 and sys.argv[1] == "--precompile":
        host.precompile(sys.argv[2], sys.argv[3])
        return
    snapshots = {}
    blobs = {}
    for line in sys.stdin.buffer:
        try:
            request = json.loads(line)
            usage = resource.getrusage(resource.RUSAGE_SELF)
            resource.setrlimit(resource.RLIMIT_CPU,
                               (int(usage.ru_utime + usage.ru_stime) + request["limits"]["cpu_seconds"] + 1,
                                resource.RLIM_INFINITY))
            if "files" in request:
                snapshot = {}
                for path, data in request["files"].items():
                    if data is None:
                        snapshot[path] = None
                    else:
                        raw = base64.b64decode(data, validate=True)
                        digest = hashlib.sha256(raw).digest()
                        snapshot[path] = blobs.setdefault(digest, raw)
                snapshots[request["snapshot"]] = snapshot
            files = dict(snapshots[request["snapshot"]])
            for path, data in request.get("overlay", {}).items():
                raw = base64.b64decode(data, validate=True)
                files[path] = blobs.setdefault(hashlib.sha256(raw).digest(), raw)
            stdout, stderr, fs = host.execute(request["module"], request["args"], files,
                                            request["limits"], request.get("directories", []))
            retained = {path: node.data for path, node in fs.nodes.items()
                        if node.writable and node.data is not None and path.endswith(".vo")}
            if sum(map(len, retained.values())) > request["limits"]["artifact_mib"] * 1024**2:
                raise RuntimeError("Compiled artifacts exceed the size limit")
            result = {"stdout": base64.b64encode(stdout).decode(),
                      "stderr": base64.b64encode(stderr).decode(),
                      "files": {path: base64.b64encode(data).decode() for path, data in retained.items()},
                      "observed": sorted(fs.observed)}
        except Exception as error:
            result = {"error": str(error)}
        print(json.dumps(result, separators=(",", ":")), flush=True)
        # Release transport buffers; only immutable input blobs and compiled
        # runtime code survive. A Store is already closed by execute().
        request = files = result = stdout = stderr = fs = retained = line = None


if __name__ == "__main__":
    main()
