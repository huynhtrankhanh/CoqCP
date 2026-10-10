"""WASI coordination and immutable sharing across isolated compiler invocations."""
import base64
import os
from pathlib import Path
import secrets
import selectors
import signal
import subprocess
import time

from wasi_cache import Cache, key, hash_bytes


class WasiSandbox:
    name = "wasmtime+wasi"
    network_isolation = "capabilities"

    def __init__(self, gate, limits, runtime=None, cache_directory=None, system_files=None):
        self.gate, self.limits = gate, limits
        self.process = None
        self.runtime = runtime if runtime is not None else gate.toolchain("wasi")
        self.host = Path("/opt/rocq/wasi/host/coqcp-wasi-host")
        if not self.host.is_file():
            raise gate.Rejected("WASI host missing; run tools/install-wasi.sh")
        self.snapshots = set()
        self.system_files = system_files
        self.cache = Cache(cache_directory, gate.read_regular, gate.encoded, gate.decoded,
                           limits["artifact_mib"] * 1024**2)

    def close(self):
        if self.process is not None:
            if self.process.poll() is None:
                os.killpg(self.process.pid, signal.SIGKILL)
            self.process.wait()
            for stream in [self.process.stdin, self.process.stdout, self.process.stderr]:
                stream.close()
            self.process = None
            self.snapshots.clear()

    def __del__(self):
        self.close()

    def _start(self):
        if self.process is not None:
            return

        bound = self.limits["memory_mib"] * 1024**2
        # Wasmtime backs trusted code with anonymous OS files. Guest files have
        # separate memory quotas. prlimit avoids Python preexec_fn after fork,
        # which is unsafe when compiler batches use multiple coordinator threads.
        file_bound = max(256, self.limits["artifact_mib"]) * 1024**2
        if not self.host.is_file():
            raise self.gate.Rejected("No safe condition for WASI sandbox: host missing")
        try:
            self.process = subprocess.Popen([self.gate.command("prlimit"), "--core=0", "--nofile=128",
                "--as=" + str(bound), "--fsize=" + str(file_bound), "--", str(self.host)], stdin=subprocess.PIPE,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, close_fds=True,
                start_new_session=True, env={})
        except OSError as error:
            raise self.gate.Rejected("No safe condition for WASI sandbox: " + str(error)) from error
        for stream in [self.process.stdin, self.process.stdout, self.process.stderr]:
            os.set_blocking(stream.fileno(), False)

    def _exchange(self, request, deadline):
        self._start()
        data = memoryview(self.gate.encoded(request) + b"\n")
        output, errors = bytearray(), bytearray()
        bound = (self.limits["artifact_mib"] * 4 // 3 + self.limits["log_mib"] * 3 + 4) * 1024**2
        try:
            with selectors.DefaultSelector() as selector:
                selector.register(self.process.stdin, selectors.EVENT_WRITE)
                selector.register(self.process.stdout, selectors.EVENT_READ, output)
                selector.register(self.process.stderr, selectors.EVENT_READ, errors)
                while b"\n" not in output:
                    remaining = deadline - time.monotonic()
                    if remaining <= 0:
                        raise self.gate.Rejected("Sandbox wall time limit exceeded")
                    for selected, _ in selector.select(min(remaining, 0.1)):
                        if selected.fileobj is self.process.stdin:
                            count = os.write(selected.fd, data[:65536])
                            data = data[count:]
                            if not data:
                                selector.unregister(selected.fileobj)
                        else:
                            chunk = os.read(selected.fd, 65536)
                            if not chunk:
                                code = self.process.poll()
                                if code is None:
                                    try:
                                        code = self.process.wait(timeout=1)
                                    except subprocess.TimeoutExpired:
                                        pass
                                if code == -signal.SIGXCPU:
                                    raise self.gate.Rejected("Sandbox CPU time limit exceeded")
                                detail = "" if code is None else f" (exit {code})"
                                raise self.gate.Rejected("Sandbox command failed" + detail + ": " +
                                                         errors.decode(errors="replace"))
                            selected.data.extend(chunk)
                            if len(selected.data) > (bound if selected.data is output else self.limits["log_mib"] * 1024**2):
                                raise self.gate.Rejected("Sandbox output limit exceeded")
            if not output.endswith(b"\n") or output.count(b"\n") != 1:
                raise self.gate.Rejected("Malformed WASI host response")
            result = self.gate.decoded(output, "WASI host response")
            if isinstance(result, dict) and set(result) == {"error"}:
                raise self.gate.Rejected("Sandbox command failed: " + result["error"])
            if not isinstance(result, dict) or set(result) != {"stdout", "stderr", "files", "observed"}:
                raise self.gate.Rejected("Unexpected WASI host response")
            for field in ["stdout", "stderr"]:
                result[field] = base64.b64decode(result[field], validate=True)
                if len(result[field]) > self.limits["log_mib"] * 1024**2:
                    raise self.gate.Rejected("Sandbox output limit exceeded")
            result["files"] = {path: base64.b64decode(raw, validate=True)
                               for path, raw in result["files"].items()}
            if sum(map(len, result["files"].values())) > self.limits["artifact_mib"] * 1024**2:
                raise self.gate.Rejected("Compiled artifacts exceed the size limit")
            if not isinstance(result["observed"], list) or any(not isinstance(p, str) for p in result["observed"]):
                raise self.gate.Rejected("Invalid WASI observation manifest")
            return result
        except BaseException:
            self.close()
            raise

    def _system(self):
        if self.system_files is None:
            self.system_files = {}
            for path in self.gate.TOOLCHAIN.joinpath("lib").rglob("*"):
                if path.is_dir():
                    self.system_files[str(path)] = None
                elif path.is_file() and (path.suffix in (".env", ".v") or path.name in ("META", "findlib.conf")):
                    self.system_files[str(path)] = self.gate.read_regular(path, 64 * 1024**2)
            for path in self.gate.WASI_LIB.joinpath("installed").rglob("*.vo"):
                target = self.gate.TOOLCHAIN / "lib" / path.relative_to(self.gate.WASI_LIB / "installed")
                self.system_files[str(target)] = self.gate.read_regular(path, 64 * 1024**2)
        return self.system_files

    def _files(self, mounts):
        files = dict(self._system())
        for host, target in mounts:
            for path in Path(host).rglob("*"):
                if path.is_dir():
                    files[target + "/" + str(path.relative_to(host))] = None
                elif path.is_file():
                    files[target + "/" + str(path.relative_to(host))] = self.gate.read_regular(path, 64 * 1024**2)
        return files

    def invoke(self, module, args, files, deadline, directories=(), overlay=None):
        snapshot = key({name: hash_bytes(data) for name, data in files.items()})
        compiled = self.gate.WASI_BIN / (module + ".cwasm")
        module_path = compiled if compiled.is_file() else self.gate.WASI_BIN / (module + ".wasm")
        request = dict(snapshot=snapshot, module=str(module_path),
                       args=args, limits=self.limits, directories=list(directories))
        if snapshot not in self.snapshots or self.process is None:
            request["files"] = {path: None if data is None else base64.b64encode(data).decode()
                                for path, data in files.items()}
        if overlay:
            request["overlay"] = {path: base64.b64encode(data).decode() for path, data in overlay.items()}
        result = self._exchange(request, deadline)
        self.snapshots.add(snapshot)
        return result

    def compile(self, inputs, sources, namespace, bundle, runtime):
        gate = self.gate
        deadline = time.monotonic() + self.limits["wall_seconds"]
        files = self._files([(inputs, "/inputs"), (bundle, "/bundle")])
        paths = ["/inputs/" + name for name in sources]
        dep_flags = [part for root in gate.library_roots(bundle) for part in ["-Q", *root]]
        if namespace == "Submission":
            dep_flags += ["-Q", "/bundle/spec", "Trusted"]
        # Installed-path discovery normally searches existing .vo files and
        # omits core dependencies. Register trusted source roots explicitly so
        # the guest scanner can request a not-yet-provisioned library. Plugins
        # are statically linked: native findlib dependency lookup is irrelevant.
        coqlib = Path(runtime["coqlib"])
        installed_roots = [(coqlib / "theories", "Corelib")]
        installed_roots += [(p, p.name) for p in sorted((coqlib / "user-contrib").iterdir()) if p.is_dir()]
        installed_flags = [part for physical, logical in installed_roots
                           for part in ("-R", str(physical), logical)]
        dep_args = ["rocq-dep", "-coqlib", runtime["coqlib"], "-dyndep", "no", *installed_flags,
                    *dep_flags, "-Q", "/inputs", namespace]
        dependency_text = self.invoke("rocq-dep", [*dep_args, *paths], files, deadline)["stdout"].decode()
        required = {name for line in dependency_text.splitlines() if ":" in line
                    for name in line.split(":", 1)[1].split()
                    if name.endswith(".vo") and name.startswith(str(gate.TOOLCHAIN / "lib") + "/")}
        if any(name not in files for name in required):
            import wasi_libraries
            wasi_libraries.build(gate, requested=required)
            self.system_files = None
            files = self._files([(inputs, "/inputs"), (bundle, "/bundle")])
            deadline = time.monotonic() + self.limits["wall_seconds"]
        # rocq dep -sort recursively opens imported .v files, including frozen
        # libraries supplied only as .vo. Sort just the submitted graph from
        # the sandboxed scanner's dependency records instead.
        by_artifact = {str(Path(path).with_suffix(".vo")): path for path in paths}
        dependencies = {path: set() for path in paths}
        seen = set()
        for line in dependency_text.splitlines():
            if ":" not in line:
                continue
            targets, consulted = line.split(":", 1)
            for target in targets.split():
                if target in by_artifact:
                    source = by_artifact[target]
                    seen.add(source)
                    dependencies[source].update(by_artifact[name] for name in consulted.split() if name in by_artifact)
                    dependencies[source].update(name for name in consulted.split() if name in dependencies and name != source)
        if seen != set(paths):
            raise gate.Rejected("rocq dep returned an unexpected dependency graph")
        order = []
        remaining = set(paths)
        while remaining:
            ready = sorted(source for source in remaining if not dependencies[source] & remaining)
            if not ready:
                raise gate.Rejected("Submission dependency cycle")
            order.extend(ready)
            remaining.difference_update(ready)
        flags = [part for root in gate.library_roots(bundle) for part in ["-Q", *root]]
        if namespace == "Submission":
            flags += ["-Q", "/bundle/spec", "Trusted"]
        flags += ["-Q", "/inputs", namespace, "-Q", "/work", namespace]
        # Library/specification contents are bound by the complete observation
        # manifest below. Keep their global digest out of this base key so an
        # unchanged helper can be reused across contracts and unrelated edits.
        compiler_runtime = {k: v for k, v in runtime.items() if k != "fingerprint"}
        if "compiler_fingerprint" not in runtime:
            compiler_runtime = runtime  # Conservative fallback for custom callers.
        context = key(dict(toolchain=compiler_runtime, namespace=namespace, flags=flags,
                           limits=self.limits, cache_format=2))
        # Reuse one immutable snapshot for the batch. Per-module source and
        # artifact overlays still expose exactly the declared closure, and the
        # host applies them to a fresh filesystem rather than the stored base.
        shared_files = {path: data for path, data in files.items()
                        if not path.startswith("/inputs/")}
        artifacts = {}
        for source in order:
            name = Path(source).with_suffix(".vo").name
            visible = {source}
            pending = list(dependencies[source])
            while pending:
                dependency = pending.pop()
                if dependency not in visible:
                    visible.add(dependency)
                    pending.extend(dependencies[dependency])
            inherited = {"/work/" + Path(path).with_suffix(".vo").name:
                         artifacts[Path(path).with_suffix(".vo").name]
                         for path in visible if path != source}
            overlay = {path: files[path] for path in visible} | inherited
            initial = shared_files | overlay
            base = key(dict(context=context, source=source, sha256=hash_bytes(files[source])))
            compiled = self.cache.get("compile", base, initial)
            if compiled is None:
                output_dir = "/work/.coqcp-output-" + secrets.token_hex(16)
                output = output_dir + "/" + name
                result = self.invoke("compile-safe", ["compile-safe", "-coqlib", runtime["coqlib"],
                    "-q", "-native-compiler", "no", "-async-proofs", "off", *flags,
                    "-Q", output_dir, namespace, "-o", output, source],
                    shared_files, deadline, [output_dir], overlay)
                if set(result["files"]) != {output}:
                    raise gate.Rejected("Submission created or removed a compiler artifact")
                compiled = result["files"][output]
                observed = [p for p in result["observed"] if not p.removeprefix("stat:").startswith(output_dir)]
                self.cache.put("compile", base, compiled, observed, initial)
            artifacts[name] = compiled
            if sum(map(len, artifacts.values())) > self.limits["artifact_mib"] * 1024**2:
                raise gate.Rejected("Compiled artifacts exceed the size limit")
        return artifacts

    def run(self, argv, mounts, *, compiler_worker=False):
        if compiler_worker or argv[0] != "/tool/spec-check":
            raise self.gate.Rejected("WASI executes only evaluator-owned tool modules")
        files = self._files(mounts)
        base = key(dict(toolchain=self.runtime, args=argv, limits=self.limits,
                        files={name: hash_bytes(data) for name, data in files.items()}, cache_format=1))
        cached = self.cache.get("kernel", base)
        if cached is not None:
            return cached
        directories = []
        output_prefix = "/work/.coqcp-checked-prefix/"
        domain = None
        if self.cache.directory is not None:
            seed = key(dict(format=1, checker=hash_bytes(
                self.gate.read_regular(self.gate.WASI_BIN / "spec-check.wasm", 64 * 1024**2)),
                compiler=self.runtime.get("compiler_fingerprint", self.runtime),
                limits=self.limits))
            domain = "checked-prefix/" + seed
            size = 0
            for directory in sorted((self.cache.directory / domain).glob("*")):
                name = directory.name
                if len(name) != 64 or any(c not in "0123456789abcdef" for c in name):
                    continue
                payload = self.cache.get(domain, name)
                if payload is None:
                    continue
                size += len(payload)
                if size > self.limits["artifact_mib"] * 1024**2:
                    break  # Omitting a certificate only causes a fresh check.
                files["/checked-prefix/" + name + ".vo"] = payload
            argv = [*argv, "--checked-prefix", "/checked-prefix",
                    output_prefix.rstrip("/"), seed,
                    str(min(120, self.limits["cpu_seconds"] / 4))]
            directories = [output_prefix.rstrip("/")]
        deadline = time.monotonic() + self.limits["wall_seconds"]
        while True:
            result = self.invoke("spec-check", argv, files, deadline, directories)
            report = self.gate.decoded(result["stdout"], "kernel checker response")
            checkpoint = report == dict(status="prefix-checked", rocq_version="9.3.0", axioms=[])
            if checkpoint:
                if domain is None or not result["files"]:
                    raise self.gate.Rejected("Kernel checkpoint made no progress")
            else:
                allowed = [argv[i + 1] for i, part in enumerate(argv) if part == "--allow-axiom"]
                self.gate.validate_kernel_report(report, allowed,
                                                "spec-checked" if "--spec-only" in argv else "accepted")
            # Prefixes certify independent kernel checks, including opaque
            # taint, but never certify contract or axiom-policy acceptance.
            for path, payload in result["files"].items():
                name = path.removeprefix(output_prefix).removesuffix(".vo")
                if (domain is None or not path.startswith(output_prefix) or
                        not path.endswith(".vo") or len(name) != 64 or
                        any(c not in "0123456789abcdef" for c in name)):
                    raise self.gate.Rejected("Unexpected kernel prefix certificate")
                self.cache.put(domain, name, payload)
                files["/checked-prefix/" + name + ".vo"] = payload
            if not checkpoint:
                self.cache.put("kernel", base, result["stdout"])
                return result["stdout"]
