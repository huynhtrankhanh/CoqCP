"""Rebuild evaluator libraries with the same 31-bit runtime as submissions.

Native 64-bit .vo files are not portable OCaml Marshal data. Never truncate them
to fit the guest: compile the trusted sources instead, with a separate taint cache.
"""
import fcntl
import os
import re
from pathlib import Path
import signal
import subprocess
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED

from wasi_backend import WasiSandbox
from wasi_cache import key, hash_bytes


def portable_source(gate, source, coqlib):
    data = gate.read_regular(source, 8 * 1024**2)
    if source == coqlib / "user-contrib/Stdlib/ZArith/ZModOffset.v":
        # The upstream nonlinear reflection certificate expands prohibitively
        # under standard conversion. Replace only this proof, never its type.
        if hash_bytes(data) != "34166a4c0be70ae49290aff3100a0e0fcc41e75719776211ddae9d78bf066f8a":
            raise gate.Rejected("Pinned ZModOffset source changed; review the portable proof")
        start = data.index(b"Proof.", data.index(b"Lemma smod_complement"))
        end = data.index(b"Qed.", start) + len(b"Qed.")
        proof = gate.read_regular(gate.TOOLS / "portable/smod_complement.v", 64 * 1024)
        data = data[:start] + proof.rstrip() + data[end:]
    return data


def build(gate, requested=()):
    gate.WASI_LIB.mkdir(parents=True, exist_ok=True)
    with (gate.WASI_LIB / ".build.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        return _build(gate, requested)


def _build(gate, requested):
    env = dict(PATH=str(gate.TOOLCHAIN / "bin") + ":/usr/bin:/bin", HOME="/tmp",
               OCAMLPATH=str(gate.TOOLCHAIN / "lib"),
               OCAMLFIND_CONF=str(gate.TOOLCHAIN / "lib/findlib.conf"))
    coqlib = Path(subprocess.check_output([gate.command("rocq"), "compile", "-where"], env=env).decode().strip())
    roots = [(coqlib / "theories", "Corelib")]
    roots += [(p, p.name) for p in sorted((coqlib / "user-contrib").iterdir()) if p.is_dir()]
    mappings, project = gate.project_layout()
    roots += [(gate.REPO / physical, logical) for physical, logical in mappings]
    sources = sorted(coqlib.rglob("*.v")) + [gate.REPO / p for p in project]
    flags = [arg for physical, logical in roots for arg in ("-R", str(physical), logical)]
    dependency_text = subprocess.check_output([gate.command("rocq"), "dep", "-boot", *flags,
                                                *map(str, sources)], env=env).decode()
    approved = set(gate.compiler_plugins())
    blocked = {str(p.with_suffix(".vo")) for p in sources
               if any(plugin not in approved for plugin in
                      re.findall(r'Declare ML Module\s+"([^"]+)"', p.read_text()))}
    dependencies = {}
    for line in dependency_text.splitlines():
        if ":" in line:
            targets_text, dependency_line = line.split(":", 1)
            for target in targets_text.split():
                if target.endswith(".vo"):
                    dependencies[target] = dependency_line.split()
    # Corelib is the foundation; its short imports must resolve inside
    # Corelib, not to similarly named Stdlib/stdpp compatibility wrappers.
    # A combined -R scan can otherwise choose those wrappers and expose both
    # aliases to the compiler. Correct its graph with an isolated core scan.
    core_sources = [p for p in sources if p.is_relative_to(coqlib / "theories")]
    core_dependency_text = subprocess.check_output([gate.command("rocq"), "dep", "-boot",
        "-R", str(coqlib / "theories"), "Corelib", *map(str, core_sources)], env=env).decode()
    for line in core_dependency_text.splitlines():
        if ":" in line:
            targets_text, dependency_line = line.split(":", 1)
            for target in targets_text.split():
                if target.endswith(".vo"):
                    dependencies[target] = dependency_line.split()
    while True:
        updated = blocked | {target for target, deps in dependencies.items() if any(d in blocked for d in deps)}
        if updated == blocked:
            break
        blocked = updated
    if any(str((gate.REPO / p).with_suffix(".vo")) in blocked for p in project):
        raise gate.Rejected("Project library requires a plugin outside the compiler policy")
    sources = [p for p in sources if str(p.with_suffix(".vo")) not in blocked]
    host_fingerprints = gate.build_fingerprints("wasi")
    compiler_identity = key(dict(compiler=gate.digest(gate.WASI_BIN / "compile-safe.wasm"),
        host={name: host_fingerprints[name] for name in ("host", "wasi_host.py", "wasi_fs.py")},
        cache_format=2, compile_protocol=1,
        cache_implementation=gate.digest(gate.TOOLS / "wasi_cache.py"),
        roots=[(str(p), n) for p, n in roots]))
    fingerprint = compiler_identity
    source_bytes = {str(p): portable_source(gate, p, coqlib) for p in sources}
    source_hashes = {name: hash_bytes(data) for name, data in source_bytes.items()}
    stamp = gate.WASI_LIB / "sources.json"
    targets = {str(p): gate.WASI_LIB / ("installed" if p.is_relative_to(gate.TOOLCHAIN / "lib") else "project") /
               p.relative_to(gate.TOOLCHAIN / "lib" if p.is_relative_to(gate.TOOLCHAIN / "lib") else gate.REPO).with_suffix(".vo")
               for p in sources}
    # Provision the project closure first. Other approved installed libraries
    # are requested by the sandboxed dependency scanner, never by parsing
    # submitted source in a native process.
    selected = {str((gate.REPO / p).with_suffix(".vo")) for p in project}
    selected.update(str(p.with_suffix(".vo")) for p in (coqlib / "theories/Init").glob("*.v"))
    known = {str(Path(name).with_suffix(".vo")): name for name in targets}
    for artifact in requested:
        if artifact in known:
            selected.add(artifact)
    compatible_cache_runtimes = []
    if stamp.is_file():
        previous = gate.decoded(stamp.read_bytes(), "trusted library manifest")
        selected.update(name for name in previous.get("selected", []) if name in known)
        # Earlier manifests coupled compilation to all three runtime images.
        # Reuse that cache domain only when it recorded this exact compiler
        # and host identity; a scanner/checker-only rebuild need not rebuild
        # every trusted proof. These are evaluator-owned manifests.
        if previous.get("compiler_identity") == compiler_identity:
            compatible_cache_runtimes = sorted(set([previous["runtime"],
                *previous.get("compatible_cache_runtimes", [])]) - {fingerprint})
    while True:
        updated = selected | {dep for name in selected for dep in dependencies.get(name, []) if dep in known}
        if updated == selected:
            break
        selected = updated
    expected = dict(format=3, runtime=fingerprint, compiler_identity=compiler_identity,
                    compatible_cache_runtimes=compatible_cache_runtimes,
                    sources=source_hashes, selected=sorted(selected),
                    dependencies={name: sorted(dependencies.get(name, [])) for name in sorted(selected)})
    targets = {name: target for name, target in targets.items() if str(Path(name).with_suffix(".vo")) in selected}
    if stamp.is_file():
        prior_artifacts = previous.get("artifacts", {})
        if ({name: value for name, value in previous.items() if name != "artifacts"} == expected
                and set(prior_artifacts) == set(targets)
                and all(p.is_file() and gate.digest(p) == prior_artifacts[name]
                        for name, p in targets.items())):
            return
    # Restored caches may contain libraries removed from the plugin policy or
    # project. Never expose those stale artifacts to subsequent submissions.
    selected_targets = set(targets.values())
    for directory in [gate.WASI_LIB / "installed", gate.WASI_LIB / "project"]:
        for artifact in directory.rglob("*.vo"):
            if artifact not in selected_targets:
                artifact.unlink()
    # This is trusted build input, not a submitted source. The native dependency
    # scanner is used only while provisioning evaluator-owned libraries.
    order = subprocess.check_output([gate.command("rocq"), "dep", "-boot", "-sort", *flags,
                                     *map(str, sources)], env=env).decode().split()
    if len(order) != len(sources) or set(order) != set(map(str, sources)):
        raise gate.Rejected("Unexpected trusted library dependency order")
    boot_sources = sorted((coqlib / "theories/Init").glob("*.v"))
    boot_flags = ["-R", str(coqlib / "theories"), "Corelib"]
    boot_order = subprocess.check_output([gate.command("rocq"), "dep", "-boot", "-sort", *boot_flags,
                                          *map(str, boot_sources)], env=env).decode().split()
    order = boot_order + [name for name in order if name not in boot_order and name in targets]
    files = {}
    for path in (gate.TOOLCHAIN / "lib").rglob("*"):
        if path.is_dir():
            files[str(path)] = None
        elif path.is_file() and (path.suffix == ".env" or path.name in ("META", "findlib.conf")):
            files[str(path)] = gate.read_regular(path, 64 * 1024**2)
    files.update(source_bytes)
    for physical, _ in roots:
        files[str(physical)] = None
    prior_limits = dict(gate.DEFAULT_LIMITS, wall_seconds=600, cpu_seconds=300, memory_mib=4096)
    prior_limits.pop("fuel", None)  # Legacy host default was five billion.
    intermediate_limits = dict(prior_limits, wall_seconds=1200, cpu_seconds=600, fuel=50_000_000_000)
    translated_limits = dict(intermediate_limits, fuel=500_000_000_000)
    # The C interpreter counts dispatch as WASM instructions too. Preserve
    # CPU/wall/memory bounds; fuel units differ from the translated backend.
    limits = dict(translated_limits, fuel=2_000_000_000_000)
    shared_files = {path: data for path, data in files.items() if not path.endswith(".v")}
    compiled = {}
    # Each worker reuses immutable inputs and runtime code, with a fresh guest
    # Store for every source. Only dependency-closure artifacts are exposed, so
    # scheduling order cannot taint a module with unrelated compiled outputs.
    workers = max(1, min(4, int(os.environ.get("COQCP_WASI_BUILD_JOBS", "2")), os.cpu_count() or 1))
    local = threading.local()
    sandboxes = []
    by_artifact = {str(Path(name).with_suffix(".vo")): name for name in order}
    needs = {name: {by_artifact[p] for p in dependencies.get(str(Path(name).with_suffix(".vo")), [])
                    if p in by_artifact} for name in order}
    # Boot resolution deliberately excludes the Stdlib compatibility aliases.
    # Use its separately checked order, rather than the normal graph's short
    # Init.* names, which can resolve back through those aliases.
    for index, name in enumerate(boot_order):
        needs[name] = set(boot_order[:index])
    for name in order:
        if name not in boot_order:
            needs[name].update(boot_order)

    def compile_one(name, inherited):
        if not hasattr(local, "sandbox"):
            local.sandbox = WasiSandbox(gate, limits,
                runtime={"backend": "wasi", "coqlib": str(coqlib), "fingerprint": fingerprint},
                cache_directory=gate.REPO / ".verification/wasi-cache", system_files={})
            sandboxes.append(local.sandbox)
        sandbox = local.sandbox
        source = Path(name)
        physical, logical = next((p, n) for p, n in roots if source.is_relative_to(p))
        namespace = ".".join([logical, *source.relative_to(physical).parent.parts])
        # Coqc scans metadata for files in every registered load path. Hide
        # unrelated source files as well as their artifacts; raw Load inputs
        # remain visible through the scanner's recorded .v dependencies.
        loaded_sources = {name}
        pending_sources = [name]
        while pending_sources:
            current = pending_sources.pop()
            for dependency in dependencies.get(str(Path(current).with_suffix(".vo")), []):
                if dependency.endswith(".v") and dependency in source_hashes and dependency not in loaded_sources:
                    loaded_sources.add(dependency)
                    pending_sources.append(dependency)
        overlay = {path: files[path] for path in loaded_sources} | inherited
        initial = shared_files | overlay
        # A successful trusted build under the earlier, stricter resource
        # bounds remains valid under these increased provisioning bounds.
        # Candidate caches still require an exact match of all their limits.
        base = key(dict(runtime=fingerprint, source=name, sha256=source_hashes[name], limits=limits))
        payload = None
        for cache_runtime in [fingerprint, *compatible_cache_runtimes]:
            for cache_limits in [limits, translated_limits, intermediate_limits, prior_limits]:
                cache_base = key(dict(runtime=cache_runtime, source=name,
                                      sha256=source_hashes[name], limits=cache_limits))
                payload = sandbox.cache.get("trusted-compile", cache_base, initial)
                if payload is not None:
                    break
            if payload is not None:
                break
        if payload is None:
            output_dir = "/work/.trusted-output"
            output = output_dir + "/" + source.with_suffix(".vo").name
            noinit = ["-boot", "-noinit"] if name in boot_order else []
            load_flags = boot_flags if name in boot_order else flags
            result = sandbox.invoke("compile-safe", ["compile-safe", "-coqlib", str(coqlib),
                "-q", "-native-compiler", "no", "-async-proofs", "off", *noinit, *load_flags,
                "-Q", output_dir, namespace, "-o", output, name],
                shared_files, time.monotonic() + limits["wall_seconds"], [output_dir], overlay)
            if set(result["files"]) != {output}:
                raise gate.Rejected("Unexpected trusted compiler artifacts: " + name)
            payload = result["files"][output]
            observed = [p for p in result["observed"] if not p.removeprefix("stat:").startswith(output_dir)]
            sandbox.cache.put("trusted-compile", base, payload, observed, initial)
        return payload

    def inherited_for(name):
        closure = set()
        todo = list(needs[name])
        while todo:
            dependency = todo.pop()
            if dependency not in closure:
                closure.add(dependency)
                todo.extend(needs[dependency])
        return {str(Path(dependency).with_suffix(".vo")): compiled[dependency] for dependency in closure}

    def retain(name, payload):
        compiled[name] = payload
        target = targets[name]
        target.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(dir=target.parent, delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(payload)
        try:
            os.replace(temporary, target)
        finally:
            temporary.unlink(missing_ok=True)
        if len(compiled) % 25 == 0 or len(compiled) == len(order):
            print(f"WASI libraries: {len(compiled)}/{len(order)} ({Path(name).name})", flush=True)

    try:
        with ThreadPoolExecutor(max_workers=workers) as executor:
            pending = list(order)
            running = {}
            try:
                while pending or running:
                    for name in list(pending):
                        if len(running) >= workers:
                            break
                        if needs[name].issubset(compiled):
                            running[executor.submit(compile_one, name, inherited_for(name))] = name
                            pending.remove(name)
                    if not running:
                        raise gate.Rejected("Trusted library dependency cycle or incomplete graph")
                    finished, _ = wait(running, return_when=FIRST_COMPLETED)
                    for future in finished:
                        name = running.pop(future)
                        try:
                            payload = future.result()
                        except Exception as error:
                            raise gate.Rejected(f"Trusted library {name}: {error}") from error
                        retain(name, payload)
            except BaseException:
                for future in running:
                    future.cancel()
                for sandbox in sandboxes:
                    process = sandbox.process
                    if process is not None and process.poll() is None:
                        try:
                            os.killpg(process.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                raise
        stamp.parent.mkdir(parents=True, exist_ok=True)
        expected["artifacts"] = {name: hash_bytes(payload) for name, payload in compiled.items()}
        with tempfile.NamedTemporaryFile(dir=stamp.parent, delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(gate.encoded(expected))
        try:
            os.replace(temporary, stamp)
        finally:
            temporary.unlink(missing_ok=True)
    finally:
        for sandbox in sandboxes:
            sandbox.close()
