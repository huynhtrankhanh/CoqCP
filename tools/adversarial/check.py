#!/usr/bin/env python3
"""Freeze evaluator specifications and check source-only Rocq submissions."""
import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import selectors
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time

from ci_policy import POLICY_FILE, trusted_axioms

REPO = Path(__file__).resolve().parents[2]
TOOLS = Path(__file__).resolve().parent
BIN = REPO / ".verification/bin"
VERSION = "8.20.1"
NAME = re.compile(r"[A-Za-z][A-Za-z0-9_]*\.v\Z")
DEFAULT_LIMITS = dict(wall_seconds=120, cpu_seconds=60, memory_mib=2048,
                      work_mib=256, artifact_mib=64, log_mib=1)


class Rejected(Exception):
    pass


def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def read_regular(path, limit):
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(fd, "rb") as stream:
        info = os.fstat(stream.fileno())
        if not stat.S_ISREG(info.st_mode) or info.st_size > limit:
            raise Rejected(f"Not a regular file within the size limit: {path.name}")
        data = stream.read(limit + 1)
        if len(data) > limit:
            raise Rejected(f"Input exceeds size limit: {path.name}")
        return data


def command(program):
    found = shutil.which(program)
    if not found:
        raise Rejected(f"Required tool missing: {program}; see docs/AdversarialChecking.md")
    found = Path(found).resolve()
    if not found.is_relative_to(Path("/usr")) or found.is_relative_to(Path("/usr/local")):
        raise Rejected(f"This sandbox profile requires system tools under /usr: {program}")
    return str(found)


def build():
    BIN.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="build-", dir=BIN.parent) as temporary:
        work = Path(temporary)
        shutil.copyfile(TOOLS / "spec_check.ml", work / "spec_check.ml")
        (work / "ci_policy.ml").write_text("let allowed_axioms = [" +
            "; ".join(json.dumps(name) for name in trusted_axioms()) + "]\n")
        subprocess.run([command("ocamlfind"), "ocamlopt", "-rectypes", "-thread", "-linkpkg",
                        "-package", "coq-core.checklib", "-o", str(work / "spec-check"),
                        "ci_policy.ml", "spec_check.ml"], cwd=work, check=True)
        subprocess.run([command("gcc"), "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2",
                        str(TOOLS / "sandbox_exec.c"), "-lseccomp", "-o",
                        str(work / "sandbox-exec")], check=True)
        for name in ["spec-check", "sandbox-exec"]:
            os.replace(work / name, BIN / name)
    (BIN / "sources.json").write_bytes(encoded(build_fingerprints()))


def build_fingerprints():
    return dict({name: digest(TOOLS / name) for name in ["spec_check.ml", "sandbox_exec.c"]},
                trusted_axioms=digest(POLICY_FILE))


def ensure_built():
    expected = build_fingerprints()
    if not all((BIN / name).is_file() for name in ["spec-check", "sandbox-exec", "sources.json"]):
        build()
    elif json.loads((BIN / "sources.json").read_bytes()) != expected:
        build()


def toolchain():
    coqc, coqdep = command("coqc"), command("coqdep")
    probe_env = {"PATH": "/usr/bin:/bin", "HOME": os.environ.get("HOME", "/tmp")}
    output = subprocess.check_output([coqc, "-q", "--version"], env=probe_env).decode()
    if not re.search(r"version " + re.escape(VERSION) + r"\b", output):
        raise Rejected(f"Supported Coq version is {VERSION}; installed: {output.strip()}")
    coqlib = Path(subprocess.check_output([coqc, "-q", "-where"],
                     env=probe_env).decode().strip()).resolve()
    if not coqlib.is_relative_to(Path("/usr/lib")):
        raise Rejected("This sandbox profile requires Coq libraries under /usr/lib")
    core = coqlib.parent / "coq-core"
    files = [Path(coqc), Path(coqdep), BIN / "spec-check", BIN / "sandbox-exec",
             TOOLS / "worker.py", TOOLS / "check.py", TOOLS / "ci_policy.py", POLICY_FILE]
    files += sorted(coqlib.rglob("*.vo")) + sorted(core.rglob("*.cmxs"))
    if Path("/etc/ocamlfind.conf").exists():
        files.append(Path("/etc/ocamlfind.conf"))
    files += sorted(Path("/etc/ocamlfind.conf.d").glob("*"))
    state = hashlib.sha256()
    for path in files:
        state.update(encoded([str(path), digest(path)]))
    return {"version": VERSION, "coqc": coqc, "coqdep": coqdep,
            "coqlib": str(coqlib), "fingerprint": state.hexdigest()}


class Sandbox:
    def __init__(self, limits):
        if os.getuid() == 0 or os.geteuid() == 0:
            raise Rejected("Run proof checking as a non-root OS user; root bypasses process-count limits")
        self.limits = limits
        self.bwrap = command("bwrap")

    def run(self, argv, mounts, *, compiler_worker=False):
        limits = self.limits
        args = [self.bwrap, "--unshare-all", "--unshare-user", "--die-with-parent", "--new-session",
                "--disable-userns", "--assert-userns-disabled", "--cap-drop", "ALL",
                "--clearenv", "--setenv", "PATH", "/usr/bin:/bin",
                "--setenv", "HOME", "/tmp", "--setenv", "TMPDIR", "/tmp",
                "--setenv", "LANG", "C.UTF-8", "--setenv", "OCAMLRUNPARAM", "b=0"]
        for directory in ["/usr/bin", "/usr/lib", "/usr/share", "/usr/lib64"]:
            if Path(directory).exists():
                args += ["--ro-bind", directory, directory]
        for config in ["/etc/ocamlfind.conf", "/etc/ocamlfind.conf.d"]:
            if Path(config).exists():
                args += ["--ro-bind", config, config]
        for target in ["bin", "lib", "lib64"]:
            args += ["--symlink", "usr/" + target, "/" + target]
        args += ["--proc", "/proc", "--dev", "/dev", "--size", str(16 * 1024**2),
                 "--tmpfs", "/tmp", "--size", str(limits["work_mib"] * 1024**2),
                 "--tmpfs", "/work", "--dir", "/tool"]
        for name in ["spec-check", "sandbox-exec"]:
            args += ["--ro-bind", str(BIN / name), "/tool/" + name]
        args += ["--ro-bind", str(TOOLS / "worker.py"), "/tool/worker.py"]
        for host, target in mounts:
            args += ["--ro-bind", str(host), target]
        args += ["--chdir", "/work", "--remount-ro", "/", "--"]
        if not compiler_worker:
            args += ["/tool/sandbox-exec", str(limits["cpu_seconds"]),
                     str(limits["memory_mib"]), str(limits["artifact_mib"])]
        args += argv

        def set_limits():
            resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
            amount = limits["memory_mib"] * 1024**2
            resource.setrlimit(resource.RLIMIT_AS, (amount, amount))
            resource.setrlimit(resource.RLIMIT_CPU, (limits["cpu_seconds"], limits["cpu_seconds"]))
            resource.setrlimit(resource.RLIMIT_FSIZE,
                               (limits["artifact_mib"] * 1024**2,) * 2)

        process = subprocess.Popen(args, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, start_new_session=True,
                                   close_fds=True, preexec_fn=set_limits, env={})
        output, errors = bytearray(), bytearray()
        capacity = ((limits["artifact_mib"] * 1024**2 * 4 // 3 + 65536)
                    if compiler_worker else limits["log_mib"] * 1024**2)
        end = time.monotonic() + limits["wall_seconds"]
        try:
            with selectors.DefaultSelector() as selector:
                selector.register(process.stdout, selectors.EVENT_READ, output)
                selector.register(process.stderr, selectors.EVENT_READ, errors)
                while selector.get_map():
                    remaining = end - time.monotonic()
                    if remaining <= 0:
                        raise Rejected("Sandbox wall time limit exceeded")
                    for key, _ in selector.select(min(remaining, 0.1)):
                        chunk = os.read(key.fileobj.fileno(), 65536)
                        if not chunk:
                            selector.unregister(key.fileobj)
                            continue
                        key.data.extend(chunk)
                        bound = capacity if key.data is output else limits["log_mib"] * 1024**2
                        if len(key.data) > bound:
                            raise Rejected("Sandbox output limit exceeded")
                process.wait(timeout=max(0.01, end - time.monotonic()))
            if process.returncode:
                # Never interpret compiler output as acceptance or a context summary.
                raise Rejected("Sandbox command failed: " + errors.decode("utf-8", errors="replace")[-8192:])
            return bytes(output)
        finally:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            process.stdout.close()
            process.stderr.close()


def library_roots(bundle):
    return [["/bundle/libraries/" + name, name] for name in ["CoqCP", "Generated", "GeneratedExamples"]
            if (bundle / "libraries" / name).exists()]


def compile_sources(inputs, sources, namespace, bundle, runtime, sandbox):
    config = dict(sandbox.limits, sources=sources, namespace=namespace,
                  coqc=runtime["coqc"], coqdep=runtime["coqdep"], roots=library_roots(bundle))
    if namespace == "Submission":
        config["roots"].append(["/bundle/spec", "Trusted"])
    (inputs / "build.json").write_bytes(encoded(config))
    raw = sandbox.run(["/usr/bin/python3", "-I", "/tool/worker.py"],
                      [(inputs, "/inputs"), (bundle, "/bundle")], compiler_worker=True)
    result = json.loads(raw)
    expected = {Path(name).with_suffix(".vo").name for name in sources}
    if set(result) != {"artifacts"} or set(result["artifacts"]) != expected:
        raise Rejected("Unexpected compiler artifact manifest")
    artifacts = {}
    for name, data in result["artifacts"].items():
        artifacts[name] = base64.b64decode(data, validate=True)
    if sum(map(len, artifacts.values())) > sandbox.limits["artifact_mib"] * 1024**2:
        raise Rejected("Compiled artifacts exceed limit")
    return artifacts


def kernel_check(bundle, artifacts, runtime, sandbox, allowed, *, spec_only=False):
    if not set(allowed).issubset(trusted_axioms()):
        raise Rejected("Axiom policy exceeds the evaluator-owned CI trust set")
    args = ["/tool/spec-check"]
    coqlib = runtime["coqlib"]
    roots = [[coqlib + "/theories", "Coq"], [coqlib + "/user-contrib", ""]]
    roots += library_roots(bundle) + [["/bundle/spec", "Trusted"]]
    mounts = [(bundle, "/bundle")]
    if spec_only:
        args += ["--spec-only"]
    else:
        roots += [["/artifacts", "Submission"]]
        mounts.append((artifacts, "/artifacts"))
        for path in sorted(artifacts.glob("*.vo")):
            args += ["--library", "Submission." + path.stem]
    for physical, logical in roots:
        args += ["--root", physical, logical]
    for axiom in allowed:
        args += ["--allow-axiom", axiom]
    report = json.loads(sandbox.run(args, mounts))
    if report.get("status") != ("spec-checked" if spec_only else "accepted"):
        raise Rejected("Unexpected kernel checker response")
    return report


def snapshot_libraries(bundle):
    tokens = (REPO / "_CoqProject").read_text().split()
    mappings, sources = [], []
    index = 0
    while index < len(tokens):
        if tokens[index] in ["-R", "-Q"]:
            mappings.append((Path(tokens[index + 1]), tokens[index + 2]))
            index += 3
        else:
            if tokens[index].endswith(".v"):
                sources.append(Path(tokens[index]))
            index += 1
    for source in sources:
        for physical, logical in mappings:
            if source.is_relative_to(physical):
                target = bundle / "libraries" / logical / source.relative_to(physical).with_suffix(".vo")
                target.parent.mkdir(parents=True, exist_ok=True)
                compiled = REPO / source.with_suffix(".vo")
                if not compiled.exists():
                    raise Rejected(f"Missing trusted library {compiled}; build the project first")
                target.write_bytes(read_regular(compiled, 64 * 1024**2))
                break


def file_manifest(directory):
    return {str(path.relative_to(directory)): digest(path)
            for path in sorted(directory.rglob("*"))
            if path.is_file() and path != directory / "manifest.json"}


def prepare(spec, bundle, runtime, sandbox, allowed):
    if not set(allowed).issubset(trusted_axioms()):
        raise Rejected("Axiom policy exceeds the evaluator-owned CI trust set")
    bundle.parent.mkdir(parents=True, exist_ok=True)
    bundle.mkdir(mode=0o700)  # Refuse to overwrite an existing specification.
    try:
        snapshot_libraries(bundle)
        (bundle / "spec").mkdir()
        source = read_regular(spec, 8 * 1024**2)
        with tempfile.TemporaryDirectory(prefix="spec-input-") as temporary:
            inputs = Path(temporary)
            (inputs / "Spec.v").write_bytes(source)
            compiled = compile_sources(inputs, ["Spec.v"], "Trusted", bundle, runtime, sandbox)
        (bundle / "spec/Spec.v").write_bytes(source)
        (bundle / "spec/Spec.vo").write_bytes(compiled["Spec.vo"])
        policy = kernel_check(bundle, None, runtime, sandbox, allowed, spec_only=True)
        manifest = dict(format=1, toolchain=runtime, allowed_axioms=sorted(set(allowed)),
                        ci_trusted_axioms=trusted_axioms(),
                        specification="Trusted.Spec.SOLUTION", implementation="Submission.Candidate.Implementation",
                        files=file_manifest(bundle), baseline=policy)
        manifest_bytes = encoded(manifest)
        (bundle / "manifest.json").write_bytes(manifest_bytes)
        return hashlib.sha256(manifest_bytes).hexdigest()
    except BaseException:
        shutil.rmtree(bundle)
        raise


def validate_bundle(bundle, spec_id, runtime):
    manifest_bytes = read_regular(bundle / "manifest.json", 2 * 1024**2)
    if hashlib.sha256(manifest_bytes).hexdigest() != spec_id:
        raise Rejected("Specification ID mismatch: use the evaluator's original ID")
    manifest = json.loads(manifest_bytes)
    if manifest["format"] != 1 or manifest["toolchain"] != runtime:
        raise Rejected("Toolchain changed since the specification was frozen; prepare a new bundle")
    if (manifest["ci_trusted_axioms"] != trusted_axioms()
            or not set(manifest["allowed_axioms"]).issubset(trusted_axioms())):
        raise Rejected("Frozen policy exceeds the evaluator-owned CI trust set")
    for path in bundle.rglob("*"):
        if path.is_symlink() or not (path.is_dir() or path.is_file()):
            raise Rejected("Specification bundle contains a symlink or special file")
    if file_manifest(bundle) != manifest["files"]:
        raise Rejected("Frozen specification bundle was modified")
    return manifest


def evaluate(bundle, spec_id, submission, output, runtime, sandbox):
    # Snapshot the whole frozen bundle before starting any untrusted process.
    validate_bundle(bundle, spec_id, runtime)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.mkdir(mode=0o700)
    report = dict(status="rejected", spec_id=spec_id, sandbox="bubblewrap+seccomp",
                  limits=sandbox.limits, toolchain_fingerprint=runtime["fingerprint"])
    try:
        with tempfile.TemporaryDirectory(prefix="evaluate-") as temporary:
            frozen = Path(temporary) / "bundle"
            shutil.copytree(bundle, frozen, symlinks=True)
            policy = validate_bundle(frozen, spec_id, runtime)
            inputs = output / "sources"
            inputs.mkdir()
            total = 0
            sources = []
            for path in sorted(submission.iterdir()):
                if not NAME.fullmatch(path.name):
                    raise Rejected("Submissions contain only top-level .v source files")
                data = read_regular(path, 8 * 1024**2)
                total += len(data)
                if total > 8 * 1024**2 or len(sources) >= 64:
                    raise Rejected("Submission exceeds source size/count limit")
                (inputs / path.name).write_bytes(data)
                sources.append(path.name)
            if "Candidate.v" not in sources:
                raise Rejected("Submission must contain Candidate.v")
            report["sources"] = {name: digest(inputs / name) for name in sources}
            report["stage"] = "compilation"
            compiled = compile_sources(inputs, sources, "Submission", frozen, runtime, sandbox)
            artifacts = output / "artifacts"
            artifacts.mkdir()
            for name, data in compiled.items():
                (artifacts / name).write_bytes(data)
            report["artifacts"] = file_manifest(artifacts)
            report["stage"] = "kernel-and-contract"
            report.update(kernel_check(frozen, artifacts, runtime, sandbox, policy["allowed_axioms"]))
            report["specification"] = policy["specification"]
            report["implementation"] = policy["implementation"]
            report["stage"] = "complete"
    except (Rejected, OSError, ValueError, subprocess.SubprocessError) as error:
        report["reason"] = str(error)
    (output / "report.json").write_bytes(encoded(report) + b"\n")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    sub.add_parser("build", help="Build the standalone kernel gate and sandbox helper")
    freeze = sub.add_parser("prepare", help="Freeze an evaluator-controlled Spec.v and its policy")
    freeze.add_argument("--spec", type=Path, required=True)
    freeze.add_argument("--bundle", type=Path, required=True)
    freeze.add_argument("--axiom-policy", choices=["none", "ci"], default="none",
                        help="No axioms (default), or exactly the set already trusted by project CI")
    check = sub.add_parser("check", help="Compile and check a source-only submission")
    check.add_argument("--bundle", type=Path, required=True)
    check.add_argument("--spec-id", required=True, help="ID recorded by the evaluator at preparation")
    check.add_argument("--submission", type=Path, required=True)
    check.add_argument("--output", type=Path, required=True, help="New directory for artifacts and report")
    for child in [freeze, check]:
        for name, default in DEFAULT_LIMITS.items():
            child.add_argument("--" + name.replace("_", "-"), type=int, default=default)
    args = parser.parse_args()
    try:
        if args.action == "build":
            build()
            print(json.dumps({"status": "built", "directory": str(BIN)}))
            return 0
        limits = {name: getattr(args, name) for name in DEFAULT_LIMITS}
        if any(value <= 0 for value in limits.values()):
            raise Rejected("All resource limits must be positive")
        ensure_built()
        runtime, sandbox = toolchain(), Sandbox(limits)
        if args.action == "prepare":
            allowed = trusted_axioms() if args.axiom_policy == "ci" else []
            spec_id = prepare(args.spec.resolve(), args.bundle.absolute(), runtime, sandbox, allowed)
            print(json.dumps({"status": "prepared", "spec_id": spec_id, "bundle": str(args.bundle.absolute())}))
            return 0
        report = evaluate(args.bundle.absolute(), args.spec_id, args.submission.absolute(),
                          args.output.absolute(), runtime, sandbox)
        print(json.dumps(report, sort_keys=True))
        return 0 if report["status"] == "accepted" else 1
    except (Rejected, OSError, ValueError, subprocess.SubprocessError) as error:
        print(json.dumps({"status": "rejected", "reason": str(error)}))
        return 1


if __name__ == "__main__":
    sys.exit(main())
