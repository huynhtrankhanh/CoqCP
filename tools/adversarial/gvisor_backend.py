"""Native Rocq in fresh, bounded gVisor containers; never fall back to runc."""
import os
from pathlib import Path
import secrets
import selectors
import signal
import subprocess
import time


RUNTIME = "coqcp-gvisor"
INSTALL = Path("/opt/rocq/gvisor")
IMAGE = "coqcp-gvisor:rocq-9.3.0"
RUNTIME_ARGS = ["--platform=systrap", "--network=none", "--gvisor-marker-file=true"]


def docker(gate):
    # Always use the local evaluator daemon, regardless of DOCKER_HOST/context.
    return [gate.command("docker"), "--host=unix:///var/run/docker.sock"]


def query(gate, args):
    try:
        result = subprocess.run(docker(gate) + args, env={}, stdin=subprocess.DEVNULL,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=30, check=True)
    except (OSError, subprocess.SubprocessError) as error:
        raise gate.Rejected("No safe condition for sandbox: Docker/gVisor unavailable: " +
                            str(error)) from error
    return gate.decoded(result.stdout, "gVisor runtime identity")


def identity(gate):
    runtimes = query(gate, ["info", "--format", "{{json .Runtimes}}"])
    expected = {"path": str(INSTALL / "runsc"), "runtimeArgs": RUNTIME_ARGS}
    actual = runtimes.get(RUNTIME, {}) if isinstance(runtimes, dict) else {}
    if any(actual.get(key) != value for key, value in expected.items()):
        raise gate.Rejected("No safe condition for sandbox: evaluator gVisor runtime changed; "
                            "run tools/install-gvisor.sh")
    if not (INSTALL / "runsc").is_file() or not (INSTALL / "gvisor-bin").is_dir():
        raise gate.Rejected("No safe condition for sandbox: incomplete gVisor installation")
    image = query(gate, ["image", "inspect", IMAGE, "--format", "{{json .Id}}"])
    if not isinstance(image, str) or not image.startswith("sha256:"):
        raise gate.Rejected("Invalid evaluator gVisor image identity")
    return {"image": image, "runtime": expected,
            "files": {str(path.relative_to(INSTALL)): gate.digest(path)
                      for path in sorted(INSTALL.rglob("*")) if path.is_file()}}


def ocaml_stdlib(gate):
    env = {"PATH": str(gate.TOOLCHAIN / "bin") + ":/usr/bin:/bin",
           "OCAMLPATH": str(gate.TOOLCHAIN / "lib"),
           "OCAMLFIND_CONF": str(gate.TOOLCHAIN / "lib/findlib.conf")}
    root = Path(subprocess.check_output([gate.command("ocamlfind"), "printconf", "stdlib"],
                                       env=env, timeout=10).decode().strip()).resolve()
    if not root.is_dir() or not (root.is_relative_to(gate.TOOLCHAIN / "lib") or
                                root.is_relative_to(Path("/usr/lib"))):
        raise gate.Rejected("OCaml standard library must be in the installed runtime")
    return root


class GvisorSandbox:
    def __init__(self, gate, limits, runtime=None):
        self.gate = gate
        self.limits = limits
        self.name = "gvisor+seccomp"
        self.network_isolation = "none+seccomp"
        if os.getuid() == 0 or os.geteuid() == 0:
            raise gate.Rejected("Run proof checking as a non-root OS user")
        current = identity(gate)
        if runtime is not None and runtime.get("sandbox_identity") != current:
            raise gate.Rejected("gVisor runtime changed since the specification was frozen")
        self.image = current["image"]
        self.stdlib = (Path(runtime["ocaml_stdlib"]) if runtime is not None
                       else ocaml_stdlib(gate))
        # Exercise the complete profile (marker, non-root user, limits, seccomp,
        # mounts and read-only filesystem) before touching submission code.
        self.run(["/usr/bin/true"], [])

    def arguments(self, name, argv, mounts, compiler_worker):
        gate, limits = self.gate, self.limits
        args = docker(gate) + [
            "create", "--name", name, "--runtime=" + RUNTIME, "--pull=never",
            "--network=none", "--read-only", "--cap-drop=ALL",
            "--security-opt=no-new-privileges", f"--user={os.getuid()}:{os.getgid()}",
            "--pids-limit=256", "--memory=" + str(limits["memory_mib"]) + "m",
            "--memory-swap=" + str(limits["memory_mib"]) + "m", "--cpus=1",
            "--ipc=none", "--log-driver=none", "--workdir=/work",
            "--env=OCAMLRUNPARAM=b=0,d=1",
            "--ulimit=core=0:0", "--ulimit=nofile=128:128", "--ulimit=nproc=256:256",
            "--tmpfs", f"/work:rw,nosuid,nodev,noexec,size={limits['work_mib']}m,mode=700,uid={os.getuid()},gid={os.getgid()}",
            "--tmpfs", f"/tmp:rw,nosuid,nodev,noexec,size=16m,mode=700,uid={os.getuid()},gid={os.getgid()}",
            "--tmpfs", "/dev:ro,nosuid,noexec,size=64k",
            "--entrypoint=/usr/bin/python3",
        ]
        bindings = []
        for directory in ["bin", "lib", "libexec", "share"]:
            path = gate.TOOLCHAIN / directory
            if path.exists():
                bindings.append((path, str(path)))
        # System-compiler switches can keep builtin package metadata outside
        # the opam switch. Include only that installed OCaml runtime directory.
        if not self.stdlib.is_relative_to(gate.TOOLCHAIN / "lib"):
            bindings.append((self.stdlib, str(self.stdlib)))
        bindings += [(gate.BIN / binary, "/tool/" + binary) for binary in gate.BINARIES]
        bindings += [(gate.TOOLS / filename, "/tool/" + filename)
                     for filename in ["worker.py", "gvisor_entry.py"]]
        bindings += list(mounts)
        for host, target in bindings:
            host = Path(host).resolve()
            # Docker's --mount syntax has no escaping for comma-delimited paths.
            if "," in str(host) or "," in target:
                raise gate.Rejected("Sandbox mount paths cannot contain commas")
            args += ["--mount", f"type=bind,src={host},dst={target},readonly,bind-recursive=disabled"]
        prefix = ["/tool/sandbox-exec"]
        if compiler_worker:
            prefix += ["--worker"]
        prefix += [str(limits["cpu_seconds"]), str(limits["memory_mib"]),
                   str(limits["artifact_mib"])]
        return args + [self.image, "-I", "/tool/gvisor_entry.py", *prefix, *argv]

    def run(self, argv, mounts, *, compiler_worker=False):
        gate, limits = self.gate, self.limits
        name = "coqcp-" + secrets.token_hex(16)
        args = self.arguments(name, argv, mounts, compiler_worker)
        process = None
        end = time.monotonic() + limits["wall_seconds"]
        output, errors = bytearray(), bytearray()
        capacity = (limits["artifact_mib"] * 1024**2 * 4 // 3 + 65536
                    if compiler_worker else limits["log_mib"] * 1024**2)
        try:
            # Complete creation before attaching: cleanup can then address a
            # known container, including when Docker's attach client is killed.
            created = subprocess.run(args, env={}, stdin=subprocess.DEVNULL,
                                     stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                     timeout=min(30, limits["wall_seconds"]))
            if created.returncode:
                raise gate.Rejected("No safe condition for sandbox: " +
                                    created.stderr.decode(errors="replace")[-8192:])
            process = subprocess.Popen(docker(gate) + ["start", "--attach", name],
                                       env={}, stdin=subprocess.DEVNULL,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                       start_new_session=True, close_fds=True)
            with selectors.DefaultSelector() as selector:
                selector.register(process.stdout, selectors.EVENT_READ, output)
                selector.register(process.stderr, selectors.EVENT_READ, errors)
                while selector.get_map():
                    remaining = end - time.monotonic()
                    if remaining <= 0:
                        raise gate.Rejected("Sandbox wall time limit exceeded")
                    for selected, _ in selector.select(min(remaining, 0.1)):
                        chunk = os.read(selected.fileobj.fileno(), 65536)
                        if not chunk:
                            selector.unregister(selected.fileobj)
                            continue
                        selected.data.extend(chunk)
                        bound = capacity if selected.data is output else limits["log_mib"] * 1024**2
                        if len(selected.data) > bound:
                            raise gate.Rejected("Sandbox output limit exceeded")
                process.wait(timeout=max(0.01, end - time.monotonic()))
            if process.returncode:
                reason = errors.decode("utf-8", errors="replace")[-8192:]
                prefix = ("No safe condition for sandbox: " if process.returncode in (125, 126, 127)
                          else "Sandbox command failed: ")
                raise gate.Rejected(prefix + reason)
            return bytes(output)
        except (OSError, subprocess.SubprocessError) as error:
            if isinstance(error, subprocess.TimeoutExpired):
                raise gate.Rejected("Sandbox wall time limit exceeded") from error
            raise gate.Rejected("No safe condition for sandbox: " + str(error)) from error
        finally:
            # Killing the Docker client does not kill a daemon-owned container.
            # Remove the named container first, including all guest descendants.
            try:
                cleanup = subprocess.run(docker(gate) + ["rm", "--force", name], env={},
                                         stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                         stderr=subprocess.PIPE, timeout=15)
                missing = any(message in cleanup.stderr.lower()
                              for message in (b"no such container", b"no such object"))
                if cleanup.returncode and not missing:
                    raise gate.Rejected("Cannot remove gVisor sandbox: " +
                                        cleanup.stderr.decode(errors="replace")[-1024:])
            except (OSError, subprocess.SubprocessError) as error:
                raise gate.Rejected("Cannot remove gVisor sandbox: " + str(error)) from error
            finally:
                if process is not None:
                    if process.poll() is None:
                        os.killpg(process.pid, signal.SIGKILL)
                        process.wait()
                    process.stdout.close()
                    process.stderr.close()

    def close(self):
        # Every run owns and removes its container, including on rejection.
        pass
