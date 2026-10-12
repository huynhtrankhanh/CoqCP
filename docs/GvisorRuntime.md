# Native proof checking with gVisor

The adversarial sandbox runs the pinned native Rocq compiler and the
independent kernel gate in fresh gVisor containers. It preserves the existing
formal execution model, frozen specification IDs, module-subtyping check,
axiom audit, statically approved tactics, and Rocq VM conversion. Native code
conversion, dynamic ML plugins, asynchronous proofs, and subprocesses from
submitted code remain disabled.
Each process sets `OCAMLRUNPARAM=b=0,d=1`: Rocq's single-domain execution does
not need OCaml's default reservation for many possible domains, which can exceed
the bounded virtual address space even before a proof starts. OCaml system
threads remain available.

## Provisioning

Follow [AdversarialChecking.md](AdversarialChecking.md) to install the native
proof toolchain, Docker, and `libseccomp-dev`. Run
`bash tools/install-gvisor.sh`, then `python3 tools/adversarial/check.py build`.
Build trusted project libraries with `make -j2` before preparing a specification
or running `examples.py`.

The installer downloads checksum-pinned gVisor `release-20261005.0`, including
the sidecar binaries required by current releases. It installs them under
`/opt/rocq/gvisor`, preserves other Docker daemon settings, and registers:

```json
{
  "coqcp-gvisor": {
    "path": "/opt/rocq/gvisor/runsc",
    "runtimeArgs": [
      "--platform=systrap",
      "--network=none",
      "--gvisor-marker-file=true"
    ]
  }
}
```

The installer restarts Docker. Run it on the evaluator machine before accepting
jobs. The non-root evaluator user needs access to the local Docker daemon;
GitHub-hosted Ubuntu runners already have that access. The guest never receives
the Docker socket. `systrap` needs no `/dev/kvm` or nested virtualization; upstream
[recommends it for virtual machines](https://gvisor.dev/docs/user_guide/platforms/).
See [gVisor installation](https://gvisor.dev/docs/user_guide/install/) for the
multi-file distribution and [Docker setup](https://gvisor.dev/docs/user_guide/quick_start/docker/).

The runtime image contains Python, GMP, and libseccomp. Its default base is
digest-pinned Ubuntu 24.04, matching the GitHub Actions runner where the native
toolchain is built. A toolchain built on another distribution needs a compatible
libc in its runtime image. Evaluators can build the same Dockerfile with
`--build-arg BASE_IMAGE=<compatible image digest>`, retaining the fixed tag
`coqcp-gvisor:rocq-9.3.0`. The checker freezes the resulting immutable image ID,
so changing the image requires new specification bundles.

## Execution and trust

`gvisor_backend.py` validates the configured runtime path and exact flags, hashes
runsc and every installed sidecar, and resolves the runtime image to its immutable
ID. These identities participate in the toolchain fingerprint. A probe exercises
the complete sandbox profile before submitted code is read. The trusted guest
entry point also verifies `/proc/gvisor/kernel_is_gvisor` and a non-root UID;
a plain-container fallback cannot pass that check.

Only installed toolchain directories, the installed OCaml standard-library
directory, evaluator executables, and explicit inputs are bound read-only.
The standard library is located through the pinned OCamlfind configuration and
fingerprinted too; system-compiler switches may install it under `/usr/lib`.
The guest has a read-only root and `/dev`, bounded
tmpfs mounts for `/work` and `/tmp`, no network, no capabilities, and no new
privileges. There are no writable host mounts. Docker limits total container
memory and tasks; seccomp and resource limits constrain each tool. CPU allocation
is capped at one core; per-process CPU limits and the host wall deadline bound
the entire compilation/checking operation.

The trusted worker can spawn compiler processes. It disables dumpability, checks
all previously captured `.vo` bytes between compilations, and publishes each
artifact only after its compiler exits. Compiler children cannot fork, open
sockets, trace or signal the worker, or create executable memory after lockdown.
The kernel gate runs in a separate container with submitted artifacts read-only;
compiler diagnostics are never treated as acceptance.

Each invocation uses a unique container name. The supervisor bounds stdout,
stderr, and wall time and forcibly removes the container on success, failure,
timeout, or output overflow. This removes guest descendants as well; killing
only the Docker client would leave daemon-owned work running. Cleanup failure
rejects the operation.

The trusted computing base includes the native OCaml runtime, Rocq kernel and VM,
approved tactic plugins, gVisor, the runtime image, Docker, and the evaluator OS.
Isolation reduces submitted code's access; it does not prove those components
correct. The formal program model is preserved; gVisor's application kernel
and native compiler restrictions enforce isolation.

## CI and validation

`.github/actions/setup-gvisor` restores the native proof toolchain, installs
gVisor, builds the runtime image and native gate. Both adversarial CI jobs build
trusted project libraries. The first runs acceptance, containment, actual plugin
payload, VM, and executable-memory regressions. The second checks every complete
candidate proof chain and uploads bundles, reports, and artifacts.

```sh
python3 -m unittest discover -s tools/adversarial/tests -v
python3 tools/adversarial/examples.py --output .verification/gvisor-examples
```

Native runs recompile candidates and independently recheck all artifacts. They
reuse installed libraries but do not reuse candidate compilation results or
kernel verdicts.
