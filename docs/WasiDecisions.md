# WASI implementation decision record

This records the technical choices behind the portable adversarial checker,
including compatibility work and approaches that were tried and abandoned.
[WasiRuntime.md](WasiRuntime.md) explains operation and troubleshooting;
[AdversarialChecking.md](AdversarialChecking.md) defines the checking contract.
The implementation and pinned dependencies are the authority for exact values.

## Execution boundary and trusted code

| Decision | Reason and consequence |
| --- | --- |
| Make WASI the default; retain explicit `--backend bubblewrap` | CI can forbid user namespaces required by bubblewrap. Existing native deployments can still select their original backend. |
| Execute evaluator-owned Rocq bytecode embedded in a C runtime compiled to Wasm | Preserve Rocq's compiler and kernel semantics while changing their execution boundary. Submissions supply proof source and serialized proof artifacts, never executable Wasm or native plugins. |
| Use Wasmtime with a small custom WASI preview1 host | Rocq needs filesystem and runtime services, but none need to reach a host directory. Implementing the used imports makes the capability boundary explicit and testable. It also makes these bindings trusted code that needs review. |
| Preserve independent kernel checking, frozen specification IDs, and axiom policy | Isolation cannot establish logical validity. Successful compilation alone never accepts a proof. All candidate helpers are audited, including helpers unused by the entry point. |
| Link only policy-approved tactic plugins statically | Approved tactics remain available without a dynamic native-code loader. The trusted build excludes libraries declaring other plugins and their transitive dependents. Direct unapproved declarations fail in the compiler. |
| Disable native compilation, asynchronous proof workers, and translated effect handlers in the translated prototype | These rely on unsupported native machinery or complicate isolation. Dynamic native loading remains outside the allowed capabilities. |
| Reject VM disablement as the final portability strategy | The initial translated prototype uses standard reduction instead of Rocq's C bytecode VM. It still checks proofs, but reflection-heavy cold proofs exceed reasonable budgets. On 2026-10-09 the requested trust model explicitly includes the kernel and VM. Preserving VM evaluation is now a requirement; increasing example timeouts is not a substitute. |
| Compile the existing C VM and OCaml C runtime together to WASI | Their shared linear-memory object representation avoids rewriting Rocq's evaluator. A local OCaml 5.4.0/WASI SDK 34 probe runs exceptions, cyclic Marshal data and GC. The unchanged Rocq 9.3 C VM passes constants, closures, Uint63 addition and a 200,000-node constructor chain across GC. Full Rocq also compiles a `vm_compute` proof and a 131,072-node computation, and rejects a false equality. The repository builder reproduces embedded WASM executables. The full acceptance suite passes; complete-example validation is recorded below. |
| Set aside an OCaml rewrite of the VM | A translation of the instruction interpreter adds evaluator maintenance and correctness burden. It reached compilation, but was not accepted as a validated runtime. The existing-C route now has executable evidence and is preferred. |
| Enable Wasm exceptions and tail calls; disable Wasm GC and multiple memories | The C runtime uses SDK exception handling and one linear memory. Disable Wasm threads, memory64, and stack switching to avoid unused capabilities. |
| Deserialize AOT code only from evaluator-owned runtime paths | Wasmtime AOT deserialization assumes trusted code. Candidate `.vo` data goes to Rocq's loader, never to Wasmtime's code deserializer. |

WASI reduces the kernel interface available to the guest. It does not remove
the OS kernel, Wasmtime, Rocq, or host bindings from the trusted implementation.
The security claim is capability confinement plus independent proof checking,
not that Wasm makes every compiler or runtime bug harmless.

## Build, packaging, and CI

| Decision | Reason and consequence |
| --- | --- |
| Use Docker only to build and export the host | GitHub Actions can build with Docker even when proof sandbox namespace setup is restricted. After export, checking invokes an ordinary executable and needs neither a container daemon nor privileged container execution. |
| Save the exported host immediately after its build | Use separate host restore/save actions inside provisioning, so a later regression or proof failure cannot discard a successfully built Docker export. Exact hits skip both Docker and the redundant host save. |
| Package Python bindings and the stock Wasmtime wheel with PyInstaller in directory mode | The runner needs a standalone host without a separate Python environment. The executable and `_internal` directory must travel together. Directory mode avoids extraction on each host startup. |
| Retire the prototype's custom Wasmtime build | The original OCaml collector handles Rocq's cyclic objects in linear memory. Wasmtime GC patches and Rust compilation are unnecessary for the C runtime. |
| Target Linux x86-64 and Ubuntu 24.04 | This matches the workflow runner and ABI. Other architectures and operating systems need separate artifacts and validation. |
| AOT compile the three evaluator modules once | Runtime compilation is expensive. Generic x86-64 code avoids depending on the build machine's optional CPU extensions. Runtime images remain bound to actual host bytes and engine configuration. |
| Use `speed_and_size`, disable parallel JIT compilation, and build with two compiler jobs | The large compiler module makes provisioning memory substantial. These choices bound peak pressure on CI; they trade some build speed for memory. |
| Use three CI cache layers | The Docker host, `/opt/rocq` toolchain, and runtime/proof artifacts change for different reasons. A hit can avoid rebuilding the expensive layer without granting acceptance to stale proof results. |
| Separate CI regressions and complete examples into dependent jobs | A cold runtime build, independent regression audits, and eight full proof chains should not compete for one six-hour job budget. The example job restores the completed regression job's host, toolchain and proof work through the shared `setup-wasi` composite action. Each job still has its own six-hour limit. |
| Include pins, source, policy, platform, and replacement proof in relevant workflow keys | Cache lookup should follow build inputs. Restore the closest proof cache first, then fall back to one for the same platform. Internal runtime, source, resource and observation validation decides which entries remain usable, including after scanner-only changes. |
| Store example configuration in versioned JSON with an independent JSON Schema | Names, source paths, axiom-policy choices, and complete named resource profiles belong to data, while Python handles orchestration. Validate before provisioning; reject duplicate names, unknown profiles, missing files, and repository escapes. The dependency-free loader implements only the schema keywords used here, rejects unsupported keywords and remote references, and permits external tooling to use a full validator. CI watches and hashes both documents. Actual selected source, limits, and frozen policy remain the semantic cache inputs. |
| Serialize C archive construction and keep runtime/library build locks separate | Coordinators share provisioned artifacts, so each build stage needs serialization. The shared C archive also has its own lock, including trusted test-program builds. Patches reject reversal and fuzz. Proof invocation workers remain independent after provisioning. |
| Reuse an immutable base snapshot with per-module overlays | The shared toolchain/bundle need not be retransmitted for every changed source closure. Source and dependency bytes are overlaid onto a fresh filesystem for each invocation, never written into the cached base. Observations and visible inputs stay identical; fewer snapshots and repeated base transfers reduce batch transport and retention costs. |
| Retain the optional native test suite behind `COQCP_TEST_BUBBLEWRAP=1` | Native executable-memory and seccomp probes require that backend's OS facilities. WASI tests exercise capability isolation and static plugin enforcement directly. |

The runtime builder reuses Dune's build tree across entry-point changes. Pinned
source patches fail when their expected input disappears instead of silently
applying to an unknown release. WASI SDK and OCaml source archives have explicit SHA-256 checks.
The host uses pinned stock Wasmtime/PyInstaller packages. The native toolchain uses a pinned OCaml compiler package in CI.

CI proof caches use separate restore/save actions and save completed work even
when a later test or example fails. Each run/attempt/job gets a new immutable key;
restore prefixes prefer another completed job in the same run, then the same
implementation and source set, before broader fallbacks. Reused entries still
undergo local content and taint validation. The composite action forwards the
restore step's primary key to the caller for its final save, using GitHub's
[composite output interface](https://docs.github.com/en/actions/reference/workflows-and-actions/metadata-syntax#outputs-for-composite-actions).
This follows the [cache save action's failure-handling interface](https://github.com/actions/cache/blob/main/save/README.md).

## C runtime and VM port

| Decision | Reason and consequence |
| --- | --- |
| Compile the original C runtime and original Rocq C VM with WASI SDK 34 | Retain the existing evaluator and shared OCaml object representation. A pure OCaml VM rewrite was set aside. Pins are SHA-256 checked by `install_wasi_assets.py`. |
| Run Rocq's OCaml implementation as bytecode inside that C runtime | The C VM evaluates Gallina reductions; OCaml's separate bytecode interpreter runs Rocq's compiler, tactics and kernel. Restoring VM reflection does not remove this general interpretation cost. Cache complete validated work and measure cold proof timings separately. |
| Enable VM conversion and regenerate checker VM bytecode | The requested trust base includes the kernel and VM. Disabled-VM fallback caused excessive reflection costs. Set both the environment flag and upstream checker flag. The checker ignores stored VM metadata and recompiles from declarations before checking. Native machine-code conversion stays disabled. |
| Hoist minimum-scan's closed integer bounds into VM-checked lemmas | Repeated ordinary conversion of `Z.of_nat 500000`/`500001` traverses half a million unary successors. Compute each equality once with `vm_compute; reflexivity`, then rewrite it after `Nat2Z` transformations. All original bounds and theorem statements remain unchanged, and the independent checker must validate the VM casts with regenerated bytecode. Timed compilation commands for the revised module total 28.3 seconds including imports. |
| Query hidden declarations without repeatedly folding all globals | Global opaque dependencies have already entered the axiom set. Query a hidden functor constant using a singleton environment and the same upstream opaque table; union its dependencies into that set. This preserves the audit while avoiding a complete global scan per hidden declaration. |
| Give the independent checker a two-million-word nursery and 200-percent space overhead | On WASM32 the nursery is 8 MiB. Imported environments stay live while typechecking creates short-lived objects, so larger minor batches and less aggressive major collection reduce repeated tracing. Together with the audit change, an experimental cold Watermelon specification audit completed in 529 seconds where the previous checker exceeded its unchanged 600-second CPU bound. The production Watermelon pair now passes; cold certification retains every proof body and VM recompile. |
| Exclude checker images from compilation identity | Full runtime identity still includes both checker images and invalidates frozen bundles/kernel results. Compiler identity includes the actual compiler, host, policy and coordination code; a checker-only rebuild can reuse compilation without reusing acceptance. |
| Embed bytecode and its primitive table in each WASM module | Runtime hashes cover all executable inputs without a second external bytecode cache domain. The common C archive is reused across the three links. A tiny shared interpreter plus separate bytecode files was investigated; embedding avoids extra visibility and identity rules. |
| Enforce `-compat-32` at compilation and link time | Native host compilation must not introduce 64-bit OCaml ints into WASM32 data. Three unsigned hash masks use runtime Int32 conversion to preserve their upstream target semantics. Building a special cross compiler was investigated and proved unnecessary after compatibility checks passed. |
| Preserve OCaml's C compilation semantics | Compile the runtime, VM and C stubs with `-fwrapv` and `-fno-strict-aliasing`, retaining the upstream assumptions about signed arithmetic and tagged-value access. |
| Calibrate C interpreter fuel separately | A full arithmetic comparison used 2.38 billion fuel in 4.04 seconds; the old one-billion probe cap was too low. Use five billion for that test. Trusted compilation uses two trillion fuel while preserving its 600-second CPU, 1,200-second wall and 4-GiB memory bounds. The earlier 500-billion cap exhausted on `TwoWaysToFill.v`; only successful entries under stricter bounds can be reused. This is an instruction-count calibration, not a disabled-VM workaround. |
| Use the same two-trillion calibration for complete example proof chains | Watermelon's cold specification audit exhausted the earlier one-trillion fuel cap. Preserve the profiles' CPU, wall and memory bounds while adjusting the backend-specific instruction budget. This does not establish a cold-proof performance gain; the full audit must still finish within those time bounds. |
| Keep primitive assumptions subject to the existing axiom policy | Upstream's assumption report classifies primitive declarations as bodyless constants. The arithmetic regression requires successful Uint63/float VM compilation and then the expected policy rejection; the natural-number VM regression also passes complete acceptance. No new primitive or logical axiom is whitelisted. |
| Retain threaded interpreter dispatch | A local 20-million-iteration tail-call benchmark took 1.13 seconds and 3.13 billion fuel with computed-goto dispatch, versus 1.79 seconds and 6.37 billion fuel with switch dispatch. Switching was rejected. Fuel counts are backend-specific; these measurements are not full-proof timings. |
| Use the stock Wasmtime wheel in the Docker host | C exception, cyclic Marshal/GC and unchanged VM probes pass with the official 49.0.0 package and Wasm GC disabled. Python/PyInstaller packaging replaces custom Rust compilation. Cache the complete standalone artifact; Docker ends after export. |
| Replace the exported host directory completely after toolchain restore | A restored `/opt/rocq` may include an older packaged host. Remove that generated directory before copying the separately cached export, so obsolete shared libraries or prototype files cannot alter the host identity or runtime. |
| Disable Wasm GC and multi-memory | OCaml and libc share one linear memory and OCaml's original collector handles cyclic values. Replace the translated-GC stress test with a bounded original-OCaml-GC test retaining 32 MB while discarding a million cycles. |
| Restore original boxed float primitives | The C port can link Rocq's existing float routines. The OCaml replacements used for the translated prototype are unnecessary and have been removed. |
| Discover macro-generated primitive signatures through preprocessing | Original boxed float entrypoints are generated by C macros. Preprocess the VM sources with the same SDK exception and emulation flags, then extract signatures; reject unknown arities instead of guessing an indirect-call type. Only the three pinned unit-taking performance-counter declarations have explicit fallback signatures. |
| Keep ordinary GC scheduling during imports instead of `Gc.ramp_up` | The Rocq configuration wrapper calls its argument directly. OCaml 5.4 ramp-up defers collection work during the callback; this port keeps ordinary scheduling while loading potentially large proof graphs. This can trade loading speed for less deferred allocation pressure. Original collection and guest/process memory bounds remain active. |
| Keep original OCaml Marshal and tracing GC | C runtime objects live in linear memory. Existing cycle/sharing handling replaces the translated Marshal patch and avoids Wasm-GC object retention costs for Rocq data. |
| Use SDK setjmp/longjmp with modern WASM exceptions | Preserve OCaml's C exception machinery, with the documented SDK flags and library. Do not rewrite exception propagation. |
| Force exactly one OCaml domain | The SDK runtime is single-threaded. Fix both parameter parsing and domain initialization; reject thread creation. Parallel proof compilation uses independent Stores. |
| Use normal SDK mutexes | Error checking mutexes dereference the SDK's unavailable thread descriptor. Normal mutexes support this synchronous guest; attempts to block remain bounded by fuel/time limits. |
| Emulate memory reservation/commit inside guest linear memory | Reserve is read/write allocation, commit clears bytes, decommit retains allocation until unmap/destruction. No host mapping authority is introduced. This trades POSIX decommit savings for portability within explicit memory limits. |
| Limit the C stack to 2 MiB and module linear memory to 2 GiB | Keep known bounds for WASM32 runtime addressing and stack use. Guest, process, work-file and execution limits still apply. |
| Link a fixed subset of original Unix/Str/Num stubs | Filesystem services operate solely on virtual WASI nodes. Address parsing/allocation is pure and needed for Unix initialization. Network/process/dynamic-code primitives reject; their true arity avoids WASM call-type mismatches. |
| Supply inert thread setup, disabled counters and private file locking | Preserve synchronous module initialization without adding threads or cross-invocation mutable files. Locks are unnecessary for an invocation's private solver cache. |
| Add positional read/tell and deny poll/readlink host bindings | Positional reads record the same content observations and restore offsets. Readlink records lookup then rejects; polling is unavailable. There are no host directories, sockets or symlinks behind these imports. |
| Use only virtual environment variables | WASI has no OS privilege identities. Secure environment helpers read only coordinator-supplied values. |
| Treat the earlier translated runtime decisions below as historical | Marshal-header patches, WOCaml fallback control and Wasmtime tracing changes describe the earlier route. The C build uses original OCaml GC/Marshal. The final host uses the stock Wasmtime 49.0.0 wheel with Wasm GC/multi-memory disabled. Custom Rust compilation and translation-specific patches have been retired. |

## Portable Rocq and OCaml compatibility

This section records the earlier translated prototype and proof optimizations.
Its float replacements, Marshal patches and compiler fallback changes were
retired by the C port described above. The Num adapters and proof changes remain.

| Decision | Reason and consequence |
| --- | --- |
| Use Rocq's existing 31-bit integer and float representations | `wasm_of_ocaml` uses 31-bit OCaml integers. Translating native 64-bit `.vo` object graphs by truncation would corrupt values. Rebuild trusted sources with the same representation as candidate compilation. |
| Adapt the 31-bit host-build assertion | The bytecode is built on a 64-bit host but executed with portable integer semantics. Remove that build-host assertion while retaining the 31-bit implementation. |
| Replace unsupported float externals with OCaml operations | Portable multiplication, addition, subtraction, division, square root, and adjacent-float operations must not call native C stubs. |
| Use Num behind `Z`/`Q` adapters instead of native Zarith/GMP | Num supplies portable bignums. Preserve signed division conventions, bit operations, and rational canonicalization; compare representative operations against native Zarith in regressions. |
| Normalize rational values and print canonical rationals | Equivalent but unreduced fractions can balloon intermediate arithmetic certificates. Correct normalization also preserves expected equality and serialization behavior. |
| Replace the WASI Marshal identity map | Its linear searches scale poorly for large proof graphs. Temporary block-header markers provide fast identity lookup; physical-identity buckets handle values that cannot be marked. |
| Restore Marshal markers on both success and OCaml exceptions | Temporary markers must never remain in live OCaml objects. A Wasm trap destroys the Store, so that heap cannot be reused. Preserve cycles, physical sharing, and distinct equal objects without changing the wire format. |
| Disable the portable compiler's embedded precompiled-runtime fallback | The explicitly patched runtime must be used; silently selecting an upstream embedded image would bypass the intended serialization changes. |
| Make virtual `Unix.lockf` succeed without an OS lock | Solver cache files live in one private, synchronous invocation. No other guest can share them, so an OS lock adds no protection. This does not permit shared writable solver caches. |
| Trap unsupported dangerous primitives | Unsupported process/native services must fail rather than acquire host access or pretend a security-relevant operation succeeded. |
| Replace one trusted proof body with a pinned equivalent proof | `ZModOffset.smod_complement`'s nonlinear reflection certificate is prohibitively expensive under standard conversion. Sign cases and small linear certificates prove the same statement. The upstream file hash is checked; adapted bytes enter source cache keys and the replacement proof enters frozen runtime identity. |
| Reduce arithmetic contexts in the project bracket proof | Two groups of `TwoWaysToFill.v` side conditions retain only counting identities, even-length/division facts, position bounds, and strict count bounds before `lia`. Accumulated list proofs made reflection certificates expensive under standard conversion. Naming the strict bounds makes the retained dependencies explicit. The theorem statements stay unchanged; native and WASI compilation check the optimized proof. |
| Balance and filter Koxia's binary divisor certificate | A unary fuel counter of 31,594 overflows the portable standard reducer's call stack. A positive binary counter splits each range into adjacent halves and handles an odd final divisor separately, bounding recursion depth logarithmically. A proved filter skips multiples of 2, 3 and 5 after checking that none divides the modulus. Nested conditionals short-circuit, and parity uses the binary representation rather than division. Coverage and divisibility lemmas establish the same complete divisor interval; the exported primality theorem and modulus stay unchanged. |
| Prove Koxia residue membership for a symbolic modulus | Applying membership lemmas to the concrete residue range can expand nearly a billion unary successors during unification. Prove the range lemma with a variable modulus, instantiate it with the existing modulus, and use explicit `proj1`/`proj2` applications and map parameters at the remaining membership sites. Clear the unused list-membership hypotheses before arithmetic tactics. The residue list, modulus, and exported number-theory statements stay unchanged. The instrumented helper compilation completes in 10.8 seconds after the original exhausted two trillion fuel. |
| Avoid eager unary arithmetic in the DSU score proofs | The disabled VM falls back to eager standard reduction, which exhausts the Wasm stack while expanding intermediate unary scores. `lazy; reflexivity` computes the same closed witness equality on demand. For the upper bound, transfer the established natural inequality to binary integers and use checked conversion for its numeric endpoint instead of simplifying a large unary product/division. The model, input sequence, and both score theorem statements stay unchanged. |
| Prove Kth Highest Score's closed search bound with binary integers | Computing the natural comparison `100000 < 2^17` eagerly expands 131,072 unary successors and exhausts the portable stack. `Nat2Z.inj_lt` and `Nat2Z.inj_pow` transfer the goal to integers before computation. The natural bound, search algorithm, and theorem statements remain identical. |

The replacement is in
[`portable/smod_complement.v`](../tools/adversarial/portable/smod_complement.v).
It changes neither definitions nor theorem type and introduces no axiom.
The normal compiler checks it, and the final checker still validates imported
proof artifacts. Changes to upstream Stdlib require review of this adaptation.

## Collector and resource policy

The first two decisions below describe the retired translated prototype.
The C port uses OCaml's original collector; the isolation and resource decisions
that follow still apply.

| Decision | Reason and consequence |
| --- | --- |
| Select Wasmtime's tracing copying collector | Rocq builds cyclic graphs; deferred reference counting cannot reclaim them. Merely increasing fuel or process memory does not fix this retention. |
| Compare copying-GC live bytes with allocatable semi-space capacity when deciding growth | Comparing against the complete two-space allocation can keep the active space almost full and repeatedly collect. The pinned patch changes growth policy, not object tracing or memory limits. |
| Use fresh Stores and explicitly close Stores and Linkers | Release each guest heap and callbacks promptly. A completed or failed module cannot retain writable state into the next invocation. |
| Enforce fuel, CPU, wall time, address space, output, artifact, and virtual workspace limits | Fuel covers guest instructions but excludes some native GC and host work. The other bounds cover those costs and transport/compilation overhead. |
| Apply OS bounds with `prlimit`, not Python `preexec_fn` | Trusted library workers use coordinator threads. Running Python after `fork` before `exec` would risk deadlock. |
| Reset the host CPU deadline for each invocation | One persistent host serves a batch, so accumulated CPU time must not consume the next source's entire allowance. Wall time is enforced by the coordinator, which kills the host process group on failure. |
| Use small linear-memory reservations and no guard reservation | A large default virtual reservation would consume the process address-space budget before real proof data. Wasmtime still enforces memory accesses. |
| Bound the guest Wasm stack at 2 MiB | Recursive guest evaluation should trap within a known stack budget. Other data remains subject to heap and process limits. |
| Give trusted library provisioning larger budgets than ordinary candidates | Bootstrapping the portable library is evaluator work. Candidate execution remains bounded by its selected limits; increasing provisioning limits does not grant a candidate more resources. |
| Give full example proof chains explicit larger limits | Complete arithmetic-heavy examples need more work than the small acceptance fixture. These limits are explicit data in `verification/adversarial-examples.json`, validated against its independent JSON Schema. |
| Give Kth Highest Score a separate larger example budget | Its generated-step proof takes roughly 33 seconds at native `Qed` and exceeds 600 seconds in the portable compiler. Keep its proof and independent audit, with explicit bounds of 1,200 seconds CPU, 1,800 seconds wall time and two trillion fuel. Cold cost remains; complete validated cache hits avoid repeating it. |

The host currently retains immutable input blobs and snapshots for its lifetime;
there is no cache-eviction policy inside a batch. This improves sharing but can
raise memory usage in a long batch. The process address-space bound still applies;
closing the sandbox releases the retained state. More trusted build workers
also mean more host processes and aggregate memory use.

## Virtual capabilities and host protocol

| Decision | Reason and consequence |
| --- | --- |
| Expose a virtual root containing only supplied memory nodes | Guest paths never become host OS paths. Input bytes are immutable; only `/work` and `/tmp` are writable regions. |
| Attach authority to nodes and open descriptors | Rename/unlink must not turn a read-only input into a writable file or transfer authority across regions. Open unlinked files still count against memory quotas. |
| Reject escaping relative paths, absolute capability paths, symlinks, sockets, and process imports | A path must stay inside its supplied directory capability. Unneeded interfaces are absent from the import allowlist. |
| Fix file timestamps and inode/device fields | Host metadata would leak state and create hidden cache dependencies. Cache observations can instead bind file type, size, content, and directory membership. |
| Allow bounded clocks and random bytes | OCaml/Rocq runtime initialization and timing need them. They grant no filesystem or network access. Artifact caching does not promise byte-for-byte replay of a fresh run's randomness or timing. |
| Bound file sizes, writable byte totals, node counts, descriptors, path lengths, and iovec counts | In-memory I/O still consumes trusted host resources. Reject oversize requests before allocating their full requested result. |
| Use a framed JSON coordinator protocol with separate guest stdout/stderr | A candidate's printed text cannot forge a host response or checker report. Validate exact schemas, output sizes, encoding, and artifact paths. |
| Launch the host with an empty inherited environment | Host secrets and unrelated configuration must not become guest state. The guest receives a small explicitly constructed environment. |
| Kill and discard the host on protocol, deadline, or execution failure | Failed transport or partial state must not contaminate a later request. A new host retransmits its snapshots. |

## Structural sharing, dependency taint, and cache soundness

| Decision | Reason and consequence |
| --- | --- |
| Share an Engine, evaluator Modules, and immutable SHA-interned input bytes | Repeated compilation avoids reparsing runtime code and copying identical dependencies. Do not share mutable Rocq environments, guest globals, heaps, or writable files. |
| Give each source a fresh Store and only its declared source/artifact closure | Independent modules do not acquire scheduling-dependent taint from unrelated compiled modules. Dependencies cross invocations as immutable serialized artifacts. |
| Scan candidate dependencies inside WASI | Submitted source must not be parsed by an unsandboxed native dependency scanner. Native dependency scanning is limited to evaluator-owned trusted sources during provisioning. |
| Register installed source roots explicitly and use `rocq dep -dyndep no` | Automatic installed-path discovery expects existing `.vo` files and can hide libraries not yet provisioned. Explicit trusted roots expose their source names to the guest scanner. Keep normal mode because `-boot` ignores frozen project/specification libraries distributed only as `.vo`. |
| Omit ML archive expansion in the portable dependency scanner | Upstream `-dyndep no` changes output but still resolves declarations through native findlib. Portable plugins are statically linked, so the scanner returns no archive dependencies. This does not authorize declarations: the compiler's fixed plugin policy still rejects them, including declarations inside loaded sources. |
| Build a topological source order from the sandboxed scanner's records | Sorting submitted sources must not recursively reopen frozen `.v` files that are distributed only as `.vo`. Reject cycles or unexpected graph records. |
| Provision approved trusted libraries lazily beyond the initial project/boot closure | Avoid compiling every installed package at startup. Complete trusted-source identity means adding an unchanged approved library does not change a frozen contract's identity. |
| Use a special boot order without Stdlib compatibility aliases | Normal short `Init.*` resolution can point back through aliases and create false boot dependencies. Boot compilation uses Corelib's separately checked order. |
| Scan Corelib's dependency graph in isolation | Corelib's short imports must resolve to foundation modules. A combined recursive scan can instead select Stdlib/stdpp wrappers named `ssreflect`, exposing ambiguous aliases to the compiler. Override Corelib's graph with a trusted core-only scan; per-module filesystem observations validate reuse when the closure changes. |
| Record the selected dependency graph in the library manifest | Identical sources and selected module names do not imply identical dependency relationships. Graph changes must force entry-level observation validation, even when every materialized artifact still matches its stored hash. |
| Cache successful modules immediately | A failure in a later source must not discard all earlier expensive compilation work. Partial work is reusable only through independently validated entries. |
| Key compilation by compiler/source/context/limits plus observed inputs | Global library hashes would invalidate unrelated subtrees. The complete observation manifest tracks actual taint while source and context keys track changes in what the module may request. |
| Observe reads, metadata, negative lookups, and directory listings | A dependency is more than `Require`: new files can change lookup resolution, and directory contents can change compilation without reading every member. Metadata-only observations bind type/size rather than unused content. |
| Hash the actual adapted trusted source | Original source identity alone would miss proof-adapter changes. Unadapted sources retain their content keys and can reuse prior work. |
| Bind transitive taint through compiled artifact bytes | A changed dependency invalidates a consumer that read it; its changed output propagates to its consumers. No history of unrelated sandbox occupants is needed because mutable state never crosses the Store boundary. |
| Keep a narrower compiler identity and a complete frozen runtime identity | Changes to unrelated trusted `.v`/`.vo` files should allow observed-input compilation reuse. Trusted compilation binds the actual compiler Wasm, packaged host and bindings, cache implementation, load roots, source and observed inputs. Scanner/checker-only changes do not invalidate that domain. Frozen contracts and kernel results still bind the complete runtime/policy identity. |
| Bridge earlier trusted compile cache domains only with a recorded matching compiler identity | The old manifest coupled all runtime images. A manifest without a matching explicit compiler/host identity cannot authorize reuse under a new domain. Compatible domains still require the usual source, resource and observation checks. |
| Version the trusted compilation protocol explicitly | Its identity includes `compile_protocol=1` and `cache_format=2`. Changes to trusted compiler arguments, environment or visibility semantics must bump that protocol; source adaptations already bind their actual bytes separately. This prevents implementation changes from silently reinterpreting earlier cache entries. |
| Give kernel results a separate, broader cache domain | The full contract, arguments, limits, runtime, and every visible artifact matter, including unused helpers subject to audit. Validate cached reports again before accepting them. |
| Cache independently checked library prefixes separately from compilation | A compilation artifact is insufficient. A prefix entry is written only after upstream `Safe_checking.import` completes that library. Reuse invokes upstream `unsafe_import` solely to reconstruct the previously checked declarations and regenerated VM code. The original `admit` and `norec` options stay empty; arbitrary unchecked libraries cannot enter this path. Final contract and axiom audits still run. |
| Bind each prefix to the complete preceding environment | Use BLAKE2b-256 over the predecessor, logical library name, complete current `.vo` bytes, and predecessor certificate payloads. This deliberately includes earlier libraries even when direct imports do not mention them; it prevents hidden environment taint. The seed binds checker bytes, compiler/host/coordination identity, and resource profile. |
| Capture indirect opaque-proof reads as additional taint | Upstream opaque accessors can fetch a proof body outside the direct import list. Record the actual source path and BLAKE2b-256 hash for each accessed opaque table. Validate these reads on reuse, and hash the certificate into the next prefix so changed indirect taint invalidates successors. |
| Preserve the full hidden-axiom dependency map in each prefix certificate | Serialize upstream `Mod_checking.opaques` with `Marshal.Compat_32`; reconstruct fresh environments and VM tables rather than saving the VM heap. The final audit uses this map to distinguish a sealed definition from a hidden axiom. Only evaluator-owned, payload-hash-verified cache entries are exposed at `/checked-prefix`; submitted metadata never supplies certificates. |
| Transport prefix payloads in private `.vo` files | The existing host returns bounded writable `.vo` outputs. Certificates use private input/output directories, never registered library paths; only the checker sees these inputs, and the coordinator requires exact 64-hex filenames. This retains the host protocol and compiler artifact restrictions. They are serialized cache payloads, not submitted Rocq libraries. |
| Checkpoint completed library checks in fresh WASI invocations | After a cache miss finishes, return a `prefix-checked` response once CPU time reaches the smaller of 120 seconds and one quarter of the invocation CPU allowance. Save completed prefix certificates and resume in a fresh Store. CPU/fuel/process limits apply to each invocation; one wall deadline covers the entire kernel operation, including checkpoint restarts. No partially checked declaration is saved, and a checkpoint is never acceptance. |
| Let the example runner resume a resource-limited operation only after completed progress | The independent JSON configuration declares `operation_attempts=3`; the schema permits only one to three attempts. Retry compilation or kernel CPU/wall/fuel failures only when new successful module-cache files or checked-prefix certificates were saved, respectively. Logical rejections, absent progress, and disabled caches do not qualify. Every attempt keeps the same limits and acceptance checks, reconstructs environments in fresh Stores, and revalidates all ordinary cache observations. Preserve the failed report/artifacts under `attempt-N`, and reserve `result` for the latest attempt. This is bounded CI orchestration; partial work never constitutes acceptance. |
| Reuse prefixes across contracts while retaining complete acceptance keys | Prefix certificates concern independent kernel imports, not the current axiom allowlist or contract. Always repeat the final interface/subtyping and axiom audits unless the broader complete-result cache hits. `--no-cache` disables prefix reuse and checkpointing as well as complete-result and compilation caches. |
| Exclude invocation-generated output directories from input observations | They are private outputs, not external taint. A random private candidate output directory and exact artifact-set checks prevent pre-supplied files from masquerading as compiler outputs. |
| Write cache entries atomically and verify payload hashes | Interrupted writes and damaged caches become misses. Materialized trusted `.vo` files also need hash verification and repair from valid entries. |
| Permit trusted-build reuse from specific earlier stricter limits | A previously successful trusted artifact remains checked under larger provisioning bounds. Candidate compile cache keys require exact limit equality. |
| Treat caches as evaluator-owned, not adversary-authenticated storage | Content hashes detect damage, not malicious replacement by someone allowed to rewrite both payload and metadata. Candidate write access to caches or frozen bundles is outside the supported trust model. |
| Make `--no-cache` disable candidate/specification and kernel-result caches | It supports fresh checking while retaining the installed runtime and trusted library artifacts. It does not reinstall the toolchain or erase provisioning caches. |

A cache hit reuses one successful checked computation; it does not reproduce
fresh clock values, random names, or diagnostics. The acceptance invariant is
that the resulting artifacts satisfy the frozen logical contract and audit.

## Performance approaches evaluated and rejected

- **Use the distributed reference-counting host:** cyclic Rocq data accumulated.
  A tracing collector was required.
- **Enable copying GC without adjusting growth policy:** repeated collections
  near active-space capacity caused severe cost. The pinned capacity fix was
  retained after cycle/retention regression checks.
- **Raise fuel to fix `smod_complement`:** longer runs exhausted the GC heap.
  Instruction budgets cannot fix this proof's memory expansion.
- **Toggle kernel conversion heuristics or disable term sharing:** diagnostic
  compilations did not solve the certificate problem; disabling sharing made
  earlier proof checking substantially worse. Neither change was retained.
- **Normalize both terms eagerly or port the pretyping CBV reducer into kernel
  conversion:** disposable native diagnostics still stalled in reflection
  certificate checking. These experimental kernel changes were removed.
- **Add physical-identity memoization to that CBV prototype:** the diagnostic
  regressed earlier proof steps, so the implementation was removed.
- **Simply split the original assertion or invoke `intuition nia`:** WASI still
  exhausted the diagnostic fuel budget. The retained proof uses explicit sign
  cases and division uniqueness, producing much smaller linear certificates.
- **Clear only two irrelevant bracket-proof hypotheses:** this did not resolve
  the expensive arithmetic certificates. The retained change keeps an explicit
  sufficient set of counting facts at the two identified side-condition groups.
  Removing strict count bounds as well left unsolved goals, so those bounds are
  named and retained rather than weakened or assumed.
- **Prune Kth's unary size bound or isolate its conversion in an opaque lemma:**
  the generated-step proof still took approximately 32–33 seconds at native
  `Qed`. Those changes were removed; its larger explicit portable example
  budget covers the existing proof without changing the checking policy.

- **Make Kth arithmetic subproofs opaque with `abstract lia`:** the native
  module still takes 43.9 seconds, including the same costly generated-step
  conversion. This experiment was discarded.
- **Use VM casts for every generated-step goal reduction:** VM normalization
  of the open generated program stalls during its initial unfolding, while the
  original native proof closes in about 35 seconds. The broad source experiment
  was discarded; the shipped kernel conversion rules are unchanged.

These were performance diagnostics, not alternative acceptance policies. No
experimental kernel conversion path is part of the shipped runtime. No theorem
was admitted or added to the trusted axiom policy to finish a build. Repeated
independent imports may use the checked-prefix certificates described above.

## Validation scope

The regression suite covers arithmetic against native Zarith, Marshal sharing
and cycles, exception cleanup, GC retention, virtual capability containment,
quotas, resource failures, and cache taint/corruption. Acceptance tests cover
frozen contracts, helper audits, unapproved axioms, plugin rejection, and cache
reuse. The example runner checks eight complete specification/candidate pairs.

A locally packaged standalone host can validate the exported executable path,
but it does not establish that the Dockerfile builds on GitHub Actions. Run the
workflow to validate Docker packaging, a cold runner, cache restoration, and CI
resource use together. Performance and platform claims should state which of
these environments was actually exercised.

Earlier translated-prototype validation on 2026-10-09 ran 134 regression cases successfully, with 58
optional native-backend cases skipped. The run used the standalone packaged
Wasmtime host and took approximately 24 minutes, including cold independent
proof checks. Docker was unavailable on this machine, so Docker packaging and
the complete GitHub Actions job still require a runner execution.

The C port passes all 24 runtime/host regressions with the stock packaged
Wasmtime host, including original OCaml GC, cross-native Marshal sharing/cycles,
arithmetic against Zarith, and capability/observation tests.

The original C VM build completed the 339-library project closure, including
`TwoWaysToFill.v`; lazy primitive-library provisioning increased the installed
selection to 343 libraries. After the checker-only changes, verified warm
runtime/library provisioning took 0.47 seconds. Larger cold audits exposed the
600-second CPU limit, motivating the measured allocation/audit changes above.
The complete regression suite now passes; complete-example validation is still
running.

The checked-prefix prototype reduced a small independent specification check
from 12.2 to 3.5 seconds. The production forced-continuation/reuse/hidden-axiom/corruption regression
passed in 92.5 seconds. All 24 runtime tests, six compilation-cache tests and
eight configuration tests passed. Complete-example validation is still running.
The preceding full-suite run passed all cases except the large interactive
fixture setup, which exceeded its cold CPU limit before prefix caching existed.

The production Watermelon example is accepted with the kernel and original C VM
enabled. Cold specification certification took 698 seconds across checkpoints;
candidate evaluation then took 43.3 seconds and reused 232 cache entries. An
identical complete rerun took 5.368 seconds with five hits and zero misses.
These are local measurements, not guarantees for a fresh GitHub runner.

Restore Three Numbers is also accepted. Cold specification certification took
735 seconds and candidate evaluation 627 seconds; an identical complete rerun
took 6.096 seconds with five hits and zero misses. An instrumented independent
specification rerun reused every prefix, regenerated VM code, repeated the
axiom audit, and finished in 41.4 seconds. Cache hit counters include validated
prefix entries supplied to the guest; they do not count individual theorems.

The updated broader regression run completed 152 selected cases successfully
in 1,535 seconds, with 63 optional native-backend cases skipped. All three
interactive-contract cases passed separately in 2,753 seconds: the full generated
certificate was accepted, and both insufficient certificates were rejected with
signature mismatches. Together these runs cover 155 cases, including the
checked-prefix continuation, hidden-axiom, corruption and unsafe flag tests
alongside the original C runtime/VM regressions.

CI sets `COQCP_TEST_CACHE` in workflow YAML so acceptance, compiler-execution,
and interactive fixtures share the persistent evaluator cache with the example
runner. Otherwise their temporary caches would discard expensive valid work at
class teardown. Local tests retain isolated temporary caches by default, and
cache corruption/taint tests explicitly create private roots even in CI. All
155 regression cases passed with isolated fixtures: 92 active cases and 63
optional native cases skipped. The focused forced-continuation, reuse,
hidden-axiom invalidation and corruption test also passed with the shared CI
setting in 81.2 seconds. This validates the opt-in plumbing locally; an actual
GitHub Actions execution is still required to validate runner packaging.
The complete shared-cache suite subsequently passed all 155 cases in 2,729
seconds, with the same 63 optional native skips. The lazy-library axiom-policy
test also passed after its temporary sandbox was switched to the shared cache,
in 425 seconds; cache corruption and taint-mutation tests retain private roots.

Knapsack is also accepted, including all ten candidate modules and its existing
functional-extensionality allowance. At this point four of eight examples have
passed: Increment, Watermelon, Restore Three Numbers and Knapsack. The remaining
four are being checked under their declared limits with the same kernel and VM.

Permuted Binary Strings also passes through the example runner, reusing the
interactive regression's compiled helpers and complete audit with twelve hits
and zero misses. Two cold attempts hit resource limits: DSU's kernel operation
exceeded its wall deadline, and Koxia's number-theory helper exhausted fuel while
rewriting membership of its concrete residue range. These are failed attempts,
not accepted examples; completed library checkpoints remain reusable. Remaining
example validation and the Koxia proof optimization are in progress.

An identical combined rerun of those four completed examples took 15.768 seconds,
with 27 cache hits and zero misses across the four reports. This includes bundle
freezing, candidate source copying and final report generation; it is a local
complete-result-cache measurement, not a cold proof-checking measurement.

DSU subsequently passes after resuming its completed prefixes under the unchanged
profile. The example runner now implements the bounded, progress-gated retry
described above. Its three orchestration regressions pass, and an actual WASI
integration test that saves a prefix, closes the sandbox, injects a resource
rejection, and completes the next audit passes in 76.3 seconds. All eleven schema
and runner tests pass. Koxia's revised number-theory helper also compiles with
native Rocq (5.1 seconds for four modules); the full WASI candidate remains under
validation. Six of eight examples are accepted so far.

The final expanded shared-cache suite passes all 160 cases in 486 seconds:
96 active cases and 64 optional native cases skipped. This includes the real
fresh-Store retry integration and the three new bounded-retry orchestration
tests. The source-level Koxia optimizations are separately validated by the
complete-example run rather than inferred from the generic regression suite.

The expanded shared-cache suite subsequently passes all 163 cases in 514.8
seconds: 98 active cases and 65 optional native cases skipped. This includes a
real WASI compilation retry: compile one helper, close the host and inject a
wall-limit failure before the dependent module, then reuse the helper and finish
the complete independent audit in a fresh Store. The focused integration passes
in 19.9 seconds. All twelve manifest/orchestration tests pass. The default
attempt cap is three so a cold compilation continuation and a later cold kernel
continuation can each make progress; every operation still keeps its original
limits and only completed, revalidated cache entries can be reused.
