# End-to-end verification

A correctness proof of an algorithm or generated procedure does not establish
correctness of the submitted program. The original CSES 3228 solution exposed
that gap: the mathematical decoder and two generated procedures were proved,
while input parsing, initialization, loop composition, final printing, and
termination were supported only by executable tests. The ordinary execution
model also erased `Flush`, so it could not distinguish correct interactive
output from output that was never flushed.

## Framework contract

`theories/InteractiveExecution.v` adds `execObserved`, an interpreter for the
same generated `Action` values used by the ordinary runtime. Each `Flush`
records both the entire output produced so far and the input still unread.
Memory operations, arithmetic, and byte reads and writes retain the ordinary
execution semantics.

The reusable `endToEnd` contract requires a witness of successful termination,
the exact complete output, complete consumption of the specified input, and
exactly the specified flush snapshots. It is not a conditional statement about
what happens if execution succeeds.

The framework proves:

- `execObserved_erases`: forgetting observations agrees with ordinary execution.
- `execObserved_NoFlush` and `observed_plain`: a proved execution of a component
  without flush effects can be reused inside an observed execution.
- `endToEnd_rejects_failure`: an always-failing program cannot meet the contract.
- `endToEnd_requires_flushes`: a program without flush effects cannot satisfy a
  contract requiring a nonempty flush sequence.
- `endToEnd_erases`: an observed end-to-end proof implies successful execution
  with the same complete input/output in the ordinary interpreter.

For an interactive problem, the contract must specify the output and unread
input at every query flush. The remaining input at that boundary includes the
reply to that query; this establishes that the reply is consumed after the
query is flushed. A final snapshot requires the complete answer and no remaining
input. Query limits concern the actual query snapshots, not a separate counter
in an abstract algorithm.

The input stream is the concatenation of the initial input and truthful grader
replies. These are proof data, not a replacement for the generated input
procedures. The snapshots provide the query/reply ordering information that an
unobserved execution of a preloaded stream lacks.

## What may be called end-to-end

The contract must name the actual generated entry point with its actual initial
arrays. A different program, an extracted loop, or an oracle replacing a reader
is a refinement proof with a smaller scope. Full coverage includes parsing,
allocation/initialization, control flow, numeric conversions, memory bounds,
complete output formatting, and successful termination. Interactive coverage
also includes the query bound and flush placement.

An evaluator-owned specification should bind its `program` field to the
compiler-generated entry point and require this complete contract. The existing
adversarial module-signature checker then rejects proofs of weaker requirements,
admitted obligations, and a different program. Executable tests remain useful
for the emitted C++ and compiler/runtime behaviour, but they do not discharge
missing Rocq obligations.

This establishes end-to-end correctness in CoqCP's execution semantics. The
TypeScript compiler and native C++ runtime remain outside the formal proof;
claiming native executable correctness also requires a verified translation or
an explicitly stated trusted compilation chain.

## CSES 3228 certificate

`verification/permuted-binary-strings/spec/Spec.v` specifies canonical decimal
input, truthful LF-terminated reply lines, complete output, and every
query/final-answer flush. The candidate's `PermutedBinaryStringsProtocol.v`
proves `replyBytes_truthful`, connecting the specified reply bytes to indexing
the actual mathematical query by the hidden permutation.

`verification/permuted-binary-strings/candidate/PermutedBinaryStringsEndToEnd.v` proves `generated_end_to_end` for the
actual generated `main`, with the generated zero-initialized arrays. Its helpers
normalize the generated procedure calls, prove the decimal and bit readers,
compose ten reconstruction rounds, and prove repeated decimal printing with the
buffer left by the previous call. `generated_runProgram` transfers the result to
the existing runtime; `generated_flush_count` proves there are eleven flushes,
ten for queries and one for the final answer. The full certificate uses the
project's approved functional extensionality assumption.

The formal stream uses LF separators. CRLF, fragmented pipe writes, and native
flush/termination behaviour have executable coverage. The execution model does
not model POSIX blocking or buffering; flush snapshots establish ordering in the
specified stream, while native transport behaviour remains part of the runtime
and compilation boundary stated above.

The shipped frozen-spec example is
`verification/permuted-binary-strings/candidate/Candidate.v`. The acceptance
regressions require the full certificate to pass and reject both a correct
abstract decoder theorem and a successful ordinary execution theorem lacking
flush observations. Run them after building the registered project libraries:

```sh
python3 -m unittest discover -s tools/adversarial/tests \
  -p test_check.py -k InteractiveContractTests -v
```

The normal `tools/adversarial/examples.py` command also checks this example.
