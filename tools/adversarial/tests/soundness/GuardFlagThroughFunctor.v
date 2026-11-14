(** * `Unset Guard Checking` vanishes from the audit across a functor application

    rocq-prover/rocq#22366, reported 2026-08-19 by `christos-spearbit` and
    **OPEN**.  A functor applied while `Unset Guard Checking` is active
    substitutes an `Inline` module parameter's body into the instantiated
    constant **without re-checking guardedness and without recording the flag
    use**, so `Print Assumptions` reports the result as axiom-free when it is
    not.

    ** What this is, and what it is not

    Ground rule 2 of [`../../../README.md`](../../../README.md) says a `False`
    that needs a flag is an *escape hatch*, and this one needs
    `Unset Guard Checking`.  The route to `False` is therefore not the finding —
    [`../../../EscapeHatches/Coq/TypingFlags.v`](../../../EscapeHatches/Coq/TypingFlags.v)
    §1 already exhibits that route, honestly, and its audit says
    `loop is assumed to be guarded.`

    The finding is that **the cost stops being reported**.  Same flag, same
    non-terminating fixpoint, same `False` — and the audit that names the flag
    in every other arrangement says nothing here.  That places it with
    [`UniverseFlagDesync.v`](UniverseFlagDesync.v) (rocq#22287) rather than with
    the escape hatches: both are the module system losing a typing flag's
    bookkeeping, and in both the local audit is what is lost.

    It is the **fourth** member of a family [`../../../CATALOG.md`](../../../CATALOG.md)
    is already tracking.  §4.2 records rocq#12155 and rocq#16646 — `Print
    Assumptions` under-reporting inconsistent flags through `Parameter Inline`
    and functor application — for the *universe* flag; §1.4 records rocq#20550,
    where `abstract` builds its side-effect constant with the global flags.  This
    is the *guard* instance, and #22366's own summary says so: "The known
    `Print Assumptions` audit-bypass class was documented for **universe**
    checking.  The same one exists for **guard** checking."

    ** Measured on Rocq 9.2, the current stable release

      - [coqc] on this file:          exit 0.
      - [Print Assumptions boom]:     "Closed under the global context".
                                      **Not caught.**
      - [rocqchk] on the .vo:         [Fatal Error: Type error: IllFormedRecBody].
                                      Caught — the checker is the residual
                                      safeguard, exactly as in #22287.

    ** The control is one token

    [`GuardFlagThroughFunctorControls.v`](GuardFlagThroughFunctorControls.v)
    runs the same construction twice more:

      - direct use, no functor at all      -> `loopD is assumed to be guarded.`
      - the same functor WITHOUT `Inline`  -> `X2.T is assumed to be guarded.`

    So the audit is working in both neighbouring arrangements, and it is
    `Parameter Inline` — one token — that makes the flag disappear.  Upstream's
    report does not isolate it that far; that pair is this repository's
    measurement.

    Upstream reports the defect on Coq 8.18.0 and on master (9.4+alpha) and
    leaves the version field blank.  **9.2 is pinned here.**

    Write-up: ../../../Reports/2026-08-20-rocq-august-wave.md *)

Module Type set.
  Parameter Inline T : (nat -> False).
End set.

Module F(S:set).
  Definition loop : nat -> False := S.T.
End F.

Module X.
  Local Unset Guard Checking.
  Fixpoint T (n:nat) : False := T (S n).
End X.

Unset Guard Checking.
Module M := F X.
Set Guard Checking.

Definition boom : False := M.loop 0.

(** Expected on 9.2: `Closed under the global context` — the defect. *)
Print Assumptions boom.
