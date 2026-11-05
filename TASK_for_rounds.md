# TASK: counted composition of a For loop's rounds

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/stmtSimForRoundsScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem eval_for_rounds:
  !memory tops ctx func cx tyv nm body vs ok Inv Done R.
    (!k es s.
       k < LENGTH vs /\ Inv k es s /\
       gas_admissible (eval_for cx tyv nm body (DROP k vs)) ok es ==>
       gas_outcome memory tops (ctx, func)
         (do push_scope_with_var nm tyv (EL k vs);
             finally
               (try (do eval_stmts cx body; return F od)
                  handle_loop_exception)
               pop_scope
          od) (es, s)
         (\res ee t. ?broke. res = INL broke /\
            (broke ==> Done ee t) /\ (~broke ==> Inv (SUC k) ee t))
         (\res ee r. ?ex. res = INR ex /\ R ex ee r)) /\
    (!es s. Inv (LENGTH vs) es s ==>
       ?t. gas_marked_path memory ctx func s 0 (OK t) /\
           Done (es with gas_obs := []) t) ==>
    !k es s.
      k <= LENGTH vs /\ Inv k es s /\
      gas_admissible (eval_for cx tyv nm body (DROP k vs)) ok es ==>
      gas_outcome memory tops (ctx, func)
        (eval_for cx tyv nm body (DROP k vs)) (es, s)
        (\res ee t. res = INL () /\ Done ee t)
        (\res ee r. ?ex. res = INR ex /\ R ex ee r)
```

`eval_for` is in `semantics/vyperInterpreterScript.sml` (the `evaluate_def`
equations); `gas_outcome` in `lowering/gasOutcomeScript.sml`;
`gas_summary_at`, `gas_marked_exec` in `lowering/gasSummaryScript.sml`;
`gas_exempt_cert` in `lowering/gasExemptCertScript.sml`; `gas_admissible` in
`lowering/gasContextScript.sml`; `gas_marked_path` in
`lowering/fragGasModeScript.sml`.

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build stmtSimForRoundsTheory` passes with zero CHEAT warnings in `stmtSimForRoundsTheory` and zero failures.
2. The statement above is unchanged.
3. No duplicate or near-duplicate lemmas: search the `lowering/` theories before adding a helper; each helper exists once, in its most general form.
4. No change to any definition, and no change to any file outside `lowering/stmtSimForRoundsScript.sml`.

**If the theorem is false as stated:** produce a concrete counterexample, state the tightest sufficient fix, and stop. Do NOT weaken the statement.

## Build

```
holbuild -j4 build stmtSimForRoundsTheory
```

## Background

The compiler-correctness proof for Vyper's lowering to Venom IR has changed its
statement judgment. A statement simulation now takes the whole source action
and its entry state instead of one fixed source result, because the gas oracle
(`msg.gas`, and the target's GAS instructions) makes the source run depend on
gas readings chosen by the actual target execution. Its core is `gas_outcome`:
either a `gas_summary_at` (an actual marked target path whose explicit GAS
readings, fed to the source, produce the source result, with a post on a
normal finish or an exit post on an exit), or a `gas_exempt_cert` (an exempt
error carried from an origin through the enclosing source structure).

A `For` loop's source is `eval_for cx tyv nm body vs`: for each value, push a
scope holding the loop variable, run the body, turn break/continue into a
boolean (`handle_loop_exception`), pop the scope, and stop on a break. This
theorem is the loop-level composition: given a counted outcome for each round
from the loop invariant `Inv k`, and a GAS-free path from the invariant after
the last round to the loop's exit, the remaining loop has a counted outcome.
`ok` is whatever admissibility the enclosing statement guarantees for the
whole remaining loop; each round's hypothesis receives it for the loop from
that round on. Range loops and array loops will each instantiate this with
their own invariant and round lemma.

## Domain Constraints

- No `cheat`, no new axioms, no oracles, no change to definitions (source
  semantics, compiler, or proof-internal judgments such as `gas_exempt_cert`).
- `gas_exempt_cert` is an inductive relation over the syntactic source term:
  a pointwise equality of two sources does not transfer a certificate. Lift
  certificates with its rules (and `vyperStateTheory.bind_assoc` rewriting of
  the source term).
- Every ordinary branch needs an actual counted path (`gas_marked_exec` /
  `gas_marked_path`).
- holbuild's per-step tactic timeout (2.5 s) is fixed: never raise it. A slow
  step is a proof bug; split it.
- Never wrap `metis_tac` or other search in `TRY`/`ORELSE`; select goals with
  `>~`, `>-`, `>|`.
- Proofs at most ~50 lines each; give a hard subgoal its own lemma.
- Follow `AGENTS.md` at the project root.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Target file | `lowering/stmtSimForRoundsScript.sml` | the theorem |
| Source semantics | `semantics/vyperInterpreterScript.sml` (`eval_for`, `handle_loop_exception_def`), `semantics/vyperStateScript.sml` (`bind_def`, `ignore_bind_def`, `return_def`, `finally_def`, `try_def`, `push_scope_with_var_def`, `pop_scope_def`, `bind_assoc`) | monad and loop |
| Gas outcome | `lowering/gasOutcomeScript.sml`, `lowering/gasSummaryScript.sml`, `lowering/gasSummaryComposeScript.sml` | `gas_outcome`, `gas_summary_at`, `gas_marked_exec`, `gas_explicit`, bind composition (`gas_marked_exec_bind_normal`, `gas_marked_exec_bind_exception`, `gas_marked_source_bind_normal`, `gas_explicit_append_path`) |
| Paths | `lowering/fragGasModeScript.sml`, `lowering/fragGasPathScript.sml`, `lowering/fragGasPathMemScript.sml` | `gas_marked_path`, `gas_marked_path_then`, `gas_path` rules |
| Exempt certificates | `lowering/gasExemptCertScript.sml` | `gas_exempt_cert` rules (`bind_bool`, `error_bool`, `bind_unit`, ...) |
| Admissibility | `lowering/gasContextScript.sml`, `lowering/stmtSimSeqEnvScript.sml` | `gas_admissible`; `gas_admissible_stmts_tail` is the analogous tail lemma for statement lists |
| Worked composition | `lowering/stmtSimSeqEnvScript.sml` | `stmt_frag_cons_env`: two counted outcomes composed in sequence, including both exempt cases |
