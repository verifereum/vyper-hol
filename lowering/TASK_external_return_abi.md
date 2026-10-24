# TASK: external return of an ABI-encoded value (halt bridge)

## Meta
Status: planned
Priority: P1
Created: 2026-10-25
Location: lowering/ (files lowering/loweringHaltScript.sml, lowering/vyperLoweringCorrectScript.sml)

## Theorem Statement (FROZEN)

In lowering/loweringHaltScript.sml:

```sml
Theorem compile_external_return_abi_frag:
  !ctx op ei msz nr nkey ut iv st x st' env ty tv v av P Q R.
    compile_external_return (SOME op) F F ei msz nr nkey ut iv st =
      (x, st') /\
    (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
    value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
    LENGTH (enc (vyper_to_abi_type env ty) av) <= msz /\
    (!s. P s ==>
         ?p. eval_operand op s = SOME p /\
             val_in_memory tv v (w2n p) s.vs_memory /\
             w2n p + type_memory_size tv <= s.vs_alloca_next /\
             alloca_inv s /\
             (!i. i IN frag_ids st st' ==> FLOOKUP s.vs_allocas i = NONE) /\
             s.vs_alloca_next + msz + 32 * (st'.cs_next_id - st.cs_next_id) <
               dimword (:256) /\
             !ss. ss.vs_returndata = enc (vyper_to_abi_type env ty) av /\
                  ss.vs_accounts = s.vs_accounts /\
                  ss.vs_transient = s.vs_transient /\
                  ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests ==>
                  R (Halt ss)) ==>
    frag_exec ctx st st' P Q R
```

In lowering/vyperLoweringCorrectScript.sml:

```sml
Theorem external_return_abi_result_rel:
  !ctx op ei msz nr nkey ut iv st x st' func cenv cx es ret tv v0 v
     tops tx srcs exps layouts Q.
    compile_external_return (SOME op) F F ei msz nr nkey ut iv st =
      (x, st') /\
    (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    evaluate_type (type_env tops) ret = SOME tv /\ safe_cast tv v0 = SOME v /\
    abi_enc_plan (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret) ei /\
    vyper_abi_size_bound (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret) <= msz ==>
    frag_exec ctx st st'
      (\s. state_rel func cenv cx es s /\
           (?p. eval_operand op s = SOME p /\
                val_in_memory tv v0 (w2n p) s.vs_memory /\
                w2n p + type_memory_size tv <= s.vs_alloca_next) /\
           alloca_inv s /\
           (!i. i IN frag_ids st st' ==> FLOOKUP s.vs_allocas i = NONE) /\
           s.vs_alloca_next + msz + 32 * (st'.cs_next_id - st.cs_next_id) <
             dimword (:256) /\
           s.vs_accounts =
             process_deletions es.pending_deletions es.accounts /\
           s.vs_transient = es.tStorage)
      Q
      (external_call_result_rel tops ret tx
         (INL v, finalize_pending_deletions
                   (abstract_machine_from_state srcs exps layouts es),
          es.requests))
```

**Do not modify these statements.** Prove them as-is, or produce a counterexample.

Weakly frozen dependencies (use as stated; other prover runs are proving them, so they may be `cheat` in your copy, which is fine; do not edit them or the definitions they use):
- `compile_abi_encode_frag` and the definitions `abi_enc_plan`, `frag_ids`, `enc_scratch`, `enc_frame`, `enc_pre` in lowering/abiEncoderPropsScript.sml
- `frag_exec_loop` in lowering/fragExecScript.sml

## Completion Criteria

1. `holbuild -j4 build vyperLoweringCorrectTheory` passes; no CHEAT in the two theorems above or in helpers you add (the cheats in the weakly frozen dependencies, and other pre-existing cheats, are out of scope).
2. Helpers in their most general form, next to the theorem that uses them; no duplicates of existing lemmas.
3. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`. Proofs under ~50 lines each; no step near the 2.5 s tactic timeout (never raise it).

**If a theorem is false as stated:** give a concrete counterexample and the tightest fix. Do NOT weaken the statement.

## Build

```
holbuild -j4 build vyperLoweringCorrectTheory
```
(run from the project root, the directory containing holproject.toml)

## Background

An external function's `return e` in the Vyper→Venom lowering (lowering/defs/stmtLoweringScript.sml `compile_external_return_def`, the non-word, non-raw path) ALLOCAs a buffer of `msz` bytes, ABI-encodes the value with `compile_abi_encode_to_buf` and RETURNs the buffer with the encoded length. The first theorem says the fragment halts with the encoding as returndata; the second ties that to the semantics' result relation `external_call_result_rel` for the external call, where the ABI wraps a single return value in a one-tuple (`needs_external_call_wrap`), and the lowering's plan is for the wrapped type when the value is ABI-dynamic (for a static one the wrapped encoding is the same bytes). This is the dynamic-return part of vyper-hol issue #640. The static-return analogues, already proved, are the closest pattern: `compile_external_return_copy_frag` (loweringHalt) and `external_return_static_result_rel` (vyperLoweringCorrect).

## Domain Constraints

- Project rules in AGENTS.md at the project root: holbuild only, no interactive g/e sessions, rename1 rather than generated names.
- Don't edit files under semantics/, venom/ or lowering/defs/, the lowering/exprSim* files, or existing theorems; add helpers.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| static-return pattern | lowering/loweringHaltScript.sml, lowering/vyperLoweringCorrectScript.sml | compile_external_return_copy_frag, compile_external_return_copy_parts, return_copy_run, external_return_static_result_rel |
| encoder lemma | lowering/abiEncoderPropsScript.sml | compile_abi_encode_frag (to_buf clause) and its definitions |
| frag_exec rules | lowering/fragExecScript.sml | frag_exec_seq, frag_exec_conseq, frag_exec_pointwise, frag_exec_run_inst_seq, cs_extends_* |
| lowering | lowering/defs/stmtLoweringScript.sml, lowering/defs/abiEncoderScript.sml | compile_external_return_def, compile_alloc_buffer_def |
| ABI | .holbuild/src/verifereum/util/contractABIScript.sml | enc, enc_tuple, is_dynamic, static_length |
| Vyper→ABI | semantics/vyperABIScript.sml, semantics/prop/vyperTypeABIScript.sml | vyper_to_abi, vyper_to_abi_type, needs_external_call_wrap, vyper_abi_size_bound, vyper_to_abi_total, vyper_to_abi_enc_length_bound, safe_cast_some_eq |
| result relation | lowering/vyperLoweringCorrectScript.sml (and its ancestors) | external_call_result_rel |
| Venom semantics | venom/defs/venomExecSemanticsScript.sml | ALLOCA (exec_alloca_def), RETURN |
| alloca invariants | venom/ (grep alloca_inv) | alloca_inv, allocas_non_overlapping, alloca_next_valid |

## Notes

The encoder lemma's `lo`/`top` parameters are for the caller to choose (for instance `lo` just above the buffer).
