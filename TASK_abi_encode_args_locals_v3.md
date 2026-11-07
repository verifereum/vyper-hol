# TASK: abi_encode's argument list as a counted path

## Meta
Status: planned
Priority: P1
Created: 2026-11-07
Location: lowering/exprSimAbiEncodeArgsScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_abi_encode_args_case_gas_sim:
  !nocalls ctx func ce cx env ann ensure mid ty args es sa ops sb s0.
    exprs_case nocalls ctx func ce cx args /\
    expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args) es /\
    (nocalls ==>
     int_calls_expr (TypeBuiltin ann (AbiEncode ensure mid) ty args) = []) /\
    compile_abi_encode_args compile_expr ce args sa = (ops,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\
    stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
      (\rr ee t. ?vs. rr = INL vs /\
         abi_args_post ctx func ce cx es sa sb s0 ee args ops vs t /\
         EVERY (abi_decoder_operand_live sb.cs_next_var) ops /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\rr ee r. wb_args_exit rr r)
```

Do not modify this statement. Prove it as-is, or produce a counterexample. `abi_args_post_def` (`lowering/abiEncodeArgsSimScript.sml`) is frozen with it.

Owner note: `wb_frame` (and `locals_kept`) now take the final environment as well (`wb_frame cenv es es' sa s0 s`). `abi_args_post_def` has been updated to match: its last conjunct is now `wb_frame ce es es' sa s0 s`, where `es'` is its existing final-environment argument. It stays frozen in that form. The other `wb_frame`/`locals_kept` uses in the harvested `abi*` theories are yours to port. Several (for example in `abiEncodeArgsSim`) still use the old arity.

## Completion Criteria

- The theorem is proved with no `cheat` in `lowering/exprSimAbiEncodeArgsScript.sml`, or in helper theories named `exprSimAbiEncodeArgs<Part>`.
- The same holds for the five harvested ancestors `abiArgsLabelBoundary`, `abiEncodeArgsWindows`, `abiEncodeMaterialize`, `abiEncodeArgsSim` and `abiEncodeArgsCase`. Their proofs no longer built after the `locals_kept`/`wb_frame` merge, so commit 1afcd65b0 admitted all of them (`cheat`) to let the ancestors build. Every one of those admissions is yours to prove. The original proofs are at commit 4cd0c6660 (`git show 4cd0c6660:lowering/<file>`); restore what still works and port the rest. Their statements may change where the new interfaces force it; `abi_args_post_def` and `compile_abi_encode_args` stay as they are.
- The harvested theories this proof needs (below) may be ported in place: change their proofs and add lemmas freely, but do not change `abi_args_post_def` or `compile_abi_encode_args`.
- No new axioms or admissions. Definitions only as proof-only helpers.
- `holbuild -j4 build exprSimAbiEncodeArgsTheory` passes at the default step limit.
- Commit checked work with the trailer `Bot: opus (Claude Opus 5.5)`; do not push.

## Build

From the project root:

```sh
holbuild -j4 build exprSimAbiEncodeArgsTheory
```

Default tactic timeout and memory limits.

Some ancestor theories on this branch are admitted by a local overlay (their files are cheated in the work tree and marked skip-worktree). Inherited admissions from them are expected and fine; do not edit, commit or un-skip those files. `exprSimAbiGasBridge` is proved on this branch (no admissions).

## Background

The counted expression judgments (`expr_sim`, `expr_vv_sim` in `lowering/exprSimDefsScript.sml`) now conclude `gas_outcome` over an actual `gas_marked_path`. The harvested argument-list proof (`compile_abi_encode_args_sim(_live)` in `lowering/abiEncodeArgsSimScript.sml`, `compile_abi_encode_args_case_sim` in `lowering/abiEncodeArgsCaseScript.sml`) was written against the older run_from form (`frag_exec`), so its operand hypotheses no longer match and it does not build.

The target is its counted analogue. The template is `lower_word_args_sim` in `lowering/exprSimWordArgsScript.sml`: induction on the operand list, composing each operand's counted `expr_vv_sim` (from `exprs_case`) with the rest via `gas_outcome` sequencing (`expr_sim_apply`, `wb_args_post_cons`, `gas_marked_exec_cons_values`, `wb_args_head_admissible`). Per operand, `compile_abi_encode_args` may also materialize a composite value into a fresh buffer (`compile_materialize_vv`), a GAS-free fragment whose proof (`lowering/abiEncodeMaterializeScript.sml`) is in `frag_exec` form; `frag_exec_gas_path` in `lowering/exprSimAbiGasBridgeScript.sml` turns such a fragment into a counted path with count 0, given `frag_gas_free`.

Notes from a statement review:
- Each operand's `gas_admissible` premise follows from `expr_body_pre_gas_admissible` (`lowering/exprSimSourceScript.sml`) and `expr_body_pre_vv_gas_admissible` (`lowering/exprSimHypsScript.sml`); each argument's `expr_body_pre` at later states from `abi_args_body_pre_arg` and `expr_body_pre_eval`. Take `Inv = expr_sim_inv ce cx env` (gas_obs-invariant: `expr_sim_inv_gas_obs`).
- The materialize step (`compile_materialize_vv`: MCOPY, bytestring copy, `unwrap_value`'s loads or `compile_word_copy_loop`) runs no GAS, INVOKE or PHI and jumps only to fresh labels. `frag_gas_free` may still be hard to discharge for it (the loop's exit label against the start block); building its counted path directly, as `compile_storage_copy_content_capacity_path` (`lowering/storageCopyGasPathScript.sml`) does, is an alternative to the bridge.
- `locals_kept` (`lowering/loweringPostsScript.sml`) was just strengthened. A local whose scope entry is the same at `es` and `es'` (it was not popped) now keeps its whole region, length words included, and the popped elements' history is kept in memory (`popped_kept`). Before, every dynamic array length word inside a local was exempt, dead ones included.
- An earlier run on the old `locals_kept` found this theorem false. Its witness (`flat_exact_outcome_excluded`, on branch `bot/opus/seq-1309-harvest-merge` at 6b5d38e2e, `lowering/exprSimAbiEncodeArgsFlatExclusion*Script.sml`) was a `Pop` of a DynArray operand returning a pointer into the root's freed slot, followed by a later operand whose callee overwrites that slot while the state relation still held. Check first that the new `locals_kept` excludes that witness. If the theorem is still false, give the new counterexample and stop; do not change the statement.
- The same branch has reusable pieces from that run (`exprSimAbiEncodeArgsFlatPath`, `...FlatCall`, `...FlatContracts`, `...Legacy`, `...HeaderFrame`). Read them with `git show bot/opus/seq-1309-harvest-merge:<path>` and port what helps. Leave out its probes and counterexample theories.
- `dynamic_local_window_kept` (`lowering/abiEncodeArgsWindowsScript.sml`) was written against an older `locals_kept`. Fix or restate it, and its users, as needed; it is not frozen.

Likely needed ports, in the order they build: `abiEncodeArgsWindows`, `abiArgsLabelBoundary` (uses the old `expr_sim_apply` and `expr_post_def`/`expr_val_rel_def`, now in `loweringPosts`), `abiEncodeMaterialize`, `abiEncodeArgsSim`, `abiEncodeArgsCase`. The non-sim lemmas in them (frame, footprint, label and post lemmas) mostly carry over.

## Domain Constraints

- Don't change theories outside the harvested `abi*` ones listed above and new `exprSimAbiEncodeArgs*` ones.
- No TRY/ORELSE around proof search, no timeout overrides, no unsafe tactics.

## Available Resources

- `lowering/exprSimWordArgsScript.sml`: `lower_word_args_sim`, `wb_args_exit`, `wb_args_post`, the cons composition.
- `lowering/exprSimHashScript.sml`: `expr_sim_suffix`, `hash_run_path` (a prefix sim followed by a counted fragment).
- `lowering/exprSimDefsScript.sml`, `lowering/loweringPostsScript.sml`: `expr_sim`, `expr_vv_sim`, `exprs_case`, `expr_post`, `expr_val_rel`, `expr_val_at`, `wb_frame`.
- `lowering/fragGasModeScript.sml`, `lowering/fragGasPathScript.sml`, `lowering/fragGasSeqScript.sml`: `gas_marked_path` and its composition lemmas.
- `lowering/exprSimAbiGasBridgeScript.sml`: `frag_code`, `frag_gas_free`, `frag_exec_gas_path`.
- `lowering/abiEncodeArgsSimScript.sml`, `lowering/abiEncodeArgsCaseScript.sml`: the old proof, whose structure (`abi_args_ready`, the captured/uncaptured cons sims) is a guide.
