# TASK: uint2str simulation under the counted gas judgment

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/exprSimUint2StrScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_uint2str_typed_vv_sim:
  expr_body_pre cenv cx env (Builtin ann (Uint2Str n) [e]) es /\
  expr_sim ctx func cenv cx ty e es ==>
  expr_vv_sim ctx func cenv cx ty (Builtin ann (Uint2Str n) [e]) es

Theorem compile_typed_unary_builtin_vv_sim_with_initial_rel:
  expr_body_pre cenv cx env (Builtin ann bt [e]) es /\
  expr_sim ctx func cenv cx ty e es /\ expr_type e = BaseT bty /\
  ~precompile_builtin bt /\ bt <> Len /\ builtin_args_length_ok bt 1 /\
  (!sa sb vv. compile_expr cenv ty (Builtin ann bt [e]) sa = (vv,sb) ==>
    ?x sm. lower_value compile_expr cenv ty e sa = (x,sm) /\
      code x sm = (vv,sb)) /\
  (!x. cs_appends (code x)) /\
  (!sa sm sb x vv s0 v gs es' s.
    lower_value compile_expr cenv ty e sa = (x,sm) /\
    code x sm = (vv,sb) /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    local_ptrs_reserved cenv sm /\
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
      (INL v,es') /\
    value_has_type (BaseTV bty) v /\ expr_sim_inv cenv cx env es' /\
    expr_res_ok (builtin_result cx es'.accounts ann bt [expr_type e] [v]) /\
    stmt_state_rel ctx func cenv cx es s0 /\
    expr_post ctx func cenv cx e es sa sm s0 es' v x s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?n r. gas_marked_path F ctx func s n r /\
      ((?t rv. r = OK t /\
          builtin_result cx es'.accounts ann bt [expr_type e] [v] = INL rv /\
          vv_post ctx func cenv cx (Builtin ann bt [e]) es sa sb s0 es'
            (Value rv) vv t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
       (exit_result r /\
        expr_exit (builtin_result cx es'.accounts ann bt [expr_type e] [v]) r))) ==>
  expr_vv_sim ctx func cenv cx ty (Builtin ann bt [e]) es

Theorem uint2str_expr_types:
  well_typed_expr env (Builtin ann (Uint2Str n) args) ==>
  ?e k. args = [e] /\ ann = BaseT (StringT n) /\
        expr_type e = BaseT (UintT k) /\ 78 <= n

Theorem compile_uint2str_layout:
  compile_uint2str op n sz sa = (out,sb) ==>
  ?ba a. compile_alloc_buffer sz sa = (ba,a) /\
         out = Var (u2s_var a 2) /\ u2s_layout a op ba.buf_operand n sb
```

`expr_vv_sim` and `expr_sim` are in `lowering/exprSimDefsScript.sml`;
`gas_outcome` in `lowering/gasOutcomeScript.sml`; `gas_summary_at`,
`gas_marked_exec` in `lowering/gasSummaryScript.sml`; `gas_marked_path` in
`lowering/fragGasModeScript.sml`; `compile_uint2str` in
`lowering/defs/builtinStringsScript.sml`.

**Do not modify these statements.** Prove them as-is, or produce a counterexample.

Every other theorem in `lowering/exprSimUint2StrScript.sml` is weakly frozen:
no theory outside this file uses them except `uint2str_expr_types`, so you may
restate, generalise, split, make `[local]` or delete them as the proofs need.

## Completion Criteria

1. `holbuild -j4 build exprSimUint2StrTheory` passes with zero CHEAT warnings in `exprSimUint2StrTheory` and zero failures.
2. The four statements above are unchanged.
3. No duplicate or near-duplicate lemmas: search the `lowering/` theories before adding a helper; each helper exists once, in its most general form. If a helper you need exists as `[local]` in an ancestor, remove its `[local]` rather than copying it.
4. No change to any definition. Change only `lowering/exprSimUint2StrScript.sml` (and the `[local]` removals of item 3).
5. Many ancestor theories in this worktree have their proofs replaced by `cheat` (uncommitted; listed in `.overlay-files`). That is expected: leave them as they are and never commit them, `.overlay-files`, or any other file you didn't mean to change. Commit only the files of item 4, by name.

**If a theorem is false as stated:** produce a concrete counterexample, state the tightest sufficient fix, and stop. Do NOT weaken the statement.

## Build

```
holbuild -j4 build exprSimUint2StrTheory
```

## Background

The compiler-correctness proof for Vyper's lowering to Venom IR changed its
expression judgment. `expr_vv_sim` now takes the whole source action and its
entry state and asks for a `gas_outcome`: either an actual counted target path
(`gas_marked_path` / `gas_marked_exec`) whose explicit GAS readings, fed to the
source, produce the source result, with a post on a normal finish or an exit
post on an exit, or an exempt certificate. The source's reads of `msg.gas`
make its result depend on the gas readings, hence `es with gas_obs := gs`.

`uint2str(x)` lowers (`compile_uint2str`) to a buffer allocation and a small
loop of blocks (setup, check, cond, body, final, zero: the `u2s_*`
templates) that stores x's decimal digits right to left and puts the length
word below the leading digit. The file's run lemmas (`u2s_*_run`,
`u2s_*_transition`, `u2s_*_exit`, `u2s_loop`) were proved for the old
judgment; the `u2s_*_path` lemmas and `uint2str_numeric_path` /
`uint2str_typed_path` are a partial migration to counted paths. The loop
issues no GAS instruction, so each path is GAS-free (count 0) on success.

`compile_typed_unary_builtin_vv_sim_with_initial_rel` is the generic
unary-builtin lemma: from a counted path after the operand, it gives
`expr_vv_sim` for the builtin. `compile_uint2str_typed_vv_sim` instantiates it.

## Domain Constraints

- No `cheat`, no new axioms, no oracles, no change to definitions.
- Every ordinary branch needs an actual counted path (`gas_marked_path`).
- holbuild's per-step tactic timeout (2.5 s) is fixed: never raise it. A slow
  step is a proof bug; split it.
- Never wrap `metis_tac` or other search in `TRY`/`ORELSE`; select goals with
  `>~`, `>-`, `>|`.
- Qualify lemmas from indirect ancestors (`fooTheory.bar`).
- Proofs at most ~50 lines each; give a hard subgoal its own lemma.
- Follow `AGENTS.md` at the project root.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Target file | `lowering/exprSimUint2StrScript.sml` | the theorems; the run lemmas and the partial path chain |
| Expression judgments | `lowering/exprSimDefsScript.sml`, `lowering/exprSimPropsScript.sml`, `lowering/exprSimStackScript.sml` | `expr_sim`, `expr_vv_sim`, posts; `expr_sim_suffix` is in `lowering/exprSimHashScript.sml` |
| Gas outcome | `lowering/gasOutcomeScript.sml`, `lowering/gasSummaryScript.sml`, `lowering/gasContextScript.sml` | `gas_outcome`, `gas_summary_at`, `gas_marked_exec`, `gas_admissible` |
| Paths | `lowering/fragGasModeScript.sml`, `lowering/fragGasPathScript.sml`, `lowering/fragGasPathMemScript.sml` | `gas_marked_path`, `gas_marked_path_then`, path rules |
| Worked path chains | `lowering/storageCopyGasPathScript.sml` | `storage_copy_seq_path`, `storage_copy_jump_path`: block-to-block path chaining for a similar loop |
| Similar migrated builtins | `lowering/exprSimHashScript.sml`, `lowering/exprSimAllocScript.sml`, `lowering/exprSimLiteralBufferScript.sml` | `hash_unary_suffix_cut`, allocation paths, buffer posts |
| Frag execution | `lowering/fragExecScript.sml` | `frag_exec`, block running |
| Venom semantics | `venom/defs/venomExecSemanticsScript.sml` | `run_block`, instruction steps |
| Source semantics | `semantics/vyperInterpreterScript.sml`, `semantics/vyperContextScript.sml` | `eval_expr`, `evaluate_builtin`, `builtin_result` |
