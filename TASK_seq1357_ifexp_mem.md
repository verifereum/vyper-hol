# TASK: memory-safe counted simulation of the conditional expression (bodyIfExpMemory)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/bodyIfExpMemoryScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

Two theorems in `lowering/bodyIfExpMemoryScript.sml`:

```sml
Theorem compile_ifexp_vv_sim_mem:
  !ctx func cenv cx ty t c a b es.
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    (is_word_type t ==> ?tvt. evaluate_type (get_tenv cx) t = SOME tvt) /\
    (~is_word_type t ==>
     !e. (e = a \/ e = b) ==>
         lowered_value_type cenv e = expr_type e \/
         is_bytestring_type (expr_type e) /\
         is_bytestring_type (lowered_value_type cenv e) /\
         arg_type_fits (lowered_value_type cenv e) (expr_type e) \/
         same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
       type_memory_bytes cenv t = type_memory_size tvt /\
       type_memory_size tvt < 2 ** 64) /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    (!e sa sb op. (e = a \/ e = b) /\
       lower_value compile_expr cenv ty e sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) c es /\
    (!gs tv es1.
       (do result <- eval_expr cx c; read_result cx result od)
         (es with gas_obs := gs) = (INL tv, es1) ==>
       expr_sim_mem ctx func cenv cx ty a es1 /\
       expr_sim_mem ctx func cenv cx ty b es1 /\
       expr_vv_sim_mem ctx func cenv cx ty a es1 /\
       expr_vv_sim_mem ctx func cenv cx ty b es1 /\
       !e gs' v es2. ~is_word_type t /\ (e = a \/ e = b) /\
         (do r <- eval_expr cx e; read_result cx r od)
           (es1 with gas_obs := gs') = (INL v, es2) ==>
         ?tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ value_has_type tvt v) ==>
    expr_vv_sim_mem ctx func cenv cx ty (IfExp t c a b) es

Theorem compile_ifexp_word_sim_mem:
  !ctx func cenv cx ty t c a b es.
    is_word_type t /\
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    (!e sa sb op. (e = a \/ e = b) /\
       lower_value compile_expr cenv ty e sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) c es /\
    (!gs tv es1.
       (do result <- eval_expr cx c; read_result cx result od)
         (es with gas_obs := gs) = (INL tv, es1) ==>
       expr_sim_mem ctx func cenv cx ty a es1 /\
       expr_sim_mem ctx func cenv cx ty b es1 /\
       expr_vv_sim_mem ctx func cenv cx ty a es1 /\
       expr_vv_sim_mem ctx func cenv cx ty b es1) ==>
    expr_sim_mem ctx func cenv cx ty (IfExp t c a b) es
```

Definitions: `expr_sim_mem_def`, `expr_vv_sim_mem_def` in `lowering/exprSimMemDefsScript.sml`;
`gas_outcome_def` in `lowering/gasOutcomeScript.sml`.

**Do not modify these statements.** Prove them as-is, or produce a counterexample.

The other theorems in `lowering/bodyIfExpMemoryScript.sml` are NOT frozen: they are an
older (pre-gas-counting, fixed-run `frag_exec_mem`) version of this proof. Keep, restate,
replace or delete them as the proof needs; their old proofs are a source of
memory-specific steps (alloca_history, frontier facts for ASSIGN/JNZ/JMP).

## Completion Criteria

1. `holbuild -j4 build bodyIfExpMemoryTheory` passes with no CHEAT from
   `lowering/bodyIfExpMemoryScript.sml` or any new helper theory you add, and no FAIL.
   Ancestor theories outside this task have their proofs admitted locally (cheat) on
   purpose; those inherited CHEAT warnings are expected and are not yours to fix.
2. No duplicate or near-duplicate lemmas: search before adding one; each helper exists
   once in its most general form.
3. Helpers go in `lowering/bodyIfExpMemoryScript.sml` or new leaf theories next to it
   (e.g. `lowering/bodyIfExpMemory<Something>Script.sml`); do not edit any other
   existing theory file.

**If a theorem is false as stated:**
- Produce a counterexample and state the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build bodyIfExpMemoryTheory
```

## Background

The Vyper-to-Venom lowering is proved correct by simulation: `expr_sim` / `expr_vv_sim`
say the lowered code of an expression runs to a state related to the source result,
counted over the GAS-reading observations (`gas_outcome`). `expr_sim_mem` /
`expr_vv_sim_mem` are their memory-safety twins: `gas_outcome T` (the memory-checked run)
instead of `gas_outcome F`, `alloca_history func s0` as a hypothesis, and
`alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` in the post.

`x if c else y` lowers (`compile_expr_ifexp`, `compile_expr_ifexp_states` in
`lowering/exprSimIfExpScript.sml`) to c's fragment, a JNZ on its operand, one block per arm
that lowers the arm (`compile_ifexp_arm`: unwrap / copy to the lowered type) and ASSIGNs
its operand to a fresh variable, and a JMP from each arm to a common exit block.

The NON-memory (F) counted version of exactly this proof is fully proved, and is the
template: `alan-ref/exprSimIfExpCounted.sml.txt` (its `compile_ifexp_vv_sim` at line
~2347 and `compile_ifexp_word_vv_sim` ~2460, with local helpers from ~1587 on). That file
is NOT in the build (the in-tree `lowering/exprSimIfExpScript.sml` is an older version
whose statements you may use as ancestors). Port what you need into your own theory.

## Domain Constraints

- HOL4 via holbuild only. Per-step tactic timeout is 2.5 s: never raise it; split slow steps.
- Never wrap metis_tac or other search in TRY/ORELSE; select goals with `>-`, `>~`, `>|`.
- No new axioms, no new definitions unless unavoidable (flag any).
- No `let` in theorem statements.
- Do not edit files outside `lowering/bodyIfExpMemory*Script.sml` and new leaf theories.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Counted F-version template | `alan-ref/exprSimIfExpCounted.sml.txt` | proved `compile_ifexp_vv_sim` (gas_outcome F) and its helpers |
| Old memory version | `lowering/bodyIfExpMemoryScript.sml` (also `alan-ref/bodyIfExpMemoryPreGas.sml.txt`) | pre-counting memory proof of the word ternary |
| Memory judgments | `lowering/exprSimMemDefsScript.sml` | expr_sim_mem, expr_vv_sim_mem |
| Counted outcome machinery | `lowering/gasOutcomeScript.sml`, `lowering/gasSummary*Script.sml`, `lowering/gasExemptCertScript.sml`, `lowering/gasNormalPrefixScript.sml`, `lowering/fragGasPathMemScript.sml`, `lowering/fragGasModeScript.sml` | gas_outcome, gas_summary_at, gas_marked_exec, gas_path / gas_path_mem |
| Memory counted examples | `lowering/exprSimMemoryStackScript.sml`, `lowering/exprSimMemoryValuesScript.sml`, `lowering/bodyExprMemoryScript.sml` | proved gas_outcome T expression proofs |
| Memory statement-if (counted) | `lowering/stmtSimIfPropsScript.sml` (`*_mem` lemmas from line ~715), `lowering/stmtSimIfCountedScript.sml` | memory/counted proof of the if statement: JNZ, branch blocks, jump to exit |
| Fragment memory | `lowering/fragExecMemScript.sml`, `lowering/allocaHistoryFragmentScript.sml`, `venom/proofs/allocaHistoryScript.sml`, `lowering/instMemFrontierScript.sml` | frag_exec_mem, alloca_history, frontier |
| Unwrap path | `lowering/exprSimUnwrapScript.sml` (`unwrap_value_path` ~1703, `expr_sim_of_vv_sim` ~1799) | zero-GAS path of unwrap_value |
| IfExp lowering facts | `lowering/exprSimIfExpScript.sml` | compile_expr_ifexp_states, eval_expr_ifexp_cases, expr_post_ifexp, vv_post_of_expr_post |

## Notes

- The worktree's ancestor proofs outside this task are admitted locally (an overlay); do
  not try to fix or rebuild them, and expect inherited CHEAT warnings from them.
