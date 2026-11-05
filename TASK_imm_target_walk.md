# TASK: Counted target walk to a constructor immutable (imm_target_walk)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/exprSimPopImmutableTargetScript.sml (project root is this directory)

## Theorem Statement (FROZEN)

```sml
Theorem imm_target_walk:
  !bt nocalls ctx func cenv cx env es ty src id sa sb r s0.
    cx.in_deploy /\ cenv.ce_is_ctor /\
    target_idx_case nocalls ctx func cenv cx bt /\
    (nocalls ==> int_calls_target bt = []) /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) /\
    (!ty0. FLOOKUP env.bare_global_assignable (src,id) = SOME ty0 ==>
           cenv.ce_module_var_type (src,id) = SOME ty0) /\
    expr_sim_inv cenv cx env es /\ target_indices_pre cenv cx env bt /\
    EVERY pure_expr (target_indices bt) /\
    type_place_target env bt = SOME (Type ty) /\
    compile_get_target_ptr compile_expr cenv bt sa = (r,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    gas_admissible (eval_base_place cx bt) target_res_ok es /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (eval_base_place cx bt) (es,s0)
      (\res ee t. ?pv. res = INL pv /\ ee = es with gas_obs := [] /\
         imm_target_post ctx func cenv cx es sa sb s0 ee pv ty r t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
```

Supporting definitions (in the same file):

```sml
Definition imm_place_at_def:
  (imm_place_at cenv cx (es:evaluation_state)
     (PlaceR (ImmutablePlace src id path)) (w:bytes32)
     ty <=>
     ?off itv iv k tv v.
       src = cenv.ce_module /\
       FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
       off + type_memory_size itv < dimword (:256) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
                  NONE => FEMPTY
                | SOME imms => get_source_immutables src imms) id =
         SOME (itv,iv) /\
       mem_path_offset itv path = SOME (k,tv) /\
       evaluate_subscripts itv iv path = INL v /\
       evaluate_type (get_tenv cx) ty = SOME tv /\
       w = n2w (off + k)) /\
  (imm_place_at cenv cx (es:evaluation_state) pv w ty <=> F)
End

Definition imm_target_post_def:
  imm_target_post ctx func cenv cx es sa sb s0 es' pv ty
    (r : operand # data_location option # place_ty option) s <=>
    stmt_state_rel ctx func cenv cx es' s /\
    (?w. eval_operand (FST r) s = SOME w /\ imm_place_at cenv cx es' pv w ty) /\
    FST (SND r) = SOME LocCode /\
    SND (SND r) = SOME (ValPT ty) /\
    (!x. FST r = Var x ==> not_fresh_at sb x) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
    locals_kept cenv es s0 s
End
```

**Do not modify this statement or these two definitions.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build exprSimPopImmutableTargetTheory` passes and `imm_target_walk` has no `cheat`. Ancestor theories may carry pre-existing admissions (some are admitted in this worktree by an uncommitted overlay; leave those files alone); add no new cheat, axiom or oracle.
2. Helper lemmas go in `lowering/exprSimPopImmutableTargetScript.sml`, or in a new leaf theory `lowering/exprSimPopImmutableWalkScript.sml` that `exprSimPopImmutableTarget` imports. Do not edit any other existing file, and do not change any other theorem's statement in the target file. Keep probes inside these files and remove them before finishing.
3. No duplicate lemmas: reuse existing ones rather than restating them.
4. Commit only the files of criterion 2 (never `.alan/`, `PLAN_`/`STATE_`/`LOG_`/`LEARNINGS_`/`DOSSIER_`/`FOCUS_` files, tool output, or the overlaid files that `git status` shows modified). Every commit message ends with the two lines:
   `Bot: opus (Claude Opus 5.5)` and `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`

**If the theorem is false as stated:** give the counterexample against the definitions (concrete target, states), state the tightest sufficient fix, and do not weaken the statement.

## Build

```
holbuild -j4 build exprSimPopImmutableTargetTheory
```

## Background

In Vyper's constructor, a complex immutable lives in a memory buffer at a fixed offset (`ImmutableLoc off`, base operand 0 by `immutable_base_zero`). For an assignment target rooted at such an immutable (e.g. `self.a.x[i]`), `compile_get_target_ptr` emits code that computes the byte address of the member: the root gives `Lit off` with location `LocCode`; each subscript adds an element offset after bounds checks (dynamic arrays read their length word through `compile_ptr_load` with `LocCode`, which in the constructor is `ADD [off; base]; ILOAD`, a memory read); each attribute adds a struct field offset. The source side `eval_base_place cx bt` looks the immutable up (`lookup_global`) and extends the place path by `extend_place`. The theorem says: the lowered fragment, run from a related state, either ends at the place's address (`imm_place_at`: offset `off + k` with `k` from `mem_path_offset`) with all frames kept and the source state unchanged, or exits as the source does (`expr_exit`, e.g. an out-of-bounds index raising in both). Index expressions are pure and their simulation judgments are given (`target_idx_case`). It is used for `x.pop()` on a member of a constructor immutable.

## Domain Constraints

- holbuild only; never raise the tactic timeout (2.5 s per step); no `TRY`/`ORELSE` around metis or other search; no `let` in statements; build at most `-j4`.
- Never run `holbuild run` or `holbuild repl`.
- Do not change any definition (`semantics/`, `frontend/`, `lowering/defs/`, `venom/`) or any judgment (`exprSim*Defs`, `exprSimHyps*`, `bodySim*`).

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Target file | lowering/exprSimPopImmutableTargetScript.sml | statement, `imm_place_at_def`, `imm_target_post_def`, `body_target_idx_case` |
| Lowering of targets | lowering/defs/exprLoweringScript.sml | `compile_get_target_ptr`, `compile_array_subscript`, `compile_dynarray_pop` |
| Pointer loads | lowering/defs/contextScript.sml | `compile_ptr_load`, `compile_imm_load_word`, `compile_fixed_region_with_id` |
| Immutable word execution | lowering/proofs/immutableWordExecutionScript.sml | `immutable_word_ctor_load`, `immutable_word_add_zero`, `immutable_word_read_frame` |
| Other immutable proofs | lowering/proofs/immutable*Script.sml | layout, relation, memory frame lemmas |
| Immutable relation | lowering/defs/compileEnvScript.sml, lowering/defs/immutableValueScript.sml | `immutables_rel_def`, `immutable_base_zero_def`, `immutable_value_bytes_rel` |
| State relation | lowering/exprLoweringPropsScript.sml | `stmt_state_rel_def`, `immutable_alloca_sep_def` |
| Value encoding | lowering/defs/valueEncodingScript.sml | `val_in_memory` |
| Posts, offsets | lowering/loweringPostsScript.sml | `mem_path_offset`, `vv_post_def`, `immutable_holds` |
| Invariants | lowering/exprSimHypsDefsScript.sml | `expr_sim_inv_def` (bare_globals clause: `ImmutableLoc off`, `off + size < dimword`), `expr_body_pre_def` |
| Type invariants | semantics/prop/vyperTypeInvariantsScript.sml | `env_context_consistent_def`, `bare_global_assignable_complete_def`, `env_consistent_bare_global_ready` |
| Target sim infrastructure | lowering/targetPlaceSimScript.sml, lowering/targetPlaceSimDefsScript.sml, lowering/targetPlaceSimCasesBaseScript.sml, lowering/targetPlaceSimCasesScript.sml, lowering/targetSubscriptCaseScript.sml | `target_idx_case_def`, `target_indices_pre_def`, `target_res_ok`, `target_sim`, `target_case_all`, `target_indices_def`, `base_assignment_target_induct`; the storage/memory-root walks to imitate |
| Gas judgments | lowering/gasOutcomeScript.sml, lowering/gasContextScript.sml | `gas_outcome`, `gas_admissible` |
| Source semantics | semantics/vyperInterpreterScript.sml, semantics/vyperStateScript.sml | `eval_base_place` (line ~1743), `lookup_global`, `extend_place`, `evaluate_subscripts` |
| Purity | semantics (grep `pure_expr`), `eval_expr_preserves_state` | pure index evaluation leaves the state unchanged |
| Similar walk (storage root, pure indices) | lowering/exprSimPopNestedBaseScript.sml | `pop_target_frag`, `pop_nested_storage_pure_sim` |
| Notes | ~/notes/repos/vyper-hol/gas-join-counted-port-gotchas.md, gas-judgment-adapters.md | GAS judgment gotchas |

## Notes

The statement was checked against the definitions before launch; no counterexample found. The check's reasoning: the root's entry, `ce_hashmap_info = NONE` and the size bound come from `expr_sim_inv`; the root's type comes from `bare_global_assignable` (the storage disjunct of `type_place_target` is ruled out by `env_context_consistent` and the `find_var_decl_by_name = NONE` premise), which the premise puts in `ce_module_var_type`; an uninitialized immutable makes `lookup_global` raise a TypeError, which `gas_admissible … target_res_ok` excludes; dynamic-array length words are covered by the mask in `immutable_value_bytes_rel`; the walk only reads memory.
