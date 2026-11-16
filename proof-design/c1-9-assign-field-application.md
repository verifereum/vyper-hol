# C1.9.1 — Assign local-field compiler-cut diagnostic

## Scope and result

This is an application diagnostic, **not a new production export or a proof of
`bodyFullAssign.body_assign_attr_local_full`**. No frozen statement or semantic
definition is changed. C1.19.4 retains sole ownership of the D0015 approved
Address/Read/Store producers; this diagnostic neither imports an unpublished
candidate nor implements a second producer.

The compiler cut and five RHS transports through ADD kernel-check. Application
of `unwrap_value_origin_ptr` matches the intended continuation and exposes two
remaining premise groups: constructor LocCode robust-memory safety and retention
of the original RHS ghosts through ADD. The temporary full-application test
intentionally omits those transported inputs and stops at `FAIL_TAC`; it is not a
falsehood result, an admission, or an external-precondition finding. No evidence
currently requires a new production header/export. Root assembly remains open.

## 1. Checked root-side typing and compiler cut

`assign_field_compiler_cut_probe` uses only a subset of the frozen root inputs:
`expr_sim_inv`, supported/type-checked assignment, local StructT lookup, field
type, word-field condition, and the actual `stmt_env` equation. It derives:

* `supported_expr tops e`, `well_typed_expr env e`, and `expr_type e = fty`;
* the unchanged compile environment and its local PtrVar/type metadata;
* field metadata in `get_struct_fields`;
* the actual order **compile_expr → ADD → unwrap_value → MSTORE**.

In particular, it does not treat `lower_value` as contiguous with compile_expr.
The typing conversion uses `type_widens_to_word`; environment/field metadata use
`expr_sim_inv_local` and `attribute_type_struct_field`; the final decomposition
is `stmtSimAssignAttr.assign_attr_local_code_parts`.

## 2. Checked conditional transport at the approved Address outcome

The exact complete D0015-approved formulas were read as approval-only text
from tool output `TO_assignment_cases-L0033-20261116T221047342908Z_m0180_t001`
(re-read as `TO_assignment_cases-L0065-20261116T221904369197Z_m0050_t001`).
The text's historical PROPOSED status is superseded by D0015's exact approval;
this does not supply proof credit. Only its following explicit outcome equations
are assumed in the transport test: concrete updated runtime state `q`,
`G' = step_prov ...`, and `tn' = step_taint ...`, for ADD at `sm`.
The test is conditional on these equations, **not** an invocation or certification
of `local_field_address_full`.

From those equations and the listed RHS inputs, the checked test transports:

1. uniform `vv_post` to `q`, retaining the **original bound `sm`**;
2. `vv_store_bound` to `q`;
3. `ptr_vv_ok` to `(G',tn',q)`;
4. the stack-value buffer obligation to `(G',q)`;
5. the located-memory buffer obligation to `(G',q)`.

Freshness follows from `compiler_compile_var` and `emitted_insts_emit_op`.
`vv_post_update_var` permits the target end-bound to remain `sm`: the intervening
fresh ADD is not a compiler-bound mismatch requiring a new interface.
The other transports use `vv_store_bound_frame_mem_src`,
`binop_source_ptr_vv_ok`, and `binop_source_ptr_buf_ok`.

Passing evidence for the first two tests:
`TO_assignment_cases-L0065-20261116T221904369197Z_m0039_t001`.
The complete source below reproduces both tests before the deliberate failure.

## 3. Exact unwrap application result and its limits

Current-source recheck:
`holbuild(targets=["assignFieldApplicationProbeTheory"], timeout=1800)`
returned the expected proof failure at
`FAIL_TAC "first residual application premises"` in
`assign_field_unwrap_application_probe`:
`TO_assignment_cases-L0065-20261116T221904369197Z_m0049_t001`.
The two preceding theorems were passed before this failure. Earlier identical
residual evidence is `TO_assignment_cases-L0065-20261116T221904369197Z_m0042_t001`.

After `strip_tac >> irule unwrap_value_origin_ptr >> simp[]`, the single
remaining formula is:

```sml
(?ty vv'.
  (!x. vv_operand vv' = Var x ==> not_fresh_at sm x) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx e es sa sm s0 ee tv vv' q) /\
  (!t p. vv' = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G' q) /\
  unwrap_value cenv vv' sn = (op,su) /\
  compile_expr cenv ty e sa = (vv',sm) /\
  (cenv.ce_is_ctor /\ vv_location vv' = SOME LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
      !w. eval_operand (vv_operand vv') q = SOME w ==>
        type_memory_size rty + w2n w <= lo /\
        !mem. mem_agree_outside tn'.t_mem q.vs_memory mem ==>
          val_in_memory rty val (w2n w) mem) /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv' q /\
  ptr_vv_ok cx (expr_type e) tv vv' ee G' tn' q) /\
ghost_kept_at lo cenv es sa Gi ti s0 G' tn'
```

Natural witnesses are `ty = expr_type e` and `vv' = vv`. Freshness, uniform
value post, located buffer and compile/unwrap equations are already explicit
inputs; the first-slot type normalization is `post_value_type_word`, since
the test assumes `is_word_type (expr_type e)`.

The **two substantive residual groups not discharged by this test** are:

* the displayed constructor LocCode read/safe-low-memory/robust-memory fact
  at `q,tn'`;
* `ghost_kept_at lo cenv es sa Gi ti s0 G' tn'`, composing the original RHS
  kept ghosts with the Address update.

These must not be added to the frozen root as new assumptions. Canonical
`expr_vv_sim_full_def` already supplies the constructor fact at the RHS state
(lines 177–184) and original kept ghosts (line 190); source evidence
`TO_assignment_cases-L0065-20261116T221904369197Z_m0043_t001`, re-read as
`TO_assignment_cases-L0065-20261116T221904369197Z_m0050_t003`.
The concrete Address equations preserve memory and update only a fresh variable;
existing binop frames (including `copy_len_binop_ghost_frame`) are the next
candidate transport tools. This report does **not** claim those two transports
have been proved. In particular, the two `ghost_kept_at` hypotheses in the
application test do not magically compose without the requisite compiler-bound
and frame reasoning.

No full Address application from the entire frozen antecedent, source outcome
composition, exceptional path, final MSTORE application, or frozen-root proof is
certified here. This is the first remaining transport obligation, not a complete
root skeleton.

## 4. Store-boundary comparison (signature only)

D0015's Store consumes the actual pre-MSTORE state, whole-local scope/layout,
field coverage, typed clean operand and the uniform state/ghost bundle. It
returns the same concrete MSTORE endpoint for every horizon, with the source
scope field updated. The compiler-cut test supplies its instruction shape.
After unwrap, the consumer still must derive actual word evaluation/cleanliness,
`store_lays_out`, field coverage, low bound, and preserved local address, and
apply the separately owned Store producer. No kernel Store application was made
in this diagnostic; Read is AugAssign-only. No independently existential
marked/memory execution is used as joint path evidence.

The comparison with `buffer_emit_add_vv_marked_path_horizons` is only about
value preservation: a marked-path theorem is not a `gas_origin_ptr_path`.
The checked generic `vv_post_update_var` transport above avoids relying on that
marked-path wrapper or assuming that ADD commutes with unwrap.

## 5. Reproduction, integrity, and cleanup

Complete temporary test source follows. To reproduce both successes plus the
exact residual, temporarily save it as
`lowering/assignFieldApplicationProbeScript.sml` and build
`assignFieldApplicationProbeTheory` on this lane's preserved receiver. It is
not installed as a production theory. To build only the successful tests,
truncate immediately after `assign_field_add_transport_probe`'s `QED`.

Admission-primitive audit of the full temporary source:
`grep` for `cheat|mk_thm|new_axiom|mk_oracle_thm|mk_axiom_thm|disk_thm|mk_proof_thm`
returned **no matches** in
`TO_assignment_cases-L0065-20261116T221904369197Z_m0050_t004`.
The diagnostic failure is explicit, not hidden by an oracle. All production
sources and frozen headers are untouched. The temporary script is removed
before publishing this report. The successful-only final build and cleanup
receipts are recorded in the closing C1.9.1 episode.

## Complete temporary source (including deliberately open application)

```sml
(* Temporary C1.9.1 conditional application diagnostic, not a producer. *)
Theory assignFieldApplicationProbe
Ancestors
  bodyFullPreds bodySimFull targetPlaceSim stmtSimAssignAttr
  bodyExprPreFacts supportedStmts exprSimHypsDefs vyperTypeSystem
  vyperTypeInvariants exprLowering compileEnv stmtLowering
  loweringPosts bodyFullUnwrap bodyPtrDefs fragGasOriginPtr
  vyperStorageFootprint venomState finite_map list
  exprSimVVFrame exprOperandVar emitHelperProps freshWrites
  bodyPtrMakeArrayAddFrame exprSimMemDefs typedCopyPtr loweringStateRelDefs
  bodyFullUnwrapRun

Theorem assign_field_compiler_cut_probe:
  expr_sim_inv cenv cx env es /\
  supported_stmt tops bindings
    (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
  type_stmt env ret_ty
    (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) = SOME env' /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  attribute_type env.type_defs (StructT sid) fld = SOME fty /\
  is_word_type fty /\
  stmt_env cenv lctx ret_ty
    (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) sa = (c,sf) ==>
  supported_expr tops e /\ well_typed_expr env e /\ expr_type e = fty /\
  c = cenv /\
  ?p sz fsz vv sm dst sn op su.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty,fsz) /\
    compile_expr cenv (expr_type e) e sa = (vv,sm) /\
    emit_op ADD [Var p; Lit (n2w (struct_field_offset
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))]
      sm = (dst,sn) /\
    unwrap_value cenv vv sn = (op,su) /\
    emit_void MSTORE [dst;op] su = ((),sf)
Proof
  strip_tac >>
  `supported_expr tops e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  `well_typed_expr env e /\ expr_type e = fty` by
    (gvs[type_stmt_def, atarget_accepts_def, well_typed_expr_def,
         AllCaseEqs()] >>
     Cases_on `FLOOKUP env.var_assignable id` >> gvs[] >>
     Cases_on `x` >> gvs[] >> metis_tac[type_widens_to_word]) >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME (StructT sid)` by fs[expr_sim_inv_def] >>
  drule attribute_type_struct_field >>
  disch_then (qspecl_then [`sid`,`fld`,`fty`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `is_word_type (expr_type e)` by simp[] >>
  drule_all assign_attr_local_code_parts >> strip_tac >> gvs[] >>
  metis_tac[]
QED

(* Conditional application at the concrete Address outcome. These three
   equations are projections of the exact D0015 approved conclusion, NOT
   invocation of the pending producer. All other inputs are RHS facts. *)
Theorem assign_field_add_transport_probe:
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [Var p; Lit (n2w (struct_field_offset flds fld))]
    sm = (Var out,sn) /\
  q = (update_var out (bw + n2w (struct_field_offset flds fld)) s
       with vs_inst_idx := SUC s.vs_inst_idx) /\
  G' = step_prov PG G
    (mk_inst sm.cs_next_id ADD
      [Var p; Lit (n2w (struct_field_offset flds fld))] [out])
    (update_var out (bw + n2w (struct_field_offset flds fld)) s) /\
  tn' = step_taint
    (mk_inst sm.cs_next_id ADD
      [Var p; Lit (n2w (struct_field_offset flds fld))] [out]) s
    (update_var out (bw + n2w (struct_field_offset flds fld)) s) tn /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
    ee tv vv s /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!t pp. vv = LocatedValue t pp /\ pp.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e pp.ptr_operand G s) ==>
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx e es sa sm s0 ee tv vv q) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
    ee tv vv q /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G' tn' q /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G' q) /\
  (!t pp. vv = LocatedValue t pp /\ pp.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e pp.ptr_operand G' q)
Proof
  strip_tac >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sm z` by
    metis_tac[cj 1 compiler_compile_var] >>
  `~not_fresh_at sm out` by
    (drule emitted_insts_emit_op >>
     simp[not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  `!z. vv_operand vv = Var z ==> z <> out` by metis_tac[] >>
  gvs[] >>
  conj_tac
  >- (rpt strip_tac >> simp[] >> irule vv_post_update_var >>
      simp[] >> qexists_tac `sm` >> simp[]) >>
  conj_tac
  >- (irule vv_store_bound_frame_mem_src >>
      qexists_tac `s` >> simp[update_var_def] >>
      Cases_on `vv_operand vv` >>
      gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  conj_tac
  >- (irule binop_source_ptr_vv_ok >> simp[]) >>
  conj_tac >> rpt strip_tac >> gvs[] >>
  irule binop_source_ptr_buf_ok >> simp[] >>
  gvs[contextTheory.vv_operand_def]
QED

(* A deliberately open application test: the five transported facts above
   are explicit hypotheses, as are the approved Address output projections.
   The report records the FIRST missing premise rather than hiding it. *)
Theorem assign_field_unwrap_application_probe:
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  unwrap_value cenv vv sn = (op,su) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sn su func /\ fn_inst_ids_distinct func /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx e es sa sm s0 ee tv vv q /\
    ghost_inv_at (DF H) lo d cenv cx ee G' tn' q) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
    ee tv vv q /\
  alloca_history func q /\ s0.vs_alloca_next <= q.vs_alloca_next /\
  ~q.vs_halted /\ q.vs_current_bb = sn.cs_current_bb /\
  q.vs_inst_idx = LENGTH sn.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G' tn' q /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G' q) /\
  (!t pp. vv = LocatedValue t pp /\ pp.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e pp.ptr_operand G' q) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  ghost_kept_at lo cenv ee sm G tn s G' tn' /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z Gz tnz.
    read_result cx tv ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (q,G',tn') [] (OK z,Gz,tnz) /\
      expr_post H ctx func cenv cx e es sa su s0 ee v op z /\
      ghost_inv_at (DF H) lo d cenv cx ee Gz tnz z) /\
    (~is_word_type (post_value_type cenv e) ==>
      vv_at cenv cx (post_value_type cenv e) sa su ee tv
        (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    (~is_word_type (post_value_type cenv e) ==>
      vv_at cenv cx (post_value_type cenv e) sa sm ee tv
        (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z \/
      vv_at cenv cx (post_value_type cenv e) sn su ee tv
        (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    z.vs_current_bb = su.cs_current_bb /\
    z.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func z /\ q.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op Gz tnz z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op Gz z) /\
    (~is_word_type (post_value_type cenv e) ==>
      !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
        eval_operand op z = SOME w ==>
        type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 Gz tnz /\
    (!x. not_fresh_at sn x ==>
      lookup_var x z = lookup_var x q /\ FLOOKUP Gz x = FLOOKUP G' x /\
      op_taint tnz (Var x) = op_taint tn' (Var x)) /\
    wb_frame cenv ee ee sn q z /\
    ghost_kept_at lo cenv ee sn G' tn' q Gz tnz
Proof
  strip_tac >> irule unwrap_value_origin_ptr >> simp[] >>
  FAIL_TAC "first residual application premises"
QED
```

## Final receipts

* Successful-only current-source build after removing the deliberately failing
  third test: `TO_assignment_cases-L0065-20261116T221904369197Z_m0052_t001`
  (`assignFieldApplicationProbeTheory`, 1/1 theories done).
* The full diagnostic source admission audit and expected-failure build above
  precede this truncation; both source variants are reconstructed from the
  complete listing. The truncation adds no proof or premise.
* Publication contains this report only; the temporary theory is removed.
  No production compiler theorem, producer contract, or frozen root is edited.
