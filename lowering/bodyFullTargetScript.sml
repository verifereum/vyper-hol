(*
 * Statement targets over the finite-horizon joint judgment: a base target
 * (a local, a module variable, a field or an element of one) resolves to
 * its place and its pointer at one joint endpoint, as expr_sim_full's
 * expression resolves to its value.  targetPlaceSimDefs' target_sim and
 * bodyPtrPopTargetDefs' target_sim_ptr over gas_outcome_full, with the
 * shadow compilation and the initial resources of expr_sim_full.
 *
 * TOP-LEVEL:
 *   target_sim_full       -- eval_base_place's judgment (a place or a mapping)
 *   target_place_sim_full -- eval_target_place's judgment (a place), which
 *                            Append, Pop, AugAssign and Assign bind on
 *   body_target_sim_full, body_target_place_sim_full -- a target meeting
 *     target_pre whose indices have their joint judgments has both
 *)
Theory bodyFullTarget
Ancestors
  bodyFullPreds bodySimFull bodyPtrPopTargetDefs targetPlaceSim
  targetPlaceSimCases targetPlaceSimDefs gasShadow gasOutcomeFull
  loweringPosts exprLowering compileEnv vyperInterpreter vyperState
  vyperAST

val _ = Parse.hide "body";

(* New definition: target_sim_ptr over the joint judgment. *)
Definition target_sim_full_def:
  target_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt es <=>
    !st0 vt sa sb shadow_sa shadow_sb r s0 G0 tn0.
      type_place_target env bt = SOME vt /\
      compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
      compile_get_target_ptr compile_expr cenv (gas_shadow_target bt)
        shadow_sa = (r, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_base_place cx bt) target_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0 (eval_base_place cx bt) (es, s0, G0, tn0)
        (\H res ee G tn t. ?pv. res = INL pv /\
          target_post H ctx func cenv cx es sa sb s0 ee pv vt r t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
          target_ptr_ok cenv pv r G tn t /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt q. expr_exit res q)
End

(* New definition: pop_target_frag_ptr over the joint judgment; a memory
   place is live in the local's current value (targetLocalLive). *)
Definition target_place_sim_full_def:
  target_place_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt es <=>
    !st0 ty sa sb shadow_sa shadow_sb r s0 G0 tn0.
      type_place_target env bt = SOME (Type ty) /\
      compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
      compile_get_target_ptr compile_expr cenv (gas_shadow_target bt)
        shadow_sa = (r, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0 (eval_target_place cx bt) (es, s0, G0, tn0)
        (\H res ee G tn t. ?p. res = INL p /\
          target_post H ctx func cenv cx es sa sb s0 ee (PlaceR p) (Type ty)
            r t /\
          (!id path. p = MemoryPlace id path ==>
             ?entry v. lookup_scopes id ee.scopes = SOME entry /\
                       evaluate_subscripts entry.type entry.value path =
                         INL v) /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
          target_ptr_ok cenv (PlaceR p) r G tn t /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt q. expr_exit res q)
End

Theorem body_target_sim_full:
  !bt DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env es.
    body_inv tops ctx cenv cx /\
    body_base_target_full_ok cx bt /\
    target_pre cenv cx env bt es ==>
    target_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx env bt es
Proof
  cheat
QED

Theorem body_target_place_sim_full:
  !bt DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env es.
    body_inv tops ctx cenv cx /\
    body_base_target_full_ok cx bt /\
    target_pre cenv cx env bt es ==>
    target_place_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx env bt es
Proof
  cheat
QED
