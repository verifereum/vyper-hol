(*
 * The judgments of the joint target simulation (bodyFullTarget): a base
 * target resolves to its place and pointer at one joint endpoint.
 *
 * TOP-LEVEL:
 *   target_sim_full       -- eval_base_place's judgment (a place or a mapping)
 *   target_place_sim_full -- eval_target_place's judgment (a place), which
 *                            Append, Pop, AugAssign and Assign bind on
 *)
Theory bodyFullTargetDefs
Ancestors
  exprSimDefs unitMemInv contextRawReachable
  bodySimFull targetPlaceSimCases targetPlaceSimDefs
  gasShadow gasOutcomeFull loweringPosts exprLowering compileEnv
  ptrDiscipline venomState vyperInterpreter vyperState vyperAST
  allocLimits vyperFixedShapePath

(* New definition: target_post H (with ghost_inv) says what the target's
   pointer holds, not where it may point, and a fresh pointer derived
   from a local's (an attribute's or an element's) needs the local's site
   for the pop's MLOAD and MSTORE access checks.  The site is the one the
   local's pointer has (ghost_inv's ptr_covers covers the local inside
   it). *)
Definition target_ptr_ok_def:
  target_ptr_ok cenv (pv : eval_result)
    (r : operand # data_location option # place_ty option) G tn
    (s : venom_state) <=>
    op_taint tn (FST r) = {} /\
    (!id path p sz.
       pv = PlaceR (MemoryPlace id path) /\
       FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
       op_prov G (FST r) = FLOOKUP G p) /\
    (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
                  op_prov G (FST r) = NONE) /\
    (!tr slot kt vt. pv = HashMapRef tr slot kt vt ==>
                     op_prov G (FST r) = NONE)
End

(* Constructor immutable targets address the immutable memory region. *)
Definition imm_target_post_def:
  imm_target_post H ctx func cenv cx es sa sb s0 ee id path ty
    (r : operand # data_location option # place_ty option) t <=>
    stmt_state_rel H ctx func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    FST (SND r) = SOME LocCode /\
    SND (SND r) = SOME (ValPT ty) /\
    (?off itv iv k ptv v.
       FLOOKUP cenv.ce_module_vars (NONE,id) = SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
                  NONE => FEMPTY
                | SOME imms => get_source_immutables NONE imms) id =
         SOME (itv,iv) /\
       mem_path_offset itv path = SOME (k,ptv) /\
       evaluate_type (get_tenv cx) ty = SOME ptv /\
       evaluate_subscripts itv iv path = INL v /\
       eval_operand (FST r) t = SOME (n2w (off+k))) /\
    (!x. FST r = Var x ==> not_fresh_at sb x) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
       (!n b len. local_region cenv es.scopes s0 n b len ==>
                  off + sz <= b \/ b + len <= off) ==>
       mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
    locals_kept cenv es ee s0 t
End

Definition imm_target_place_sim_judgment_def:
  imm_target_place_sim_judgment outcome
    (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx env bt es <=>
    !st0 ty sa sb shadow_sa shadow_sb r s0 G0 tn0.
      type_place_target env bt = SOME (Type ty) /\
      compile_get_target_ptr compile_expr cenv bt sa = (r,sb) /\
      compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
        (gas_shadow_target bt)
        shadow_sa = (r,shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
      return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      outcome
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0 sa sb (eval_target_place cx bt) (es,s0,G0,tn0)
        (\H res ee G tn t. ?id path. res = INL (ImmutablePlace NONE id path) /\
          target_root bt = TopLevelNameTarget (NONE,id) /\
          imm_target_post H ctx func cenv cx es sa sb s0 ee id path ty r t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
          target_ptr_ok cenv (PlaceR (ImmutablePlace NONE id path)) r G tn t /\
          op_prov G (FST r) = NONE /\
          (!itv iv. ~target_through_dynarray cenv bt /\
             FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
               | SOME imms => get_source_immutables NONE imms) id = SOME (itv,iv)
             ==> fixed_shape_path itv path) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt q.
          expr_exit res q /\ halt_exit H cx ee res q /\
          (ctx_has_dalloca ctx ==> !s. q = Halt s ==> allocas_below_fmp s))
End

Theorem imm_target_place_sim_judgment_mono:
  imm_target_place_sim_judgment outcome
    (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx env bt es /\
  (!tops cx st0 sa sb source seed Q R.
    outcome (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      tops cx st0 sa sb source seed Q R ==>
    outcome' (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      tops cx st0 sa sb source seed Q R) ==>
  imm_target_place_sim_judgment outcome'
    (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx env bt es
Proof
  simp[imm_target_place_sim_judgment_def] >> rpt strip_tac >>
  first_x_assum irule >> first_x_assum irule >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`shadow_sa`,`shadow_sb`] >> simp[]
QED

Definition imm_target_place_sim_full_def:
  imm_target_place_sim_full
    (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx env bt es <=>
    !st0 ty sa sb shadow_sa shadow_sb r s0 G0 tn0.
      type_place_target env bt = SOME (Type ty) /\
      compile_get_target_ptr compile_expr cenv bt sa = (r,sb) /\
      compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
        (gas_shadow_target bt)
        shadow_sa = (r,shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
      return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0 (eval_target_place cx bt) (es,s0,G0,tn0)
        (\H res ee G tn t. ?id path. res = INL (ImmutablePlace NONE id path) /\
          target_root bt = TopLevelNameTarget (NONE,id) /\
          imm_target_post H ctx func cenv cx es sa sb s0 ee id path ty r t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
          target_ptr_ok cenv (PlaceR (ImmutablePlace NONE id path)) r G tn t /\
          op_prov G (FST r) = NONE /\
          (!itv iv. ~target_through_dynarray cenv bt /\
             FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
               | SOME imms => get_source_immutables NONE imms) id = SOME (itv,iv)
             ==> fixed_shape_path itv path) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt q.
          expr_exit res q /\ halt_exit H cx ee res q /\
          (ctx_has_dalloca ctx ==> !s. q = Halt s ==> allocas_below_fmp s))
End

Theorem imm_target_place_sim_full_internal_def:
  imm_target_place_sim_full p cenv cx env bt es <=>
  imm_target_place_sim_judgment
    (\bundle tops cx st0 sa sb. gas_outcome_full bundle tops cx st0)
    p cenv cx env bt es
Proof
  PairCases_on `p` >>
  simp[imm_target_place_sim_full_def, imm_target_place_sim_judgment_def]
QED

(* Keep the precondition and posts shared by the full and refined
   witness producers. The outcome receives the two compile cursors. *)
Definition target_sim_judgment_def:
  target_sim_judgment outcome (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt es <=>
    !st0 vt sa sb shadow_sa shadow_sb r s0 G0 tn0.
      type_place_target env bt = SOME vt /\
      compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
      compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
        (gas_shadow_target bt)
        shadow_sa = (r, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_base_place cx bt) target_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      outcome
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0 sa sb (eval_base_place cx bt) (es, s0, G0, tn0)
        (\H res ee G tn t. ?pv. res = INL pv /\
          target_post H ctx func cenv cx es sa sb s0 ee pv vt r t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
          target_ptr_ok cenv pv r G tn t /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt q.
          expr_exit res q /\ halt_exit H cx ee res q /\
          (ctx_has_dalloca ctx ==> !s. q = Halt s ==> allocas_below_fmp s))
End

Theorem target_sim_judgment_mono:
  target_sim_judgment outcome (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt es /\
  (!tops cx st0 sa sb source seed Q R.
    outcome (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      tops cx st0 sa sb source seed Q R ==>
    outcome' (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      tops cx st0 sa sb source seed Q R) ==>
  target_sim_judgment outcome' (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt es
Proof
  simp[target_sim_judgment_def] >> rpt strip_tac >>
  first_x_assum irule >> first_x_assum irule >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`shadow_sa`,`shadow_sb`] >> simp[]
QED

(* New definition: target_sim_ptr over the joint judgment. *)
Definition target_sim_full_def:
  target_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt es <=>
    !st0 vt sa sb shadow_sa shadow_sb r s0 G0 tn0.
      type_place_target env bt = SOME vt /\
      compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
      compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
        (gas_shadow_target bt)
        shadow_sa = (r, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_base_place cx bt) target_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
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
          alloca_history func t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
          target_ptr_ok cenv pv r G tn t /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt q.
          expr_exit res q /\ halt_exit H cx ee res q /\
          (ctx_has_dalloca ctx ==> !s. q = Halt s ==> allocas_below_fmp s))
End

Theorem target_sim_full_internal_def:
  target_sim_full p cenv cx env bt es <=>
  target_sim_judgment (\F tops cx st0 sa sb. gas_outcome_full F tops cx st0)
    p cenv cx env bt es
Proof
  PairCases_on `p` >> simp[target_sim_full_def, target_sim_judgment_def]
QED

(* New definition: pop_target_frag_ptr over the joint judgment; a memory
   place is live in the local's current value (targetLocalLive). *)
Definition target_place_sim_full_def:
  target_place_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt es <=>
    !st0 ty sa sb shadow_sa shadow_sb r s0 G0 tn0.
      type_place_target env bt = SOME (Type ty) /\
      compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
      compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
        (gas_shadow_target bt)
        shadow_sa = (r, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
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
          alloca_history func t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
          target_ptr_ok cenv (PlaceR p) r G tn t /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt q.
          expr_exit res q /\ halt_exit H cx ee res q /\
          (ctx_has_dalloca ctx ==> !s. q = Halt s ==> allocas_below_fmp s))
End

Definition assign_target_post_def:
  assign_target_post imm H ctx func ce cx es sa sb s0 ee p ty r G t <=>
    if imm then
      ?id path. p = ImmutablePlace NONE id path /\
        imm_target_post H ctx func ce cx es sa sb s0 ee id path ty r t /\
        op_prov G (FST r) = NONE
    else target_post H ctx func ce cx es sa sb s0 ee (PlaceR p) (Type ty) r t
End

Definition assign_target_place_sim_full_def:
  assign_target_place_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt es <=>
    !st0 ty sa sb shadow_sa shadow_sb r s0 G0 tn0.
      type_place_target env bt = SOME (Type ty) /\
      compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
      compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
        (gas_shadow_target bt)
        shadow_sa = (r, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
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
          assign_target_post (immutable_root cx bt) H ctx func cenv cx
            es sa sb s0 ee p ty r G t /\
          (!id path. p = MemoryPlace id path ==>
             ?entry v. lookup_scopes id ee.scopes = SOME entry /\
                       evaluate_subscripts entry.type entry.value path =
                         INL v) /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
          target_ptr_ok cenv (PlaceR p) r G tn t /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt q.
          expr_exit res q /\ halt_exit H cx ee res q /\
          (ctx_has_dalloca ctx ==> !s. q = Halt s ==> allocas_below_fmp s))
End

Theorem assign_target_place_sim_full:
  (if immutable_root cx bt then
     imm_target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       ce cx env bt es
   else target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       ce cx env bt es) ==>
  assign_target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx env bt es
Proof
  Cases_on `immutable_root cx bt` >>
  simp[assign_target_place_sim_full_def,imm_target_place_sim_full_def,
       target_place_sim_full_def] >> strip_tac >> rpt gen_tac >> strip_tac
  >- (first_x_assum drule_all >> strip_tac >>
      irule gas_outcome_full_post_mono >> first_assum (irule_at Any) >>
      simp[assign_target_post_def] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  first_x_assum drule_all >>
  simp[assign_target_post_def]
QED

Theorem assign_target_post_frame:
  assign_target_post imm H ctx func ce cx es sa sb s0 ee p ty r G t ==>
  stmt_state_rel H ctx func ce cx ee t /\
  storage_well_formed_on cx ee (FST H) /\
  (!x. FST r = Var x ==> not_fresh_at sb x) /\
  wb_frame ce es ee sa s0 t
Proof
  Cases_on `imm` >>
  simp[assign_target_post_def,imm_target_post_def,target_post_def,wb_frame_def] >>
  metis_tac[]
QED

Theorem assign_target_post_alloca_frame:
  assign_target_post imm H ctx func ce cx es sa sb s0 ee p ty r G t /\
  stmt_state_rel H ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes ==>
  alloca_frame ce es sa s0 ce ee t
Proof
  strip_tac >> drule_then strip_assume_tac assign_target_post_frame >>
  fs[wb_frame_def] >> irule stmtSimDefsTheory.alloca_frame_of_mem_frame >> metis_tac[]
QED

Theorem assign_target_post_gas_obs[simp]:
  assign_target_post imm H ctx func ce cx (es with gas_obs := gs) sa sb s0 ee p ty r G t =
    assign_target_post imm H ctx func ce cx es sa sb s0 ee p ty r G t /\
  assign_target_post imm H ctx func ce cx es sa sb s0 (ee with gas_obs := hs)
      p ty r G t =
    assign_target_post imm H ctx func ce cx es sa sb s0 ee p ty r G t
Proof
  `storage_well_formed_on cx (ee with gas_obs := hs) (FST H) <=>
   storage_well_formed_on cx ee (FST H)` by
    (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >> simp[]) >>
  Cases_on `imm` >>
  simp[assign_target_post_def,imm_target_post_def,target_post_def,
       locals_kept_def,popped_kept_def]
QED
