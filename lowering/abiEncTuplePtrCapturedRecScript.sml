(* Readiness discharges the captured head's proper-tail continuation. *)
Theory abiEncTuplePtrCapturedRec
Ancestors
  abiEncTuplePtrCapturedHead gasSummaryComposePtr
  bodyPtrBytestringBuiltinsEval vyperEvalExprPreservesScopesDom
  exprSimHyps freshWrites

Theorem abi_args_captured_rec_ptr:
  abi_args_ready ctx func ce cx Inv (e::args) /\ Inv es /\
  (!s gs. Inv s ==> Inv (s with gas_obs := gs)) /\
  expr_vv_sim_ptr d ctx PG func ce cx (expr_type e) e es /\
  expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  compile_materialize_vv ce (lowered_value_type ce e) vv mid = (op,sm) /\
  compile_abi_encode_args compile_expr ce args sm = (ops,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func ce cx es s0 /\ ghost_inv d ce cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~is_word_type (expr_type e) /\
  (!tvv v ee tv G tn r.
    vv_post ctx func ce cx e es sa mid s0 ee tvv vv r /\
    read_result cx tvv ee = (INL v,ee) /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
    value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
    type_memory_size tv < 2 ** 64 /\
    type_memory_size tv + 64 < dimword (:256) /\
    ghost_inv d ce cx ee G tn r /\
    ptr_vv_ok cx (post_value_type ce e) tvv vv ee G tn r /\
    (!t' a. vv = StackValue t' a /\ ~is_word_type (post_value_type ce e) ==>
      ptr_buf_ok ce e a G r) /\
    (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand G r) /\
    ghost_kept ce es sa G0 tn0 s0 G tn /\
    ~r.vs_halted /\ r.vs_current_bb = mid.cs_current_bb /\
    r.vs_inst_idx = LENGTH mid.cs_current_insts ==>
    ?H tm t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn r 0 H tm (OK t) /\
      materialize_owned_post ctx func ce cx e es sa mid sm s0 ee v op tv t /\
      ptr_val_ok cx (lowered_value_type ce e) v op H tm t /\
      ghost_inv d ce cx ee H tm t /\ ghost_kept ce es sa G0 tn0 s0 H tm /\
      ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts) /\
  (!es1 sa1 ops1 sb1 t G1 tn1.
    abi_args_ready ctx func ce cx Inv args /\ Inv es1 /\
    compile_abi_encode_args compile_expr ce args sa1 = (ops1,sb1) /\
    fn_has_code sa1 sb1 func /\ local_ptrs_reserved ce sa1 /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa1 x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa1 x) /\
    stmt_state_rel ctx func ce cx es1 t /\ ghost_inv d ce cx es1 G1 tn1 t /\
    ~t.vs_halted /\ t.vs_current_bb = sa1.cs_current_bb /\
    t.vs_inst_idx = LENGTH sa1.cs_current_insts ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG (eval_exprs cx args)
      (es1,t,G1,tn1)
      (\rr ee G tn u. ?vs. rr = INL vs /\
        abi_args_post ctx func ce cx es1 sa1 sb1 t ee args ops1 vs u /\
        LIST_REL (\op ev. ptr_val_ok cx (lowered_value_type ce (FST ev))
          (SND ev) op G tn u) ops1 (ZIP (args,vs)) /\
        EVERY (abi_decoder_operand_live sb1.cs_next_var) ops1 /\
        u.vs_current_bb = sb1.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb1.cs_current_insts /\
        ghost_inv d ce cx ee G tn u /\ ghost_kept ce es1 sa1 G1 tn1 t G tn)
      (\rr ee ghosts r. wb_args_exit rr r)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx (e::args)) (es,s0,G0,tn0)
    (\rr ee G tn u. ?vs. rr = INL vs /\
      abi_args_post ctx func ce cx es sa sb s0 ee (e::args) (op::ops) vs u /\
      LIST_REL (\op ev. ptr_val_ok cx (lowered_value_type ce (FST ev))
        (SND ev) op G tn u) (op::ops) (ZIP (e::args,vs)) /\
      EVERY (abi_decoder_operand_live sb.cs_next_var) (op::ops) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d ce cx ee G tn u /\ ghost_kept ce es sa G0 tn0 s0 G tn)
    (\rr ee ghosts r. wb_args_exit rr r)
Proof
  strip_tac >> drule_all abiEncTuplePtrArgsContextTheory.abi_args_compile_captured_ptr_context >> strip_tac >>
  irule abi_args_captured_head_ptr >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      drule_all abiEncTuplePtrArgsContextTheory.abi_args_success_ready_ptr >> simp[]) >>
  conj_tac
  >- (conj_tac >- (gvs[]) >>
      rpt gen_tac >> strip_tac >>
      drule_all abiEncTuplePtrArgsContextTheory.abi_args_success_ready_ptr >> strip_tac >>
      `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
       (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
        (gvs[exprLoweringPropsTheory.ci_mono_def] >>
         metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
      qpat_x_assum `!es1 sa1 ops1 sb1 t G1 tn1. _` drule_all >> strip_tac >>
      dxrule bodyPtrBytestringBuiltinsEvalTheory.gas_outcome_ptr_eval_evidence >> strip_tac >>
      irule gasSummaryComposePtrTheory.gas_outcome_ptr_conseq >>
      goal_assum (drule_at Any) >> simp[] >> rpt gen_tac >> strip_tac >> gnvs[] >>
      qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >>
      drule eval_exprs_preserves_scopes_dom >> simp[]) >>
  conj_tac >- metis_tac[expr_body_pre_vv_gas_admissible] >>
  qexists `env` >> simp[]
QED
