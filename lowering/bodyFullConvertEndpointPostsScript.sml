Theory bodyFullConvertEndpointPosts
Ancestors
  bodyFullConvertScalarFrame exprSimHyps vyperFiniteStoragePreservation
  exprSimMemDefs bodyPtrDefs exprLoweringProps vyperInterpreter vyperState vyperAST

Theorem dynamic_word_vv_post:
  expr_post H ctx func cenv cx (TypeBuiltin typ Convert typ [e])
    es sa sb s0 ee v op s /\ storage_well_formed_on cx ee (FST H) ==>
  vv_post H ctx func cenv cx (TypeBuiltin typ Convert typ [e])
    es sa sb s0 ee (Value v) (StackValue typ op) s
Proof
  simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.vv_post_def,
    loweringPostsTheory.vv_holds_def, loweringPostsTheory.vv_at_def,
    expr_type_def, read_result_def, return_def] >>
  strip_tac >> simp[]
QED

Theorem dynamic_endpoint_vv_posts:
  expr_post H ctx func cenv cx e es sa sm s0 ee v1 x t /\
  ghost_inv_at D lo d cenv cx ee G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  storage_well_formed_on cx ee (FST H) /\
  is_word_type typ /\ evaluate_type (get_tenv cx) typ = SOME tv /\
  value_has_type tv v /\ eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  local_ptrs_reserved cenv sm /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  sa.cs_next_var <= sm.cs_next_var /\
  state_frame s = state_frame (t with vs_inst_idx := s.vs_inst_idx) /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!z. not_fresh_at sm z ==> lookup_var z s = lookup_var z t /\
    FLOOKUP Gf z = FLOOKUP G z /\ op_taint tnf (Var z) = op_taint tn (Var z)) /\
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  op_taint tnf op = {} /\ op_prov Gf op = NONE /\
  alloca_history func s /\ s0.vs_alloca_next <= t.vs_alloca_next ==>
  vv_post H ctx func cenv cx (TypeBuiltin typ Convert typ [e]) es sa sb s0
    ee (Value v) (StackValue typ op) s /\
  vv_store_bound cx typ lt ee (Value v) (StackValue typ op) s /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_inv_at D lo d cenv cx ee Gf tnf s /\
  ptr_vv_ok cx typ (Value v) (StackValue typ op) ee Gf tnf s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >>
  drule_all scalar_convert_endpoint_frames >> strip_tac >>
  `s = (t with vs_inst_idx := s.vs_inst_idx) with vs_vars := s.vs_vars` by
    metis_tac[stateFrameTheory.state_frame_eq_reconstruct] >>
  `s.vs_allocas = t.vs_allocas /\ s.vs_alloca_next = t.vs_alloca_next` by
    (pop_assum SUBST1_TAC >> simp[]) >>
  simp[exprSimMemDefsTheory.vv_store_bound_stack_word,
    bodyPtrDefsTheory.ptr_vv_ok_def, read_result_def, return_def] >>
  irule dynamic_word_vv_post >> simp[]
QED

Theorem dynamic_read_storage_well_formed:
  expr_body_pre cenv cx env e s /\
  storage_well_formed_on cx s (FST H) /\
  valid_horizon cx st0 H mid.storage_trace /\
  bind (eval_expr cx e) (read_result cx) s = (INL v,mid) ==>
  storage_well_formed_on cx mid (FST H)
Proof
  strip_tac >>
  `well_typed_expr env e /\ runtime_consistent env cx s /\
   functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e)` by
    gvs[exprSimHypsDefsTheory.expr_body_pre_def,
        exprSimHypsDefsTheory.expr_sim_inv_def,
        vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
  gvs[bind_def, AllCaseEqs()] >>
  drule read_result_state >> strip_tac >> gvs[] >>
  gvs[vyperStorageFootprintTheory.valid_horizon_def] >>
  drule_all (cj 5 (SPEC_ALL eval_storage_well_formed_on_mutual)) >> simp[]
QED
