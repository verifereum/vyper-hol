(* The actual generic AugAssign load: query coverage and RHS-entry frame. *)
Theory augAssignFullLoad
Ancestors
  augAssignFullLoadFrame augAssignFullLoadMemoryJoin augAssignFullLoadStorageJoin
  bodySimAugPlaceLive loweringShapeRules exprLoweringProps freshWrites
  emitHelperProps loweringPosts bodyFullTargetDefs bodyPtrDefs ptrDiscipline
  venomState venomInst compileEnv finite_map words list arithmetic

Theorem augassign_load_rhs_frame[local]:
  target_post H ctx func cenv cx es sa sb s0 st (PlaceR p) (Type ty) r s /\
  target_ptr_ok cenv (PlaceR p) r G tn s /\
  ghost_inv_at D lo d cenv cx st G tn s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sb /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  sa.cs_next_var <= sb.cs_next_var /\
  return_buf_frame d cenv sb s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  emit_op opc [FST r] sb = (old,sc) /\ opc <> ALLOCA /\ fn_has_code sb sc func /\
  eval_operand (FST r) s = SOME addr /\
  state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
  tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
  tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
  (!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)) /\
  u.vs_inst_idx = LENGTH sc.cs_current_insts
  ==>
  (!x. old = Var x ==> not_fresh_at sc x) /\
  (!x. FST r = Var x ==> not_fresh_at sc x) /\
  local_ptrs_reserved cenv sc /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  stmt_state_rel H ctx func cenv cx st u /\
  ghost_inv_at D lo d cenv cx st G1 tn1 u /\
  target_ptr_ok cenv (PlaceR p) r G1 tn1 u /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  return_buf_frame d cenv sc u /\ alloca_history func u /\
  u.vs_alloca_next = s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  eval_operand (FST r) u = SOME addr
Proof
  strip_tac >>
  drule emit_op_facts >> strip_tac >>
  `sb.cs_next_var <= sc.cs_next_var` by simp[] >>
  `stmt_state_rel H ctx func cenv cx st s /\
   (!x. FST r = Var x ==> not_fresh_at sb x)` by fs[target_post_def] >>
  `sc.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sc /\
   EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sb sc)` by
    (drule emitted_insts_emit_op >> simp[mk_inst_def]) >>
  drule_all augassign_load_endpoint_frame >> strip_tac >>
  simp[] >> metis_tac[not_fresh_at_mono, local_ptrs_reserved_next_var]
QED

Theorem augassign_load_joint:
  expr_sim_inv cenv cx env es /\
  supported_target_info tops bindings bt = SOME info /\
  eval_target_place cx bt es = (INL p,st) /\
  compile_get_target_ptr compile_expr cenv bt sa = (r,sb) /\
  is_word_type ty /\
  ((FST (SND r) = NONE /\ emit_void INVALID [] sb = ((),sf)) \/
   (?loc old sc. FST (SND r) = SOME loc /\
      emit_op (case loc of LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD)
        [FST r] sb = (old,sc) /\ fn_has_code sb sc func)) /\
  local_ptrs_reserved cenv sb /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  sa.cs_next_var <= sb.cs_next_var /\
  (!H. valid_horizon cx st0 H st.storage_trace ==>
    target_post H ctx func cenv cx es sa sb s0 st (PlaceR p) (Type ty) r s /\
    target_ptr_ok cenv (PlaceR p) r G tn s /\
    ghost_inv_at (DF H) lo d cenv cx st G tn s /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    dead_lo_ok H (DF H) lo cenv cx /\
    return_buf_frame d cenv sb s /\ alloca_history func s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts)
  ==>
  ?loc old sc addr cur ptv u G1 tn1.
    !H. valid_horizon cx st0 H st.storage_trace ==>
      FST (SND r) = SOME loc /\
      emit_op (case loc of LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD)
        [FST r] sb = (old,sc) /\ fn_has_code sb sc func /\
      read_place cx p st = (INL cur,st) /\
      place_type_value cx p st = (INL ptv,st) /\
      evaluate_type (get_tenv cx) ty = SOME ptv /\ value_has_type ptv cur /\
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK u,G1,tn1) /\
      eval_operand old u = SOME (typed_val_to_w256 ptv cur) /\
      eval_operand (FST r) s = SOME addr /\
      eval_operand (FST r) u = SOME addr /\
      op_taint tn1 old = {} /\ op_prov G1 old = NONE /\
      (!x. old = Var x ==> not_fresh_at sc x) /\
      (!x. FST r = Var x ==> not_fresh_at sc x) /\
      local_ptrs_reserved cenv sc /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
      stmt_state_rel H ctx func cenv cx st u /\
      ghost_inv_at (DF H) lo d cenv cx st G1 tn1 u /\
      target_ptr_ok cenv (PlaceR p) r G1 tn1 u /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
      return_buf_frame d cenv sc u /\ alloca_history func u /\
      u.vs_alloca_next = s.vs_alloca_next /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
      u.vs_inst_idx = LENGTH sc.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `?H. valid_horizon cx st0 H st.storage_trace`
  >- (pop_assum (qx_choose_then `H0` assume_tac) >>
      qpat_assum `!H. valid_horizon _ _ _ _ ==> _` drule >> strip_tac >>
      Cases_on `p`
      >- suspend "storage"
      >- suspend "memory"
      >> fs[target_post_def, place_ptr_rel_def]) >>
  gvs[]
QED

Resume augassign_load_joint[memory]:
  rename1 `MemoryPlace id path` >>
  `?entry v. lookup_scopes id st.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL v` by
    metis_tac[aug_place_target_memory_live] >>
  drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    augassign_memory_load_queries >>
  disch_then (drule_at (Pat `supported_target_info _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  `?addr. eval_operand (FST r) s = SOME addr /\ FST (SND r) = SOME LocMemory` by
    (qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [target_post_def, place_ptr_rel_def] >> metis_tac[]) >>
  qpat_x_assum `_ \/ ?loc old sc. _` strip_assume_tac >> gvs[] >>
  `?u G1 tn1. !H. valid_horizon cx st0 H st.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G1,tn1) /\
    evaluate_type (get_tenv cx) ty = SOME ptv /\ value_has_type ptv cur /\
    eval_operand old u = SOME (typed_val_to_w256 ptv cur) /\
    eval_operand (FST r) u = SOME addr /\
    op_taint tn1 old = {} /\ op_prov G1 old = NONE /\
    ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!q. not_fresh_at sb q ==> lookup_var q u = lookup_var q s /\
      FLOOKUP G1 q = FLOOKUP G q /\ op_taint tn1 (Var q) = op_taint tn (Var q))` by
    (irule augassign_memory_load_joint >> simp[] >>
     goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `supported_target_info _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`LocMemory`, `old`, `sc`, `addr`, `cur`, `ptv`, `u`, `G1`, `tn1`] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    drule >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    drule >> strip_tac >>
  drule_all augassign_load_rhs_frame >> simp[] >> strip_tac >> simp[]
QED

Resume augassign_load_joint[storage]:
  FAIL_TAC "storage"
QED

Finalise augassign_load_joint
