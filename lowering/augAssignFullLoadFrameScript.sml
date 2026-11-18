(* Fresh-register loads preserve the resources at their supplied endpoint. *)
Theory augAssignFullLoadFrame
Ancestors
  assignTuplePtrLoadStep bodyFullGhostFrame bodyFullUnwrapRun bodyMemoryDefs
  bodyFullTargetDefs bodyBinopFragMemory exprSimConcatPath freshWrites
  bodyPtrDefs ptrDiscipline stateFrame venomState finite_map list rich_list arithmetic
  allocaHistory loweringStateRelDefs

(* The history argument uses only the emitted non-allocating slice.  It
   requires no horizon, pointer path, or additional alloca invariant. *)
Theorem augassign_load_endpoint_history:
  alloca_history func s /\
  state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  alloca_history func u
Proof
  strip_tac >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `state_frame _ = _` mp_tac >>
     simp[state_frame_def] >> metis_tac[]) >>
  drule_all concat_code_prefix >> strip_tac >>
  gvs[IS_PREFIX_APPEND] >>
  `alloca_history func
     (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))` by
    (irule alloca_history_no_alloca_slice >> metis_tac[]) >>
  irule alloca_history_frame >>
  goal_assum (drule_at Any) >> simp[LENGTH_APPEND]
QED

(* Low-level load frames suffice; no semantic endpoint post is assumed. *)
Theorem augassign_load_endpoint_frame:
  stmt_state_rel H ctx func cenv cx st s /\
  ghost_inv_at D lo d cenv cx st G tn s /\
  target_ptr_ok cenv (PlaceR p) r G tn s /\
  ghost_kept_at lo cenv es entry G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  entry.cs_next_var <= sa.cs_next_var /\
  sa.cs_next_var <= sb.cs_next_var /\
  return_buf_frame d cenv sa s /\
  state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
  tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
  tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
  (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\
       FLOOKUP G1 x = FLOOKUP G x /\
       op_taint tn1 (Var x) = op_taint tn (Var x)) /\
  (!x. FST r = Var x ==> not_fresh_at sa x) /\
  eval_operand (FST r) s = SOME addr /\
  alloca_history func s /\
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  stmt_state_rel H ctx func cenv cx st u /\
  ghost_inv_at D lo d cenv cx st G1 tn1 u /\
  target_ptr_ok cenv (PlaceR p) r G1 tn1 u /\
  ghost_kept_at lo cenv es entry G0 tn0 s0 G1 tn1 /\
  return_buf_frame d cenv sb u /\
  u.vs_alloca_next = s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s ==> allocas_below_fmp u) /\
  eval_operand (FST r) u = SOME addr /\
  alloca_history func u
Proof
  strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
   u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables /\
   u.vs_labels = s.vs_labels /\ u.vs_fmp = s.vs_fmp /\
   u.vs_initial_fmp = s.vs_initial_fmp` by
    (qpat_x_assum `state_frame _ = _` mp_tac >>
     simp[state_frame_def] >> metis_tac[]) >>
  conj_tac >- (irule stmt_state_rel_old_vars_frame_ptr >> metis_tac[]) >>
  conj_tac >- (irule ghost_inv_at_exterior_frame >> metis_tac[]) >>
  conj_tac >-
    (`op_taint tn1 (FST r) = op_taint tn (FST r) /\
      op_prov G1 (FST r) = op_prov G (FST r)` by
       (Cases_on `FST r` >> gvs[op_taint_def, op_prov_def] >> metis_tac[]) >>
     gvs[target_ptr_ok_def] >> rpt strip_tac >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  conj_tac >-
    (irule ghost_kept_at_clean_suffix >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  conj_tac >-
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s`, `sa`] >>
     simp[] >> metis_tac[]) >>
  conj_tac >- simp[] >>
  conj_tac >- (simp[allocas_below_fmp_def] >> metis_tac[]) >>
  conj_tac >-
    (Cases_on `FST r` >> gvs[eval_operand_def] >> metis_tac[]) >>
  irule augassign_load_endpoint_history >> metis_tac[]
QED
