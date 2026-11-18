(* Normal resources at a supplied scalar operator endpoint.  The actual
   machine run and the endpoint metadata are shared with the origin proof. *)
Theory augAssignFullOperatorNormal
Ancestors
  fragGasFresh freshWrites varsExt bodyBinopFragMemory bodyFullGhostFrame
  bodyFullTargetDefs augAssignFullSaved bodyMemoryDefs loweringPosts
  bodyPtrDefs ptrDiscipline compileEnv exprLoweringProps
  venomExecSemantics venomState finite_map list rich_list arithmetic

Theorem augassign_operator_normal_resources:
  straight_fresh m /\ m sa = (op,sb) /\ fn_has_code sa sb func /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  storage_well_formed_on cx es (FST H) /\
  ghost_inv_at D lo d cenv cx es G tn s0 /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) (drop_fresh sa s0) = OK t0 /\
  eval_operand op t0 = SOME w /\
  run_inst_seq (emitted_insts sa sb) s0 = OK t /\ vars_ext t0 t /\
  expr_val_rel cx ann v op t0 /\
  (!x. not_fresh_at sa x ==>
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  op_prov G' op = NONE /\ op_taint tn' op = {} /\
  (!x. FST r = Var x ==> not_fresh_at sa x) /\
  (!x. old = Var x ==> not_fresh_at sa x) /\
  eval_operand (FST r) s0 = SOME addr /\
  eval_operand old s0 = SOME oldword /\
  target_ptr_ok cenv (PlaceR p) r G tn s0 /\
  op_taint tn old = {} /\ op_prov G old = NONE /\
  s1 = (t with vs_inst_idx := LENGTH sb.cs_current_insts) ==>
  stmt_state_rel H ctx func cenv cx es s1 /\
  storage_well_formed_on cx es (FST H) /\
  expr_val_rel cx ann v op s1 /\ eval_operand op s1 = SOME w /\
  (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==>
         lookup_var x s1 = SOME z) /\
  s1.vs_memory = s0.vs_memory /\ s1.vs_allocas = s0.vs_allocas /\
  s1.vs_alloca_next = s0.vs_alloca_next /\
  s1.vs_labels = s0.vs_labels /\
  return_buf_frame d cenv sb s1 /\ alloca_history func s1 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s1) /\
  ~s1.vs_halted /\ s1.vs_current_bb = sb.cs_current_bb /\
  s1.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ghost_inv_at D lo d cenv cx es G' tn' s1 /\
  ghost_kept_at lo cenv es sa G tn s0 G' tn' /\
  eval_operand (FST r) s1 = SOME addr /\
  eval_operand old s1 = SOME oldword /\
  target_ptr_ok cenv (PlaceR p) r G' tn' s1 /\
  op_taint tn' old = {} /\ op_prov G' old = NONE /\
  op_prov G' op = NONE /\ op_taint tn' op = {}
Proof
  strip_tac >>
  drule_all straight_fresh_run_post >> strip_tac >>
  `writes_fresh sa (emitted_insts sa sb) /\
   sb.cs_current_bb = sa.cs_current_bb /\
   sa.cs_next_var <= sb.cs_next_var /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    metis_tac[straight_fresh_def] >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  `s1.vs_memory = s0.vs_memory /\ s1.vs_allocas = s0.vs_allocas /\
   s1.vs_alloca_next = s0.vs_alloca_next /\ s1.vs_labels = s0.vs_labels /\
   s1.vs_fmp = s0.vs_fmp /\ s1.vs_call_ctx = s0.vs_call_ctx /\
   s1.vs_accounts = s0.vs_accounts /\ s1.vs_transient = s0.vs_transient /\
   s1.vs_immutables = s0.vs_immutables` by
    (qpat_assum `s1 = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_x_assum `t = s0 with vs_vars := _`
       (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `ghost_inv_at D lo d cenv cx es G' tn' s1` by
    (drule ghost_inv_at_exterior_frame >> disch_then irule >> simp[] >>
     qexists_tac `sa` >> simp[] >> rpt strip_tac >>
     simp[lookup_var_def] >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa G tn s0 G' tn'` by
    (simp[ghost_kept_at_def] >> metis_tac[]) >>
  `return_buf_frame d cenv sb s1` by
    (drule return_buf_frame_frame >> disch_then irule >> gvs[]) >>
  `alloca_history func s1` by suspend "history" >>
  `expr_val_rel cx ann v op s1` by suspend "encoding" >>
  `!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==>
         lookup_var x s1 = SOME z` by
    (simp[lookup_var_def] >> metis_tac[]) >>
  drule_all augassign_saved_rhs_frame >> strip_tac >>
  gvs[allocas_below_fmp_def] >>
  qpat_x_assum `t = s0 with vs_vars := _`
    (fn th => once_rewrite_tac[th]) >> simp[] >>
  strip_tac >> qpat_x_assum `ctx_has_dalloca ctx ==> _` drule >>
  metis_tac[]
QED

Resume augassign_operator_normal_resources[history]:
  drule_all straight_fresh_code_prefix >> strip_tac >>
  gvs[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
    (gvs[writes_fresh_def, EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> simp[fresh_write_op_def] >> metis_tac[]) >>
  `alloca_history func (t with vs_inst_idx :=
      s0.vs_inst_idx + LENGTH (emitted_insts sa sb))` by
    (irule alloca_history_no_alloca_slice >> metis_tac[]) >>
  gvs[LENGTH_APPEND]
QED

Resume augassign_operator_normal_resources[encoding]:
  gvs[expr_val_rel_def, vars_ext_def] >>
  `t.vs_memory = t0.vs_memory` by
    (qpat_x_assum `t = t0 with vs_vars := _`
       (fn th => once_rewrite_tac[th]) >> simp[]) >>
  gvs[]
QED

Finalise augassign_operator_normal_resources
