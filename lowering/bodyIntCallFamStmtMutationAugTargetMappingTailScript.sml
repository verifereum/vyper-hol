(* Readonly emissions after scratch allocation, retaining the concrete frame. *)
Theory bodyIntCallFamStmtMutationAugTargetMappingTail
Ancestors
  bodyIntCallFamStmtMutationAugTargetMapping bodyIntCallFamStmtMutationBinop
  exprSimHash exprSimMapKey emitHelperProps exprLoweringProps compileEnv
  emitHelper venomInst bodyIntCallJointContract venomState loweringShapeRules loweringStateRelDefs exprSimHashBoundary

Theorem intcall_readonly_emit_run:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  emit_op opc args sa = (op,sb) /\ fn_has_code sa sb fp.jc_func /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  (t with vs_vars := s.vs_vars) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  gas_marked_path F fp.jc_ctx fp.jc_func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  intcall_expr_cont fp ce env es sa s es sb
    (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_facts >> strip_tac >>
  `gas_marked_path F fp.jc_ctx fp.jc_func s 0
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb` by
    (drule hash_run_path >>
     disch_then (qspecl_then [`t`, `s`, `emitted_insts sa sb`, `fp.jc_ctx`] mp_tac) >>
     gvs[mk_inst_def]) >>
  simp[] >> irule intcall_expr_cont_readonly_path >> simp[] >>
  `local_ptrs_reserved ce sa /\
   stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s` by
    fs[intcall_expr_res_def] >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es t` by
    metis_tac[hash_readonly_state_rel] >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas` by
    gvs[venomStateTheory.venom_state_component_equality] >>
  simp[stmt_state_rel_inst_idx] >>
  conj_tac
  >- (rpt strip_tac >> gvs[venomStateTheory.lookup_var_def]) >>
  conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  qexistsl [`F`, `0`] >> gvs[]
QED
