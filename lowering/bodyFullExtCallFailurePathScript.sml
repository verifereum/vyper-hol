(* Checked failure forwarding after an unsuccessful external call. *)
Theory bodyFullExtCallFailurePath
Ancestors
  rawCallBufferPtr fragGasSeqPtr fragGasOriginPtr fragGasOrigin fragGasPathPtr
  fragGasEmitCtrl exprSimAccounts exprLoweringProps emitHelperProps emitHelper
  exprLowering compileEnv fragExec ptrSafeRun ptrDiscipline memSafeRun
  instMemFrontier contextCodegenRel contextCodegenRelProps
  venomExecProps venomInstProps venomExecSemantics venomInst venomState
  gasEvents gasCount finite_map pred_set list

Theorem extcall_forward_copy_edge[local]:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME copy /\
  copy.inst_opcode = RETURNDATACOPY /\ copy.inst_outputs = [] /\
  in_revert_forward func s /\ about_to_revert func copy s /\
  EVERY (\op. op_taint tn op = {}) copy.inst_operands /\
  inst_mem_below_frontier copy s /\ inst_dload_in_section copy s /\
  step_inst_base copy s = OK u ==>
  !D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G copy u, step_taint copy s u tn)
Proof
  strip_tac >> gen_tac >>
  `access_ok lo G func copy s /\ taint_ok func tn copy s` by
    (irule revert_forward_access_taint >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn copy s` by
    (qpat_x_assum `step_inst_base copy s = OK u` mp_tac >>
     simp[step_inst_base_opcode_eqs, write_memory_with_expansion_def,
       write_memory_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
     simp[ptr_inst_ok_def, step_inst_non_invoke,
       step_inst_base_opcode_eqs, write_memory_with_expansion_def,
       write_memory_def, AllCaseEqs()]) >>
  `copy.inst_opcode <> INVOKE /\ ~is_terminator copy.inst_opcode` by
    simp[is_terminator_def] >>
  drule_all straight_line_origin_ptr_edge >> simp[]
QED

Theorem extcall_forward_revert_edge[local]:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME rev /\
  rev.inst_opcode = REVERT /\ in_revert_forward func s /\
  EVERY (\op. op_taint tn op = {}) rev.inst_operands /\
  inst_mem_below_frontier rev s /\ inst_dload_in_section rev s /\
  step_inst_base rev s = Abort Revert_abort u ==>
  !D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (Abort Revert_abort u,G,tn)
Proof
  strip_tac >> gen_tac >>
  `access_ok lo G func rev s /\ taint_ok func tn rev s` by
    (irule revert_forward_access_taint >> simp[about_to_revert_def]) >>
  `ptr_inst_ok D lo 0 ctx func G tn rev s` by
    simp[ptr_inst_ok_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
         AllCaseEqs()] >>
  rewrite_tac[gas_origin_ptr_edge_def] >> conj_tac
  >- (rewrite_tac[gas_origin_edge_def] >> simp[] >>
      qexists_tac `0` >>
      simp[step_inst_non_invoke, gas_events_step_def,
           mem_safe_step_non_invoke, exit_result_def]) >>
  rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
  qexists_tac `0` >>
  simp[step_inst_non_invoke, gas_count_step_def, ptr_safe_step_def,
       exit_result_def]
QED
