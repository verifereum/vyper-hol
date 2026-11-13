(* Checked failure forwarding after an unsuccessful external call. *)
Theory bodyFullExtCallFailurePath
Ancestors
  rawCallBufferPtr fragGasSeqPtr fragGasOriginPtr fragGasOrigin fragGasPathPtr
  fragGasEmitCtrl exprSimAccounts exprLoweringProps emitHelperProps emitHelper
  exprLowering compileEnv fragExec ptrSafeRun ptrDiscipline memSafeRun
  instMemFrontier contextCodegenRel contextCodegenRelProps
  venomExecProps venomInstProps venomExecSemantics venomInst venomState
  gasEvents gasCount finite_map pred_set list context

Theorem extcall_forward_copy_edge[local]:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME copy /\
  copy.inst_opcode = RETURNDATACOPY /\ copy.inst_outputs = [] /\
  in_revert_forward func s /\ about_to_revert func copy s /\
  EVERY (\op. op_taint tn op = {}) copy.inst_operands /\
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
  `step_inst 0 ctx copy s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted` by metis_tac[step_preserves_halted] >>
  rewrite_tac[gas_origin_ptr_edge_def] >> conj_tac
  >- (rewrite_tac[gas_origin_edge_def] >> simp[] >>
      qexists_tac `0` >>
      simp[step_inst_non_invoke, gas_events_step_def] >>
      gvs[in_revert_forward_def, revert_forward_at_def] >> metis_tac[]) >>
  drule_all straight_line_ptr_edge >> simp[]
QED

Theorem extcall_forward_revert_edge[local]:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME rev /\
  rev.inst_opcode = REVERT /\ in_revert_forward func s /\
  EVERY (\op. op_taint tn op = {}) rev.inst_operands /\
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
           mem_safe_step_non_invoke, exit_result_def] >>
      gvs[in_revert_forward_def, revert_forward_at_def] >> metis_tac[]) >>
  rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
  qexists_tac `0` >>
  simp[step_inst_non_invoke, gas_count_step_def, ptr_safe_step_def,
       exit_result_def]
QED

Theorem extcall_forward_pair_path:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME copy /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME rev /\
  copy.inst_opcode = RETURNDATACOPY /\ copy.inst_outputs = [] /\
  copy.inst_operands = [p; Lit 0w; rds] /\
  rev.inst_opcode = REVERT /\ rev.inst_operands = [p; rds] /\
  op_taint tn p = {} /\ op_taint tn rds = {} /\
  step_inst_base copy s = OK u /\
  step_inst_base rev (u with vs_inst_idx := SUC s.vs_inst_idx) =
    Abort Revert_abort t ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (Abort Revert_abort t,step_prov PG G copy u,step_taint copy s u tn)
Proof
  strip_tac >> gen_tac >>
  `step_inst 0 ctx copy s = OK u` by simp[step_inst_non_invoke] >>
  `~is_terminator copy.inst_opcode` by simp[is_terminator_def] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted, step_preserves_control_flow] >>
  `allocas_from lo u` by
    (irule frameActivationSeparationTheory.allocas_from_step >>
     goal_assum (drule_at (Pat `step_inst _ _ _ _ = _`)) >> simp[]) >>
  `in_revert_forward func s` by
    (irule forwarding_pair_active >> metis_tac[]) >>
  `about_to_revert func copy s` by
    (simp[about_to_revert_def, active_inst_def] >>
     qexists_tac `rev` >> simp[] >> qexists_tac `bb` >>
     drule lookup_block_MEM >> drule lookup_block_label >>
     fs[get_instruction_def, AllCaseEqs()]) >>
  `in_revert_forward func (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule forwarding_pair_active >> simp[] >> metis_tac[]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G copy u,step_taint copy s u tn)` by
    (irule extcall_forward_copy_edge >> simp[] >>
     simp[op_taint_def] >> gvs[op_taint_def]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
    (u with vs_inst_idx := SUC s.vs_inst_idx,
     step_prov PG G copy u,step_taint copy s u tn) []
    (Abort Revert_abort t,step_prov PG G copy u,step_taint copy s u tn)` by
    (irule extcall_forward_revert_edge >>
     simp[forwarding_copy_operand_taint] >> fs[allocas_from_def] >> metis_tac[]) >>
  qpat_x_assum `gas_origin_ptr_edge _ _ _ (Abort _ _,_,_)`
    (mp_then Any mp_tac (cj 3 gas_origin_ptr_path_rules)) >>
  simp[exit_result_def] >> strip_tac >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >> simp[] >> disch_then irule >> simp[]
QED

Theorem extcall_failure_layout:
  emit_inst JNZ [cond;Label ok;Label fl] [] sa = (a,sx) /\
  new_block fl sx = (x,sf) /\
  emit_op RETURNDATASIZE [] sf = (z,sz) /\
  compile_alloc_buffer 0 sz = (rb,sp) /\
  emit_void RETURNDATACOPY [rb.buf_operand;Lit 0w;z] sp = (b,sc) /\
  emit_inst REVERT [rb.buf_operand;z] [] sc = (c,se) /\
  new_block ok se = (y,sk) /\ fn_has_code sa sk func ==>
  ?v p entry fail.
    z = Var v /\ rb.buf_operand = Var p /\ v <> p /\
    sf.cs_current_bb = fl /\ sf.cs_current_insts = [] /\
    sz.cs_next_id = sa.cs_next_id + 2 /\
    lookup_block sa.cs_current_bb func.fn_blocks = SOME entry /\
    get_instruction entry (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id JNZ [cond;Label ok;Label fl] []) /\
    lookup_block fl func.fn_blocks = SOME fail /\
    get_instruction fail 0 =
      SOME (mk_inst (sa.cs_next_id + 1) RETURNDATASIZE [] [v]) /\
    get_instruction fail 1 =
      SOME (mk_inst (sa.cs_next_id + 2) ALLOCA [Lit 0w] [p]) /\
    get_instruction fail 2 =
      SOME (mk_inst (sa.cs_next_id + 3) RETURNDATACOPY
        [Var p;Lit 0w;Var v] []) /\
    get_instruction fail 3 =
      SOME (mk_inst (sa.cs_next_id + 4) REVERT [Var p;Var v] [])
Proof
  simp[emit_inst_def, emit_op_def, emit_void_def, compile_alloc_buffer_def,
    new_block_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  fs[fn_has_code_def, emitted_blocks_def] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[get_instruction_def, EL_APPEND_EQN]
QED
