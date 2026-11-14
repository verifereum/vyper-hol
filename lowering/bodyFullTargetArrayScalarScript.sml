(* The array suffix's raw runs, certified at the same pointer/memory
   endpoint. Safety is explicit: the caller supplies checks for the actual
   emitted code, not an independently chosen target run. *)
Theory bodyFullTargetArrayScalar
Ancestors
  exprSimArrayIndex bodyFullUnwrapRun fragGasSeqPtr fragGasOriginPtr
  fragExecMem fragExec exprLoweringProps compileEnv venomState venomInst
  list rich_list venomExecSemantics venomExecProofs fragGasSeq
  fragGasOrigin gasEvents memSafeRun fragGasSeqAbort venomInstProofs instIdxIndep fragGasPathPtr gasCount ptrSafeRun
  augAssignPtrScalarRun augAssignPtrScalarCertificate augAssignPtrScalarSafety
  augAssignPtrScalarExec ptrDiscipline emitHelper pred_set finite_map
  unitTransformDefs freshWrites contextCodegenRel codegenRel

Theorem array_assert_abort_frame_diagnostic[local]:
  ~s.vs_halted ==>
  let t = revert_state (set_returndata [] s) in
    t with vs_vars := s.vs_vars <> s
Proof
  simp[revert_state_def, set_returndata_def] >>
  strip_tac >> strip_tac >>
  pop_assum (mp_tac o AP_TERM ``\s:venom_state. s.vs_halted``) >> simp[]
QED

Theorem array_bounds_check_scalar_code[local]:
  array_bounds_check idx len sgn sa = ((),sb) /\
  scalar_available A idx /\ scalar_available A len ==>
  scalar_code A (emitted_insts sa sb)
Proof
  Cases_on `sgn` >>
  simp[array_bounds_check_def, array_bounds_valid_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def,
       emitted_insts_def, scalar_code_def, scalar_shape_def,
       scalar_binary_def, scalar_unary_def, scalar_available_def, mk_inst_def] >>
  rpt strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, scalar_code_def, scalar_shape_def,
       scalar_binary_def, scalar_unary_def, scalar_available_def]
QED

Theorem array_scalar_clean_operand_step[local]:
  scalar_shape ins /\
  EVERY (\op. op_prov G op = NONE /\ op_taint tn op = {}) ins.inst_operands ==>
  (!op. op_prov G op = NONE /\ op_taint tn op = {} ==>
     op_prov (step_prov PG G ins u) op = NONE /\
     op_taint (step_taint ins s u tn) op = {}) /\
  (!v. MEM v ins.inst_outputs ==>
     op_prov (step_prov PG G ins u) (Var v) = NONE /\
     op_taint (step_taint ins s u tn) (Var v) = {})
Proof
  strip_tac >> drule_all scalar_step_prov >> strip_tac >>
  drule_all scalar_step_var_taint >> strip_tac >>
  qpat_x_assum `!u PG. _` (qspecl_then [`u`, `PG`] strip_assume_tac) >>
  qpat_x_assum `!u s. _` (qspecl_then [`u`, `s`] strip_assume_tac) >>
  conj_tac
  >- (Cases >> simp[op_prov_def, op_taint_def] >>
      Cases_on `MEM s' ins.inst_outputs` >>
      gvs[op_prov_def, op_taint_def]) >>
  metis_tac[]
QED

Theorem array_scalar_cons_ptr[local]:
  scalar_shape ins /\
  EVERY (\op. op_prov G op = NONE /\ op_taint tn op = {}) ins.inst_operands /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!u H tm.
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!op. op_prov G op = NONE /\ op_taint tn op = {} ==>
      op_prov H op = NONE /\ op_taint tm op = {}) /\
    (!v. MEM v ins.inst_outputs ==>
      op_prov H (Var v) = NONE /\ op_taint tm (Var v) = {}) ==>
    ?G' tn'. inst_seq_ptr D lo ctx func PG H tm code u G' tn') ==>
  ?G' tn'. inst_seq_ptr D lo ctx func PG G tn (ins::code) s G' tn'
Proof
  strip_tac >>
  `ptr_inst_ok D lo 0 ctx func G tn ins s` by
    (irule scalar_ptr_inst_ok_lo >> simp[]) >>
  Cases_on `step_inst_base ins s` >> simp[inst_seq_ptr_def] >>
  first_x_assum irule >>
  drule_all array_scalar_clean_operand_step >> strip_tac >>
  drule_all (cj 1 scalar_exec_result) >> strip_tac >>
  gvs[allocas_from_def, allocas_below_fmp_def, update_var_def] >>
  metis_tac[]
QED

Theorem array_bounds_check_ptr_exists[local]:
  array_bounds_check idx len sgn sa = ((),sb) /\
  eval_operand idx s = SOME i /\ eval_operand len s = SOME n /\
  op_prov G idx = NONE /\ op_prov G len = NONE /\
  op_taint tn idx = {} /\ op_taint tn len = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?G' tn'. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn'
Proof
  Cases_on `sgn` >>
  simp[array_bounds_check_def, array_bounds_valid_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, GSYM mk_inst_def] >>
  rpt (irule array_scalar_cons_ptr >>
       simp[scalar_shape_def, scalar_binary_def, scalar_unary_def, mk_inst_def] >>
       rpt strip_tac) >>
  simp[inst_seq_ptr_def, op_prov_def, op_taint_def] >> metis_tac[]
QED

Theorem array_bounds_check_mem_ok[local]:
  array_bounds_check idx len sgn sa = ((),sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  Cases_on `sgn` >>
  simp[array_bounds_check_def, array_bounds_valid_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND] >>
  irule run_inst_seq_mem_ok_every >>
  simp[inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]
QED

Theorem array_bounds_check_writes_fresh[local]:
  array_bounds_check idx len sgn sa = ((),sb) ==>
  writes_fresh sa (emitted_insts sa sb)
Proof
  `straight_fresh (array_bounds_check idx len sgn)` suffices_by
    metis_tac[straight_fresh_def] >>
  rw[array_bounds_check_def, array_bounds_valid_def] >>
  rpt (FIRST [irule straight_fresh_bind >> conj_tac,
              irule straight_fresh_ignore_bind >> conj_tac,
              gen_tac >> BETA_TAC,
              irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
              irule straight_fresh_emit_void >> simp[fresh_write_op_def] >> NO_TAC,
              MATCH_ACCEPT_TAC straight_fresh_return,
              IF_CASES_TAC])
QED

Theorem array_bounds_check_ok_frame[local]:
  array_bounds_check idx len sgn sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >> drule array_bounds_check_writes_fresh >> strip_tac >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >> simp[] >>
  qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem array_bounds_check_joint_ok:
  array_bounds_check idx len sgn sa = ((),sb) /\
  eval_operand idx s = SOME i /\ eval_operand len s = SOME n /\
  fresh_vars_wrt sa s /\ idx_in_range sgn i n /\
  fn_has_code sa sb func /\
  EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
               ~is_terminator ins.inst_opcode) (emitted_insts sa sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn' ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn') /\
    fresh_vars_wrt sb t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >> drule_all array_bounds_check_ok >> strip_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (ss' with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')` by
    (irule emitted_origin_ptr_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> fs[same_blocks_def]) >>
  qexists_tac `ss'` >> simp[]
QED

Theorem array_elem_ptr_joint:
  array_elem_ptr bop idx dyn ws esz sa = (p,sb) /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME i /\
  fresh_vars_wrt sa s /\ fn_has_code sa sb func /\
  EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
               ~is_terminator ins.inst_opcode) (emitted_insts sa sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn' ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn') /\
    fresh_vars_wrt sb t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    eval_operand p t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz)
Proof
  strip_tac >> drule_all array_elem_ptr_run >> strip_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (ss' with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')` by
    (irule emitted_origin_ptr_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> fs[same_blocks_def]) >>
  qexists_tac `ss'` >> simp[]
QED

(* On ASSERT failure only the executed prefix is certified. The cursor
   of the raw sequence is restored by run_inst_seq, hence the explicit j. *)
Theorem array_abort_joint_run[local]:
  !code s t a G tn G' tn' ctx func bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                 ~is_terminator ins.inst_opcode) code /\
    run_inst_seq_mem_ok code s /\
    inst_seq_ptr D lo ctx func PG G tn code s G' tn' /\
    run_inst_seq code s = Abort a t ==>
    ?j. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
          (Abort a (t with vs_inst_idx := j),G',tn')
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, inst_seq_ptr_def, run_inst_seq_mem_ok_def]
  >~ [`step_inst_base h s = OK u`]
  >- (`step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
      `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_halted, step_preserves_control_flow] >>
      `EVERY (\ins. ~is_terminator ins.inst_opcode) code` by fs[EVERY_MEM] >>
      first_x_assum (qspecl_then [`u with vs_inst_idx := SUC s.vs_inst_idx`,
        `t with vs_inst_idx := SUC s.vs_inst_idx`, `a`, `step_prov PG G h u`,
        `step_taint h s u tn`, `G'`, `tn'`, `ctx`, `func`, `bb`] mp_tac) >>
      simp[run_inst_seq_inst_idx, exec_result_map_def] >> strip_tac >>
      qexists_tac `j` >>
      `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
         step_prov PG G h u, step_taint h s u tn)` by
        (drule_all straight_line_origin_ptr_edge >> simp[]) >>
      drule (cj 2 gas_origin_ptr_path_rules) >> disch_then drule >> simp[]) >>
  qexists_tac `t.vs_inst_idx` >> simp[] >>
  irule (cj 3 gas_origin_ptr_path_rules) >> simp[exit_result_def] >>
  simp[gas_origin_ptr_edge_def] >> conj_tac
  >- (simp[gas_origin_edge_def] >>
      qexists_tac `0` >>
      simp[step_inst_non_invoke, gas_events_step_def,
           mem_safe_step_non_invoke, exit_result_def]) >>
  simp[gas_path_ptr_edge_def] >> qexists_tac `0` >>
  simp[gas_count_step_def, ptr_safe_step_def, step_inst_non_invoke,
       exit_result_def]
QED

Theorem array_bounds_check_joint_abort:
  array_bounds_check idx len sgn sa = ((),sb) /\
  eval_operand idx s = SOME i /\ eval_operand len s = SOME n /\
  fresh_vars_wrt sa s /\ ~idx_in_range sgn i n /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  fn_has_code sa sb func /\
  EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
               ~is_terminator ins.inst_opcode) (emitted_insts sa sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn' ==>
  ?t j. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort Revert_abort (t with vs_inst_idx := j),G',tn')
Proof
  strip_tac >> drule_all array_bounds_check_oob >> strip_tac >>
  `?j. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (Abort Revert_abort (ss' with vs_inst_idx := j),G',tn')` by
    (irule array_abort_joint_run >> simp[] >>
     fs[fn_has_code_def, IS_PREFIX_APPEND] >>
     qexistsl_tac [`bb`, `emitted_insts sa sb`] >>
     gvs[IS_PREFIX_APPEND, DROP_APPEND, DROP_LENGTH_NIL,
         APPEND_ASSOC]) >>
  metis_tac[]
QED
