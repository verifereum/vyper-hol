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
  fragGasOriginPtrDead
  unitTransformDefs freshWrites contextCodegenRel codegenRel loweringStateRelDefs

Theorem array_scalar_step_abort_frame[local]:
  scalar_shape ins /\ step_inst_base ins s = Abort Revert_abort t ==>
  t = revert_state (set_returndata [] s)
Proof
  simp[scalar_shape_def, scalar_binary_def, scalar_unary_def,
       LENGTH_EQ_NUM_compute] >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, exec_pure1_def, exec_pure2_def,
      AllCaseEqs()]
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

Theorem array_bounds_check_shape[local]:
  array_bounds_check idx len sgn sa = ((),sb) ==>
  EVERY scalar_shape (emitted_insts sa sb)
Proof
  Cases_on `sgn` >>
  simp[array_bounds_check_def, array_bounds_valid_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, scalar_shape_def, scalar_binary_def, scalar_unary_def]
QED

Theorem array_scalar_seq_abort_frame[local]:
  !code s t.
  EVERY scalar_shape code /\ writes_fresh sa code /\
  run_inst_seq code s = Abort Revert_abort t ==>
  (t with vs_vars := s.vs_vars) = revert_state (set_returndata [] s) /\
  (!x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> simp[run_inst_seq_def, writes_fresh_def] >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[]
  >~ [`step_inst_base h s = OK u`]
  >- (drule_all step_fresh_write_op >> strip_tac >>
      first_x_assum (qspecl_then [`u`, `t`] mp_tac) >>
      simp[writes_fresh_def] >> strip_tac >>
      conj_tac
      >- (qpat_x_assum `u = _` SUBST_ALL_TAC >>
          gvs[revert_state_def, set_returndata_def, venom_state_component_equality]) >>
      gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all array_scalar_step_abort_frame >> strip_tac >>
  gvs[revert_state_def, set_returndata_def, venom_state_component_equality]
QED

Theorem array_bounds_check_metadata[local]:
  array_bounds_check idx len sgn sa = ((),sb) /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s H tm ==>
  (!x. not_fresh_at sa x ==>
    FLOOKUP H x = FLOOKUP G x /\
    FLOOKUP tm.t_var x = FLOOKUP tn.t_var x) /\
  tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
  tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule array_bounds_check_shape >> strip_tac >>
  drule_all scalar_shape_seq_metadata_frame >> strip_tac >>
  drule array_bounds_check_writes_fresh >>
  simp[writes_fresh_def, EVERY_MEM] >> strip_tac >>
  rpt strip_tac >>
  `~MEM x (FLAT (MAP (\i. i.inst_outputs) (emitted_insts sa sb)))` by
    (simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  metis_tac[]
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

Theorem array_bounds_check_certified:
  array_bounds_check idx len sgn sa = ((),sb) /\
  eval_operand idx s = SOME i /\ eval_operand len s = SOME n /\
  fresh_vars_wrt sa s /\
  op_prov G idx = NONE /\ op_prov G len = NONE /\
  op_taint tn idx = {} /\ op_taint tn len = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  ?G' tn'. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x) /\
    (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
      (t with vs_vars := s.vs_vars) = s /\
      (!x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)) /\
    (!t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t ==>
      (t with vs_vars := s.vs_vars) = revert_state (set_returndata [] s) /\
      (!x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x))
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[array_bounds_check_mem_ok] >> simp[] >>
  `?G' tn'. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn'`
    by (irule array_bounds_check_ptr_exists >> metis_tac[]) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  drule_all array_bounds_check_metadata >> strip_tac >> simp[] >>
  conj_tac >- metis_tac[array_bounds_check_ok_frame] >>
  metis_tac[array_scalar_seq_abort_frame, array_bounds_check_shape,
            array_bounds_check_writes_fresh]
QED

Theorem array_address_ptr_inst_ok[local]:
  (opc = ADD \/ opc = MUL) /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D lo fuel ctx func G tn (mk_inst id opc [left;right] [out]) s
Proof
  strip_tac >>
  `scalar_shape (mk_inst id opc [left;right] [out])` by
    simp[scalar_shape_def, scalar_binary_def, mk_inst_def] >>
  `access_ok lo G func (mk_inst id opc [left;right] [out]) s /\
   taint_ok func tn (mk_inst id opc [left;right] [out]) s` by
    (gvs[] >> simp[access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def] >>
     metis_tac[]) >>
  drule scalar_shape_control >> strip_tac >>
  drule scalar_step_shape >> strip_tac >>
  simp[ptr_inst_ok_def, step_inst_non_invoke] >>
  rpt strip_tac >> gvs[] >>
  drule_all (cj 1 scalar_exec_result) >> strip_tac >>
  gvs[update_var_def]
QED

Theorem array_address_taint_step[local]:
  (opc = ADD \/ opc = MUL) /\ op_taint tn left = {} /\ op_taint tn right = {} ==>
  op_taint (step_taint (mk_inst id opc [left;right] [out]) s u tn) (Var out) = {} /\
  (!op. op_taint tn op = {} ==>
    op_taint (step_taint (mk_inst id opc [left;right] [out]) s u tn) op = {})
Proof
  strip_tac >>
  `out_taint tn (mk_inst id opc [left;right] [out]) s = {}` by
    (Cases_on `eval_operand left s` >> simp[out_taint_def, mk_inst_def]) >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, op_taint_def,
       FLOOKUP_UPDATE] >>
  Cases >> simp[op_taint_def] >>
  Cases_on `out = s'` >> simp[]
QED

Theorem array_address_cons_ptr[local]:
  (opc = ADD \/ opc = MUL) /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!u H tm.
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!op. op_taint tn op = {} ==> op_taint tm op = {}) /\
    op_taint tm (Var out) = {} ==>
    ?G' tn'. inst_seq_ptr D lo ctx func PG H tm code u G' tn') ==>
  ?G' tn'. inst_seq_ptr D lo ctx func PG G tn
    (mk_inst id opc [left;right] [out]::code) s G' tn'
Proof
  strip_tac >>
  `ptr_inst_ok D lo 0 ctx func G tn (mk_inst id opc [left;right] [out]) s` by
    (irule array_address_ptr_inst_ok >> simp[]) >>
  Cases_on `step_inst_base (mk_inst id opc [left;right] [out]) s` >>
  simp[inst_seq_ptr_def] >> first_x_assum irule >>
  `scalar_shape (mk_inst id opc [left;right] [out])` by
    simp[scalar_shape_def, scalar_binary_def, mk_inst_def] >>
  drule_all (cj 1 scalar_exec_result) >> strip_tac >>
  gvs[allocas_from_def, allocas_below_fmp_def, update_var_def] >>
  metis_tac[array_address_taint_step]
QED

Theorem array_elem_ptr_exists[local]:
  array_elem_ptr bop idx dyn ws esz sa = (p,sb) /\
  op_taint tn bop = {} /\ op_taint tn idx = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?G' tn'. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn'
Proof
  Cases_on `dyn` >>
  simp[array_elem_ptr_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, GSYM mk_inst_def] >>
  rpt (irule array_address_cons_ptr >> simp[] >> rpt strip_tac) >>
  simp[inst_seq_ptr_def, op_taint_def] >> metis_tac[]
QED

Theorem array_elem_ptr_writes_fresh[local]:
  array_elem_ptr bop idx dyn ws esz sa = (p,sb) ==>
  writes_fresh sa (emitted_insts sa sb)
Proof
  `straight_fresh (array_elem_ptr bop idx dyn ws esz)` suffices_by
    metis_tac[straight_fresh_def] >>
  rw[array_elem_ptr_def] >>
  rpt (FIRST [irule straight_fresh_bind >> conj_tac,
              gen_tac >> BETA_TAC,
              irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
              MATCH_ACCEPT_TAC straight_fresh_return,
              IF_CASES_TAC])
QED

Theorem array_elem_ptr_shape_mem[local]:
  array_elem_ptr bop idx dyn ws esz sa = (p,sb) ==>
  EVERY scalar_shape (emitted_insts sa sb) /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  Cases_on `dyn` >>
  simp[array_elem_ptr_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND] >>
  (conj_tac >- simp[scalar_shape_def, scalar_binary_def]) >>
  irule run_inst_seq_mem_ok_every >>
  simp[inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]
QED

Theorem array_address_cons_success[local]:
  run_inst_seq (ins::code) s = OK t /\
  EVERY (\i. ~is_terminator i.inst_opcode) code /\ 
  inst_seq_ptr D lo ctx func PG G tn (ins::code) s H tm ==>
  ?u. step_inst_base ins s = OK u /\
    run_inst_seq code (u with vs_inst_idx := SUC s.vs_inst_idx) =
      OK (t with vs_inst_idx := SUC s.vs_inst_idx) /\
    inst_seq_ptr D lo ctx func PG (step_prov PG G ins u) (step_taint ins s u tn)
      code (u with vs_inst_idx := SUC s.vs_inst_idx) H tm
Proof
  simp[run_inst_seq_def, inst_seq_ptr_def] >> strip_tac >>
  Cases_on `step_inst_base ins s` >> gvs[] >>
  simp[run_inst_seq_inst_idx, exec_result_map_def]
QED

Theorem array_elem_ptr_nonalias_metadata[local]:
  array_elem_ptr bop idx dyn ws esz sa = (p,sb) /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME i /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\ op_prov G idx = NONE /\
  op_taint tn bop = {} /\ op_taint tn idx = {} /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s H tm ==>
  op_prov H p = op_prov G bop /\ op_taint tm p = {}
Proof
  Cases_on `dyn` >>
  simp[array_elem_ptr_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  fs[DROP_LENGTH_APPEND, mk_inst_def] >>
  rpt (dxrule array_address_cons_success >>
       simp[is_terminator_def] >> disch_then drule >> strip_tac) >>
  gvs[inst_seq_ptr_def] >>
  Cases_on `op_prov G bop` >>
  simp[step_prov_def, out_prov_def, first_prov_def, set_prov_def,
       op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[array_address_taint_step, op_taint_def] >>
  Cases_on `bop` >> gvs[op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  `s' <> STRING #"%" (toString sa.cs_next_var)` by
    (gvs[not_fresh_at_def]) >>
  gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem array_elem_ptr_output_metadata[local]:
  array_elem_ptr bop idx dyn ws esz sa = (p,sb) /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME i /\
  fresh_vars_wrt sa s /\ op_prov G idx = NONE /\
  op_taint tn bop = {} /\ op_taint tn idx = {} /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s H tm ==>
  op_prov H p = op_prov G bop /\ op_taint tm p = {}
Proof
  strip_tac >>
  `!x. bop = Var x ==> not_fresh_at sa x` by
    (gen_tac >> disch_tac >> rewrite_tac[not_fresh_at_def] >>
     gen_tac >> disch_tac >>
     irule emitHelperPropsTheory.fresh_vars_wrt_eval_operand >>
     qexistsl [`bop`, `s`, `sa`, `b`] >> simp[]) >>
  drule_all array_elem_ptr_nonalias_metadata >> simp[]
QED

Theorem array_elem_ptr_certified:
  array_elem_ptr bop idx dyn ws esz sa = (p,sb) /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME i /\
  fresh_vars_wrt sa s /\ op_taint tn bop = {} /\ op_taint tn idx = {} /\
  op_prov G idx = NONE /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  ?t H tm. run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s H tm /\
    op_taint tm p = {} /\ op_prov H p = op_prov G bop /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP tm.t_var x = FLOOKUP tn.t_var x /\
      FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x) /\
    (t with vs_vars := s.vs_vars) = s /\
    eval_operand p t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz)
Proof
  strip_tac >>
  `EVERY scalar_shape (emitted_insts sa sb) /\
   run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[array_elem_ptr_shape_mem] >> simp[] >>
  drule_all array_elem_ptr_run >> strip_tac >>
  `?H tm. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s H tm`
    by (irule array_elem_ptr_exists >> metis_tac[]) >>
  qexistsl_tac [`ss'`, `H`, `tm`] >> simp[] >>
  drule_all array_elem_ptr_output_metadata >> strip_tac >> simp[] >>
  drule_all scalar_shape_seq_metadata_frame >> strip_tac >> simp[] >>
  drule array_elem_ptr_writes_fresh >> strip_tac >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  `ss' with vs_vars := s.vs_vars = s` by
    (qpat_x_assum `ss' = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  simp[] >> rpt strip_tac >>
  `~MEM x (FLAT (MAP (\i. i.inst_outputs) (emitted_insts sa sb)))` by
    (fs[writes_fresh_def, EVERY_MEM] >>
     simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem array_elem_ptr_nonalias_run[local]:
  array_elem_ptr bop idx dyn ws esz sa = (p,sb) /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME i /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  (!x. idx = Var x ==> not_fresh_at sa x) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand p t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz)
Proof
  Cases_on `dyn` >>
  simp[array_elem_ptr_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, GSYM mk_inst_def] >>
  `!n w u. sa.cs_next_var <= n ==>
     eval_operand bop (update_var (STRING #"%" (toString n)) w u) = eval_operand bop u /\
     eval_operand idx (update_var (STRING #"%" (toString n)) w u) = eval_operand idx u` by
    (rpt strip_tac >> Cases_on `bop` >> Cases_on `idx` >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
         not_fresh_at_def]) >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def] >>
  simp[exec_pure2_def, eval_operand_def] >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, exec_pure2_def] >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, exec_pure2_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[run_inst_seq_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem array_elem_ptr_nonalias_uniform:
  array_elem_ptr bop idx dyn ws esz sa = (p,sb) /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME iw /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  (!x. idx = Var x ==> not_fresh_at sa x) /\
  op_taint tn bop = {} /\ op_taint tn idx = {} /\
  op_prov G idx = NONE /\ allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  ?t H tm. run_inst_seq (emitted_insts sa sb) s = OK t /\
    (!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s H tm) /\
    op_taint tm p = {} /\ op_prov H p = op_prov G bop /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP H x = FLOOKUP G x /\ FLOOKUP tm.t_var x = FLOOKUP tn.t_var x /\
      FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x) /\
    (t with vs_vars := s.vs_vars) = s /\
    eval_operand p t = SOME ((if dyn then b + n2w ws else b) + iw * n2w esz)
Proof
  strip_tac >>
  `EVERY scalar_shape (emitted_insts sa sb) /\
   run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[array_elem_ptr_shape_mem] >> simp[] >>
  drule_all array_elem_ptr_nonalias_run >> strip_tac >>
  `?H tm. inst_seq_ptr ARB lo ctx func PG G tn (emitted_insts sa sb) s H tm`
    by (irule array_elem_ptr_exists >> metis_tac[]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s H tm` by
    (gen_tac >>
     `?H' tm'. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s H' tm'`
       by (irule array_elem_ptr_exists >> metis_tac[]) >>
     metis_tac[inst_seq_ptr_ghost_unique]) >>
  qexistsl [`t`, `H`, `tm`] >> simp[] >>
  drule_all array_elem_ptr_nonalias_metadata >> strip_tac >> simp[] >>
  drule_all scalar_shape_seq_metadata_frame >> strip_tac >> simp[] >>
  drule array_elem_ptr_writes_fresh >> strip_tac >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  `t with vs_vars := s.vs_vars = s` by
    (qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  simp[] >> rpt strip_tac >>
  `~MEM x (FLAT (MAP (\i. i.inst_outputs) (emitted_insts sa sb)))` by
    (fs[writes_fresh_def, EVERY_MEM] >>
     simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem array_bounds_check_nonalias_run[local]:
  array_bounds_check idx len sgn sa = ((),sb) /\
  eval_operand idx s = SOME iw /\ eval_operand len s = SOME nw /\
  (!x. idx = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s =
    (if idx_in_range sgn iw nw then OK t else Abort Revert_abort t)
Proof
  Cases_on `sgn` >>
  simp[array_bounds_check_def, array_bounds_valid_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND] >>
  `!n w u. sa.cs_next_var <= n ==>
     eval_operand idx (update_var (STRING #"%" (toString n)) w u) = eval_operand idx u /\
     eval_operand len (update_var (STRING #"%" (toString n)) w u) = eval_operand len u` by
    (rpt strip_tac >> Cases_on `idx` >> Cases_on `len` >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
         not_fresh_at_def]) >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def] >>
  simp[exec_pure2_def, exec_pure1_def, eval_operand_def] >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def] >>
  simp[exec_pure2_def, exec_pure1_def] >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def] >>
  simp[exec_pure2_def, exec_pure1_def] >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def] >>
  simp[exec_pure2_def, exec_pure1_def] >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  Cases_on `iw < 0w` >> Cases_on `w2n iw < w2n nw` >>
  simp[bool_to_word_def, idx_in_range_def, wordsTheory.WORD_OR_CLAUSES] >>
  simp[Once run_inst_seq_def] >>
  qmatch_goalsub_abbrev_tac `step_inst_base ins st` >>
  simp[Abbr `ins`, step_inst_base_opcode_eqs] >>
  simp[exec_pure1_def, Abbr `st`, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >>
  simp[Once run_inst_seq_def] >>
  simp[step_inst_base_opcode_eqs, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, run_inst_seq_def]
QED

Theorem array_bounds_check_nonalias_uniform:
  array_bounds_check idx len sgn sa = ((),sb) /\
  eval_operand idx s = SOME iw /\ eval_operand len s = SOME nw /\
  (!x. idx = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\
  op_prov G idx = NONE /\ op_prov G len = NONE /\
  op_taint tn idx = {} /\ op_taint tn len = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  fn_has_code sa sb func /\
  EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
               ~is_terminator ins.inst_opcode) (emitted_insts sa sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t j H tm.
    run_inst_seq (emitted_insts sa sb) s =
      (if idx_in_range sgn iw nw then OK t else Abort Revert_abort t) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (if idx_in_range sgn iw nw then
         (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,tm)
       else (Abort Revert_abort (t with vs_inst_idx := j),H,tm))) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP H x = FLOOKUP G x /\ FLOOKUP tm.t_var x = FLOOKUP tn.t_var x /\
      FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x) /\
    (t with vs_vars := s.vs_vars) =
      (if idx_in_range sgn iw nw then s else revert_state (set_returndata [] s))
Proof
  strip_tac >> drule_all array_bounds_check_nonalias_run >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[array_bounds_check_mem_ok] >>
  `?H tm. inst_seq_ptr
    <|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>
    lo ctx func PG G tn (emitted_insts sa sb) s H tm` by
    (irule array_bounds_check_ptr_exists >> metis_tac[]) >>
  drule_all array_bounds_check_metadata >> strip_tac >>
  Cases_on `idx_in_range sgn iw nw` >> gvs[]
  >- (`gas_origin_ptr_path
        (<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>,
         lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,tm)` by
        (irule emitted_origin_ptr_path >> simp[] >>
         qexistsl [`emitted_insts sa sb`, `sa`] >> fs[same_blocks_def]) >>
      qexistsl [`H`, `tm`] >> simp[] >>
      conj_tac
      >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> gvs[]) >>
      metis_tac[array_bounds_check_ok_frame]) >>
  `?j. gas_origin_ptr_path
      (<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>,
       lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort Revert_abort (t with vs_inst_idx := j),H,tm)` by
    (irule array_abort_joint_run >> simp[] >>
     fs[fn_has_code_def, IS_PREFIX_APPEND] >>
     qexistsl [`bb`, `emitted_insts sa sb`] >>
     gvs[IS_PREFIX_APPEND, DROP_APPEND, DROP_LENGTH_NIL, APPEND_ASSOC]) >>
  qexistsl [`j`, `H`, `tm`] >> simp[] >>
  conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> gvs[]) >>
  metis_tac[array_scalar_seq_abort_frame, array_bounds_check_shape,
            array_bounds_check_writes_fresh]
QED
