(* Deterministic instruction ghosts shared by array setup consumers. *)
Theory decoderSetupStepPtr
Ancestors wordLoadStorePtr typedCopyPtr entryDispatchPtr ptrSafetyTransport decoderGhostFramePtr
  fragExecPtr bodyPtrDefs ptrSafeRun ptrDiscipline venomExecSemantics venomInst
  venomState compileEnv emitHelper emitHelperProps exprLoweringProps
  words finite_map pred_set list arithmetic codegenRel fragExec contextCodegenRel

Theorem setup_mload_ghost:
  lookup_var q s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  t = update_var x (mload (w2n a) s) s /\
  H = step_prov PG G (mk_inst id MLOAD [Var q] [x]) t /\
  u = step_taint (mk_inst id MLOAD [Var q] [x]) s t tn ==>
  op_taint u (Var x) = {} /\ op_prov H (Var x) = NONE /\
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_allocas = s.vs_allocas /\
  u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
  u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
  (!y. y <> x ==> lookup_var y t = lookup_var y s /\
    FLOOKUP H y = FLOOKUP G y /\ op_taint u (Var y) = op_taint tn (Var y))
Proof
  strip_tac >>
  `op_taint u (Var x) = {} /\ u.t_mem = tn.t_mem /\
   u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans` by
    (gvs[] >> irule mload_ghost_clean >> simp[eval_operand_def] >> metis_tac[]) >>
  simp[] >>
  (conj_tac >- gvs[op_prov_def, step_prov_def, out_prov_def,
    set_prov_def, mk_inst_def, FLOOKUP_DRESTRICT]) >>
  simp[update_var_def] >>
  (conj_tac >- simp[step_taint_def, imm_taint_def, mk_inst_def]) >>
  rpt strip_tac >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    step_prov_other_output, step_taint_other_output, mk_inst_def]
QED

Theorem setup_instruction_continuation:
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ [inst] /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  step_inst_base inst s = OK t /\ t.vs_current_bb = s.vs_current_bb /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  H = step_prov PG G inst t /\ u = step_taint inst s t tn /\
  (!fuel. ptr_inst_ok D lower fuel ctx func G tn inst s) /\
  (!fuel. ptr_safe_run D lower fuel ctx func PG H u
    (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
  !fuel. ptr_safe_run D lower fuel ctx func PG G tn s
Proof
  strip_tac >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    !k. k < LENGTH [inst] ==>
      get_instruction bb (LENGTH sa.cs_current_insts + k) = SOME (EL k [inst])` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >> simp[]) >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (qpat_x_assum `!k. k < LENGTH _ ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  gen_tac >> irule ptr_safe_run_scalar_continuation >>
  qexistsl_tac [`bb`,`inst`,`t`] >>
  gvs[step_inst_non_invoke, ADD1, ptr_safe_step_def]
QED

Theorem setup_emit_continuation:
  emit_op opc ops sa = (Var x,sb) /\
  opc <> INVOKE /\ ~is_terminator opc /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  t.vs_current_bb = s.vs_current_bb /\
  fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  H = step_prov PG G (mk_inst sa.cs_next_id opc ops [x]) t /\
  u = step_taint (mk_inst sa.cs_next_id opc ops [x]) s t tn /\
  (!fuel. ptr_inst_ok D lower fuel ctx func G tn
    (mk_inst sa.cs_next_id opc ops [x]) s) /\
  (!fuel. ptr_safe_run D lower fuel ctx func PG H u
    (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
  !fuel. ptr_safe_run D lower fuel ctx func PG G tn s
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id opc ops [x]) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `same_blocks sa sb` by metis_tac[emit_op_same_blocks] >>
  irule setup_instruction_continuation >> simp[] >>
  goal_assum (drule_at Any) >> qexistsl_tac [`sa`,`sb`] >>
  gvs[mk_inst_def, same_blocks_def]
QED

Theorem setup_mload_continuation:
  emit_op MLOAD [Var q] sa = (Var x,sb) /\
  lookup_var q s = SOME a /\ ptr_covers G tn q s 32 /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  H = step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var q] [x]) t /\
  u = step_taint (mk_inst sa.cs_next_id MLOAD [Var q] [x]) s t tn /\
  (!fuel. ptr_safe_run D lower fuel ctx func PG H u
    (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
  !fuel. ptr_safe_run D lower fuel ctx func PG G tn s
Proof
  strip_tac >>
  `t = update_var x (mload (w2n a) s) s` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def,
       exec_read1_def, eval_operand_def]) >>
  `!fuel. ptr_inst_ok D lower fuel ctx func G tn
    (mk_inst sa.cs_next_id MLOAD [Var q] [x]) s` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[] >> irule ptr_inst_ok_mload >> simp[]) >>
  `MLOAD <> INVOKE /\ ~is_terminator MLOAD /\
   t.vs_current_bb = s.vs_current_bb` by simp[is_terminator_def, update_var_def] >>
  drule_all setup_emit_continuation >> simp[]
QED

Theorem setup_scalar_binop_ghost:
  (opc = ADD \/ opc = MUL) /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  op_prov G left = NONE /\ op_prov G right = NONE /\
  t = update_var x value s /\
  H = step_prov PG G (mk_inst id opc [left;right] [x]) t /\
  u = step_taint (mk_inst id opc [left;right] [x]) s t tn ==>
  op_taint u (Var x) = {} /\ op_prov H (Var x) = NONE /\
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_allocas = s.vs_allocas /\
  u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
  u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
  (!y. y <> x ==> lookup_var y t = lookup_var y s /\
    FLOOKUP H y = FLOOKUP G y /\ op_taint u (Var y) = op_taint tn (Var y))
Proof
  strip_tac >>
  `new_site_bytes s t = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[step_prov_def, step_taint_def, out_prov_def, first_prov_def,
    set_prov_def, mk_inst_def, op_prov_def, set_var_taint_def,
    out_taint_def, op_taint_def, mem_taint_def, new_site_bytes_def,
    step_writes_def, written_taint_def, store_taint_def, imm_taint_def,
    adopt_reset_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
    source_memory_write_ranges_def, range_bytes_def, update_var_def,
    lookup_var_def, SF CONJ_ss] >>
  Cases_on `eval_operand left s` >> gvs[op_taint_def]
QED

Theorem setup_scalar_binop_safe:
  (opc = ADD \/ opc = MUL) /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  allocas_from lower s /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D lower fuel ctx func G tn
    (mk_inst id opc [left;right] [x]) s
Proof
  strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
    source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
    combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem setup_scalar_binop_continuation:
  (opc = ADD \/ opc = MUL) /\
  emit_op opc [left;right] sa = (Var x,sb) /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  H = step_prov PG G (mk_inst sa.cs_next_id opc [left;right] [x]) t /\
  u = step_taint (mk_inst sa.cs_next_id opc [left;right] [x]) s t tn /\
  (!fuel. ptr_safe_run D lower fuel ctx func PG H u
    (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
  !fuel. ptr_safe_run D lower fuel ctx func PG G tn s
Proof
  strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def,
       exec_pure2_def, AllCaseEqs(), update_var_def]) >>
  `!fuel. ptr_inst_ok D lower fuel ctx func G tn
    (mk_inst sa.cs_next_id opc [left;right] [x]) s` by
    (gen_tac >> irule setup_scalar_binop_safe >> simp[]) >>
  `opc <> INVOKE /\ ~is_terminator opc` by gvs[is_terminator_def] >>
  drule_all setup_emit_continuation >> simp[]
QED
