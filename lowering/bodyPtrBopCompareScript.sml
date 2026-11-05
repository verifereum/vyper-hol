Theory bodyPtrBopCompare
Ancestors
  ptrSafeRun ptrDiscipline venomExecSemantics venomInstProofs venomInst
  venomState codegenRel contextCodegenRel fragGasSeqPtr fragGasPathPtr finite_map

Theorem bop_compare_ptr_inst_ok:
  ((opc = EQ /\ ops = [left; right] /\
    op_prov G left = NONE /\ op_prov G right = NONE) \/
   (opc = ISZERO /\ ops = [left])) /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops [tmp]) s
Proof
  rpt strip_tac >> gvs[] >>
  (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  TRY (conj_tac >- (rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF])) >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, exec_pure1_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[])
QED

Theorem bop_compare_counted_edge:
  ((opc = EQ /\ ops = [left; right] /\
    op_prov G left = NONE /\ op_prov G right = NONE) \/
   (opc = ISZERO /\ ops = [left])) /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [tmp]) /\
  step_inst_base (mk_inst id opc ops [tmp]) s = OK u ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc ops [tmp]) u)
    (step_taint (mk_inst id opc ops [tmp]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops [tmp]) s` by
    (irule bop_compare_ptr_inst_ok >> metis_tac[]) >>
  `(mk_inst id opc ops [tmp]).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst id opc ops [tmp]).inst_opcode` by
    gvs[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >> simp[mk_inst_def]
QED

Theorem bop_compare_ghost_frame:
  ((opc = EQ /\ ops = [left; right]) \/ (opc = ISZERO /\ ops = [left])) /\
  u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp ==>
  op_prov (step_prov PG G (mk_inst id opc ops [tmp]) u) (Var tmp) = NONE /\
  op_taint (step_taint (mk_inst id opc ops [tmp]) s u tn) (Var tmp) = {} /\
  (step_taint (mk_inst id opc ops [tmp]) s u tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id opc ops [tmp]) s u tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc ops [tmp]) s u tn).t_trans = tn.t_trans /\
  (!x. x <> tmp ==>
    FLOOKUP (step_prov PG G (mk_inst id opc ops [tmp]) u) x = FLOOKUP G x /\
    FLOOKUP (step_taint (mk_inst id opc ops [tmp]) s u tn).t_var x =
      FLOOKUP tn.t_var x)
Proof
  strip_tac >> gvs[] >>
  simp[op_prov_def, step_prov_def, set_prov_def, out_prov_def,
       op_taint_def, step_taint_def, set_var_taint_def, out_taint_def,
       mk_inst_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
       mem_taint_def, store_taint_def, adopt_reset_def,
       new_site_bytes_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, range_bytes_def] >>
  Cases_on `eval_operand left s` >> simp[] >>
  simp[pred_setTheory.EXTENSION] >>
  rpt strip_tac >> (eq_tac >- (strip_tac >> gvs[FLOOKUP_DEF])) >> simp[]
QED

Theorem bop_compare_state_frame:
  ((opc = EQ /\ ops = [left; right]) \/ (opc = ISZERO /\ ops = [left])) /\
  step_inst_base (mk_inst id opc ops [tmp]) s = OK u ==>
  (u with vs_vars := s.vs_vars) = s
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, exec_pure2_def, exec_pure1_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), update_var_def]
QED

