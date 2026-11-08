Theory bodyPtrBopScalarStep
Ancestors
  bodyPtrBopCompare typedCopyPtr fragGasSeqPtr ptrSafeRun ptrDiscipline
  venomExecSemantics venomExecProofs venomInstProofs venomInst venomState
  codegenRel contextCodegenRel finite_map list pred_set

(* This whitelist is deliberately finite and excludes memory, allocation,
   calls, PHIs and ASSERT (which has its own successful/abort boundary). *)
Theorem bop_scalar_state_frame:
  MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
           LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
           SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN] /\
  step_inst_base (mk_inst id opc ops [tmp]) s = OK u ==>
  (u with vs_vars := s.vs_vars) = s
Proof
  strip_tac >> gvs[MEM] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors,
                   instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[mk_inst_def, exec_pure1_def, exec_pure2_def, exec_pure3_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), update_var_def]
QED

Theorem bop_scalar_ptr_inst_ok:
  MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
           LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
           SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN] /\
  EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) ops /\
  step_inst_base (mk_inst id opc ops [tmp]) s = OK u /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops [tmp]) s
Proof
  strip_tac >>
  drule_all bop_scalar_state_frame >> strip_tac >>
  `u.vs_requests = s.vs_requests` by
    (qpat_x_assum `(u with vs_vars := _) = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `!f. step_inst f ctx (mk_inst id opc ops [tmp]) s = OK u` by
    (gvs[MEM, mk_inst_def, step_inst_non_invoke]) >>
  simp[ptr_inst_ok_def, allocas_from_def] >>
  gvs[MEM, EVERY_CONJ] >>
  simp[access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  rpt strip_tac >> gvs[EVERY_DEF, EVERY_MEM]
  >>~- ([`~MEM a ops \/ op_taint tn a = {}`],
    qpat_x_assum `!a. MEM a ops ==> op_taint tn a = {}`
      (qspec_then `a` mp_tac) >> simp[GSYM IMP_DISJ_THM]) >>
  rename1 `step_inst_base (mk_inst id opc [Var a; Var b] [tmp]) s = OK u` >>
  qpat_assum `!op. _ ==> op_prov G op = NONE`
    (qspec_then `Var a` mp_tac) >>
  qpat_x_assum `!op. _ ==> op_prov G op = NONE`
    (qspec_then `Var b` mp_tac) >>
  simp[op_prov_def, FLOOKUP_DEF]
QED

Theorem first_prov_none:
  !ops. EVERY (\op. op_prov G op = NONE) ops ==>
    first_prov G ops = NONE
Proof
  Induct >> simp[first_prov_def]
QED

Theorem bop_scalar_out_prov:
  MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
           LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
           SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN] /\
  EVERY (\op. op_prov G op = NONE) ops ==>
  out_prov PG G (mk_inst id opc ops outs) u = NONE
Proof
  strip_tac >> drule first_prov_none >> strip_tac >>
  gvs[MEM, out_prov_def, mk_inst_def]
QED

Theorem bop_scalar_out_taint:
  MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
           LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
           SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN] /\
  EVERY (\op. op_taint tn op = {}) ops ==>
  out_taint tn (mk_inst id opc ops outs) s = {}
Proof
  strip_tac >> gvs[MEM] >>
  (namedCases_on `ops` ["", "a rest"]
  >- simp[out_taint_def, mk_inst_def] >>
  namedCases_on `rest` ["", "b more"]
  >- (Cases_on `eval_operand a s` >> gvs[out_taint_def, mk_inst_def]) >>
  namedCases_on `more` ["", "c tail"]
  >- (Cases_on `eval_operand a s` >>
      gvs[out_taint_def, mk_inst_def, shift_taint_def] >> gvs[EXTENSION]) >>
  Cases_on `tail` >> simp[out_taint_def, mk_inst_def])
QED

Theorem bop_scalar_ghost_frame:
  MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
           LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
           SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN] /\
  EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) ops /\
  u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp ==>
  op_prov (step_prov PG G (mk_inst id opc ops [tmp]) u) (Var tmp) = NONE /\
  op_taint (step_taint (mk_inst id opc ops [tmp]) s u tn) (Var tmp) = {} /\
  (step_taint (mk_inst id opc ops [tmp]) s u tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id opc ops [tmp]) s u tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc ops [tmp]) s u tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id opc ops [tmp]) s u tn).t_imm = tn.t_imm /\
  (!x. x <> tmp ==>
    FLOOKUP (step_prov PG G (mk_inst id opc ops [tmp]) u) x = FLOOKUP G x /\
    FLOOKUP (step_taint (mk_inst id opc ops [tmp]) s u tn).t_var x =
      FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  `out_taint tn (mk_inst id opc ops [tmp]) s = {}` by
    (irule bop_scalar_out_taint >> fs[EVERY_CONJ]) >>
  `out_prov PG G (mk_inst id opc ops [tmp]) u = NONE` by
    (irule bop_scalar_out_prov >> fs[EVERY_CONJ]) >>
  simp[op_prov_def, step_prov_def, set_prov_def,
       op_taint_def, step_taint_def, set_var_taint_def,
       mk_inst_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  gvs[MEM] >>
  simp[mem_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       new_site_bytes_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, range_bytes_def, mk_inst_def,
       FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  namedCases_on `ops` ["", "a rest"] >>
  gvs[] >>
  namedCases_on `rest` ["", "b more"] >>
  gvs[] >>
  namedCases_on `more` ["", "c tail"] >>
  gvs[] >> Cases_on `tail` >> gvs[]
QED

Theorem bop_scalar_ptr_edge:
  MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
           LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
           SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN] /\
  EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) ops /\
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
    (irule bop_scalar_ptr_inst_ok >> simp[]) >>
  `(mk_inst id opc ops [tmp]).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst id opc ops [tmp]).inst_opcode` by
    (gvs[MEM, mk_inst_def, is_terminator_def]) >>
  drule_all straight_line_ptr_edge >> gvs[MEM, mk_inst_def]
QED
