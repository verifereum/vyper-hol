(* Scalar instructions for checked range initialization.  ASSIGN needs
   absent operand provenance: cleanliness alone does not clear provenance. *)
Theory forPtrCheckedScalar
Ancestors
  forPtrAdmin exprSendPtr stmtAppendStorageRunPtr ptrDiscipline ptrSafeRun
  fragGasSeqPtr fragGasPathPtr codegenRel contextCodegenRel venomExecSemantics
  venomInst venomState finite_map pred_set list

Theorem for_checked_clean_implication[local]:
  (!x. MEM x ops ==> op_taint tn x = {}) ==>
  (!x. ~MEM x ops \/ op_taint tn x = {})
Proof
  rewrite_tac[GSYM IMP_DISJ_THM] >> strip_tac >> first_assum ACCEPT_TAC
QED

Theorem for_checked_scalar_inst_ok:
  MEM opc [ASSIGN; SUB; SGT; GT; ISZERO; ADD] /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id opc ops [out]) s = OK u /\
  u.vs_requests = s.vs_requests ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops [out]) s
Proof
  strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  fs[GSYM IMP_DISJ_THM] >> rpt strip_tac >> gvs[] >>
  first_assum (qspec_then `Var u'` mp_tac) >>
  first_x_assum (qspec_then `Var w` mp_tac) >>
  simp[op_prov_def, FLOOKUP_DEF]
QED

Theorem for_checked_scalar_path_ptr:
  MEM opc [ASSIGN; SUB; SGT; GT; ISZERO; ADD] /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) /\
  step_inst_base (mk_inst id opc ops [out]) s = OK u /\
  u.vs_requests = s.vs_requests ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc ops [out]) u)
    (step_taint (mk_inst id opc ops [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops [out]) s` by
    (irule for_checked_scalar_inst_ok >> simp[]) >>
  irule straight_line_zero_path_ptr >>
  gvs[] >> simp[GSYM mk_inst_def, is_terminator_def]
QED


Theorem for_checked_scalar_out_taint:
  MEM opc [ASSIGN; SUB; SGT; GT; ISZERO; ADD] /\
  (!op. MEM op ops ==> op_taint tn op = {}) ==>
  out_taint tn (mk_inst id opc ops outs) s = {}
Proof
  strip_tac >>
  namedCases_on `ops` ["", "a rest"]
  >- simp[out_taint_def, mk_inst_def] >>
  namedCases_on `rest` ["", "b more"]
  >- (Cases_on `eval_operand a s` >>
      gvs[out_taint_def, mk_inst_def]) >>
  namedCases_on `more` ["", "c tail"]
  >- (Cases_on `eval_operand a s` >>
      gvs[out_taint_def, mk_inst_def]) >>
  Cases_on `tail` >> simp[out_taint_def, mk_inst_def]
QED

Theorem for_checked_scalar_step_prov:
  MEM opc [ASSIGN; SUB; SGT; GT; ISZERO; ADD] /\
  (!op. MEM op ops ==> op_prov G op = NONE) ==>
  step_prov PG G (mk_inst id opc ops [out]) u = DRESTRICT G (COMPL {out})
Proof
  strip_tac >>
  `first_prov G ops = NONE` by
    simp[bodyPtrDefsTheory.first_prov_eq_none, EVERY_MEM] >>
  gvs[step_prov_def, out_prov_def, set_prov_def, mk_inst_def]
QED

Theorem for_checked_scalar_step_taint:
  MEM opc [ASSIGN; SUB; SGT; GT; ISZERO; ADD] /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  new_site_bytes s u = {} ==>
  step_taint (mk_inst id opc ops [out]) s u tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >>
  `out_taint tn (mk_inst id opc ops [out]) s = {}` by
    (irule for_checked_scalar_out_taint >> simp[]) >>
  `written_taint tn (mk_inst id opc ops [out]) s = {}` by
    (namedCases_on `ops` ["", "a rest"]
     >- simp[written_taint_def, mk_inst_def] >>
     namedCases_on `rest` ["", "b more"]
     >- simp[written_taint_def, mk_inst_def] >>
     namedCases_on `more` ["", "c tail"]
     >- gvs[written_taint_def, mk_inst_def] >>
     Cases_on `tail` >> gvs[written_taint_def, mk_inst_def]) >>
  simp[step_taint_def, set_var_taint_def] >>
  gvs[mk_inst_def, mem_taint_def, step_writes_def,
      source_memory_write_ranges_def, store_taint_def, adopt_reset_def,
      imm_taint_def, range_bytes_def, taint_component_equality]
QED

Theorem for_checked_scalar_clean_path_ptr:
  MEM opc [ASSIGN; SUB; SGT; GT; ISZERO; ADD] /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) /\
  step_inst_base (mk_inst id opc ops [out]) s = OK u /\
  u.vs_requests = s.vs_requests /\ new_site_bytes s u = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  drule_all for_checked_scalar_path_ptr >>
  `step_prov PG G (mk_inst id opc ops [out]) u = DRESTRICT G (COMPL {out})` by
    (irule for_checked_scalar_step_prov >> simp[]) >>
  `step_taint (mk_inst id opc ops [out]) s u tn =
     tn with t_var := tn.t_var |+ (out,{})` by
    (irule for_checked_scalar_step_taint >> simp[]) >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[]
QED
