Theory lowerDloadPureEffects
Ancestors
  ptrDiscipline venomExecSemantics venomState memLocDefs venomInst
  finite_map list pred_set codegenRel

Theorem ld_pure_update:
  MEM i.inst_opcode [ADD;SUB;EQ;LT;GT;MUL;Div;Mod;SDIV;SMOD;Exp;
    ADDMOD;MULMOD;SLT;SGT;ISZERO;AND;OR;XOR;NOT] /\
  i.inst_outputs = [out] /\ step_inst fuel C i s = OK s' ==>
  ?w. s' = update_var out w s
Proof
  strip_tac >>
  qpat_x_assum `step_inst fuel C i s = OK s'` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
  simp[MEM] >> strip_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  qpat_assum `i.inst_opcode = _` (fn th => pure_rewrite_tac[th]) >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def, SimpLHS] >>
  strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_pure_taint_nonvar:
  MEM i.inst_opcode [ADD;SUB;EQ;LT;GT;MUL;Div;Mod;SDIV;SMOD;Exp;
    ADDMOD;MULMOD;SLT;SGT;ISZERO;AND;OR;XOR;NOT] /\
  i.inst_outputs = [out] /\ step_inst fuel C i s = OK s' ==>
  (step_taint i s s' tn).t_mem = tn.t_mem /\
  (step_taint i s s' tn).t_stor = tn.t_stor /\
  (step_taint i s s' tn).t_trans = tn.t_trans /\
  (step_taint i s s' tn).t_imm = tn.t_imm
Proof
  strip_tac >> drule_all ld_pure_update >> strip_tac >> gvs[] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
    written_taint_def, step_writes_def, source_memory_write_ranges_def,
    store_taint_def, imm_taint_def, adopt_reset_def, update_var_def,
    range_bytes_def, EXTENSION, FLOOKUP_DEF] >>
  simp[SF CONJ_ss] >>
  namedCases_on `i.inst_operands` ["", "a ops1"] >> simp[] >>
  namedCases_on `ops1` ["", "b ops2"] >> simp[] >>
  namedCases_on `ops2` ["", "c ops3"] >> simp[] >>
  Cases_on `ops3` >> simp[]
QED
