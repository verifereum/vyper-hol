Theory dftPacketSuccessfulRowBoundary
Ancestors
  dftIndexedExec venomExecProofs venomInstProofs venomExecSemantics
  venomInst venomState finite_map list rich_list
Libs
  stepInstBaseLib

Theorem dft_packet_static_success[local]:
  !inst s u. step_inst fuel C inst s = OK u /\ s.vs_call_ctx.cc_static ==>
    ~MEM inst.inst_opcode [SSTORE; TSTORE; LOG; CREATE; CREATE2]
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  gvs[] >>
  gvs[Once step_inst_def] >>
  with_opcode_clause gvs >>
  gvs[exec_write2_def, AllCaseEqs(), eval_operands_def] >>
  gvs[eval_operand_def] >>
  `2 <= LENGTH (REVERSE rest)` by simp[] >>
  Cases_on `REVERSE rest` >> gvs[] >>
  rename1 `REVERSE rest = op::rs` >>
  Cases_on `rs` >> gvs[] >>
  `IS_SOME (eval_operands (REVERSE rest) s)` by simp[eval_operands_def] >>
  fs[eval_operands_IS_SOME_EVERY, EVERY_REVERSE] >>
  qpat_x_assum `EVERY _ rest` mp_tac >>
  rewrite_tac[GSYM eval_operands_IS_SOME_EVERY] >> simp[]
QED

Theorem dft_packet_codecopy_success_label[local]:
  !inst s u l.
    inst.inst_opcode = CODECOPY /\ step_inst fuel C inst s = OK u /\
    MEM (Label l) inst.inst_operands ==> l IN FDOM s.vs_labels
Proof
  rpt strip_tac >>
  gvs[Once step_inst_def] >>
  with_opcode_clause gvs >>
  gvs[AllCaseEqs()] >>
  gvs[eval_operand_def, FLOOKUP_DEF]
QED

Theorem dft_packet_successful_prefix_applicability:
  !pre s u.
    EVERY (\i. ~is_terminator i.inst_opcode) pre /\
    FOLDR (dft_exec_cons fuel C) OK pre s = OK u ==>
    (s.vs_call_ctx.cc_static ==>
      EVERY (\i. ~MEM i.inst_opcode [SSTORE; TSTORE; LOG; CREATE; CREATE2]) pre) /\
    (!i l. MEM i pre /\ i.inst_opcode = CODECOPY /\
      MEM (Label l) i.inst_operands ==> l IN FDOM s.vs_labels)
Proof
  Induct_on `pre` >- simp[] >>
  rpt gen_tac >> strip_tac >>
  gvs[Once dft_exec_cons_def, AllCaseEqs()] >>
  `t.vs_call_ctx = s.vs_call_ctx` by
    (drule step_inst_ok_preserves_call_ctx >> simp[]) >>
  `t.vs_labels = s.vs_labels` by
    (drule step_inst_preserves_labels_always >> simp[]) >>
  first_x_assum drule >> simp[] >> strip_tac >>
  conj_tac
  >- (strip_tac >> drule_all dft_packet_static_success >> simp[]) >>
  rpt strip_tac >> gvs[] >> metis_tac[dft_packet_codecopy_success_label]
QED
