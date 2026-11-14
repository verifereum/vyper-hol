Theory staticShadowForbidden
Ancestors
  staticShadowDefs venomExecSemantics venomState venomInst list rich_list
Libs
  stepInstBaseLib

Theorem static_shadow_forbidden_fixed[local]:
  MEM inst.inst_opcode [SELFDESTRUCT; CREATE; CREATE2] /\
  s.vs_call_ctx.cc_static ==>
  static_shadow_result_rel (step_inst_base inst s) r
Proof
  strip_tac >>
  Cases_on `IS_SOME (eval_operands inst.inst_operands s)`
  >- (fs[] >> with_opcode_clause simp >> simp[static_shadow_result_rel_def]) >>
  fs[] >> with_opcode_clause simp >>
  namedCases_on `inst.inst_operands` ["", "a rest"] >> gvs[static_shadow_result_rel_def, eval_operands_def, AllCaseEqs()] >>
  namedCases_on `rest` ["", "b more"] >> gvs[static_shadow_result_rel_def, eval_operands_def, AllCaseEqs()] >>
  namedCases_on `more` ["", "c last"] >> gvs[static_shadow_result_rel_def, eval_operands_def, AllCaseEqs()] >>
  namedCases_on `last` ["", "d tail"] >> gvs[static_shadow_result_rel_def, eval_operands_def, AllCaseEqs()] >>
  Cases_on `tail` >> simp[static_shadow_result_rel_def] >>
  gvs[eval_operands_def, AllCaseEqs()] >> simp[static_shadow_result_rel_def]
QED

Theorem static_shadow_eval_prefix2[local]:
  2 <= LENGTH ops /\ IS_SOME (eval_operand (EL 0 ops) s) /\
  IS_SOME (eval_operand (EL 1 ops) s) /\
  IS_SOME (eval_operands (DROP 2 ops) s) ==>
  IS_SOME (eval_operands ops s)
Proof
  namedCases_on `ops` ["", "a rest"] >> simp[] >>
  namedCases_on `rest` ["", "b tail"] >>
  simp[eval_operands_IS_SOME_EVERY]
QED

Theorem static_shadow_log[local]:
  inst.inst_opcode = LOG /\ s.vs_call_ctx.cc_static ==>
  static_shadow_result_rel (step_inst_base inst s) r
Proof
  strip_tac >>
  Cases_on `IS_SOME (eval_operands inst.inst_operands s)`
  >- (with_opcode_clause simp >> simp[static_shadow_result_rel_def]) >>
  with_opcode_clause simp >>
  namedCases_on `inst.inst_operands` ["", "a rest"] >> simp[static_shadow_result_rel_def] >>
  Cases_on `a` >> simp[static_shadow_result_rel_def] >>
  IF_CASES_TAC >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operand (HD (REVERSE rest)) s` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operand (EL 1 (REVERSE rest)) s` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_operands (DROP 2 (REVERSE rest)) s` >> simp[static_shadow_result_rel_def] >>
  `IS_SOME (eval_operands (REVERSE rest) s)` by
    (irule static_shadow_eval_prefix2 >> simp[] >> gvs[]) >>
  `IS_SOME (eval_operands (Lit c::rest) s)` by
    fs[eval_operands_IS_SOME_EVERY, EVERY_REVERSE, eval_operand_def] >>
  gvs[]
QED

Theorem static_shadow_forbidden:
  MEM inst.inst_opcode [LOG; SELFDESTRUCT; CREATE; CREATE2] /\
  s.vs_call_ctx.cc_static ==>
  static_shadow_result_rel (step_inst_base inst s) r
Proof
  strip_tac >> fs[] >>
  FIRST [irule static_shadow_log >> simp[] >> NO_TAC,
         irule static_shadow_forbidden_fixed >> simp[] >> NO_TAC]
QED
