Theory algebraicOptLocalProofs
Ancestors
  algebraicOptDefs venomExecSemantics venomState stateFrame

(* Successful source evaluation supplies the definedness needed when an
   identity drops an operand. *)
Theorem ao_opt_shift_correct:
  !inst s t out.
    (inst.inst_opcode = SHL \/ inst.inst_opcode = SHR \/
     inst.inst_opcode = SAR) /\
    step_inst_base inst s = OK t /\
    MEM out (ao_opt_shift inst) ==>
    step_inst_base out s = OK t
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[ao_opt_shift_def] >>
  rename1 `inst.inst_operands = a::rest` >>
  Cases_on `rest` >> gvs[ao_opt_shift_def] >>
  rename1 `inst.inst_operands = a::b::tail` >>
  Cases_on `tail` >> gvs[ao_opt_shift_def] >>
  Cases_on `a` >>
  gvs[passSharedDefsTheory.lit_eq_def] >>
  Cases_on `c = 0w` >> gvs[] >>
  Cases_on `inst` >> gvs[] >>
  qpat_x_assum `step_inst_base _ s = OK t` mp_tac >>
  asm_simp_tac (srw_ss()) [Once step_inst_base_def] >>
  gvs[exec_pure2_def, exec_pure1_def, eval_operand_def,
      AllCaseEqs()] >> strip_tac >>
  asm_simp_tac (srw_ss()) [Once step_inst_base_def] >>
  gvs[exec_pure1_def, wordsTheory.SHIFT_ZERO]
QED


val local_opcode_eqs = List.filter
  (fn th => let val opc = rhs (fst (dest_imp (concl (SPEC_ALL th))))
            in aconv opc ``AND`` orelse aconv opc ``ASSIGN`` end)
  (CONJUNCTS step_inst_base_opcode_eqs);

Theorem ao_opt_and_correct:
  !inst s t out.
    inst.inst_opcode = AND /\ step_inst_base inst s = OK t /\
    MEM out (ao_opt_and inst) ==>
    step_inst_base out s = OK t
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[ao_opt_and_def] >>
  rename1 `inst.inst_operands = a::rest` >>
  Cases_on `rest` >> gvs[ao_opt_and_def] >>
  rename1 `inst.inst_operands = a::b::tail` >>
  Cases_on `tail` >> gvs[ao_opt_and_def] >>
  Cases_on `lit_eq b (0w - 1w)` >> gvs[] >>
  Cases_on `lit_eq a 0w \/ lit_eq b 0w` >> gvs[] >>
  gvs local_opcode_eqs >>
  gvs[exec_pure2_def, AllCaseEqs()] >>
  gvs[passSharedDefsTheory.lit_eq_def, AllCaseEqs()] >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[eval_operand_def, exec_pure1_def,
      wordsTheory.WORD_AND_CLAUSES, wordsTheory.WORD_NEG_1,
      wordsTheory.WORD_SUB_LZERO,
      wordsTheory.WORD_EQ_SUB_ZERO]
QED
