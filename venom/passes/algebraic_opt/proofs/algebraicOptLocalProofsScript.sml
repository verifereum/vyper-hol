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


fun local_opcode_eqs opcs = List.filter
  (fn th => let val opc = rhs (fst (dest_imp (concl (SPEC_ALL th))))
            in List.exists (aconv opc) opcs end)
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
  gvs (local_opcode_eqs [``AND``, ``ASSIGN``]) >>
  gvs[exec_pure2_def, AllCaseEqs()] >>
  gvs[passSharedDefsTheory.lit_eq_def, AllCaseEqs()] >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[eval_operand_def] >>
  gvs[exec_pure1_def,
      wordsTheory.WORD_AND_CLAUSES, wordsTheory.WORD_NEG_1,
      wordsTheory.WORD_SUB_LZERO,
      wordsTheory.WORD_EQ_SUB_ZERO]
QED

Theorem ao_opt_addsub_correct:
  !inst s t out.
    (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
     inst.inst_opcode = XOR) /\
    step_inst_base inst s = OK t /\ MEM out (ao_opt_addsub inst) ==>
    step_inst_base out s = OK t
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[ao_opt_addsub_def] >>
  rename1 `inst.inst_operands = a::rest` >>
  Cases_on `rest` >> gvs[ao_opt_addsub_def] >>
  rename1 `inst.inst_operands = a::b::tail` >>
  Cases_on `tail` >> gvs[ao_opt_addsub_def] >>
  gvs[AllCaseEqs()] >>
  gvs (local_opcode_eqs [``ADD``, ``SUB``, ``XOR``, ``ASSIGN``, ``NOT``]) >>
  gvs[exec_pure2_def, AllCaseEqs()] >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[passSharedDefsTheory.lit_eq_def, eval_operand_def, AllCaseEqs()] >>
  cheat >>
  gvs (local_opcode_eqs [``ADD``, ``SUB``, ``XOR``, ``ASSIGN``, ``NOT``]) >>
  gvs[exec_pure1_def, eval_operand_def,
      wordsTheory.WORD_SUB_REFL, wordsTheory.WORD_XOR_CLAUSES,
      wordsTheory.WORD_SUB_LZERO, wordsTheory.WORD_NEG_1] >>
  cheat
QED

Theorem ao_opt_exp_correct:
  !inst s t out.
    inst.inst_opcode = Exp /\ step_inst_base inst s = OK t /\
    MEM out (ao_opt_exp inst) ==> step_inst_base out s = OK t
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[ao_opt_exp_def] >>
  rename1 `inst.inst_operands = a::rest` >>
  Cases_on `rest` >> gvs[ao_opt_exp_def] >>
  rename1 `inst.inst_operands = a::b::tail` >>
  Cases_on `tail` >> gvs[ao_opt_exp_def] >>
  Cases_on `lit_eq b 0w` >> gvs[] >>
  Cases_on `lit_eq b 1w` >> gvs[] >>
  Cases_on `lit_eq a 1w` >> gvs[] >>
  Cases_on `lit_eq a 0w` >> gvs[] >>
  gvs (local_opcode_eqs [``Exp``, ``ASSIGN``, ``ISZERO``]) >>
  gvs[exec_pure2_def, AllCaseEqs()] >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[passSharedDefsTheory.lit_eq_def, eval_operand_def, AllCaseEqs()] >>
  gvs[exec_pure1_def, eval_operand_def, wordsTheory.word_exp_def,
      arithmeticTheory.ZERO_EXP, bool_to_word_def,
      wordsTheory.w2n_eq_0] >>
  Cases_on `v2 = 0w` >> gvs[bool_to_word_def]
QED

(* The only permitted inexact result is truthification to one.  Both results
   are writes to the same output over the same original frame. *)
Theorem ao_opt_or_correct:
  !dfg inst s t out.
    inst.inst_opcode = OR /\ step_inst_base inst s = OK t /\
    MEM out (ao_opt_or dfg inst) ==>
    ?x v w. inst.inst_outputs = [x] /\ t = update_var x v s /\
      step_inst_base out s = OK (update_var x w s) /\
      (v = 0w <=> w = 0w) /\
      (w = v \/ (ao_all_truthy dfg inst /\ w = 1w /\ v <> 0w))
Proof
  rpt gen_tac >> strip_tac >>
  gvs (local_opcode_eqs [``OR``]) >>
  gvs[exec_pure2_def, AllCaseEqs()] >>
  rename1 `inst.inst_operands = [a; b]` >>
  Cases_on `lit_eq b (0w - 1w)`
  >- (gvs[ao_opt_or_def] >>
      gvs (local_opcode_eqs [``ASSIGN``]) >>
      Cases_on `b` >>
      gvs[passSharedDefsTheory.lit_eq_def, eval_operand_def] >>
      gvs[exec_pure1_def, eval_operand_def,
          wordsTheory.WORD_SUB_LZERO, wordsTheory.WORD_NEG_1,
          wordsTheory.WORD_OR_CLAUSES] >> metis_tac[]) >>
  Cases_on `ao_all_truthy dfg inst /\ is_lit_op b /\ ~lit_eq b 0w`
  >- (gvs[ao_opt_or_def] >>
      gvs (local_opcode_eqs [``ASSIGN``]) >>
      Cases_on `b` >>
      gvs[passSharedDefsTheory.lit_eq_def, passSharedDefsTheory.is_lit_op_def,
          eval_operand_def] >>
      gvs[exec_pure1_def, eval_operand_def] >>
      `word_or v1 c <> 0w` by
        (strip_tac >>
         qspecl_then [`c`, `v1`] mp_tac wordsTheory.WORD_OR_ABSORB >>
         gvs[wordsTheory.WORD_OR_COMM, wordsTheory.WORD_AND_CLAUSES]) >>
      `(1w : 256 word) <> 0w` by simp[] >>
      qexistsl [`word_or v1 c`, `1w`] >> simp[]) >>
  Cases_on `lit_eq b 0w`
  >- (gvs[ao_opt_or_def] >>
      gvs (local_opcode_eqs [``ASSIGN``]) >>
      Cases_on `b` >>
      gvs[passSharedDefsTheory.lit_eq_def, eval_operand_def] >>
      gvs[exec_pure1_def, wordsTheory.WORD_OR_CLAUSES] >> metis_tac[]) >>
  gvs[ao_opt_or_def] >>
  gvs (local_opcode_eqs [``OR``]) >>
  gvs[exec_pure2_def] >> metis_tac[]
QED
