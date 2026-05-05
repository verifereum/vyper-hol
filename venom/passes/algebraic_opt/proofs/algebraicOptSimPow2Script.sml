(*
 * Algebraic Optimization — Power-of-Two & OR Simulation Helpers
 *
 * TOP-LEVEL:
 *   ao_mul_sim  — MUL case of ao_opt_muldiv
 *   ao_div_sim  — Div case of ao_opt_muldiv
 *   ao_mod_sim  — Mod case of ao_opt_muldiv
 *   ao_or_sim   — OR case of ao_opt_or (truthy case disabled)
 *)
Theory algebraicOptSimPow2
Ancestors
  algebraicOptDefs algebraicOptRules algebraicOptRules2
  venomExecSemantics venomState passSharedDefs passSharedPow2
Libs
  pairLib BasicProvers

(* ===== Per-opcode step_inst_base dispatch ===== *)

Triviality step_mul[local]:
  !inst s. inst.inst_opcode = MUL ==>
    step_inst_base inst s = exec_pure2 $* inst s
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

Triviality step_div[local]:
  !inst s. inst.inst_opcode = Div ==>
    step_inst_base inst s = exec_pure2 safe_div inst s
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

Triviality step_mod[local]:
  !inst s. inst.inst_opcode = Mod ==>
    step_inst_base inst s = exec_pure2 safe_mod inst s
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

Triviality step_or[local]:
  !inst s. inst.inst_opcode = OR ==>
    step_inst_base inst s = exec_pure2 word_or inst s
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

Triviality neg1_is_max[local]:
  (0w : 'a word) - 1w = UINT_MAXw
Proof
  rewrite_tac[GSYM wordsTheory.WORD_NOT_0] >>
  simp[wordsTheory.WORD_NOT, wordsTheory.word_sub_def, wordsTheory.WORD_NEG_0]
QED

(* ===== MUL simulation ===== *)

Theorem ao_mul_sim:
  !inst0 s.
    inst0.inst_opcode = MUL /\
    LENGTH inst0.inst_operands = 2 /\
    LENGTH inst0.inst_outputs = 1 ==>
    step_inst_base (HD (ao_opt_muldiv inst0)) s = step_inst_base inst0 s \/
    ?e. step_inst_base inst0 s = Error e
Proof
  rpt strip_tac >>
  `?op1 op2. inst0.inst_operands = [op1; op2]` by
    (Cases_on `inst0.inst_operands` >> gvs[] >>
     Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[]) >>
  `?out. inst0.inst_outputs = [out]` by
    (Cases_on `inst0.inst_outputs` >> gvs[]) >>
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[ao_opt_muldiv_def, LET_THM, lit_eq_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (simp[] >> NO_TAC) >>
  TRY (
    DISJ1_TAC >>
    drule is_power_of_two_exp >> strip_tac >>
    irule ao_rule_mul_pow2 >> simp[] >>
    qexists_tac `k` >> simp[] >> NO_TAC) >>
  simp[step_mul, exec_pure2_def, eval_operand_def,
       wordsTheory.WORD_MULT_CLAUSES] >>
  simp[Once step_inst_base_def, eval_operand_def] >>
  every_case_tac >> gvs[wordsTheory.WORD_MULT_CLAUSES]
QED

(* ===== Div simulation ===== *)

Theorem ao_div_sim:
  !inst0 s.
    inst0.inst_opcode = Div /\
    LENGTH inst0.inst_operands = 2 /\
    LENGTH inst0.inst_outputs = 1 ==>
    step_inst_base (HD (ao_opt_muldiv inst0)) s = step_inst_base inst0 s \/
    ?e. step_inst_base inst0 s = Error e
Proof
  rpt strip_tac >>
  `?op1 op2. inst0.inst_operands = [op1; op2]` by
    (Cases_on `inst0.inst_operands` >> gvs[] >>
     Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[]) >>
  `?out. inst0.inst_outputs = [out]` by
    (Cases_on `inst0.inst_outputs` >> gvs[]) >>
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[ao_opt_muldiv_def, LET_THM, lit_eq_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (simp[] >> NO_TAC) >>
  TRY (
    DISJ1_TAC >>
    drule is_power_of_two_exp >> strip_tac >>
    irule ao_rule_div_pow2 >> simp[] >>
    qexists_tac `k` >> simp[] >> NO_TAC) >>
  simp[step_div, exec_pure2_def, eval_operand_def,
       safe_div_def, wordsTheory.word_div_1,
       wordsTheory.word_div_def, arithmeticTheory.ZERO_DIV] >>
  simp[Once step_inst_base_def, eval_operand_def] >>
  every_case_tac >>
  gvs[safe_div_def, wordsTheory.word_div_1,
      wordsTheory.word_div_def, arithmeticTheory.ZERO_DIV]
QED

(* ===== Mod simulation ===== *)

Theorem ao_mod_sim:
  !inst0 s.
    inst0.inst_opcode = Mod /\
    LENGTH inst0.inst_operands = 2 /\
    LENGTH inst0.inst_outputs = 1 ==>
    step_inst_base (HD (ao_opt_muldiv inst0)) s = step_inst_base inst0 s \/
    ?e. step_inst_base inst0 s = Error e
Proof
  rpt strip_tac >>
  `?op1 op2. inst0.inst_operands = [op1; op2]` by
    (Cases_on `inst0.inst_operands` >> gvs[] >>
     Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[]) >>
  `?out. inst0.inst_outputs = [out]` by
    (Cases_on `inst0.inst_outputs` >> gvs[]) >>
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[ao_opt_muldiv_def, LET_THM, lit_eq_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (simp[] >> NO_TAC) >>
  TRY (
    DISJ1_TAC >>
    drule is_power_of_two_exp >> strip_tac >>
    irule ao_rule_mod_pow2 >> simp[] >>
    qexists_tac `k` >> simp[] >> NO_TAC) >>
  simp[step_mod, exec_pure2_def, eval_operand_def,
       safe_mod_def, wordsTheory.WORD_MOD_1,
       wordsTheory.word_mod_def, arithmeticTheory.ZERO_MOD] >>
  simp[Once step_inst_base_def, eval_operand_def] >>
  every_case_tac >>
  gvs[safe_mod_def, wordsTheory.WORD_MOD_1,
      wordsTheory.word_mod_def, arithmeticTheory.ZERO_MOD]
QED

(* ===== OR simulation ===== *)

Theorem ao_or_sim:
  !dfg inst0 s.
    inst0.inst_opcode = OR /\
    LENGTH inst0.inst_operands = 2 /\
    LENGTH inst0.inst_outputs = 1 ==>
    step_inst_base (HD (ao_opt_or dfg inst0)) s = step_inst_base inst0 s \/
    ?e. step_inst_base inst0 s = Error e
Proof
  rpt strip_tac >>
  `?op1 op2. inst0.inst_operands = [op1; op2]` by
    (Cases_on `inst0.inst_operands` >> gvs[] >>
     Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[]) >>
  `?out. inst0.inst_outputs = [out]` by
    (Cases_on `inst0.inst_outputs` >> gvs[]) >>
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[ao_opt_or_def, lit_eq_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (simp[] >> NO_TAC) >>
  simp[step_or, exec_pure2_def, eval_operand_def,
       neg1_is_max, wordsTheory.WORD_OR_CLAUSES] >>
  simp[Once step_inst_base_def, eval_operand_def] >>
  every_case_tac >> gvs[neg1_is_max, wordsTheory.WORD_OR_CLAUSES]
QED

val _ = export_theory();
