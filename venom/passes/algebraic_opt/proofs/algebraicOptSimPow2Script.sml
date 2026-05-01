(*
 * Algebraic Optimization — Power-of-Two & OR Simulation Helpers
 *
 * Proves that ao_opt_muldiv (MUL, Div, Mod cases) and ao_opt_or
 * produce replacement instructions with equivalent step_inst_base,
 * or the original instruction errors.
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
  venomExecSemantics venomState passSharedDefs
Libs
  pairLib wordsLib

(* ===== Local helpers ===== *)

(* safe_div with zero first operand always returns 0w *)
Triviality safe_div_zero_l[local]:
  !v : bytes32. safe_div 0w v = 0w
Proof
  gen_tac >> simp[safe_div_def] >>
  Cases_on `v = 0w` >> simp[wordsTheory.word_div_def]
QED

(* safe_mod with zero first operand always returns 0w *)
Triviality safe_mod_zero_l[local]:
  !v : bytes32. safe_mod 0w v = 0w
Proof
  gen_tac >> simp[safe_mod_def] >>
  Cases_on `v = 0w` >> simp[wordsTheory.word_mod_def]
QED

(* 0w - 1w = UINT_MAXw *)
Triviality neg1_is_max[local]:
  (0w : 'a word) - 1w = UINT_MAXw
Proof
  simp[wordsTheory.word_sub_def, wordsTheory.WORD_NEG_1,
       wordsTheory.WORD_ADD_0]
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
    (Cases_on `inst0.inst_outputs` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[ao_opt_muldiv_def, LET_THM, lit_eq_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (simp[] >> NO_TAC) >>
  (* Power-of-two case: use bridge + rule *)
  TRY (
    DISJ1_TAC >>
    drule is_power_of_two_exp >> strip_tac >>
    irule ao_rule_mul_pow2 >> simp[] >>
    qexists_tac `k` >> simp[] >> NO_TAC) >>
  (* Zero/one cases: direct computation *)
  simp[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
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
    (Cases_on `inst0.inst_outputs` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[ao_opt_muldiv_def, LET_THM, lit_eq_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (simp[] >> NO_TAC) >>
  (* Power-of-two case *)
  TRY (
    DISJ1_TAC >>
    drule is_power_of_two_exp >> strip_tac >>
    irule ao_rule_div_pow2 >> simp[] >>
    qexists_tac `k` >> simp[] >> NO_TAC) >>
  (* Zero/one cases *)
  simp[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  every_case_tac >>
  gvs[safe_div_def, safe_div_zero_l, wordsTheory.word_div_1]
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
    (Cases_on `inst0.inst_outputs` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[ao_opt_muldiv_def, LET_THM, lit_eq_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (simp[] >> NO_TAC) >>
  (* Power-of-two case *)
  TRY (
    DISJ1_TAC >>
    drule is_power_of_two_exp >> strip_tac >>
    irule ao_rule_mod_pow2 >> simp[] >>
    qexists_tac `k` >> simp[] >> NO_TAC) >>
  (* Zero/one cases *)
  simp[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  every_case_tac >>
  gvs[safe_mod_def, safe_mod_zero_l, wordsTheory.WORD_MOD_1]
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
    (Cases_on `inst0.inst_outputs` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[ao_opt_or_def, lit_eq_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (simp[] >> NO_TAC) >>
  simp[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  every_case_tac >>
  gvs[neg1_is_max, wordsTheory.WORD_OR_CLAUSES]
QED

val _ = export_theory();
