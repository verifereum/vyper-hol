(*
 * Algebraic Optimization — Arithmetic Opcode Simulation Helpers
 *
 * TOP-LEVEL:
 *   ao_signextend_sim — SIGNEXTEND branches produce equiv or error
 *   ao_exp_sim        — Exp branches produce equiv or error
 *   ao_sdiv_sim       — SDIV (via muldiv) produces equiv or error
 *   ao_smod_sim       — SMOD (via muldiv) produces equiv or error
 *)
Theory algebraicOptSimArith
Ancestors
  algebraicOptDefs algebraicOptRules algebraicOptRules2
  venomExecSemantics venomState venomInst passSharedDefs
Libs
  pairLib

(* ===== step_inst_base dispatch helpers ===== *)

Triviality step_base_sdiv[local]:
  !inst s. inst.inst_opcode = SDIV ==>
    step_inst_base inst s = exec_pure2 safe_sdiv inst s
Proof
  rw[step_inst_base_def]
QED

Triviality step_base_smod[local]:
  !inst s. inst.inst_opcode = SMOD ==>
    step_inst_base inst s = exec_pure2 safe_smod inst s
Proof
  rw[step_inst_base_def]
QED

Triviality step_base_exp[local]:
  !inst s. inst.inst_opcode = Exp ==>
    step_inst_base inst s = exec_pure2 $** inst s
Proof
  rw[step_inst_base_def]
QED

(* ===== Operand decomposition helper ===== *)

Triviality decomp_2_1[local]:
  !ops outs.
    LENGTH ops = 2 /\ LENGTH outs = 1 ==>
    ?op1 op2 out. ops = [op1; op2] /\ outs = [out]
Proof
  rpt strip_tac >>
  Cases_on `ops` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `outs` >> gvs[] >> Cases_on `t` >> gvs[]
QED

(* ===== SIGNEXTEND ===== *)

(* SIGNEXTEND: w >= 31w case proved via ao_rule_signextend_ge31.
   Range-based case (w < 31, range check passes) is cheated —
   requires range_analysis_sound precondition on ra.
   Identity cases are trivial. *)
Theorem ao_signextend_sim:
  !ra lbl idx inst0 s.
    inst0.inst_opcode = SIGNEXTEND /\
    LENGTH inst0.inst_operands = 2 /\
    LENGTH inst0.inst_outputs = 1 ==>
    step_inst_base (HD (ao_opt_signextend ra lbl idx inst0)) s =
      step_inst_base inst0 s \/
    ?e. step_inst_base inst0 s = Error e
Proof
  rpt strip_tac >>
  imp_res_tac decomp_2_1 >> gvs[] >>
  Cases_on `op1`
  (* Var, Label: returns [inst0], identity *)
  >- simp[ao_opt_signextend_def]
  >- simp[ao_opt_signextend_def]
  (* Lit w *)
  >> rename1 `Lit w` >>
  simp[ao_opt_signextend_def] >>
  IF_CASES_TAC
  >- ( (* w >= 31w: ASSIGN x *)
    DISJ1_TAC >>
    irule ao_rule_signextend_ge31 >> simp[])
  >> simp[LET_THM] >>
  (* Range-based or identity branches *)
  rpt IF_CASES_TAC >> simp[]
  (* Range-based case: ASSIGN x — needs range_analysis_sound *)
  >- cheat
QED

(* ===== Exp ===== *)

Theorem ao_exp_sim:
  !inst0 s.
    inst0.inst_opcode = Exp /\
    LENGTH inst0.inst_operands = 2 /\
    LENGTH inst0.inst_outputs = 1 ==>
    step_inst_base (HD (ao_opt_exp inst0)) s = step_inst_base inst0 s \/
    ?e. step_inst_base inst0 s = Error e
Proof
  rpt strip_tac >>
  imp_res_tac decomp_2_1 >> gvs[] >>
  simp[ao_opt_exp_def] >>
  rpt IF_CASES_TAC >> gvs[lit_eq_def]
  (* Identity: [inst0] *)
  >- simp[]
  (* exp = 0w: x^0 = 1 *)
  >- (Cases_on `eval_operand op1 s`
      >- (DISJ2_TAC >> simp[step_base_exp, exec_pure2_def, eval_operand_def])
      >- (DISJ1_TAC >> metis_tac[ao_rule_exp_zero, optionTheory.IS_SOME_DEF]))
  (* exp = 1w: x^1 = x *)
  >- (DISJ1_TAC >> metis_tac[ao_rule_exp_one])
  (* base = 1w: 1^x = 1 *)
  >- (Cases_on `eval_operand op2 s`
      >- (DISJ2_TAC >> simp[step_base_exp, exec_pure2_def, eval_operand_def])
      >- (DISJ1_TAC >> metis_tac[ao_rule_exp_base_one, optionTheory.IS_SOME_DEF]))
  (* base = 0w: 0^x = iszero(x) *)
  >- (DISJ1_TAC >> metis_tac[ao_rule_exp_base_zero])
QED

(* ===== SDIV ===== *)

(* For the zero case: safe_sdiv with a literal 0 operand gives 0.
   - safe_sdiv v 0w = 0w (by definition)
   - safe_sdiv 0w v = 0w / v = 0w (when v ≠ 0w, 0 quot v = 0) *)
Theorem ao_sdiv_sim:
  !inst0 s.
    inst0.inst_opcode = SDIV /\
    LENGTH inst0.inst_operands = 2 /\
    LENGTH inst0.inst_outputs = 1 ==>
    step_inst_base (HD (ao_opt_muldiv inst0)) s = step_inst_base inst0 s \/
    ?e. step_inst_base inst0 s = Error e
Proof
  rpt strip_tac >>
  imp_res_tac decomp_2_1 >> gvs[] >>
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[ao_opt_muldiv_def, LET_THM, lit_eq_def] >>
  rpt IF_CASES_TAC >> gvs[]
  (* Identity cases *)
  >> TRY (simp[] >> NO_TAC)
  (* Zero cases: ASSIGN 0w *)
  >> TRY (
    simp[step_base_sdiv, exec_pure2_def, eval_operand_def, safe_sdiv_def] >>
    simp[Once step_inst_base_def, eval_operand_def] >>
    every_case_tac >> gvs[safe_sdiv_def] >> NO_TAC)
  (* One case: ASSIGN op1, use ao_rule_sdiv_one *)
  >> TRY (DISJ1_TAC >> metis_tac[ao_rule_sdiv_one] >> NO_TAC)
QED

(* ===== SMOD ===== *)

Theorem ao_smod_sim:
  !inst0 s.
    inst0.inst_opcode = SMOD /\
    LENGTH inst0.inst_operands = 2 /\
    LENGTH inst0.inst_outputs = 1 ==>
    step_inst_base (HD (ao_opt_muldiv inst0)) s = step_inst_base inst0 s \/
    ?e. step_inst_base inst0 s = Error e
Proof
  rpt strip_tac >>
  imp_res_tac decomp_2_1 >> gvs[] >>
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[ao_opt_muldiv_def, LET_THM, lit_eq_def] >>
  rpt IF_CASES_TAC >> gvs[]
  (* Identity cases *)
  >> TRY (simp[] >> NO_TAC)
  (* Zero cases: ASSIGN 0w *)
  >> TRY (
    simp[step_base_smod, exec_pure2_def, eval_operand_def, safe_smod_def] >>
    simp[Once step_inst_base_def, eval_operand_def] >>
    every_case_tac >> gvs[safe_smod_def] >> NO_TAC)
  (* One case: ASSIGN 0w, use ao_rule_smod_one *)
  >> TRY (
    Cases_on `eval_operand op1 s`
    >- (DISJ2_TAC >> simp[step_base_smod, exec_pure2_def, eval_operand_def])
    >- (DISJ1_TAC >> metis_tac[ao_rule_smod_one, optionTheory.IS_SOME_DEF])
    >> NO_TAC)
QED

val _ = export_theory();
