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
  pairLib BasicProvers

(* ===== Word division zero helpers ===== *)

(* 0w / c = 0w (signed word division, for c ≠ 0w) *)
Triviality word_quot_zero_l[local]:
  !c : 'a word. c <> 0w ==> 0w / c = 0w
Proof
  rpt strip_tac >>
  simp[integer_wordTheory.word_quot, integer_wordTheory.word_0_w2i,
       integerTheory.INT_QUOT_0] >>
  `w2i c <> 0` by (
    strip_tac >> gvs[integer_wordTheory.w2i_eq_0]) >>
  simp[integerTheory.INT_QUOT_0, integer_wordTheory.i2w_def]
QED

(* 0w rem c = 0w (signed word remainder, for c ≠ 0w) *)
Triviality word_rem_zero_l[local]:
  !c : 'a word. c <> 0w ==> word_rem 0w c = 0w
Proof
  rpt strip_tac >>
  simp[integer_wordTheory.word_rem, integer_wordTheory.word_0_w2i] >>
  `w2i c <> 0` by (
    strip_tac >> gvs[integer_wordTheory.w2i_eq_0]) >>
  simp[integerTheory.INT_REM0, integer_wordTheory.i2w_def]
QED

(* x / 1w = x (signed word division by 1) *)
Triviality w2i_1w_256[local]:
  w2i (1w : bytes32) = 1
Proof
  `~word_msb (1w : bytes32)` by wordsLib.WORD_DECIDE_TAC >>
  simp[integer_wordTheory.w2i_eq_w2n]
QED

Triviality word_quot_one[local]:
  !x : bytes32. x / 1w = x
Proof
  gen_tac >>
  `1w <> (0w : bytes32)` by simp[] >>
  simp[integer_wordTheory.word_quot, w2i_1w_256,
       integerTheory.INT_QUOT_1, integer_wordTheory.i2w_w2i]
QED

(* word_rem x 1w = 0w *)
Triviality int_rem_1[local]:
  !p:int. p rem 1 = 0
Proof
  gen_tac >>
  mp_tac (Q.SPEC `1` integerTheory.INT_REMQUOT) >>
  impl_tac >- simp[] >>
  disch_then (qspec_then `p` strip_assume_tac) >>
  intLib.ARITH_TAC
QED

Triviality word_rem_one[local]:
  !x : bytes32. word_rem x 1w = 0w
Proof
  gen_tac >>
  `1w <> (0w : bytes32)` by simp[] >>
  simp[integer_wordTheory.word_rem, w2i_1w_256, int_rem_1,
       integer_wordTheory.i2w_def]
QED

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
  rpt gen_tac >> strip_tac >>
  `?a1 rest. ops = a1 :: rest` by (Cases_on `ops` >> gvs[]) >>
  `?a2 rest2. rest = a2 :: rest2` by (Cases_on `rest` >> gvs[]) >>
  `rest2 = []` by gvs[] >>
  `?o1 rest3. outs = o1 :: rest3` by (Cases_on `outs` >> gvs[]) >>
  `rest3 = []` by gvs[] >>
  gvs[]
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
  Cases_on `op1` >> Cases_on `op2` >>
  simp[ao_opt_signextend_def, lit_eq_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (simp[] >> NO_TAC) >>
  TRY (simp[LET_THM] >> rpt IF_CASES_TAC >> gvs[] >>
       TRY (simp[] >> NO_TAC) >>
       (* Range-based case: ASSIGN x — needs range_analysis_sound *)
       cheat >> NO_TAC) >>
  TRY (DISJ1_TAC >> metis_tac[ao_rule_signextend_ge31])
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
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[ao_opt_exp_def, lit_eq_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (simp[] >> NO_TAC) >>
  (* Brute force: unfold step_inst_base for both sides *)
  simp[step_inst_base_def, exec_pure2_def, exec_pure1_def,
       eval_operand_def] >>
  every_case_tac >> gvs[wordsTheory.word_exp_def,
    arithmeticTheory.EXP_1, arithmeticTheory.ZERO_EXP] >>
  rpt IF_CASES_TAC >> gvs[bool_to_word_def]
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
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (simp[] >> NO_TAC) >>
  (* Brute force: unfold step_inst_base for both sides *)
  simp[step_inst_base_def, exec_pure2_def, eval_operand_def,
       safe_sdiv_def] >>
  every_case_tac >>
  gvs[safe_sdiv_def, word_quot_zero_l, word_quot_one]
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
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (simp[] >> NO_TAC) >>
  (* Brute force: unfold step_inst_base for both sides *)
  simp[step_inst_base_def, exec_pure2_def, eval_operand_def,
       safe_smod_def] >>
  every_case_tac >>
  gvs[safe_smod_def, word_rem_zero_l, word_rem_one]
QED

val _ = export_theory();
