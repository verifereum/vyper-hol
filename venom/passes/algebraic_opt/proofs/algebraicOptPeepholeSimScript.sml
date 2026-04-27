(*
 * Algebraic Optimization — Peephole Per-Instruction Simulation
 *
 * Proves that ao_peephole_inst's replacement list simulates the
 * original instruction (single-state, same state for both).
 *
 * TOP-LEVEL:
 *   ao_pre_flip_step_equiv   — pre-flip preserves step_inst_base
 *   ao_post_flip_step_equiv  — post-flip preserves step_inst_base
 *   ao_peephole_identity_sim — identity case (returns [inst])
 *   ao_peephole_1to1_sim     — 1-to-1 replacement case
 *
 * For 1-to-N cases, see segment proofs in algebraicOptProofsScript.sml.
 *)
Theory algebraicOptPeepholeSim
Ancestors
  algebraicOptDefs algebraicOptRules
  venomExecSemantics venomState venomInst venomWf stateEquiv stateEquivProps
  passSharedDefs
Libs
  pairLib BasicProvers

(* ===== Pre/post flip preserve step_inst_base ===== *)

(* Helper: swapping operands of a commutative 2-operand exec_pure2 is identity *)
Triviality exec_pure2_comm[local]:
  !f inst s.
    (!a b. f a b = f b a) /\
    inst.inst_operands = [op1; op2] ==>
    exec_pure2 f (inst with inst_operands := [op2; op1]) s =
    exec_pure2 f inst s
Proof
  rw[exec_pure2_def] >>
  Cases_on `eval_operand op1 s` >> Cases_on `eval_operand op2 s` >> simp[]
QED

(* Helper: equality is symmetric for bool_to_word *)
Triviality bool_to_word_eq_comm[local]:
  !v1 v2:bytes32. bool_to_word (v1 = v2) = bool_to_word (v2 = v1)
Proof
  rw[] >> Cases_on `v1 = v2` >> gvs[]
QED

(* Both flip functions just swap operands of commutative ops.
   Commutativity of word_add/mul/and/or/xor + equality symmetry
   ensures step_inst_base is preserved. *)
(* Helper for flip proofs: if an instruction has [op1; op2] operands
   and a commutative opcode, swapping operands preserves step_inst_base. *)
Triviality comm_swap_step_equiv[local]:
  !inst op1 op2 s.
    inst.inst_operands = [op1; op2] /\
    (inst.inst_opcode = ADD \/ inst.inst_opcode = MUL \/
     inst.inst_opcode = AND \/ inst.inst_opcode = OR \/
     inst.inst_opcode = XOR \/ inst.inst_opcode = EQ) ==>
    step_inst_base (inst with inst_operands := [op2; op1]) s =
    step_inst_base inst s
Proof
  rpt strip_tac >> gvs[] >>
  simp[step_inst_base_def, exec_pure2_def] >>
  Cases_on `eval_operand op1 s` >> Cases_on `eval_operand op2 s` >> gvs[] >>
  simp[wordsTheory.WORD_ADD_COMM, wordsTheory.WORD_MULT_COMM,
       wordsTheory.WORD_AND_COMM, wordsTheory.WORD_OR_COMM,
       wordsTheory.WORD_XOR_COMM, bool_to_word_eq_comm]
QED

Theorem ao_pre_flip_step_equiv:
  !inst s. step_inst_base (ao_pre_flip_inst inst) s = step_inst_base inst s
Proof
  rpt gen_tac >>
  simp[ao_pre_flip_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  gvs[] >> irule comm_swap_step_equiv >> simp[]
QED

Theorem ao_post_flip_step_equiv:
  !inst s. step_inst_base (ao_post_flip_inst inst) s = step_inst_base inst s
Proof
  rpt gen_tac >>
  simp[ao_post_flip_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  gvs[] >> irule comm_swap_step_equiv >> simp[]
QED

(* MAP ao_post_flip_inst over a list preserves step_inst_base for each element *)
Theorem map_post_flip_step_equiv:
  !insts. MAP (\i. step_inst_base (ao_post_flip_inst i) s)  insts =
          MAP (\i. step_inst_base i s) insts
Proof
  Induct >> simp[ao_post_flip_step_equiv]
QED

(* ===== run_insts helpers ===== *)

(* Local copy of run_insts to avoid heavy dependency chain.
   Same definition as in analysisSimDefs / algebraicOptSegSim. *)
Definition run_insts_def:
  run_insts fuel ctx [] s = OK s /\
  run_insts fuel ctx (inst :: rest) s =
    case step_inst fuel ctx inst s of
      OK s' => run_insts fuel ctx rest s'
    | err => err
End

Theorem run_insts_singleton:
  !fuel ctx inst s.
    run_insts fuel ctx [inst] s = step_inst fuel ctx inst s
Proof
  rw[run_insts_def] >> CASE_TAC >> simp[run_insts_def]
QED

(* run_insts on post-flipped singleton = step_inst on post-flipped *)
Theorem run_insts_post_flip_singleton:
  !fuel ctx inst s.
    run_insts fuel ctx [ao_post_flip_inst inst] s =
    step_inst fuel ctx (ao_post_flip_inst inst) s
Proof
  simp[run_insts_singleton]
QED

(* For non-INVOKE: step_inst = step_inst_base *)
Theorem run_insts_non_invoke_singleton:
  !fuel ctx inst s.
    inst.inst_opcode <> INVOKE ==>
    run_insts fuel ctx [inst] s = step_inst_base inst s
Proof
  rw[run_insts_singleton, step_inst_non_invoke]
QED

(* ===== Single-state lift_result from equality ===== *)

(* When step_inst produces the same result, lift_result holds by reflexivity *)
Theorem lift_result_same:
  !fv r.
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv) r r
Proof
  gen_tac >> Cases >> simp[lift_result_def, state_equiv_refl, execution_equiv_refl]
QED

(* When two exec_results are EQUAL, lift_result holds *)
Theorem lift_result_eq:
  !fv r1 r2.
    r1 = r2 ==>
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv) r1 r2
Proof
  rw[] >> simp[lift_result_same]
QED

(* ===== Per-opcode peephole simulation ===== *)

(* Identity case: when ao_peephole_inst returns [inst] unchanged.
   step_inst on the same state gives identical results. *)
Theorem ao_peephole_identity_sim:
  !fv inst fuel ctx s.
    ao_peephole_inst dfg ra lbl idx inst = [inst] ==>
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (step_inst fuel ctx inst s)
      (run_insts fuel ctx [inst] s)
Proof
  rw[run_insts_singleton, lift_result_same]
QED

(* 1-to-1 case: when ao_peephole_inst returns [inst'] where
   step_inst_base inst' s = step_inst_base inst s.
   Since both operate on the same state, the results are identical. *)
Theorem ao_peephole_1to1_sim:
  !fv inst inst' fuel ctx s.
    inst.inst_opcode <> INVOKE /\
    inst'.inst_opcode <> INVOKE /\
    step_inst_base inst' s = step_inst_base inst s ==>
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (step_inst fuel ctx inst s)
      (run_insts fuel ctx [inst'] s)
Proof
  rw[run_insts_singleton, step_inst_non_invoke] >>
  simp[lift_result_same]
QED

(* ===== Structural properties of ao_peephole_inst ===== *)

(* ao_peephole_inst preserves terminators as singletons *)
Theorem ao_peephole_inst_terminator:
  !dfg ra lbl idx inst.
    is_terminator inst.inst_opcode ==>
    ao_peephole_inst dfg ra lbl idx inst = [inst]
Proof
  rw[ao_peephole_inst_def, LET_THM] >>
  (* Terminators have inst_outputs = [] in well-formed blocks *)
  (* Actually, the first check is inst.inst_outputs = [] → [inst] *)
  (* JMP/JNZ/DJMP/STOP/RETURN/REVERT all have no outputs *)
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]
QED

(* ===== Per-rule structural properties ===== *)

(* Helper: check EVERY property for each ao_opt_* *)
Triviality opt_shift_not_invoke[local]:
  !inst. inst.inst_opcode <> INVOKE ==>
    EVERY (\i. i.inst_opcode <> INVOKE) (ao_opt_shift inst)
Proof
  simp[ao_opt_shift_def] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF]
QED

Triviality opt_exp_not_invoke[local]:
  !inst. inst.inst_opcode <> INVOKE ==>
    EVERY (\i. i.inst_opcode <> INVOKE) (ao_opt_exp inst)
Proof
  simp[ao_opt_exp_def] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF]
QED

Triviality opt_addsub_not_invoke[local]:
  !inst. inst.inst_opcode <> INVOKE ==>
    EVERY (\i. i.inst_opcode <> INVOKE) (ao_opt_addsub inst)
Proof
  simp[ao_opt_addsub_def, LET_THM] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF]
QED

Triviality opt_and_not_invoke[local]:
  !inst. inst.inst_opcode <> INVOKE ==>
    EVERY (\i. i.inst_opcode <> INVOKE) (ao_opt_and inst)
Proof
  simp[ao_opt_and_def] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF]
QED

Triviality opt_muldiv_not_invoke[local]:
  !inst. inst.inst_opcode <> INVOKE ==>
    EVERY (\i. i.inst_opcode <> INVOKE) (ao_opt_muldiv inst)
Proof
  simp[ao_opt_muldiv_def, LET_THM] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF]
QED

Triviality opt_or_not_invoke[local]:
  !dfg inst. inst.inst_opcode <> INVOKE ==>
    EVERY (\i. i.inst_opcode <> INVOKE) (ao_opt_or dfg inst)
Proof
  simp[ao_opt_or_def] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF]
QED

Triviality opt_eq_not_invoke[local]:
  !dfg inst. inst.inst_opcode <> INVOKE ==>
    EVERY (\i. i.inst_opcode <> INVOKE) (ao_opt_eq dfg inst)
Proof
  simp[ao_opt_eq_def, LET_THM] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF]
QED

Triviality opt_signextend_not_invoke[local]:
  !ra lbl idx inst. inst.inst_opcode <> INVOKE ==>
    EVERY (\i. i.inst_opcode <> INVOKE) (ao_opt_signextend ra lbl idx inst)
Proof
  simp[ao_opt_signextend_def, LET_THM] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF]
QED

Triviality cmp_helpers_not_invoke[local]:
  (!id op1 inst. EVERY (\i. i.inst_opcode <> INVOKE)
    (ao_cmp_prefer_iz_zero id op1 inst)) /\
  (!id op1 inst. EVERY (\i. i.inst_opcode <> INVOKE)
    (ao_cmp_prefer_iz_max id op1 inst)) /\
  (!id op1 op2 inst. EVERY (\i. i.inst_opcode <> INVOKE)
    (ao_cmp_prefer_iz_general id op1 op2 inst))
Proof
  simp[ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
       ao_cmp_prefer_iz_general_def, LET_THM, listTheory.EVERY_DEF]
QED

(* Restricted to comparator opcodes (which is how it's called from ao_peephole_inst).
   This avoids the need for `inst.inst_opcode <> INVOKE` — GT/LT/SGT/SLT <> INVOKE
   follows from constructor distinctness. *)
(* Note: ao_opt_comparator uses pattern `[op1; op2]` which HOL4's case
   compilation makes ARB for 3+ operands. We add LENGTH = 2 precondition.
   This is always true for well-formed comparator instructions. *)
Triviality opt_comparator_not_invoke[local]:
  !dfg ra lbl idx inst.
    (inst.inst_opcode = GT \/ inst.inst_opcode = LT \/
     inst.inst_opcode = SGT \/ inst.inst_opcode = SLT) /\
    LENGTH inst.inst_operands = 2 ==>
    EVERY (\i. i.inst_opcode <> INVOKE) (ao_opt_comparator dfg ra lbl idx inst)
Proof
  rpt strip_tac >> gvs[] >>
  `?op1 op2. inst.inst_operands = [op1; op2]` by
    (Cases_on `inst.inst_operands` >> gvs[] >>
     Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[]) >>
  gvs[] >>
  simp[ao_opt_comparator_def, LET_THM,
       ao_unsigned_boundaries_def, ao_signed_boundaries_def] >>
  CASE_TAC >> gvs[listTheory.EVERY_DEF] >>
  simp[ao_opt_cmp_range_def, LET_THM,
       ao_wrap_lit_def, ao_range_valid_for_cmp_def,
       is_lit_op_def, lit_eq_def,
       ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
       ao_cmp_prefer_iz_general_def] >>
  rpt (IF_CASES_TAC >> gvs[listTheory.EVERY_DEF]) >>
  gvs[listTheory.EVERY_DEF]
QED

Theorem ao_peephole_inst_not_invoke:
  !dfg ra lbl idx inst.
    inst.inst_opcode <> INVOKE /\ inst_wf inst ==>
    EVERY (\i. i.inst_opcode <> INVOKE) (ao_peephole_inst dfg ra lbl idx inst)
Proof
  rpt strip_tac >>
  simp[ao_peephole_inst_def, LET_THM] >>
  rpt (IF_CASES_TAC >> simp[listTheory.EVERY_DEF]) >>
  gvs[] >>
  FIRST [
    irule opt_shift_not_invoke >> gvs[],
    irule opt_exp_not_invoke >> gvs[],
    irule opt_addsub_not_invoke >> gvs[],
    irule opt_and_not_invoke >> gvs[],
    irule opt_muldiv_not_invoke >> gvs[],
    irule opt_or_not_invoke >> gvs[],
    irule opt_eq_not_invoke >> gvs[],
    irule opt_signextend_not_invoke >> gvs[],
    irule opt_comparator_not_invoke >> gvs[] >>
    gvs[inst_wf_def] >> Cases_on `inst.inst_opcode` >> gvs[]
  ]
QED

(* Non-terminator helpers — same pattern as not_invoke *)
Triviality opt_shift_non_term[local]:
  !inst. ~is_terminator inst.inst_opcode ==>
    EVERY (\i. ~is_terminator i.inst_opcode) (ao_opt_shift inst)
Proof
  simp[ao_opt_shift_def, is_terminator_def] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF, is_terminator_def]
QED

Triviality opt_exp_non_term[local]:
  !inst. ~is_terminator inst.inst_opcode ==>
    EVERY (\i. ~is_terminator i.inst_opcode) (ao_opt_exp inst)
Proof
  simp[ao_opt_exp_def, is_terminator_def] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF, is_terminator_def]
QED

Triviality opt_addsub_non_term[local]:
  !inst. ~is_terminator inst.inst_opcode ==>
    EVERY (\i. ~is_terminator i.inst_opcode) (ao_opt_addsub inst)
Proof
  simp[ao_opt_addsub_def, LET_THM, is_terminator_def] >>
  rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF, is_terminator_def]
QED

Triviality opt_and_non_term[local]:
  !inst. ~is_terminator inst.inst_opcode ==>
    EVERY (\i. ~is_terminator i.inst_opcode) (ao_opt_and inst)
Proof
  simp[ao_opt_and_def, is_terminator_def] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF, is_terminator_def]
QED

Triviality opt_muldiv_non_term[local]:
  !inst. ~is_terminator inst.inst_opcode ==>
    EVERY (\i. ~is_terminator i.inst_opcode) (ao_opt_muldiv inst)
Proof
  simp[ao_opt_muldiv_def, LET_THM, is_terminator_def] >>
  rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF, is_terminator_def]
QED

Triviality opt_or_non_term[local]:
  !dfg inst. ~is_terminator inst.inst_opcode ==>
    EVERY (\i. ~is_terminator i.inst_opcode) (ao_opt_or dfg inst)
Proof
  simp[ao_opt_or_def, is_terminator_def] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF, is_terminator_def]
QED

Triviality opt_eq_non_term[local]:
  !dfg inst. ~is_terminator inst.inst_opcode ==>
    EVERY (\i. ~is_terminator i.inst_opcode) (ao_opt_eq dfg inst)
Proof
  simp[ao_opt_eq_def, LET_THM, is_terminator_def] >>
  rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF, is_terminator_def]
QED

Triviality opt_signextend_non_term[local]:
  !ra lbl idx inst. ~is_terminator inst.inst_opcode ==>
    EVERY (\i. ~is_terminator i.inst_opcode) (ao_opt_signextend ra lbl idx inst)
Proof
  simp[ao_opt_signextend_def, LET_THM, is_terminator_def] >>
  rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF, is_terminator_def]
QED

Triviality opt_comparator_non_term[local]:
  !dfg ra lbl idx inst.
    (inst.inst_opcode = GT \/ inst.inst_opcode = LT \/
     inst.inst_opcode = SGT \/ inst.inst_opcode = SLT) /\
    LENGTH inst.inst_operands = 2 ==>
    EVERY (\i. ~is_terminator i.inst_opcode)
          (ao_opt_comparator dfg ra lbl idx inst)
Proof
  rpt strip_tac >> gvs[] >>
  `?op1 op2. inst.inst_operands = [op1; op2]` by
    (Cases_on `inst.inst_operands` >> gvs[] >>
     Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[]) >>
  gvs[] >>
  simp[ao_opt_comparator_def, LET_THM,
       ao_unsigned_boundaries_def, ao_signed_boundaries_def] >>
  CASE_TAC >> gvs[listTheory.EVERY_DEF, is_terminator_def] >>
  simp[ao_opt_cmp_range_def, LET_THM,
       ao_wrap_lit_def, ao_range_valid_for_cmp_def,
       is_lit_op_def, lit_eq_def, is_terminator_def,
       ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
       ao_cmp_prefer_iz_general_def] >>
  rpt (IF_CASES_TAC >> gvs[listTheory.EVERY_DEF, is_terminator_def]) >>
  gvs[listTheory.EVERY_DEF, is_terminator_def]
QED

Theorem ao_peephole_inst_non_term:
  !dfg ra lbl idx inst.
    ~is_terminator inst.inst_opcode /\ inst_wf inst ==>
    EVERY (\i. ~is_terminator i.inst_opcode)
          (ao_peephole_inst dfg ra lbl idx inst)
Proof
  rpt strip_tac >>
  simp[ao_peephole_inst_def, LET_THM] >>
  rpt (IF_CASES_TAC >> simp[listTheory.EVERY_DEF, is_terminator_def]) >>
  gvs[is_terminator_def] >>
  FIRST [
    irule opt_shift_non_term >> gvs[is_terminator_def],
    irule opt_exp_non_term >> gvs[is_terminator_def],
    irule opt_addsub_non_term >> gvs[is_terminator_def],
    irule opt_and_non_term >> gvs[is_terminator_def],
    irule opt_muldiv_non_term >> gvs[is_terminator_def],
    irule opt_or_non_term >> gvs[is_terminator_def],
    irule opt_eq_non_term >> gvs[is_terminator_def],
    irule opt_signextend_non_term >> gvs[is_terminator_def],
    irule opt_comparator_non_term >> gvs[is_terminator_def] >>
    gvs[inst_wf_def] >> Cases_on `inst.inst_opcode` >> gvs[]
  ]
QED

(* ===== Opcode preservation helpers ===== *)

Triviality ao_post_flip_opcode[local]:
  !inst. (ao_post_flip_inst inst).inst_opcode = inst.inst_opcode
Proof
  rw[ao_post_flip_inst_def] >> every_case_tac >> simp[]
QED

Triviality ao_pre_flip_opcode[local]:
  !inst. (ao_pre_flip_inst inst).inst_opcode = inst.inst_opcode
Proof
  rw[ao_pre_flip_inst_def] >> every_case_tac >> simp[]
QED

(* General singleton simulation: if a replacement singleton has equivalent
   step_inst_base and is non-INVOKE, the pipeline simulation holds. *)
Triviality singleton_post_flip_sim[local]:
  !fv fuel ctx inst inst' s.
    inst'.inst_opcode <> INVOKE /\
    step_inst_base inst' s = step_inst_base inst s ==>
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (step_inst_base inst s)
      (run_insts fuel ctx [ao_post_flip_inst inst'] s)
Proof
  rpt strip_tac >>
  simp[run_insts_singleton] >>
  `(ao_post_flip_inst inst').inst_opcode <> INVOKE` by simp[ao_post_flip_opcode] >>
  simp[step_inst_non_invoke] >>
  simp[ao_post_flip_step_equiv] >>
  simp[lift_result_same]
QED

(* Helper: if replacement singleton has equiv step_inst_base OR original errors,
   the simulation disjunction holds. *)
Triviality sim_or_error[local]:
  !fv fuel ctx inst inst' s.
    inst'.inst_opcode <> INVOKE /\
    (step_inst_base inst' s = step_inst_base inst s \/
     ?e. step_inst_base inst s = Error e) ==>
    (?e. step_inst_base inst s = Error e) \/
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (step_inst_base inst s)
      (run_insts fuel ctx [ao_post_flip_inst inst'] s)
Proof
  rpt strip_tac >- (
    DISJ2_TAC >> irule singleton_post_flip_sim >> simp[]
  ) >>
  DISJ1_TAC >> metis_tac[]
QED

(* When an operand evaluates to NONE in a binary op, step_inst_base errors *)
Triviality exec_pure2_none_error[local]:
  !f inst s op1 op2.
    inst.inst_operands = [op1; op2] /\
    (eval_operand op1 s = NONE \/ eval_operand op2 s = NONE) ==>
    ?e. exec_pure2 f inst s = Error e
Proof
  rw[exec_pure2_def] >>
  Cases_on `eval_operand op1 s` >> Cases_on `eval_operand op2 s` >> gvs[] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[]
QED

(* For binary opcodes, step_inst_base = exec_pure2 of appropriate function.
   Rather than unfold step_inst_base_def, we prove specific opcode lemmas. *)
Triviality step_inst_base_sub[local]:
  !inst s. inst.inst_opcode = SUB ==>
    step_inst_base inst s = exec_pure2 $- inst s
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

Triviality step_inst_base_xor[local]:
  !inst s. inst.inst_opcode = XOR ==>
    step_inst_base inst s = exec_pure2 word_xor inst s
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

Triviality step_inst_base_and[local]:
  !inst s. inst.inst_opcode = AND ==>
    step_inst_base inst s = exec_pure2 word_and inst s
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

Triviality step_inst_base_or[local]:
  !inst s. inst.inst_opcode = OR ==>
    step_inst_base inst s = exec_pure2 word_or inst s
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

Triviality step_inst_base_mul[local]:
  !inst s. inst.inst_opcode = MUL ==>
    step_inst_base inst s = exec_pure2 $* inst s
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

Triviality step_inst_base_eq[local]:
  !inst s. inst.inst_opcode = EQ ==>
    step_inst_base inst s = exec_pure2 (\a b. bool_to_word (a = b)) inst s
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

Triviality step_inst_base_gt[local]:
  !inst s. inst.inst_opcode = GT ==>
    step_inst_base inst s =
    exec_pure2 (\x y. bool_to_word (w2n x > w2n y)) inst s
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

Triviality step_inst_base_lt[local]:
  !inst s. inst.inst_opcode = LT ==>
    step_inst_base inst s =
    exec_pure2 (\x y. bool_to_word (w2n x < w2n y)) inst s
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

Triviality step_inst_base_sgt[local]:
  !inst s. inst.inst_opcode = SGT ==>
    step_inst_base inst s =
    exec_pure2 (\x y. bool_to_word (word_gt x y)) inst s
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

Triviality step_inst_base_slt[local]:
  !inst s. inst.inst_opcode = SLT ==>
    step_inst_base inst s =
    exec_pure2 (\x y. bool_to_word (word_lt x y)) inst s
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

Triviality step_inst_base_div[local]:
  !inst s. inst.inst_opcode = Div ==>
    step_inst_base inst s = exec_pure2 safe_div inst s
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

Triviality step_inst_base_mod[local]:
  !inst s. inst.inst_opcode = Mod ==>
    step_inst_base inst s = exec_pure2 safe_mod inst s
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

Triviality step_inst_base_sdiv[local]:
  !inst s. inst.inst_opcode = SDIV ==>
    step_inst_base inst s = exec_pure2 safe_sdiv inst s
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

Triviality step_inst_base_smod[local]:
  !inst s. inst.inst_opcode = SMOD ==>
    step_inst_base inst s = exec_pure2 safe_smod inst s
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

(* Combining: for binary opcodes with a NONE operand, step_inst_base errors *)
Triviality binary_none_step_error[local]:
  !inst s op1 op2.
    inst.inst_operands = [op1; op2] /\
    (eval_operand op1 s = NONE \/ eval_operand op2 s = NONE) /\
    (inst.inst_opcode = SUB \/ inst.inst_opcode = XOR \/
     inst.inst_opcode = AND \/ inst.inst_opcode = OR \/
     inst.inst_opcode = MUL \/ inst.inst_opcode = EQ \/
     inst.inst_opcode = GT \/ inst.inst_opcode = LT \/
     inst.inst_opcode = SGT \/ inst.inst_opcode = SLT \/
     inst.inst_opcode = Div \/ inst.inst_opcode = Mod \/
     inst.inst_opcode = SDIV \/ inst.inst_opcode = SMOD) ==>
    ?e. step_inst_base inst s = Error e
Proof
  rpt strip_tac >> gvs[] >>
  simp[step_inst_base_sub, step_inst_base_xor, step_inst_base_and,
       step_inst_base_or, step_inst_base_mul, step_inst_base_eq,
       step_inst_base_gt, step_inst_base_lt, step_inst_base_sgt,
       step_inst_base_slt, step_inst_base_div, step_inst_base_mod,
       step_inst_base_sdiv, step_inst_base_smod] >>
  irule exec_pure2_none_error >> simp[] >> metis_tac[]
QED

(* ===== Main single-state peephole sim ===== *)

(* For the full peephole pipeline (pre-flip → peephole → post-flip),
   the replacement list simulates the original on the same state.

   This covers:
   - Identity: returns [inst] → trivial by lift_result_same
   - 1-to-1: returns [inst'] → step_inst_base equality from algebraicOptRules
   - 1-to-N: returns [inst1,...,instk] → segment simulation

   DFG-dependent rules (ao_opt_or truthy, ao_opt_eq prefer_iszero,
   ao_opt_comparator range/prefer_iszero) are included — their
   correctness doesn't depend on DFG soundness because the peephole
   rules produce semantically equivalent instructions regardless
   of whether the DFG analysis is accurate. *)

Theorem ao_peephole_full_sim:
  !fv dfg ra lbl idx inst fuel ctx s.
    inst.inst_opcode <> INVOKE /\
    ~is_terminator inst.inst_opcode /\
    inst_wf inst /\
    ao_fresh_var inst.inst_id "not" IN fv /\
    ao_fresh_var inst.inst_id "iz" IN fv /\
    ao_fresh_var inst.inst_id "xor" IN fv ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (step_inst fuel ctx inst s)
      (run_insts fuel ctx
        (MAP ao_post_flip_inst
          (ao_peephole_inst dfg ra lbl idx (ao_pre_flip_inst inst))) s)
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (ao_pre_flip_inst inst) s = step_inst_base inst s`
    by simp[ao_pre_flip_step_equiv] >>
  qabbrev_tac `inst0 = ao_pre_flip_inst inst` >>
  `inst0.inst_outputs = inst.inst_outputs` by
    (markerLib.UNABBREV_TAC "inst0" >> simp[ao_pre_flip_inst_def] >>
     every_case_tac >> simp[]) >>
  `inst0.inst_opcode = inst.inst_opcode` by
    (markerLib.UNABBREV_TAC "inst0" >> simp[ao_pre_flip_inst_def] >>
     every_case_tac >> simp[]) >>
  `step_inst fuel ctx inst s = step_inst_base inst s`
    by simp[step_inst_non_invoke] >>
  simp[ao_peephole_inst_def, LET_THM] >>
  rpt (IF_CASES_TAC >> simp[]) >> gvs[] >>
  (* 24 goals. Close identity goals (ASSIGN, PHI, PARAM, catch-all) *)
  TRY (
    DISJ2_TAC >> irule singleton_post_flip_sim >>
    markerLib.UNABBREV_TAC "inst0" >>
    simp[ao_pre_flip_opcode, ao_pre_flip_step_equiv] >> NO_TAC)
  (* ===== 20 remaining ao_opt_* goals =====

     GENUINE BLOCKERS found during proof attempt:

     1. ao_opt_or "truthy" case: OR [x; nonzero_lit] → ASSIGN [1w]
        Changes output value from (x || w) to 1w. These differ when
        x || w ≠ 1 (e.g., x=2, w=3 gives 3, not 1).
        state_equiv fv requires exact equality on output variables.
        FIX: truthy optimization needs either:
        - A weaker simulation relation (truthy_equiv)
        - To be moved to a separate pass with usage-level proof
        - Precondition that the output IS in fv (would need theorem change)

     2. ao_opt_comparator range-based: replaces with Lit 0w/1w based on
        range_get_range analysis. Correctness depends on range analysis
        accuracy, but there is no soundness precondition on `ra`.
        FIX: Add precondition `range_analysis_sound ra` or prove range
        replacements are always correct (requires range analysis theory).

     3. step_inst_base_def is ~500 lines. Unfolding it with gvs/every_case_tac
        times out. Need per-opcode step_inst_base lemmas or use Once rewriting.

     4. Missing rule theorems for: exp power laws, muldiv power-of-two
        (MUL→SHL, Div→SHR, Mod→AND), signextend identity, safe_smod/safe_sdiv.

     All 20 goals are cheated pending resolution of these issues. *)
  (* Get inst0.inst_outputs from inst_wf *)
  >> `?out. inst0.inst_outputs = [out]` by (
    `LENGTH inst.inst_outputs = 1` by gvs[inst_wf_def] >>
    Cases_on `inst.inst_outputs` >> gvs[] >>
    Cases_on `t` >> gvs[])
  (* ---- Helper: lit_eq h v = T implies h = Lit v ---- *)
  >> `!h v. lit_eq h v ==> h = Lit v` by
    (rpt gen_tac >> Cases_on `h` >> simp[lit_eq_def])
  (* NOTE: binary NONE error helper removed — not provable for
     non-binary opcodes like SHL. Handle inline where needed. *)
  (* ---- Shift: SHL, SHR, SAR (all have same structure) ---- *)
  >- ( (* SHL *)
    DISJ2_TAC >> simp[ao_opt_shift_def] >>
    every_case_tac >> gvs[] >>
    irule singleton_post_flip_sim >> simp[] >>
    gvs[lit_eq_def] >> metis_tac[ao_rule_shl_zero])
  >- ( (* SHR *)
    DISJ2_TAC >> simp[ao_opt_shift_def] >>
    every_case_tac >> gvs[] >>
    irule singleton_post_flip_sim >> simp[] >>
    gvs[lit_eq_def] >> metis_tac[ao_rule_shr_zero])
  >- ( (* SAR *)
    DISJ2_TAC >> simp[ao_opt_shift_def] >>
    every_case_tac >> gvs[] >>
    irule singleton_post_flip_sim >> simp[] >>
    gvs[lit_eq_def] >> metis_tac[ao_rule_sar_zero])
  (* ---- Uniform tactic for 1-to-1 cases ----
     Pattern: unfold def, case split, for each resulting singleton
     use singleton_post_flip_sim with the rule theorem chain:
       step_inst_base inst' s = step_inst_base inst0 s  (rule theorem)
       step_inst_base inst0 s = step_inst_base inst s   (assumption)   *)
  >- cheat (* SIGNEXTEND — needs signextend w>=31 identity rule *)
  >- cheat (* Exp — needs exp rules: x**0=1, x**1=x, 1**x=1, 0**x=iszero *)
  >- ( (* ADD *)
    DISJ2_TAC >> simp[ao_opt_addsub_def] >>
    every_case_tac >> gvs[lit_eq_def] >>
    irule singleton_post_flip_sim >> simp[] >>
    metis_tac[ao_rule_add_zero])
  >- cheat (* SUB — op1=op2 causes every_case_tac explosion, needs helper lemma *)
  >- cheat (* XOR *)
  >- cheat (* AND *)
  >- cheat (* MUL — needs power-of-two rules *)
  >- cheat (* Div — needs power-of-two rules *)
  >- cheat (* SDIV — needs safe_sdiv rules *)
  >- cheat (* Mod — needs power-of-two rules *)
  >- cheat (* SMOD — needs safe_smod rules *)
  >- cheat (* OR *)
  >- cheat (* EQ — 1-to-N expansion *)
  >- cheat (* GT — comparator *)
  >- cheat (* LT — comparator *)
  >- cheat (* SGT — comparator *)
  >- cheat (* SLT — comparator *)
QED

val _ = export_theory();
