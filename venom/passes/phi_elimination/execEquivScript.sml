(*
 * Execution Equivalence Theorems
 *
 * This theory proves that semantic operations preserve state equivalence.
 * These are the main theorems clients use for correctness proofs.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL THEOREMS:
 *   - step_inst_result_equiv     : Instruction stepping preserves equiv
 *   - step_in_block_result_equiv : Block stepping preserves equiv
 *   - run_block_result_equiv     : Block execution preserves equiv
 *
 * KEY LEMMAS:
 *   - step_inst_state_equiv      : Single instruction step (success case)
 *   - step_in_block_state_equiv  : Single block step (success case)
 *   - run_block_state_equiv      : Block execution (success case)
 *
 * HELPER THEOREMS:
 *   - exec_binop/unop/modop_state_equiv : Operation helpers
 *   - exec_binop/unop/modop_result_equiv : Full result versions
 *
 * ============================================================================
 *)

Theory execEquiv
Ancestors
  stateEquiv venomSem venomState

(* ==========================================================================
   Binary/Unary/Mod Operations Preserve Equivalence
   ========================================================================== *)

(* Helper: Binary operation preserves state_equiv when it succeeds *)
Theorem exec_binop_state_equiv:
  !f inst s1 s2 r1.
    state_equiv s1 s2 /\
    exec_binop f inst s1 = OK r1
  ==>
    ?r2. exec_binop f inst s2 = OK r2 /\ state_equiv r1 r2
Proof
  rw[exec_binop_def] >>
  gvs[AllCaseEqs()] >>
  drule eval_operand_state_equiv >> strip_tac >> gvs[] >>
  irule update_var_state_equiv >> simp[]
QED

Theorem exec_unop_state_equiv:
  !f inst s1 s2 r1.
    state_equiv s1 s2 /\
    exec_unop f inst s1 = OK r1
  ==>
    ?r2. exec_unop f inst s2 = OK r2 /\ state_equiv r1 r2
Proof
  rw[exec_unop_def] >>
  gvs[AllCaseEqs()] >>
  drule eval_operand_state_equiv >> strip_tac >> gvs[] >>
  irule update_var_state_equiv >> simp[]
QED

Theorem exec_modop_state_equiv:
  !f inst s1 s2 r1.
    state_equiv s1 s2 /\
    exec_modop f inst s1 = OK r1
  ==>
    ?r2. exec_modop f inst s2 = OK r2 /\ state_equiv r1 r2
Proof
  rw[exec_modop_def] >>
  gvs[AllCaseEqs()] >>
  drule eval_operand_state_equiv >> strip_tac >> gvs[] >>
  irule update_var_state_equiv >> simp[]
QED

(* ==========================================================================
   Instruction Stepping Preserves Equivalence
   ========================================================================== *)

(* KEY LEMMA: Single instruction step preserves state_equiv (success case) *)
Theorem step_inst_state_equiv:
  !inst s1 s2 r1.
    state_equiv s1 s2 /\
    step_inst inst s1 = OK r1
  ==>
    ?r2. step_inst inst s2 = OK r2 /\ state_equiv r1 r2
Proof
  rpt strip_tac >>
  fs[step_inst_def] >>
  Cases_on `inst.inst_opcode` >> fs[] >>
  FIRST [
    drule_all exec_binop_state_equiv >> simp[],
    drule_all exec_modop_state_equiv >> simp[],
    drule_all exec_unop_state_equiv >> simp[],
    (* Remaining cases: use case analysis *)
    gvs[AllCaseEqs()] >>
    drule eval_operand_state_equiv >> strip_tac >> gvs[] >>
    (* Update var with direct value - ASSIGN case *)
    TRY (irule update_var_state_equiv >> simp[] >> NO_TAC) >>
    (* Jump cases *)
    TRY (irule jump_to_state_equiv >> simp[] >> NO_TAC) >>
    (* Load operations - prove load values equal, then update_var *)
    TRY (drule_all mload_state_equiv >> strip_tac >> gvs[] >>
         irule update_var_state_equiv >> simp[] >> NO_TAC) >>
    TRY (drule_all sload_state_equiv >> strip_tac >> gvs[] >>
         irule update_var_state_equiv >> simp[] >> NO_TAC) >>
    TRY (drule_all tload_state_equiv >> strip_tac >> gvs[] >>
         irule update_var_state_equiv >> simp[] >> NO_TAC) >>
    (* Store operations *)
    TRY (irule mstore_state_equiv >> simp[] >> NO_TAC) >>
    TRY (irule sstore_state_equiv >> simp[] >> NO_TAC) >>
    TRY (irule tstore_state_equiv >> simp[] >> NO_TAC) >>
    (* PHI case - prev_bb is same in both states *)
    TRY (`s1.vs_prev_bb = s2.vs_prev_bb` by fs[state_equiv_def] >> gvs[] >>
         irule update_var_state_equiv >> simp[] >> NO_TAC) >>
    simp[state_equiv_refl]
  ]
QED

(* ==========================================================================
   Block Stepping Preserves Equivalence
   ========================================================================== *)

(* KEY LEMMA: Single step in block preserves state_equiv (success case) *)
Theorem step_in_block_state_equiv:
  !fn bb s1 s2 r1 is_term.
    state_equiv s1 s2 /\
    step_in_block fn bb s1 = (OK r1, is_term)
  ==>
    ?r2. step_in_block fn bb s2 = (OK r2, is_term) /\ state_equiv r1 r2
Proof
  rw[step_in_block_def] >>
  fs[state_equiv_def] >> fs[] >>
  Cases_on `get_instruction bb s1.vs_inst_idx` >> fs[] >>
  Cases_on `step_inst x s1` >> fs[] >>
  `state_equiv s1 s2` by fs[state_equiv_def] >>
  drule_all step_inst_state_equiv >> strip_tac >>
  Cases_on `is_terminator x.inst_opcode` >> fs[state_equiv_def] >>
  gvs[next_inst_def, var_equiv_def, lookup_var_def]
QED

(* ==========================================================================
   Block Execution Preserves Equivalence
   ========================================================================== *)

(* KEY LEMMA: Block execution preserves state_equiv (success case) *)
Theorem run_block_state_equiv:
  !fn bb s1 s2 r1.
    state_equiv s1 s2 /\
    run_block fn bb s1 = OK r1
  ==>
    ?r2. run_block fn bb s2 = OK r2 /\ state_equiv r1 r2
Proof
  ho_match_mp_tac run_block_ind >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_block _ _ _ = _` mp_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block fn bb s1` >>
  Cases_on `q` >> simp[] >>
  strip_tac >>
  drule_all step_in_block_state_equiv >>
  strip_tac >>
  simp[Once run_block_def] >>
  `(v.vs_halted <=> r2.vs_halted)` by fs[state_equiv_def] >>
  Cases_on `v.vs_halted` >> fs[] >>
  Cases_on `r` >> fs[] >-
    (gvs[] >> simp[Once run_block_def] >> first_x_assum irule >> simp[]) >>
  simp[Once run_block_def]
QED

(* ==========================================================================
   Result Equivalence for Operations (handles all result types)
   ========================================================================== *)

(* Helper: Binary operation result_equiv *)
Theorem exec_binop_result_equiv:
  !f inst s1 s2.
    state_equiv s1 s2 ==>
    result_equiv (exec_binop f inst s1) (exec_binop f inst s2)
Proof
  rw[exec_binop_def] >>
  drule eval_operand_state_equiv >> strip_tac >>
  rpt (CASE_TAC >> gvs[result_equiv_def]) >>
  irule update_var_state_equiv >> simp[]
QED

Theorem exec_unop_result_equiv:
  !f inst s1 s2.
    state_equiv s1 s2 ==>
    result_equiv (exec_unop f inst s1) (exec_unop f inst s2)
Proof
  rw[exec_unop_def] >>
  drule eval_operand_state_equiv >> strip_tac >>
  rpt (CASE_TAC >> gvs[result_equiv_def]) >>
  irule update_var_state_equiv >> simp[]
QED

Theorem exec_modop_result_equiv:
  !f inst s1 s2.
    state_equiv s1 s2 ==>
    result_equiv (exec_modop f inst s1) (exec_modop f inst s2)
Proof
  rw[exec_modop_def] >>
  drule eval_operand_state_equiv >> strip_tac >>
  rpt (CASE_TAC >> gvs[result_equiv_def]) >>
  irule update_var_state_equiv >> simp[]
QED

(* Helper: JNZ case handled separately due to complex control flow *)
Theorem jnz_result_equiv:
  !inst s1 s2.
    state_equiv s1 s2 /\ inst.inst_opcode = JNZ ==>
    result_equiv (step_inst inst s1) (step_inst inst s2)
Proof
  rpt strip_tac >>
  simp[step_inst_def] >>
  drule eval_operand_state_equiv >> strip_tac >>
  rpt CASE_TAC >> gvs[result_equiv_def] >>
  irule jump_to_state_equiv >> simp[]
QED

(* TOP-LEVEL: Instruction stepping preserves result_equiv (all cases) *)
Theorem step_inst_result_equiv:
  !inst s1 s2.
    state_equiv s1 s2 ==>
    result_equiv (step_inst inst s1) (step_inst inst s2)
Proof
  rpt strip_tac >>
  (* Handle JNZ specially before unfolding *)
  Cases_on `inst.inst_opcode = JNZ` >- (
    irule jnz_result_equiv >> simp[]
  ) >>
  simp[step_inst_def] >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  (* Binary ops *)
  TRY (irule exec_binop_result_equiv >> simp[] >> NO_TAC) >>
  (* Unary ops *)
  TRY (irule exec_unop_result_equiv >> simp[] >> NO_TAC) >>
  (* Mod ops *)
  TRY (irule exec_modop_result_equiv >> simp[] >> NO_TAC) >>
  (* Default case: Error = Error *)
  TRY (simp[result_equiv_def] >> NO_TAC) >>
  (* Load operations: MLOAD, SLOAD, TLOAD *)
  TRY (
    drule eval_operand_state_equiv >> strip_tac >>
    rpt CASE_TAC >> gvs[result_equiv_def] >>
    TRY (drule_all mload_state_equiv >> strip_tac >> gvs[]) >>
    TRY (drule_all sload_state_equiv >> strip_tac >> gvs[]) >>
    TRY (drule_all tload_state_equiv >> strip_tac >> gvs[]) >>
    irule update_var_state_equiv >> simp[] >> NO_TAC
  ) >>
  (* Store operations: MSTORE, SSTORE, TSTORE *)
  TRY (
    drule eval_operand_state_equiv >> strip_tac >>
    rpt CASE_TAC >> gvs[result_equiv_def] >>
    TRY (irule mstore_state_equiv >> simp[]) >>
    TRY (irule sstore_state_equiv >> simp[]) >>
    TRY (irule tstore_state_equiv >> simp[]) >> NO_TAC
  ) >>
  (* Control flow - JMP *)
  TRY (
    Cases_on `inst.inst_operands` >> simp[result_equiv_def] >>
    Cases_on `h` >> simp[result_equiv_def] >>
    Cases_on `t` >> simp[result_equiv_def] >>
    irule jump_to_state_equiv >> simp[] >> NO_TAC
  ) >>
  (* Terminators: STOP, RETURN, SINK *)
  TRY (
    simp[result_equiv_def] >> irule halt_state_state_equiv >> simp[] >> NO_TAC
  ) >>
  (* REVERT *)
  TRY (
    simp[result_equiv_def] >> irule revert_state_state_equiv >> simp[] >> NO_TAC
  ) >>
  (* PHI *)
  TRY (
    `s1.vs_prev_bb = s2.vs_prev_bb` by fs[state_equiv_def] >>
    pop_assum (fn th => SUBST_ALL_TAC (SYM th)) >>
    drule eval_operand_state_equiv >> strip_tac >>
    rpt CASE_TAC >> gvs[result_equiv_def] >>
    irule update_var_state_equiv >> simp[] >> NO_TAC
  ) >>
  (* ASSIGN *)
  TRY (
    Cases_on `inst.inst_operands` >> simp[result_equiv_def] >>
    Cases_on `t` >> simp[result_equiv_def] >>
    Cases_on `inst.inst_outputs` >> simp[result_equiv_def] >>
    Cases_on `t` >> simp[result_equiv_def] >>
    drule eval_operand_state_equiv >> strip_tac >> gvs[] >>
    Cases_on `eval_operand h s1` >> simp[result_equiv_def] >>
    irule update_var_state_equiv >> simp[] >> NO_TAC
  ) >>
  (* NOP *)
  simp[result_equiv_def, state_equiv_refl]
QED

(* TOP-LEVEL: Block stepping preserves result_equiv and termination flag *)
Theorem step_in_block_result_equiv:
  !fn bb s1 s2.
    state_equiv s1 s2 ==>
      result_equiv (FST (step_in_block fn bb s1)) (FST (step_in_block fn bb s2)) /\
      SND (step_in_block fn bb s1) = SND (step_in_block fn bb s2)
Proof
  rpt strip_tac >>
  `s1.vs_inst_idx = s2.vs_inst_idx` by fs[state_equiv_def] >>
  simp[step_in_block_def] >>
  Cases_on `get_instruction bb s1.vs_inst_idx` >> simp[] >>
  drule step_inst_result_equiv >> strip_tac >>
  first_x_assum (qspec_then `x` mp_tac) >> strip_tac >>
  Cases_on `step_inst x s1` >> Cases_on `step_inst x s2` >> gvs[] >>
  Cases_on `is_terminator x.inst_opcode` >> gvs[] >>
  gvs[next_inst_def, state_equiv_def, var_equiv_def, lookup_var_def]
QED

(* TOP-LEVEL: Block execution preserves result_equiv (all cases) *)
Theorem run_block_result_equiv:
  !fn bb s1 s2.
    state_equiv s1 s2 ==>
    result_equiv (run_block fn bb s1) (run_block fn bb s2)
Proof
  ho_match_mp_tac run_block_ind >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  (* Unfold run_block on LHS *)
  simp[Once run_block_def] >>
  (* Unfold run_block on RHS using CONV_TAC to target the argument *)
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  (* Get step_in_block result_equiv and SND equality *)
  drule step_in_block_result_equiv >>
  disch_then (qspecl_then [`fn`, `bb`] strip_assume_tac) >>
  Cases_on `step_in_block fn bb s1` >>
  Cases_on `step_in_block fn bb s2` >>
  gvs[] >>
  (* Now case split on the result type *)
  Cases_on `q` >> Cases_on `q'` >> gvs[] >>
  (* OK/OK case: v from s1, v' from s2, both have state_equiv *)
  TRY (
    `v.vs_halted <=> v'.vs_halted` by fs[state_equiv_def] >>
    Cases_on `v.vs_halted` >> gvs[] >>
    Cases_on `r` >> gvs[] >>
    (* If not is_term, use IH - need state_equiv v v' *)
    first_x_assum irule >> simp[] >> NO_TAC
  )
QED

