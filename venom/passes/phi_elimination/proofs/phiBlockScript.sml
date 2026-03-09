(*
 * PHI Elimination Block-Level Correctness
 *
 * This theory proves block-level correctness of PHI elimination.
 * transform_block_correct handles the OK case.
 * transform_block_result_equiv handles all result types.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * KEY LEMMAS:
 *   - block_step_equiv            : Single step produces equivalent states
 *   - transform_block_correct        : Block OK case
 *   - transform_block_result_equiv   : Block result equivalence
 *
 * HELPER THEOREMS:
 *   - step_inst_*                    : PHI/ASSIGN evaluation lemmas
 *   - block_step_*_transform      : Halt/Revert/Error cases
 *   - step_*_preserves_prev_bb       : prev_bb preservation
 *
 * ============================================================================
 *)

Theory phiBlock
Ancestors
  phiWellFormed execEquivProps venomExecProofs venomExecSemantics venomState venomInst phiDefs phiOrigins phiTransform stateEquiv stateEquivProps list

(* ==========================================================================
   Instruction Step Lemmas
   ========================================================================== *)

Theorem step_inst_assign_eval:
  !inst out op s.
    inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [op] /\
    inst.inst_outputs = [out]
  ==>
    step_inst_base inst s =
      case eval_operand op s of
        SOME v => OK (update_var out v s)
      | NONE => Error "undefined operand"
Proof
  rw[step_inst_base_def]
QED

Theorem step_inst_phi_resolves_var_ok:
  !inst s s' src_var out prev.
    is_phi_inst inst /\
    inst.inst_outputs = [out] /\
    s.vs_prev_bb = SOME prev /\
    resolve_phi prev inst.inst_operands = SOME (Var src_var) /\
    step_inst_base inst s = OK s'
  ==>
    ?v. lookup_var src_var s = SOME v /\ s' = update_var out v s
Proof
  rpt strip_tac >>
  fs[is_phi_inst_def] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def, eval_operand_def] >>
  Cases_on `lookup_var src_var s` >> simp[]
QED

(* ==========================================================================
   Transform Instruction Correctness
   ========================================================================== *)

(* KEY LEMMA: Transform instruction correctness *)
Theorem transform_inst_correct:
  !dfg inst s s' origin prev_bb v.
    step_inst_base inst s = OK s' /\
    phi_single_origin dfg inst = SOME origin /\
    s.vs_prev_bb = SOME prev_bb /\
    resolve_phi prev_bb inst.inst_operands = SOME (Var v) /\
    dfg_lookup dfg v = SOME origin
  ==>
    ?s''. step_inst_base (transform_inst dfg inst) s = OK s'' /\
          state_equiv {} s' s''
Proof
  rpt strip_tac >>
  `is_phi_inst inst` by metis_tac[phi_single_origin_is_phi] >>
  `origin.inst_outputs = [v]` by metis_tac[dfg_lookup_single_output] >>
  fs[transform_inst_def, is_phi_inst_def] >>
  qexists_tac `s'` >>
  conj_tac >- (
    qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
    simp[step_inst_base_def, eval_operand_def] >>
    Cases_on `lookup_var v s` >> simp[] >>
    strip_tac >> fs[] >>
    Cases_on `inst.inst_outputs` >> fs[] >>
    Cases_on `t` >> fs[]
  ) >>
  simp[state_equiv_refl]
QED

(* ==========================================================================
   Block Step Equivalence
   ========================================================================== *)

(* KEY LEMMA: Single step in block produces equivalent states *)
Theorem block_step_equiv:
  !dfg bb s s' is_term.
    block_step bb s = (OK s', is_term) /\
    (!idx inst. get_instruction bb idx = SOME inst /\ is_phi_inst inst ==>
       phi_well_formed inst.inst_operands) /\
    (!idx inst origin prev_bb v.
       get_instruction bb idx = SOME inst /\
       phi_single_origin dfg inst = SOME origin /\
       s.vs_prev_bb = SOME prev_bb /\
       resolve_phi prev_bb inst.inst_operands = SOME (Var v) ==>
       dfg_lookup dfg v = SOME origin)
  ==>
    ?s''. block_step (transform_block dfg bb) s = (OK s'', is_term) /\
          state_equiv {} s' s''
Proof
  rpt strip_tac >>
  fs[block_step_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> fs[] >>
  rename1 `get_instruction bb _ = SOME curr_inst` >>
  imp_res_tac get_instruction_transform >>
  simp[] >>
  Cases_on `step_inst_base curr_inst s` >> fs[] >>
  simp[transform_inst_preserves_terminator] >>
  Cases_on `is_phi_inst curr_inst` >- (
    Cases_on `phi_single_origin dfg curr_inst` >- (
      imp_res_tac transform_inst_identity >> simp[state_equiv_refl]
    ) >>
    rename1 `phi_single_origin dfg curr_inst = SOME origin_inst` >>
    `phi_well_formed curr_inst.inst_operands` by metis_tac[] >>
    fs[is_phi_inst_def, step_inst_base_def] >>
    Cases_on `curr_inst.inst_outputs` >> fs[] >>
    Cases_on `t` >> fs[] >>
    rename1 `curr_inst.inst_outputs = [out_var]` >>
    Cases_on `s.vs_prev_bb` >> fs[] >>
    rename1 `s.vs_prev_bb = SOME prev_label` >>
    Cases_on `resolve_phi prev_label curr_inst.inst_operands` >> fs[] >>
    rename1 `resolve_phi _ _ = SOME resolved_op` >>
    Cases_on `eval_operand resolved_op s` >> fs[] >>
    `?var. resolved_op = Var var` by metis_tac[resolve_phi_well_formed] >>
    gvs[] >>
    (* Use the compatibility lookup assumption. *)
    first_x_assum (qspecl_then [`s.vs_inst_idx`, `curr_inst`, `origin_inst`, `var`] mp_tac) >>
    simp[] >> strip_tac >>
    `origin_inst.inst_outputs = [var]` by metis_tac[dfg_lookup_single_output] >>
    fs[transform_inst_def, eval_operand_def, step_inst_base_def] >>
    simp[state_equiv_refl]
  ) >>
  imp_res_tac transform_inst_non_phi >>
  simp[state_equiv_refl]
QED

(* ==========================================================================
   Halt/Revert/Error Cases
   ========================================================================== *)

(* Halt/Abort/IntRet results only come from non-PHI instructions *)
Theorem step_inst_halt_abort_not_phi:
  !inst s r.
    (step_inst_base inst s = Halt r \/ step_inst_base inst s = Abort a r \/
     (?vs. step_inst_base inst s = IntRet vs r)) ==>
    ~is_phi_inst inst
Proof
  rpt strip_tac >> fs[is_phi_inst_def, step_inst_base_def] >> gvs[AllCaseEqs()]
QED

(* For Halt/Abort/IntRet cases, block_step on transformed block gives same result *)
Theorem block_step_nonOK_transform:
  !dfg bb s s' is_term.
    (block_step bb s = (Halt s', is_term) \/
     block_step bb s = (Abort a s', is_term) \/
     (?vs. block_step bb s = (IntRet vs s', is_term)))
  ==>
    block_step (transform_block dfg bb) s = block_step bb s
Proof
  rw[block_step_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> fs[] >>
  imp_res_tac get_instruction_transform >> fs[] >>
  gvs[AllCaseEqs()] >>
  `~is_phi_inst x` by (
    CCONTR_TAC >> fs[is_phi_inst_def, step_inst_base_def] >> gvs[AllCaseEqs()]
  ) >>
  imp_res_tac transform_inst_non_phi >> fs[]
QED

(* Convenient corollaries for the specific cases *)
Theorem block_step_halt_transform:
  !dfg bb s s' is_term.
    block_step bb s = (Halt s', is_term) ==>
    block_step (transform_block dfg bb) s = (Halt s', is_term)
Proof
  metis_tac[block_step_nonOK_transform]
QED

Theorem block_step_abort_transform:
  !dfg bb s a s' is_term.
    block_step bb s = (Abort a s', is_term) ==>
    block_step (transform_block dfg bb) s = (Abort a s', is_term)
Proof
  metis_tac[block_step_nonOK_transform]
QED

(* IntRet results only come from RET, not PHI *)
Theorem block_step_intret_transform:
  !dfg bb s vals s' is_term.
    block_step bb s = (IntRet vals s', is_term) ==>
    block_step (transform_block dfg bb) s = (IntRet vals s', is_term)
Proof
  rw[block_step_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> fs[] >>
  imp_res_tac get_instruction_transform >> fs[] >>
  gvs[AllCaseEqs()] >>
  `~is_phi_inst x` by (
    CCONTR_TAC >> fs[is_phi_inst_def, step_inst_base_def] >> gvs[AllCaseEqs()]
  ) >>
  imp_res_tac transform_inst_non_phi >> fs[]
QED

(* ==========================================================================
   prev_bb Preservation
   ========================================================================== *)

(* Helper: step_inst_base preserves vs_prev_bb for non-terminator instructions *)
Theorem step_inst_preserves_prev_bb:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  qpat_x_assum `~is_terminator _` mp_tac >>
  simp[step_inst_base_def] >>
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def] >>
  simp[exec_pure2_def, exec_pure1_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, exec_write2_def,
       exec_ext_call_def, exec_delegatecall_def,
       exec_create_def, exec_alloca_def,
       extract_venom_result_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[AllCaseEqs()]) >>
  gvs[update_var_def, mstore_def, sstore_def, tstore_def,
      write_memory_with_expansion_def, mcopy_def, revert_state_def]
QED

(* Helper: block_step preserves vs_prev_bb for non-terminator steps *)
Theorem block_step_preserves_prev_bb:
  !bb s s' is_term.
    block_step bb s = (OK s', is_term) /\
    ~is_term ==>
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  rw[block_step_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> fs[] >>
  gvs[AllCaseEqs()] >>
  drule_all step_inst_preserves_prev_bb >>
  simp[next_inst_def]
QED

(* Helper: terminator instructions that give OK set vs_prev_bb (via jump_to) *)
Theorem step_inst_terminator_sets_prev_bb:
  !inst s s'.
    is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s' /\
    ~s'.vs_halted ==>
    s'.vs_prev_bb <> NONE
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  qpat_x_assum `is_terminator _` mp_tac >>
  simp[step_inst_base_def] >>
  (* Only JMP/JNZ give OK without halting, both use jump_to *)
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def] >>
  strip_tac >> gvs[AllCaseEqs(), jump_to_def]
QED

(* run_block returning OK with ~halted means vs_prev_bb is set *)
(* TEMPORARILY CHEATED - needs induction restructuring for fuel/ctx *)
Theorem run_block_ok_not_halted_sets_prev_bb:
  !fuel ctx bb s s'.
    EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
    run_block fuel ctx bb s = OK s' /\ ~s'.vs_halted ==>
    s'.vs_prev_bb <> NONE
Proof
  cheat
  (* Original proof used ho_match_mp_tac run_block_ind.
     Needs restructuring to use cj 1 run_block_ind with P1 = T
     and run_block_block_step for unfolding. *)
QED

(* ==========================================================================
   Block-level Correctness
   ========================================================================== *)

(* Helper: Block-level correctness for OK result *)
(* TEMPORARILY CHEATED - needs induction restructuring for fuel/ctx *)
Theorem transform_block_correct:
  !fuel ctx bb st graph final_st.
    EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
    run_block fuel ctx bb st = OK final_st /\
    (!idx inst. get_instruction bb idx = SOME inst /\ is_phi_inst inst ==>
       phi_well_formed inst.inst_operands) /\
    (!idx inst origin prev_bb v.
       get_instruction bb idx = SOME inst /\
       phi_single_origin graph inst = SOME origin /\
       resolve_phi prev_bb inst.inst_operands = SOME (Var v) ==>
       dfg_lookup graph v = SOME origin)
  ==>
    ?xformed_st. run_block fuel ctx (transform_block graph bb) st = OK xformed_st /\
                 state_equiv {} final_st xformed_st
Proof
  cheat
  (* Original proof used ho_match_mp_tac run_block_ind.
     Needs restructuring for mutual run_block/run_function recursion.
     With EVERY ¬INVOKE precondition, run_block never calls run_function,
     so ho_match_mp_tac (cj 1 run_block_ind) with P1 := \_ _ _ _. T
     should work (run_function clause is vacuously satisfied).
     Alternative: completeInduct_on fuel + structural induction on inst_idx. *)
QED

(* Block-level correctness: transform preserves result equivalence. *)
(* TEMPORARILY CHEATED - needs induction restructuring for mutual recursion *)
Theorem transform_block_result_equiv:
  !fuel ctx bb st graph.
    EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
    st.vs_prev_bb <> NONE /\  (* Not at entry - PHI semantics require prev_bb *)
    (!idx inst. get_instruction bb idx = SOME inst /\ is_phi_inst inst ==>
       phi_well_formed inst.inst_operands) /\
    (!idx inst origin prev_bb v.
       get_instruction bb idx = SOME inst /\
       phi_single_origin graph inst = SOME origin /\
       resolve_phi prev_bb inst.inst_operands = SOME (Var v) ==>
       dfg_lookup graph v = SOME origin) /\
    (* For Error case: if PHI with single origin errors, origin's output undefined *)
    (!inst origin src_var prev e s' fuel' ctx'.
       get_instruction bb s'.vs_inst_idx = SOME inst /\
       phi_single_origin graph inst = SOME origin /\
       origin.inst_outputs = [src_var] /\
       s'.vs_prev_bb = SOME prev /\
       step_inst fuel' ctx' inst s' = Error e ==>
       lookup_var src_var s' = NONE)
  ==>
    result_equiv {} (run_block fuel ctx bb st) (run_block fuel ctx (transform_block graph bb) st)
Proof
  cheat
  (* TEMPORARILY CHEATED - needs rewrite for new run_block (no step_in_block).
     Original proof used recInduct run_block_ind and step_in_block_* helpers
     which no longer exist after run-context refactor.
     Approach: completeInduct_on inst_idx (like rtaCorrectnessProof),
     or ho_match_mp_tac (cj 1 run_block_ind) with vacuous run_function clause.
     The block_step_* helpers above (halt/revert/intret_transform, block_step_equiv)
     still work — just need to restructure around the new run_block unfolding
     which dispatches on get_instruction + step_inst_base directly.
  *)
QED
