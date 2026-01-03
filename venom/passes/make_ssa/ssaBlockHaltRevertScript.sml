(*
 * SSA Construction Block-Level: Halt/Revert Equivalence
 *
 * TOP-LEVEL:
 *   - step_inst_halt_ssa_equiv
 *   - step_inst_revert_ssa_equiv
 *
 * Helpers:
 *   - step_inst_assert_unreachable_halt
 *   - step_inst_returndatacopy_revert
 *   - step_inst_revert_cases
 *   - exec_*_not_revert
 *)

Theory ssaBlockHaltRevert
Ancestors
  ssaBlockCompat ssaStateEquiv venomSem

(* Helper: ASSERT_UNREACHABLE halting conditions *)
Theorem step_inst_assert_unreachable_halt:
  !inst s r.
    inst.inst_opcode = ASSERT_UNREACHABLE /\
    step_inst inst s = Halt r ==>
    ?cond_op cond.
      inst.inst_operands = [cond_op] /\
      eval_operand cond_op s = SOME cond /\
      cond <> 0w /\
      r = halt_state s
Proof
  rpt strip_tac >>
  fs[step_inst_def] >>
  Cases_on `inst.inst_operands` >> gvs[AllCaseEqs()] >>
  Cases_on `t` >> gvs[AllCaseEqs()] >>
  Cases_on `eval_operand h s` >> gvs[AllCaseEqs()] >>
  qexistsl_tac [`h`, `a`] >> gvs[]
QED

(* KEY LEMMA: Non-PHI instruction step that returns Halt.
   When the original instruction halts, the SSA version also halts
   with an equivalent state. *)
Theorem step_inst_halt_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm r_orig.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa_compatible vm inst inst_ssa /\
    step_inst inst s_orig = Halt r_orig ==>
    ?r_ssa.
      step_inst inst_ssa s_ssa = Halt r_ssa /\
      ssa_state_equiv vm r_orig r_ssa
Proof
  let
    val halt_tac =
      qexists_tac `halt_state s_ssa` >>
      gvs[step_inst_def] >>
      irule halt_state_ssa_equiv >> simp[] >> NO_TAC
    val assert_tac =
      `inst.inst_opcode = ASSERT_UNREACHABLE` by simp[] >>
      drule_all step_inst_assert_unreachable_halt >> strip_tac >>
      qexists_tac `halt_state s_ssa` >>
      simp[step_inst_def] >>
      `eval_operand cond_op s_orig =
       eval_operand (ssa_operand vm cond_op) s_ssa` by
        (irule eval_operand_ssa_equiv >> simp[]) >>
      gvs[] >>
      irule halt_state_ssa_equiv >> simp[] >> NO_TAC
    val no_halt_tac =
      gvs[step_inst_def, exec_binop_not_halt, exec_unop_not_halt,
          exec_modop_not_halt, AllCaseEqs()] >> NO_TAC
  in
    rpt strip_tac >>
    fs[inst_ssa_compatible_def] >>
    Cases_on `inst.inst_opcode` >>
    FIRST [halt_tac, assert_tac, no_halt_tac]
  end
QED

(* Helper: exec_binop never returns Revert *)
Theorem exec_binop_not_revert:
  !f inst s r. exec_binop f inst s <> Revert r
Proof
  rw[exec_binop_def] >> rpt (CASE_TAC >> gvs[])
QED

(* Helper: exec_unop never returns Revert *)
Theorem exec_unop_not_revert:
  !f inst s r. exec_unop f inst s <> Revert r
Proof
  rw[exec_unop_def] >> rpt (CASE_TAC >> gvs[])
QED

(* Helper: exec_modop never returns Revert *)
Theorem exec_modop_not_revert:
  !f inst s r. exec_modop f inst s <> Revert r
Proof
  rw[exec_modop_def] >> rpt (CASE_TAC >> gvs[])
QED

(* Helper: Revert only arises from REVERT/ASSERT/RETURNDATACOPY *)
Theorem step_inst_revert_cases:
  !inst s r.
    step_inst inst s = Revert r ==>
    inst.inst_opcode = REVERT \/
    inst.inst_opcode = ASSERT \/
    inst.inst_opcode = RETURNDATACOPY
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[step_inst_def, exec_binop_not_revert, exec_unop_not_revert,
      exec_modop_not_revert, AllCaseEqs()]
QED

(* Helper: ASSERT revert conditions *)
Theorem step_inst_assert_revert:
  !inst s r.
    inst.inst_opcode = ASSERT /\
    step_inst inst s = Revert r ==>
    ?cond_op.
      inst.inst_operands = [cond_op] /\
      eval_operand cond_op s = SOME 0w /\
      r = revert_state s
Proof
  rpt strip_tac >>
  fs[step_inst_def] >>
  Cases_on `inst.inst_operands` >> gvs[AllCaseEqs()] >>
  Cases_on `t` >> gvs[AllCaseEqs()] >>
  qexists_tac `h` >> gvs[]
QED

(* Helper: RETURNDATACOPY revert conditions *)
Theorem step_inst_returndatacopy_revert:
  !inst s r.
    inst.inst_opcode = RETURNDATACOPY /\
    step_inst inst s = Revert r ==>
    ?op_size op_offset op_destOffset size_val offset destOffset.
      inst.inst_operands = [op_size; op_offset; op_destOffset] /\
      eval_operand op_size s = SOME size_val /\
      eval_operand op_offset s = SOME offset /\
      eval_operand op_destOffset s = SOME destOffset /\
      w2n offset + w2n size_val > LENGTH s.vs_returndata /\
      r = revert_state s
Proof
  rpt strip_tac >>
  fs[step_inst_def] >>
  Cases_on `inst.inst_operands` >> gvs[AllCaseEqs()] >>
  Cases_on `t` >> gvs[AllCaseEqs()] >>
  Cases_on `t'` >> gvs[AllCaseEqs()] >>
  Cases_on `t''` >> gvs[AllCaseEqs()] >>
  qexistsl_tac [`h`, `h'`, `h''`, `size_val`, `offset`, `destOffset`] >>
  gvs[]
QED

(* KEY LEMMA: Non-PHI instruction step that returns Revert.
   Similar to step_inst_halt_ssa_equiv but for Revert results. *)
Theorem step_inst_revert_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm r_orig.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa_compatible vm inst inst_ssa /\
    step_inst inst s_orig = Revert r_orig ==>
    ?r_ssa.
      step_inst inst_ssa s_ssa = Revert r_ssa /\
      ssa_state_equiv vm r_orig r_ssa
Proof
  rpt strip_tac >>
  fs[inst_ssa_compatible_def] >>
  drule_all step_inst_revert_cases >> strip_tac >| [
    (gvs[] >>
     qexists_tac `revert_state s_ssa` >>
     simp[step_inst_def] >>
     gvs[step_inst_def] >>
     irule revert_state_ssa_equiv >> simp[]),
    (gvs[] >>
     drule_all step_inst_assert_revert >> strip_tac >>
     qexists_tac `revert_state s_ssa` >>
     conj_tac >- (
       simp[step_inst_def] >>
       `eval_operand cond_op s_orig =
        eval_operand (ssa_operand vm cond_op) s_ssa` by
         (irule eval_operand_ssa_equiv >> simp[]) >>
       gvs[]
     ) >>
     simp[] >>
     irule revert_state_ssa_equiv >> simp[]),
    (gvs[] >>
     drule_all step_inst_returndatacopy_revert >> strip_tac >>
     qexists_tac `revert_state s_ssa` >>
     conj_tac >- (
       simp[step_inst_def] >>
       `eval_operand op_size s_orig =
        eval_operand (ssa_operand vm op_size) s_ssa` by
         (irule eval_operand_ssa_equiv >> simp[]) >>
       `eval_operand op_offset s_orig =
        eval_operand (ssa_operand vm op_offset) s_ssa` by
         (irule eval_operand_ssa_equiv >> simp[]) >>
       `eval_operand op_destOffset s_orig =
        eval_operand (ssa_operand vm op_destOffset) s_ssa` by
         (irule eval_operand_ssa_equiv >> simp[]) >>
       gvs[ssa_state_equiv_def]
     ) >>
     simp[] >>
     irule revert_state_ssa_equiv >> simp[])
  ]
QED
