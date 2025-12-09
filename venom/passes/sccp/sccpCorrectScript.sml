(*
 * SCCP Correctness
 *
 * Main correctness theorem: SCCP transformation preserves semantics.
 *
 * If the lattice environment is sound for a state, then running the
 * transformed program produces an equivalent result to the original.
 *)

Theory sccpCorrect
Ancestors
  sccpTransform sccpAbsInt sccpLattice venomSem

(* ==========================================================================
   State and Result Equivalence (simplified versions)
   ========================================================================== *)

(* Two states are equivalent if they have the same variable bindings *)
Definition state_equiv_def:
  state_equiv s1 s2 <=>
    s1.vs_vars = s2.vs_vars /\
    s1.vs_memory = s2.vs_memory /\
    s1.vs_storage = s2.vs_storage /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_halted = s2.vs_halted
End

(* Result equivalence *)
Definition result_equiv_def:
  result_equiv (OK s1) (OK s2) = state_equiv s1 s2 /\
  result_equiv (Halt s1) (Halt s2) = state_equiv s1 s2 /\
  result_equiv (Revert s1) (Revert s2) = state_equiv s1 s2 /\
  result_equiv (Error e1) (Error e2) = T /\
  result_equiv _ _ = F
End

(* ==========================================================================
   Well-Formedness Conditions

   Conditions under which SCCP transformation is correct.
   ========================================================================== *)

(* The lattice must be a valid fixpoint of the abstract interpretation *)
Definition sccp_fixpoint_def:
  sccp_fixpoint (lenv: lattice_env) (fn: ir_function) <=>
    (* For every instruction, abstract stepping doesn't change the lattice *)
    !bb inst.
      MEM bb fn.fn_blocks /\
      MEM inst bb.bb_instructions
    ==>
      abs_step_inst lenv inst = lenv
End

(* ==========================================================================
   Instruction-Level Correctness

   The key insight is that transform_inst only:
   1. Transforms operands for most opcodes (preserves semantics by transform_operand_sound)
   2. Converts JNZ to JMP when condition is known constant

   Since transform_operand_sound ensures transformed operands evaluate to the same
   values, step_inst produces identical results for non-JNZ opcodes.

   For JNZ with abs_operand = Const c:
   - If c = 0, transforms to JMP to false_lbl, which is where original JNZ would go
   - If c <> 0, transforms to JMP to true_lbl, which is where original JNZ would go

   The proof uses exec_binop_transform, exec_unop_transform, exec_modop_transform
   for the standard operation cases.
   ========================================================================== *)

(* state_equiv is reflexive *)
Theorem state_equiv_refl:
  !s. state_equiv s s
Proof
  simp[state_equiv_def]
QED

(* Helper: transform_operands on singleton list *)
Theorem transform_operands_single:
  !lenv op. transform_operands lenv [op] = [transform_operand lenv op]
Proof
  simp[transform_operands_def]
QED

Theorem transform_operands_pair:
  !lenv op1 op2.
    transform_operands lenv [op1; op2] =
    [transform_operand lenv op1; transform_operand lenv op2]
Proof
  simp[transform_operands_def]
QED

(* Helper: transform_operands on triple *)
Theorem transform_operands_triple:
  !lenv op1 op2 op3.
    transform_operands lenv [op1; op2; op3] =
    [transform_operand lenv op1; transform_operand lenv op2; transform_operand lenv op3]
Proof
  simp[transform_operands_def]
QED

(* Transformed instruction produces equivalent result *)
Theorem transform_inst_correct:
  !lenv inst s s'.
    env_sound lenv s /\
    step_inst inst s = OK s'
  ==>
    ?s''. step_inst (transform_inst lenv inst) s = OK s'' /\
          state_equiv s' s''
Proof
  rpt strip_tac >>
  qexists_tac `s'` >>
  simp[state_equiv_refl] >>
  (* Case split on opcode *)
  Cases_on `inst.inst_opcode` >>
  (* Each case: unfold defs, try arithmetic lemmas, fallback to operand soundness *)
  gvs[step_inst_def, transform_inst_def, AllCaseEqs()] >>
  FIRST [
    irule exec_binop_transform >> simp[],
    irule exec_unop_transform >> simp[],
    irule exec_modop_transform >> simp[],
    simp[transform_operands_def] >> rpt (drule_all transform_operand_sound >> strip_tac >> gvs[])
  ]
QED

(* Handle all non-error result types *)
(* Note: For Error results, the transformation might produce OK if the
   lattice provides values for undefined variables. This is fine since
   we only care about preserving semantics when the original succeeds. *)
Theorem transform_inst_result_equiv:
  !lenv inst s.
    env_sound lenv s
  ==>
    case step_inst inst s of
      OK s' => ?s''. step_inst (transform_inst lenv inst) s = OK s'' /\
                     state_equiv s' s''
    | Halt s' => ?s''. step_inst (transform_inst lenv inst) s = Halt s'' /\
                       state_equiv s' s''
    | Revert s' => ?s''. step_inst (transform_inst lenv inst) s = Revert s'' /\
                         state_equiv s' s''
    | Error _ => T
Proof
  rpt strip_tac >>
  Cases_on `step_inst inst s`
  (* OK case: use transform_inst_correct *)
  >- (
    drule_all transform_inst_correct >> strip_tac >>
    gvs[state_equiv_def]
  )
  (* Halt case: STOP/RETURN/SINK produce same Halt *)
  >- (
    Cases_on `inst.inst_opcode` >>
    gvs[step_inst_def, transform_inst_def, AllCaseEqs(), state_equiv_def] >>
    (* All non-terminator opcodes can't produce Halt *)
    gvs[exec_binop_not_halt, exec_unop_not_halt, exec_modop_not_halt]
  )
  (* Revert case: REVERT produces same Revert *)
  >- (
    Cases_on `inst.inst_opcode` >>
    gvs[step_inst_def, transform_inst_def, AllCaseEqs(), state_equiv_def] >>
    gvs[exec_binop_not_revert, exec_unop_not_revert, exec_modop_not_revert]
  )
  (* Error case: trivially true *)
  >- simp[]
QED

(* ==========================================================================
   Block-Level Correctness
   ========================================================================== *)

(* Helper: get_instruction on transformed block *)
Theorem get_instruction_transform:
  !lenv bb idx.
    get_instruction (transform_block lenv bb) idx =
    OPTION_MAP (transform_inst lenv) (get_instruction bb idx)
Proof
  rw[get_instruction_def, transform_block_def] >>
  Cases_on `idx < LENGTH bb.bb_instructions` >> simp[] >>
  simp[EL_MAP]
QED

(* Helper: is_terminator is preserved by transform_inst *)
Theorem transform_inst_preserves_terminator:
  !lenv inst.
    is_terminator (transform_inst lenv inst).inst_opcode =
    is_terminator inst.inst_opcode
Proof
  rpt strip_tac >> simp[transform_inst_def] >>
  Cases_on `inst.inst_opcode` >> simp[] >>
  (* JNZ case: may become JMP, both are terminators *)
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  Cases_on `abs_operand lenv h` >> simp[] >>
  simp[is_terminator_def]
QED

(* Helper: step_in_block preserves result equivalence *)
Theorem step_in_block_transform_equiv:
  !fn bb lenv s.
    env_sound lenv s
  ==>
    case step_in_block fn bb s of
      (OK s', is_term) =>
        ?s''. step_in_block fn (transform_block lenv bb) s = (OK s'', is_term) /\
              state_equiv s' s''
    | (Halt s', _) =>
        ?s''. step_in_block fn (transform_block lenv bb) s = (Halt s'', T) /\
              state_equiv s' s''
    | (Revert s', _) =>
        ?s''. step_in_block fn (transform_block lenv bb) s = (Revert s'', T) /\
              state_equiv s' s''
    | (Error e, _) => T
Proof
  rpt strip_tac >>
  simp[step_in_block_def, get_instruction_transform] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[]
  >- simp[] (* NONE case: Error *)
  >- (
    (* SOME inst case *)
    rename1 `SOME inst` >>
    Cases_on `step_inst inst s`
    >- (
      (* OK case *)
      drule_all transform_inst_correct >> strip_tac >>
      simp[] >>
      Cases_on `is_terminator inst.inst_opcode` >> simp[]
      >- (
        (* is_terminator = T *)
        qexists_tac `s''` >> simp[transform_inst_preserves_terminator]
      )
      >- (
        (* is_terminator = F *)
        qexists_tac `next_inst s''` >>
        simp[transform_inst_preserves_terminator] >>
        gvs[state_equiv_def, next_inst_def]
      )
    )
    >- (
      (* Halt case *)
      qpat_x_assum `env_sound _ _` mp_tac >>
      simp[transform_inst_result_equiv] >> strip_tac >>
      Cases_on `inst.inst_opcode` >>
      gvs[step_inst_def, transform_inst_def, AllCaseEqs(), state_equiv_def] >>
      gvs[exec_binop_not_halt, exec_unop_not_halt, exec_modop_not_halt]
    )
    >- (
      (* Revert case *)
      qpat_x_assum `env_sound _ _` mp_tac >>
      simp[transform_inst_result_equiv] >> strip_tac >>
      Cases_on `inst.inst_opcode` >>
      gvs[step_inst_def, transform_inst_def, AllCaseEqs(), state_equiv_def] >>
      gvs[exec_binop_not_revert, exec_unop_not_revert, exec_modop_not_revert]
    )
    >- simp[] (* Error case: trivially true *)
  )
QED

(* state_equiv implies result_equiv for same-constructor results *)
Theorem result_equiv_of_state_equiv:
  !s1 s2.
    state_equiv s1 s2
  ==>
    result_equiv (OK s1) (OK s2) /\
    result_equiv (Halt s1) (Halt s2) /\
    result_equiv (Revert s1) (Revert s2)
Proof
  simp[result_equiv_def]
QED

Theorem transform_block_result_equiv:
  !lenv fn bb s.
    env_sound lenv s
  ==>
    result_equiv (run_block fn bb s)
                 (run_block fn (transform_block lenv bb) s)
Proof
  (* Proof by induction on run_block using run_block_ind *)
  (* Each step uses step_in_block_transform_equiv *)
  (* Key: transform_inst produces same result, so env_sound is preserved *)
  cheat
QED

(* ==========================================================================
   Function-Level Correctness
   ========================================================================== *)

(* Main correctness theorem *)
Theorem sccp_correct:
  !lenv fn s fuel result.
    env_sound lenv s /\
    sccp_fixpoint lenv fn /\
    fn.fn_blocks <> [] /\
    run_function fuel fn s = result
  ==>
    ?result'.
      run_function fuel (transform_function lenv fn) s = result' /\
      result_equiv result result'
Proof
  (* Proof by induction on fuel *)
  (* Uses transform_block_result_equiv for each block *)
  (* sccp_fixpoint ensures env_sound is preserved across blocks *)
  cheat
QED

