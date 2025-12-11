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
  sccpTransform sccpAbsInt sccpLattice venomSem venomInst list

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
  Cases_on `inst.inst_opcode` >>
  fs[step_inst_def, transform_inst_def] >> gvs[AllCaseEqs()] >>
  (* exec_binop/unop/modop cases produce identical states - reflexivity *)
  TRY (drule_all exec_binop_transform >> strip_tac >> qexists_tac `s'` >> simp[state_equiv_def]) >>
  TRY (drule_all exec_unop_transform >> strip_tac >> qexists_tac `s'` >> simp[state_equiv_def]) >>
  TRY (drule_all exec_modop_transform >> strip_tac >> qexists_tac `s'` >> simp[state_equiv_def]) >>
  (* PHI/ASSIGN: same state, use reflexivity *)
  TRY (simp[state_equiv_def]) >>
  (* Memory/storage ops: transform_operand_sound shows same operand value *)
  TRY (
    simp[transform_operands_def] >> qexists_tac `s'` >> simp[state_equiv_def] >>
    drule_all transform_operand_sound >> simp[]
  ) >>
  TRY (
    simp[transform_operands_def] >> qexists_tac `s'` >> simp[state_equiv_def] >>
    ntac 2 (drule_all transform_operand_sound >> strip_tac) >> gvs[]
  ) >>
  (* JNZ: case analysis on abs_operand, simplified JMP works same *)
  TRY (Cases_on `abs_operand lenv cond_op` >> gvs[] >> qexists_tac `s'` >> simp[state_equiv_def])
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
  (* Halt case: use step_inst_halt_transform *)
  >- (
    drule step_inst_halt_transform >> simp[] >>
    simp[state_equiv_def]
  )
  (* Revert case: use step_inst_revert_transform *)
  >- (
    drule step_inst_revert_transform >> simp[] >>
    simp[state_equiv_def]
  )
  (* Error case: trivially true *)
  >- simp[]
QED

(* ==========================================================================
   Block-Level Correctness
   ========================================================================== *)

(* Block-level fixpoint: abstract stepping doesn't change lattice for any inst *)
Definition block_fixpoint_def:
  block_fixpoint (lenv: lattice_env) (bb: basic_block) <=>
    !inst. MEM inst bb.bb_instructions ==> abs_step_inst lenv inst = lenv
End

(* env_sound preservation with fixpoint assumption *)
Theorem env_sound_step_fixpoint:
  !lenv inst s s'.
    env_sound lenv s /\
    step_inst inst s = OK s' /\
    abs_step_inst lenv inst = lenv
  ==>
    env_sound lenv s'
Proof
  rpt strip_tac >>
  drule_all abs_step_inst_sound >> simp[]
QED

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
  (* JNZ is the only interesting case - use full_case_tac to split all nested cases *)
  rpt BasicProvers.full_case_tac >> simp[is_terminator_def]
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
      (* Halt case: use step_inst_halt_transform *)
      drule step_inst_halt_transform >> simp[] >>
      drule step_inst_halt_opcode >> strip_tac >>
      gvs[is_terminator_def, transform_inst_preserves_terminator, state_equiv_def]
    )
    >- (
      (* Revert case: use step_inst_revert_transform *)
      drule step_inst_revert_transform >> simp[] >>
      drule step_inst_revert_opcode >> strip_tac >>
      gvs[is_terminator_def, transform_inst_preserves_terminator, state_equiv_def]
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

(* Helper: get_instruction membership *)
Theorem get_instruction_mem:
  !bb idx inst.
    get_instruction bb idx = SOME inst ==>
    MEM inst bb.bb_instructions
Proof
  rw[get_instruction_def] >> simp[MEM_EL]
QED

(* Helper: step_in_block gets instruction at vs_inst_idx *)
Theorem step_in_block_inst_mem:
  !fn bb s s' is_term inst.
    step_in_block fn bb s = (OK s', is_term) /\
    get_instruction bb s.vs_inst_idx = SOME inst
  ==>
    MEM inst bb.bb_instructions
Proof
  rpt strip_tac >> drule get_instruction_mem >> simp[]
QED

(* Key insight: transform_inst_correct produces the SAME state (not just equivalent) *)
(* This means both run_blocks continue from identical states *)
Theorem transform_block_result_equiv:
  !lenv fn bb s.
    env_sound lenv s /\
    block_fixpoint lenv bb
  ==>
    result_equiv (run_block fn bb s)
                 (run_block fn (transform_block lenv bb) s)
Proof
  (* Use well-founded induction on the termination measure *)
  gen_tac >> gen_tac >> gen_tac >>
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  (* Unfold run_block once *)
  simp[Once run_block_def] >>
  (* Get step_in_block result for original *)
  Cases_on `step_in_block fn bb s`
  >- (
    (* (res, is_term) case - need to case split on res *)
    rename1 `step_in_block fn bb s = (res, is_term)` >>
    Cases_on `res`
    >- (
      (* OK s' case *)
      rename1 `step_in_block fn bb s = (OK s', is_term)` >>
      (* Use step_in_block_transform_equiv to get transformed result *)
      `env_sound lenv s` by simp[] >>
      drule_all step_in_block_transform_equiv >>
      simp[] >> strip_tac >>
      (* s'' = s' by transform_inst_correct witnessing *)
      `s'' = s'` by gvs[state_equiv_def, venom_state_component_equality] >>
      gvs[] >>
      (* Now unfold run_block for transformed *)
      simp[Once run_block_def] >>
      Cases_on `s'.vs_halted` >> simp[]
      >- simp[result_equiv_def, state_equiv_def]
      >- (
        Cases_on `is_term` >> simp[]
        >- simp[result_equiv_def, state_equiv_def]
        >- (
          (* Recursive case: both continue from s' *)
          (* Need to show env_sound lenv s' *)
          (* First, get the instruction that was executed *)
          `?inst. get_instruction bb s.vs_inst_idx = SOME inst` by
            (gvs[step_in_block_def, AllCaseEqs()]) >>
          `MEM inst bb.bb_instructions` by
            (irule get_instruction_mem >> simp[]) >>
          `abs_step_inst lenv inst = lenv` by
            (fs[block_fixpoint_def]) >>
          `step_inst inst s = OK s'` by
            (gvs[step_in_block_def, AllCaseEqs()]) >>
          (* Now get env_sound lenv s' *)
          `env_sound lenv s'` by
            (irule env_sound_step_fixpoint >> qexists_tac `inst` >>
             qexists_tac `s` >> simp[]) >>
          (* Apply IH *)
          first_x_assum (qspec_then `LENGTH bb.bb_instructions - s'.vs_inst_idx` mp_tac) >>
          impl_tac
          >- (
            (* Show measure decreases *)
            gvs[step_in_block_def, AllCaseEqs()] >>
            simp[next_inst_def, get_instruction_def]
          )
          >- (
            strip_tac >>
            first_x_assum (qspecl_then [`s'`] mp_tac) >> simp[]
          )
        )
      )
    )
    >- (
      (* Halt case *)
      drule_all step_in_block_transform_equiv >>
      simp[] >> strip_tac >>
      simp[Once run_block_def] >>
      gvs[result_equiv_def, state_equiv_def]
    )
    >- (
      (* Revert case *)
      drule_all step_in_block_transform_equiv >>
      simp[] >> strip_tac >>
      simp[Once run_block_def] >>
      gvs[result_equiv_def, state_equiv_def]
    )
    >- (
      (* Error case *)
      simp[Once run_block_def, result_equiv_def]
    )
  )
QED

(* ==========================================================================
   Function-Level Correctness
   ========================================================================== *)

(* sccp_fixpoint implies block_fixpoint for all blocks in function *)
Theorem sccp_fixpoint_block:
  !lenv fn bb.
    sccp_fixpoint lenv fn /\
    MEM bb fn.fn_blocks
  ==>
    block_fixpoint lenv bb
Proof
  simp[sccp_fixpoint_def, block_fixpoint_def]
QED

(* lookup_block MEM implies block_fixpoint *)
Theorem lookup_block_fixpoint:
  !lenv fn lbl bb.
    sccp_fixpoint lenv fn /\
    lookup_block lbl fn.fn_blocks = SOME bb
  ==>
    block_fixpoint lenv bb
Proof
  rpt strip_tac >> irule sccp_fixpoint_block >> simp[] >>
  gvs[lookup_block_def, AllCaseEqs()] >>
  irule FIND_MEM >> qexists_tac `\bb. bb.bb_label = lbl` >> simp[]
QED

(* run_block preserves env_sound with block_fixpoint *)
Theorem run_block_env_sound:
  !fn bb lenv s s'.
    env_sound lenv s /\
    block_fixpoint lenv bb /\
    run_block fn bb s = OK s'
  ==>
    env_sound lenv s'
Proof
  (* Use same induction as run_block termination *)
  gen_tac >> gen_tac >> gen_tac >>
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `run_block _ _ _ = _` mp_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block fn bb s` >>
  rename1 `step_in_block fn bb s = (res, is_term)` >>
  Cases_on `res` >> simp[]
  >- (
    (* OK s'' case *)
    rename1 `step_in_block _ _ _ = (OK s'', _)` >>
    Cases_on `s''.vs_halted` >> simp[]
    >- (
      (* halted - s'' = s' *)
      strip_tac >> gvs[]
    )
    >- (
      Cases_on `is_term` >> simp[]
      >- (
        (* terminated - s'' = s' *)
        strip_tac >> gvs[] >>
        (* Need env_sound for s'' after one step *)
        gvs[step_in_block_def, AllCaseEqs()] >>
        irule env_sound_step_fixpoint >> qexists_tac `x` >> qexists_tac `s` >>
        simp[] >> fs[block_fixpoint_def] >>
        first_x_assum irule >> irule get_instruction_mem >> simp[]
      )
      >- (
        (* continue - recursive case *)
        strip_tac >>
        (* Get env_sound s'' first *)
        `?inst. get_instruction bb s.vs_inst_idx = SOME inst` by
          (gvs[step_in_block_def, AllCaseEqs()]) >>
        `MEM inst bb.bb_instructions` by
          (irule get_instruction_mem >> simp[]) >>
        `abs_step_inst lenv inst = lenv` by
          (fs[block_fixpoint_def]) >>
        `step_inst inst s = OK s''` by
          (gvs[step_in_block_def, AllCaseEqs()]) >>
        `env_sound lenv s''` by
          (irule env_sound_step_fixpoint >> qexists_tac `inst` >>
           qexists_tac `s` >> simp[]) >>
        (* Apply IH *)
        first_x_assum (qspec_then `LENGTH bb.bb_instructions - s''.vs_inst_idx` mp_tac) >>
        impl_tac
        >- (
          gvs[step_in_block_def, AllCaseEqs()] >>
          simp[next_inst_def, get_instruction_def]
        )
        >- (
          strip_tac >>
          first_x_assum irule >> simp[]
        )
      )
    )
  )
  >- simp[] (* Halt case - no OK result *)
  >- simp[] (* Revert case - no OK result *)
  >- simp[] (* Error case - no OK result *)
QED

(* Helper: transform_function preserves block structure *)
Theorem lookup_block_transform:
  !lenv fn lbl.
    lookup_block lbl (transform_function lenv fn).fn_blocks =
    OPTION_MAP (transform_block lenv) (lookup_block lbl fn.fn_blocks)
Proof
  simp[transform_function_def, lookup_block_def] >>
  rpt strip_tac >>
  Induct_on `fn.fn_blocks` >> simp[] >>
  rpt strip_tac >> simp[transform_block_def] >>
  COND_CASES_TAC >> simp[]
QED

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
  gen_tac >> gen_tac >>
  Induct_on `fuel` >> rpt strip_tac
  >- (
    (* Base case: fuel = 0 *)
    gvs[run_function_def] >>
    qexists_tac `Error "out of fuel"` >>
    simp[result_equiv_def]
  )
  >- (
    (* Inductive case: fuel = SUC fuel' *)
    gvs[run_function_def] >>
    Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[]
    >- (
      (* Block not found *)
      qexists_tac `Error "block not found"` >>
      simp[lookup_block_transform, result_equiv_def]
    )
    >- (
      (* Block found *)
      rename1 `lookup_block _ _ = SOME bb` >>
      (* Get block_fixpoint for bb *)
      `block_fixpoint lenv bb` by (irule lookup_block_fixpoint >> simp[]) >>
      (* Use transform_block_result_equiv *)
      `result_equiv (run_block fn bb s)
                    (run_block fn (transform_block lenv bb) s)` by
        (irule transform_block_result_equiv >> simp[]) >>
      simp[lookup_block_transform] >>
      Cases_on `run_block fn bb s`
      >- (
        (* OK s' case *)
        rename1 `run_block _ _ _ = OK s'` >>
        gvs[result_equiv_def] >>
        Cases_on `s'.vs_halted` >> simp[]
        >- (
          (* halted *)
          qexists_tac `Halt s'` >> simp[result_equiv_def, state_equiv_def]
        )
        >- (
          (* continue - need IH *)
          (* Get env_sound lenv s' using run_block_env_sound *)
          `env_sound lenv s'` by
            (irule run_block_env_sound >> qexists_tac `fn` >> qexists_tac `bb` >>
             qexists_tac `s` >> simp[]) >>
          (* Apply IH *)
          first_x_assum (qspecl_then [`s'`, `fuel'`] mp_tac) >>
          simp[]
        )
      )
      >- (
        (* Halt case *)
        gvs[result_equiv_def] >>
        qexists_tac `Halt v` >> simp[result_equiv_def, state_equiv_def]
      )
      >- (
        (* Revert case *)
        gvs[result_equiv_def] >>
        qexists_tac `Revert v` >> simp[result_equiv_def, state_equiv_def]
      )
      >- (
        (* Error case *)
        gvs[result_equiv_def] >>
        qexists_tac `Error s'` >> simp[result_equiv_def]
      )
    )
  )
QED

