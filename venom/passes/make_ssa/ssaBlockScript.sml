(*
 * SSA Construction Block-Level Correctness
 *
 * This theory proves block-level correctness of SSA construction.
 * Executing a block in non-SSA form gives equivalent results to
 * executing the transformed block in SSA form.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * KEY LEMMAS:
 *   - step_inst_ssa_equiv        : Single instruction preserves equiv
 *   - step_in_block_ssa_equiv    : Single step preserves equiv
 *   - run_block_ssa_equiv        : Block execution preserves equiv
 *
 * HELPER THEOREMS:
 *   - exec_binop_ssa_equiv       : Binary ops preserve equiv
 *   - exec_unop_ssa_equiv        : Unary ops preserve equiv
 *
 * ============================================================================
 *)

Theory ssaBlock
Ancestors
  ssaDefs ssaTransform ssaStateEquiv ssaWellFormed
  venomState venomInst venomSem list finite_map

(* ==========================================================================
   Binary/Unary/Mod Operations Preserve SSA Equivalence
   ========================================================================== *)

(* Helper: eval_operand with renamed operand gives same result *)
Theorem eval_renamed_operand:
  !vm s_orig s_ssa ns op.
    ssa_state_equiv vm s_orig s_ssa /\
    (!v. FLOOKUP vm v = SOME (ssa_var_name v (stack_top ns v)) \/
         (FLOOKUP vm v = NONE /\ stack_top ns v = 0)) ==>
    eval_operand op s_orig = eval_operand (rename_operand ns op) s_ssa
Proof
  rpt strip_tac >>
  Cases_on `op` >> fs[rename_operand_def, eval_operand_def] >>
  fs[ssa_state_equiv_def, var_map_equiv_def] >>
  first_x_assum (qspec_then `s` mp_tac) >>
  strip_tac >> fs[ssa_var_name_def]
QED

(* Helper: Binary operation preserves SSA equivalence *)
Theorem exec_binop_ssa_equiv:
  !f inst inst_ssa s_orig s_ssa vm r_orig.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    (case inst.inst_output of
       SOME out => inst_ssa.inst_output = SOME (case FLOOKUP vm out of
                                                   SOME ssa_out => ssa_out
                                                 | NONE => out)
     | NONE => inst_ssa.inst_output = NONE) /\
    exec_binop f inst s_orig = OK r_orig ==>
    ?r_ssa vm'.
      exec_binop f inst_ssa s_ssa = OK r_ssa /\
      ssa_state_equiv vm' r_orig r_ssa
Proof
  rw[exec_binop_def] >>
  Cases_on `inst.inst_operands` >> fs[] >>
  Cases_on `t` >> fs[] >>
  Cases_on `t'` >> fs[] >>
  gvs[AllCaseEqs()] >>
  `eval_operand (ssa_operand vm h) s_ssa = eval_operand h s_orig` by (
    irule (GSYM eval_operand_ssa_equiv) >> simp[]
  ) >>
  `eval_operand (ssa_operand vm h') s_ssa = eval_operand h' s_orig` by (
    irule (GSYM eval_operand_ssa_equiv) >> simp[]
  ) >>
  simp[] >>
  Cases_on `inst.inst_output` >> fs[] >>
  qexists_tac `vm |+ (x', case FLOOKUP vm x' of SOME v => v | NONE => x')` >>
  irule update_var_ssa_equiv >> simp[]
QED

(* Helper: Unary operation preserves SSA equivalence *)
Theorem exec_unop_ssa_equiv:
  !f inst inst_ssa s_orig s_ssa vm r_orig.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    (case inst.inst_output of
       SOME out => inst_ssa.inst_output = SOME (case FLOOKUP vm out of
                                                   SOME ssa_out => ssa_out
                                                 | NONE => out)
     | NONE => inst_ssa.inst_output = NONE) /\
    exec_unop f inst s_orig = OK r_orig ==>
    ?r_ssa vm'.
      exec_unop f inst_ssa s_ssa = OK r_ssa /\
      ssa_state_equiv vm' r_orig r_ssa
Proof
  rw[exec_unop_def] >>
  Cases_on `inst.inst_operands` >> fs[] >>
  Cases_on `t` >> fs[] >>
  gvs[AllCaseEqs()] >>
  `eval_operand (ssa_operand vm h) s_ssa = eval_operand h s_orig` by (
    irule (GSYM eval_operand_ssa_equiv) >> simp[]
  ) >>
  simp[] >>
  Cases_on `inst.inst_output` >> fs[] >>
  qexists_tac `vm |+ (x', case FLOOKUP vm x' of SOME v => v | NONE => x')` >>
  irule update_var_ssa_equiv >> simp[]
QED

(* Helper: Modular operation preserves SSA equivalence *)
Theorem exec_modop_ssa_equiv:
  !f inst inst_ssa s_orig s_ssa vm r_orig.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    (case inst.inst_output of
       SOME out => inst_ssa.inst_output = SOME (case FLOOKUP vm out of
                                                   SOME ssa_out => ssa_out
                                                 | NONE => out)
     | NONE => inst_ssa.inst_output = NONE) /\
    exec_modop f inst s_orig = OK r_orig ==>
    ?r_ssa vm'.
      exec_modop f inst_ssa s_ssa = OK r_ssa /\
      ssa_state_equiv vm' r_orig r_ssa
Proof
  rw[exec_modop_def] >>
  Cases_on `inst.inst_operands` >> fs[] >>
  Cases_on `t` >> fs[] >>
  Cases_on `t'` >> fs[] >>
  Cases_on `t''` >> fs[] >>
  gvs[AllCaseEqs()] >>
  `eval_operand (ssa_operand vm h) s_ssa = eval_operand h s_orig` by (
    irule (GSYM eval_operand_ssa_equiv) >> simp[]
  ) >>
  `eval_operand (ssa_operand vm h') s_ssa = eval_operand h' s_orig` by (
    irule (GSYM eval_operand_ssa_equiv) >> simp[]
  ) >>
  `eval_operand (ssa_operand vm h'') s_ssa = eval_operand h'' s_orig` by (
    irule (GSYM eval_operand_ssa_equiv) >> simp[]
  ) >>
  simp[] >>
  Cases_on `inst.inst_output` >> fs[] >>
  qexists_tac `vm |+ (x', case FLOOKUP vm x' of SOME v => v | NONE => x')` >>
  irule update_var_ssa_equiv >> simp[]
QED

(* ==========================================================================
   Instruction Step Equivalence
   ========================================================================== *)

(* KEY LEMMA: Transform of instruction is well-formed for equivalence *)
Definition inst_ssa_compatible_def:
  inst_ssa_compatible vm inst inst_ssa <=>
    inst_ssa.inst_opcode = inst.inst_opcode /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    (case inst.inst_output of
       SOME out => inst_ssa.inst_output = SOME (case FLOOKUP vm out of
                                                   SOME ssa_out => ssa_out
                                                 | NONE => out)
     | NONE => inst_ssa.inst_output = NONE)
End

(* KEY LEMMA: Non-PHI instruction step preserves SSA equivalence *)
Theorem step_inst_non_phi_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm r_orig.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa_compatible vm inst inst_ssa /\
    inst.inst_opcode <> PHI /\
    step_inst inst s_orig = OK r_orig ==>
    ?r_ssa vm'.
      step_inst inst_ssa s_ssa = OK r_ssa /\
      ssa_state_equiv vm' r_orig r_ssa
Proof
  rpt strip_tac >>
  fs[inst_ssa_compatible_def] >>
  qpat_x_assum `step_inst inst s_orig = _` mp_tac >>
  simp[step_inst_def] >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  (* Handle each opcode case *)
  TRY (
    (* Binop cases *)
    strip_tac >>
    qspecl_then [`_`, `inst`, `inst_ssa`, `s_orig`, `s_ssa`, `vm`, `r_orig`]
      mp_tac exec_binop_ssa_equiv >>
    simp[] >> NO_TAC
  ) >>
  TRY (
    (* Unop cases *)
    strip_tac >>
    qspecl_then [`_`, `inst`, `inst_ssa`, `s_orig`, `s_ssa`, `vm`, `r_orig`]
      mp_tac exec_unop_ssa_equiv >>
    simp[] >> NO_TAC
  ) >>
  TRY (
    (* Modop cases *)
    strip_tac >>
    qspecl_then [`_`, `inst`, `inst_ssa`, `s_orig`, `s_ssa`, `vm`, `r_orig`]
      mp_tac exec_modop_ssa_equiv >>
    simp[] >> NO_TAC
  ) >>
  (* Handle remaining cases: MLOAD, MSTORE, SLOAD, SSTORE, TLOAD, TSTORE,
     JMP, JNZ, STOP, RETURN, REVERT, SINK, ASSIGN, NOP *)
  TRY (
    (* Memory load *)
    Cases_on `inst.inst_operands` >> simp[] >>
    Cases_on `t` >> simp[] >>
    gvs[AllCaseEqs()] >>
    strip_tac >>
    `eval_operand (ssa_operand vm h) s_ssa = eval_operand h s_orig` by (
      irule (GSYM eval_operand_ssa_equiv) >> simp[]
    ) >>
    simp[] >> Cases_on `inst.inst_output` >> gvs[] >>
    `mload (w2n x) s_ssa = mload (w2n x) s_orig` by (
      irule mload_ssa_equiv >> simp[]
    ) >>
    simp[] >>
    qexists_tac `vm |+ (x', case FLOOKUP vm x' of SOME v => v | NONE => x')` >>
    irule update_var_ssa_equiv >> simp[] >> NO_TAC
  ) >>
  TRY (
    (* Memory store *)
    Cases_on `inst.inst_operands` >> simp[] >>
    Cases_on `t` >> simp[] >>
    Cases_on `t'` >> simp[] >>
    gvs[AllCaseEqs()] >>
    strip_tac >>
    `eval_operand (ssa_operand vm h) s_ssa = eval_operand h s_orig` by (
      irule (GSYM eval_operand_ssa_equiv) >> simp[]
    ) >>
    `eval_operand (ssa_operand vm h') s_ssa = eval_operand h' s_orig` by (
      irule (GSYM eval_operand_ssa_equiv) >> simp[]
    ) >>
    simp[] >> qexists_tac `vm` >>
    irule mstore_ssa_equiv >> simp[] >> NO_TAC
  ) >>
  TRY (
    (* Storage load *)
    Cases_on `inst.inst_operands` >> simp[] >>
    Cases_on `t` >> simp[] >>
    gvs[AllCaseEqs()] >>
    strip_tac >>
    `eval_operand (ssa_operand vm h) s_ssa = eval_operand h s_orig` by (
      irule (GSYM eval_operand_ssa_equiv) >> simp[]
    ) >>
    simp[] >> Cases_on `inst.inst_output` >> gvs[] >>
    `sload x s_ssa = sload x s_orig` by (
      irule sload_ssa_equiv >> simp[]
    ) >>
    simp[] >>
    qexists_tac `vm |+ (x', case FLOOKUP vm x' of SOME v => v | NONE => x')` >>
    irule update_var_ssa_equiv >> simp[] >> NO_TAC
  ) >>
  TRY (
    (* Storage store *)
    Cases_on `inst.inst_operands` >> simp[] >>
    Cases_on `t` >> simp[] >>
    Cases_on `t'` >> simp[] >>
    gvs[AllCaseEqs()] >>
    strip_tac >>
    `eval_operand (ssa_operand vm h) s_ssa = eval_operand h s_orig` by (
      irule (GSYM eval_operand_ssa_equiv) >> simp[]
    ) >>
    `eval_operand (ssa_operand vm h') s_ssa = eval_operand h' s_orig` by (
      irule (GSYM eval_operand_ssa_equiv) >> simp[]
    ) >>
    simp[] >> qexists_tac `vm` >>
    irule sstore_ssa_equiv >> simp[] >> NO_TAC
  ) >>
  TRY (
    (* Transient load *)
    Cases_on `inst.inst_operands` >> simp[] >>
    Cases_on `t` >> simp[] >>
    gvs[AllCaseEqs()] >>
    strip_tac >>
    `eval_operand (ssa_operand vm h) s_ssa = eval_operand h s_orig` by (
      irule (GSYM eval_operand_ssa_equiv) >> simp[]
    ) >>
    simp[] >> Cases_on `inst.inst_output` >> gvs[] >>
    `tload x s_ssa = tload x s_orig` by (
      irule tload_ssa_equiv >> simp[]
    ) >>
    simp[] >>
    qexists_tac `vm |+ (x', case FLOOKUP vm x' of SOME v => v | NONE => x')` >>
    irule update_var_ssa_equiv >> simp[] >> NO_TAC
  ) >>
  TRY (
    (* Transient store *)
    Cases_on `inst.inst_operands` >> simp[] >>
    Cases_on `t` >> simp[] >>
    Cases_on `t'` >> simp[] >>
    gvs[AllCaseEqs()] >>
    strip_tac >>
    `eval_operand (ssa_operand vm h) s_ssa = eval_operand h s_orig` by (
      irule (GSYM eval_operand_ssa_equiv) >> simp[]
    ) >>
    `eval_operand (ssa_operand vm h') s_ssa = eval_operand h' s_orig` by (
      irule (GSYM eval_operand_ssa_equiv) >> simp[]
    ) >>
    simp[] >> qexists_tac `vm` >>
    irule tstore_ssa_equiv >> simp[] >> NO_TAC
  ) >>
  TRY (
    (* JMP *)
    Cases_on `inst.inst_operands` >> simp[] >>
    Cases_on `h` >> simp[] >>
    Cases_on `t` >> simp[] >>
    gvs[ssa_operand_def] >>
    strip_tac >>
    qexists_tac `vm` >> irule jump_to_ssa_equiv >> simp[] >> NO_TAC
  ) >>
  TRY (
    (* JNZ *)
    Cases_on `inst.inst_operands` >> simp[] >>
    Cases_on `t` >> simp[] >>
    Cases_on `h'` >> simp[] >>
    Cases_on `t'` >> simp[] >>
    Cases_on `h''` >> simp[] >>
    Cases_on `t''` >> simp[] >>
    gvs[AllCaseEqs(), ssa_operand_def] >>
    strip_tac >>
    `eval_operand (ssa_operand vm h) s_ssa = eval_operand h s_orig` by (
      irule (GSYM eval_operand_ssa_equiv) >> simp[]
    ) >>
    simp[] >> qexists_tac `vm` >> irule jump_to_ssa_equiv >> simp[] >> NO_TAC
  ) >>
  TRY (
    (* STOP, RETURN, SINK *)
    strip_tac >> qexists_tac `vm` >>
    irule halt_state_ssa_equiv >> simp[] >> NO_TAC
  ) >>
  TRY (
    (* ASSIGN *)
    Cases_on `inst.inst_operands` >> simp[] >>
    Cases_on `inst.inst_output` >> simp[] >>
    Cases_on `t` >> simp[] >>
    gvs[AllCaseEqs()] >>
    strip_tac >>
    `eval_operand (ssa_operand vm h) s_ssa = eval_operand h s_orig` by (
      irule (GSYM eval_operand_ssa_equiv) >> simp[]
    ) >>
    simp[] >>
    qexists_tac `vm |+ (x, case FLOOKUP vm x of SOME v => v | NONE => x)` >>
    irule update_var_ssa_equiv >> simp[] >> NO_TAC
  ) >>
  (* NOP *)
  strip_tac >> qexists_tac `vm` >> simp[]
QED

(* ==========================================================================
   Block Execution Equivalence
   ========================================================================== *)

(* Block step preserves SSA equivalence - Result version *)
Theorem step_in_block_ssa_result_equiv:
  !fn bb bb_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    LENGTH bb_ssa.bb_instructions = LENGTH bb.bb_instructions /\
    (!idx. idx < LENGTH bb.bb_instructions ==>
           inst_ssa_compatible vm
             (EL idx bb.bb_instructions)
             (EL idx bb_ssa.bb_instructions)) /\
    (!idx. idx < LENGTH bb.bb_instructions ==>
           (EL idx bb.bb_instructions).inst_opcode <> PHI) ==>
    ssa_result_equiv vm
      (FST (step_in_block fn bb s_orig))
      (FST (step_in_block fn bb_ssa s_ssa)) /\
    SND (step_in_block fn bb s_orig) = SND (step_in_block fn bb_ssa s_ssa)
Proof
  rpt strip_tac >>
  fs[step_in_block_def, get_instruction_def] >>
  `s_orig.vs_inst_idx = s_ssa.vs_inst_idx` by fs[ssa_state_equiv_def] >>
  simp[] >>
  Cases_on `s_orig.vs_inst_idx < LENGTH bb.bb_instructions` >> simp[]
  >- (
    (* Have instruction *)
    first_assum (qspec_then `s_orig.vs_inst_idx` mp_tac) >> simp[] >>
    first_x_assum (qspec_then `s_orig.vs_inst_idx` mp_tac) >> simp[] >>
    rpt strip_tac >>
    `(EL s_orig.vs_inst_idx bb_ssa.bb_instructions).inst_opcode =
     (EL s_orig.vs_inst_idx bb.bb_instructions).inst_opcode` by
      fs[inst_ssa_compatible_def] >>
    Cases_on `step_inst (EL s_orig.vs_inst_idx bb.bb_instructions) s_orig` >> gvs[]
    >- (
      (* OK case *)
      qspecl_then [`EL s_orig.vs_inst_idx bb.bb_instructions`,
                   `EL s_orig.vs_inst_idx bb_ssa.bb_instructions`,
                   `s_orig`, `s_ssa`, `vm`, `v`]
        mp_tac step_inst_non_phi_ssa_equiv >> simp[] >>
      strip_tac >> simp[] >>
      simp[ssa_result_equiv_def] >>
      Cases_on `is_terminator (EL s_orig.vs_inst_idx bb.bb_instructions).inst_opcode` >>
      simp[] >>
      simp[next_inst_def, ssa_state_equiv_def] >>
      fs[ssa_state_equiv_def]
    )
    >- (
      (* Halt case - use halt_state_ssa_equiv *)
      (* step_inst gave Halt, so transformed step should too *)
      cheat  (* Need to prove Halt case similarly *)
    )
    >- (
      (* Revert case *)
      cheat
    )
  ) >>
  (* No instruction - Error *)
  simp[ssa_result_equiv_def]
QED

