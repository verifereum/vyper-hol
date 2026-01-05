(*
 * SSA Construction Block-Level: Instruction Step Equivalence
 *
 * TOP-LEVEL:
 *   - step_inst_result_ssa_equiv
 *   - step_inst_non_phi_ssa_equiv
 *)

Theory mkSsaBlockStep
Ancestors
  mkSsaBlockResultCopy mkSsaBlockResultContext mkSsaBlockResultMem
  mkSsaBlockResultCore mkSsaBlockCompat
  mkSsaStateEquiv venomSem

(* KEY LEMMA: Instruction step gives ssa_result_equiv with SAME vm.
 * This is stronger than step_inst_non_phi_ssa_equiv which uses ?vm'.
 * The proof works because inst_ssa_compatible determines the output mapping
 * such that ssa_state_equiv vm is preserved after update_var.
 *
 * PROOF VERIFIED INTERACTIVELY (Dec 2025):
 * After opcode case split + simp[] (NOT gvs[AllCaseEqs()]), goals have form exec_*_result.
 * Each category proven via:
 * - Binop/unop/modop: irule exec_*_result_ssa_equiv + output/FLOOKUP case splits
 * - Load: irule mload/sload/tload_result_ssa_equiv + output/FLOOKUP case splits
 * - Store: irule mstore/sstore/tstore_result_ssa_equiv (no outputs)
 * - JMP/JNZ/ASSIGN: Use dedicated result-equivalence lemmas
 * - Halt/Revert: simp[ssa_result_equiv_def] + irule halt/revert_state_ssa_equiv
 * - Error/NOP/PHI: simp[ssa_result_equiv_def]
 *)
(* Helper: resolve_phi commutes with ssa_operand mapping. *)
Theorem MAP_CONS2:
  !f x y xs. MAP f (x::y::xs) = f x :: f y :: MAP f xs
Proof
  simp[]
QED

Theorem resolve_phi_ssa_operand:
  !prev ops vm.
    resolve_phi prev (MAP (ssa_operand vm) ops) =
    OPTION_MAP (ssa_operand vm) (resolve_phi prev ops)
Proof
  ho_match_mp_tac resolve_phi_ind >>
  rpt strip_tac
  >- simp[resolve_phi_def]
  >- simp[resolve_phi_def]
  >- (
    simp[resolve_phi_def, ssa_operand_def] >>
    Cases_on `lbl = prev` >> simp[] >>
    first_x_assum (qspec_then `vm` mp_tac) >> simp[]
  )
  >- (
    simp[resolve_phi_def, ssa_operand_def] >>
    first_x_assum (qspec_then `vm` mp_tac) >> simp[]
  )
  >- (
    simp[resolve_phi_def, ssa_operand_def] >>
    Cases_on `FLOOKUP vm v9` >> simp[resolve_phi_def, ssa_operand_def] >>
    first_x_assum (qspec_then `vm` mp_tac) >> simp[]
  )
QED

(* Helper: PHI instruction preserves ssa_result_equiv with SAME vm. *)
Theorem phi_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst.inst_opcode = PHI /\
    inst_ssa.inst_opcode = PHI /\
    inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands /\
    LENGTH inst.inst_outputs <= 1 /\
    (case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T) ==>
    ssa_result_equiv vm
      (step_inst inst s_orig)
      (step_inst inst_ssa s_ssa)
Proof
  rpt strip_tac >>
  pop_assum mp_tac >>
  simp[step_inst_def] >>
  Cases_on `inst.inst_outputs` >| [
    strip_tac >>
    fs[step_inst_def, ssa_result_equiv_def],
    Cases_on `t` >| [
      simp[] >> strip_tac >>
      `s_orig.vs_prev_bb = s_ssa.vs_prev_bb` by
        (drule_all ssa_state_equiv_prev_bb >> simp[]) >>
      Cases_on `s_ssa.vs_prev_bb` >| [
        simp[step_inst_def, ssa_result_equiv_def],
        rename1 `s_ssa.vs_prev_bb = SOME prev` >>
        `s_orig.vs_prev_bb = SOME prev` by simp[] >>
        simp[] >>
        ONCE_REWRITE_TAC [resolve_phi_ssa_operand] >>
        Cases_on `resolve_phi prev inst.inst_operands` >| [
          simp[ssa_result_equiv_def],
          rename1 `resolve_phi prev inst.inst_operands = SOME val_op` >>
          `eval_operand val_op s_orig =
           eval_operand (ssa_operand vm val_op) s_ssa` by
            (drule_all eval_operand_ssa_equiv >> simp[]) >>
          Cases_on `eval_operand (ssa_operand vm val_op) s_ssa` >| [
            simp[ssa_result_equiv_def],
            rename1 `eval_operand (ssa_operand vm val_op) s_ssa = SOME v` >>
            `eval_operand val_op s_orig = SOME v` by simp[] >>
            drule_all ssa_state_equiv_update_same_vm >> simp[ssa_result_equiv_def]
          ]
        ]
      ],
      fs[ssa_result_equiv_def]
    ]
  ]
QED

Theorem step_inst_result_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa_compatible vm inst inst_ssa /\
    LENGTH inst.inst_outputs <= 1 ==>
    ssa_result_equiv vm
      (step_inst inst s_orig)
      (step_inst inst_ssa s_ssa)
Proof
  let
    fun result4_forward lemma =
      `inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands` by
        (irule inst_ssa_compatible_operands >> simp[]) >>
      irule lemma >>
      simp[] >> NO_TAC
    fun result3_forward lemma =
      irule lemma >>
      simp[] >> NO_TAC
    val binop_tac = result4_forward exec_binop_result_ssa_equiv
    val unop_tac = result4_forward exec_unop_result_ssa_equiv
    val modop_tac = result4_forward exec_modop_result_ssa_equiv
    val mload_tac = result4_forward mload_result_ssa_equiv
    val sload_tac = result4_forward sload_result_ssa_equiv
    val tload_tac = result4_forward tload_result_ssa_equiv
    val load_tac = FIRST [mload_tac, sload_tac, tload_tac]
    val store_tac =
      `inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands` by
        (irule inst_ssa_compatible_operands >> simp[]) >>
      simp[mstore_result_ssa_equiv, sstore_result_ssa_equiv,
           tstore_result_ssa_equiv] >> NO_TAC
    val assert_tac =
      `inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands` by
        (irule inst_ssa_compatible_operands >> simp[]) >>
      irule assert_result_ssa_equiv >> simp[] >> NO_TAC
    val assert_unreachable_tac =
      `inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands` by
        (irule inst_ssa_compatible_operands >> simp[]) >>
      irule assert_unreachable_result_ssa_equiv >> simp[] >> NO_TAC
    val blockhash_tac = result4_forward blockhash_result_ssa_equiv
    val balance_tac = result4_forward balance_result_ssa_equiv
    val calldataload_tac = result4_forward calldataload_result_ssa_equiv
    val sha3_tac = result3_forward sha3_result_ssa_equiv
    val sha3_64_tac = result3_forward sha3_64_result_ssa_equiv
    val calldatacopy_tac =
      `inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands` by
        (irule inst_ssa_compatible_operands >> simp[]) >>
      irule calldatacopy_result_ssa_equiv >> simp[] >> NO_TAC
    val returndatacopy_tac =
      `inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands` by
        (irule inst_ssa_compatible_operands >> simp[]) >>
      irule returndatacopy_result_ssa_equiv >> simp[] >> NO_TAC
    val jmp_tac =
      `inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands` by
        (irule inst_ssa_compatible_operands >> simp[]) >>
      irule jmp_result_ssa_equiv >> simp[] >> NO_TAC
    val jnz_tac =
      `inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands` by
        (irule inst_ssa_compatible_operands >> simp[]) >>
      irule jnz_result_ssa_equiv >> simp[] >> NO_TAC
    val assign_tac = result4_forward assign_result_ssa_equiv
    val phi_tac =
      `inst_ssa.inst_operands = MAP (ssa_operand vm) inst.inst_operands` by
        (irule inst_ssa_compatible_operands >> simp[]) >>
      `case inst.inst_outputs of
         [] => inst_ssa.inst_outputs = []
       | [out] =>
           let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
           inst_ssa.inst_outputs = [ssa_out] /\
           (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
           (FLOOKUP vm ssa_out = NONE ==>
            FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
       | _ => T` by
        (irule inst_ssa_compatible_outputs_ok >> simp[]) >>
      irule phi_result_ssa_equiv >>
      simp[] >> NO_TAC
    (* Output-only ops: use value equality under ssa_state_equiv. *)
    val state_out_tac =
      irule single_output_result_ssa_equiv >>
      fs[ssa_state_equiv_def] >> NO_TAC
    (* NOP: OK states are equivalent under the same vm. *)
    val nop_tac = simp[ssa_result_equiv_def] >> NO_TAC
    (* Halt/Revert: Goal is ssa_result_equiv vm (Halt ...) (Halt ...).
     * First expand ssa_result_equiv_def to get ssa_state_equiv goal,
     * then apply halt/revert_state_ssa_equiv. *)
    val halt_tac = simp[ssa_result_equiv_def] >> irule halt_state_ssa_equiv >> simp[] >> NO_TAC
    val revert_tac = simp[ssa_result_equiv_def] >> irule revert_state_ssa_equiv >> simp[] >> NO_TAC
    (* Error cases: ssa_result_equiv_def for Error-Error gives T *)
    val error_tac = simp[ssa_result_equiv_def]
    val prep_tac = simp[step_inst_def]
  in
    rpt strip_tac >>
    `inst_ssa.inst_opcode = inst.inst_opcode` by fs[inst_ssa_compatible_def] >>
    `case inst.inst_outputs of
       [] => inst_ssa.inst_outputs = []
     | [out] =>
         let ssa_out = case FLOOKUP vm out of SOME x => x | NONE => out in
         inst_ssa.inst_outputs = [ssa_out] /\
         (!v. v <> out ==> FLOOKUP vm v <> SOME ssa_out) /\
         (FLOOKUP vm ssa_out = NONE ==>
          FLOOKUP vm out = NONE \/ FLOOKUP vm out = SOME out)
     | _ => T` by
     (irule inst_ssa_compatible_outputs_ok >> simp[]) >>
    Cases_on `inst.inst_opcode` >| [
      (prep_tac >> binop_tac),
      (prep_tac >> binop_tac),
      (prep_tac >> binop_tac),
      (prep_tac >> binop_tac),
      (prep_tac >> binop_tac),
      (prep_tac >> binop_tac),
      (prep_tac >> binop_tac),
      (prep_tac >> error_tac),
      (prep_tac >> modop_tac),
      (prep_tac >> modop_tac),
      (prep_tac >> binop_tac),
      (prep_tac >> binop_tac),
      (prep_tac >> binop_tac),
      (prep_tac >> binop_tac),
      (prep_tac >> binop_tac),
      (prep_tac >> unop_tac),
      (prep_tac >> binop_tac),
      (prep_tac >> binop_tac),
      (prep_tac >> binop_tac),
      (prep_tac >> unop_tac),
      (prep_tac >> binop_tac),
      (prep_tac >> binop_tac),
      (prep_tac >> binop_tac),
      (prep_tac >> error_tac),
      (prep_tac >> mload_tac),
      (prep_tac >> store_tac),
      (prep_tac >> error_tac),
      (prep_tac >> state_out_tac),
      (prep_tac >> sload_tac),
      (prep_tac >> store_tac),
      (prep_tac >> tload_tac),
      (prep_tac >> store_tac),
      (prep_tac >> error_tac),
      (prep_tac >> error_tac),
      (prep_tac >> jmp_tac),
      (prep_tac >> jnz_tac),
      (prep_tac >> error_tac),
      (prep_tac >> error_tac),
      (prep_tac >> halt_tac),
      (prep_tac >> revert_tac),
      (prep_tac >> halt_tac),
      (prep_tac >> halt_tac),
      phi_tac,
      (prep_tac >> error_tac),
      (prep_tac >> assign_tac),
      (prep_tac >> nop_tac),
      (prep_tac >> error_tac),
      (prep_tac >> error_tac),
      (prep_tac >> error_tac),
      (prep_tac >> error_tac),
      (prep_tac >> state_out_tac),
      (prep_tac >> state_out_tac),
      (prep_tac >> calldataload_tac),
      (prep_tac >> state_out_tac),
      (prep_tac >> calldatacopy_tac),
      (prep_tac >> state_out_tac),
      (prep_tac >> state_out_tac),
      (prep_tac >> state_out_tac),
      (prep_tac >> state_out_tac),
      (prep_tac >> state_out_tac),
      (prep_tac >> state_out_tac),
      (prep_tac >> state_out_tac),
      (prep_tac >> state_out_tac),
      (prep_tac >> state_out_tac),
      (prep_tac >> state_out_tac),
      (prep_tac >> state_out_tac),
      (prep_tac >> balance_tac),
      (prep_tac >> blockhash_tac),
      (prep_tac >> state_out_tac),
      (prep_tac >> error_tac),
      (prep_tac >> error_tac),
      (prep_tac >> error_tac),
      (prep_tac >> error_tac),
      (prep_tac >> error_tac),
      (prep_tac >> state_out_tac),
      (prep_tac >> returndatacopy_tac),
      (prep_tac >> error_tac),
      (prep_tac >> state_out_tac),
      (prep_tac >> sha3_tac),
      (prep_tac >> sha3_64_tac),
      (prep_tac >> error_tac),
      (prep_tac >> error_tac),
      (prep_tac >> error_tac),
      (prep_tac >> error_tac),
      (prep_tac >> error_tac),
      (prep_tac >> error_tac),
      (prep_tac >> error_tac),
      (prep_tac >> error_tac),
      (prep_tac >> assert_tac),
      (prep_tac >> assert_unreachable_tac),
      (prep_tac >> error_tac),
      (prep_tac >> error_tac),
      (prep_tac >> error_tac)
    ]
  end
QED

(* KEY LEMMA: Non-PHI instruction step preserves SSA equivalence (single-output). *)
Theorem step_inst_non_phi_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm r_orig.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa_compatible vm inst inst_ssa /\
    inst.inst_opcode <> PHI /\
    LENGTH inst.inst_outputs <= 1 /\
    step_inst inst s_orig = OK r_orig ==>
    ?r_ssa vm'.
      step_inst inst_ssa s_ssa = OK r_ssa /\
      ssa_state_equiv vm' r_orig r_ssa
Proof
  rpt strip_tac >>
  `ssa_result_equiv vm (step_inst inst s_orig) (step_inst inst_ssa s_ssa)` by
    (irule step_inst_result_ssa_equiv >> simp[]) >>
  Cases_on `step_inst inst_ssa s_ssa` >| [
    (rename1 `OK r_ssa` >>
     qexists_tac `r_ssa` >> qexists_tac `vm` >> gvs[ssa_result_equiv_def]),
    gvs[ssa_result_equiv_def],
    gvs[ssa_result_equiv_def],
    gvs[ssa_result_equiv_def]
  ]
QED

(* ==========================================================================
   Block Execution Equivalence
   ========================================================================== *)
