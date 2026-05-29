(* Phase 1 WF & SSA preservation: ao_handle_offset_inst
 *
 * TOP-LEVEL:
 *   ao_phase1_preserves_wf  — wf_function preserved
 *   ao_phase1_preserves_ssa — ssa_form preserved
 *   ao_phase1_preserves_inst_wf — EVERY inst_wf preserved
 *)

Theory aoPhase1Wf
Ancestors
  algebraicOptDefs
  venomState venomWf venomInst passSimulationProps passSimulationDefs
  passSharedDefs
Libs
  pairLib BasicProvers

(* ===== ao_handle_offset_inst preserves structural fields ===== *)

Theorem ao_handle_offset_inst_preserves_id:
  !inst. (ao_handle_offset_inst inst).inst_id = inst.inst_id
Proof
  gen_tac >> simp[ao_handle_offset_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `h'` >> simp[] >>
  Cases_on `t'` >> simp[]
QED

Theorem ao_handle_offset_inst_outputs:
  !inst. (ao_handle_offset_inst inst).inst_outputs = inst.inst_outputs
Proof
  gen_tac >> simp[ao_handle_offset_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `h'` >> simp[] >>
  Cases_on `t'` >> simp[]
QED

Triviality term_not_add[local]:
  !opc. is_terminator opc ==> opc <> ADD
Proof
  Cases >> simp[is_terminator_def]
QED

Theorem ao_handle_offset_inst_term:
  !inst. is_terminator inst.inst_opcode ==> ao_handle_offset_inst inst = inst
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> ADD` by metis_tac[term_not_add] >>
  simp[ao_handle_offset_inst_def]
QED

Theorem ao_handle_offset_inst_not_term:
  !inst. ~is_terminator inst.inst_opcode ==>
    ~is_terminator (ao_handle_offset_inst inst).inst_opcode
Proof
  gen_tac >> simp[ao_handle_offset_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `h'` >> simp[] >>
  Cases_on `t'` >> simp[is_terminator_def]
QED

Theorem ao_handle_offset_inst_phi:
  !inst. inst.inst_opcode = PHI ==>
    (ao_handle_offset_inst inst).inst_opcode = PHI
Proof
  simp[ao_handle_offset_inst_def]
QED

Theorem ao_handle_offset_inst_not_phi:
  !inst. inst.inst_opcode <> PHI ==>
    (ao_handle_offset_inst inst).inst_opcode <> PHI
Proof
  gen_tac >> simp[ao_handle_offset_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `h'` >> simp[] >>
  Cases_on `t'` >> simp[]
QED

Theorem ao_handle_offset_inst_wf:
  !inst. inst_wf inst ==> inst_wf (ao_handle_offset_inst inst)
Proof
  gen_tac >> strip_tac >>
  simp[ao_handle_offset_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `h'` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  fs[inst_wf_def]
QED

Theorem ao_handle_offset_inst_not_add:
  !inst. inst.inst_opcode <> ADD ==> ao_handle_offset_inst inst = inst
Proof
  simp[ao_handle_offset_inst_def]
QED

(* ===== Phase 1 preserves wf_function ===== *)

Theorem ao_phase1_preserves_wf:
  !fn. wf_function fn ==>
    wf_function (function_map_transform
      (block_map_transform ao_handle_offset_inst) fn)
Proof
  rpt strip_tac >>
  irule map_transform_preserves_wf >> simp[] >>
  metis_tac[ao_handle_offset_inst_preserves_id,
            ao_handle_offset_inst_term,
            ao_handle_offset_inst_not_term,
            ao_handle_offset_inst_phi,
            ao_handle_offset_inst_not_phi]
QED

(* ===== Phase 1 preserves ssa_form ===== *)

Theorem ao_phase1_preserves_ssa:
  !fn. wf_function fn /\ ssa_form fn ==>
    ssa_form (function_map_transform
      (block_map_transform ao_handle_offset_inst) fn)
Proof
  rpt strip_tac >>
  irule map_transform_preserves_ssa >>
  simp[ao_handle_offset_inst_preserves_id, ao_handle_offset_inst_outputs]
QED

(* ===== Phase 1 preserves EVERY inst_wf ===== *)

Triviality fn_insts_blocks_every[local]:
  !blocks p. EVERY p (fn_insts_blocks blocks) <=>
    EVERY (\bb. EVERY p bb.bb_instructions) blocks
Proof
  Induct >> simp[fn_insts_blocks_def, listTheory.EVERY_APPEND]
QED

Triviality phase1_preserves_inst_wf_blocks[local]:
  !blocks. EVERY (\bb. EVERY inst_wf bb.bb_instructions) blocks ==>
    EVERY (\bb. EVERY inst_wf bb.bb_instructions)
      (MAP (block_map_transform ao_handle_offset_inst) blocks)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  simp[block_map_transform_def, listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
  rpt strip_tac >> gvs[listTheory.MEM_MAP] >>
  irule ao_handle_offset_inst_wf >>
  fs[listTheory.EVERY_MEM]
QED

Theorem ao_phase1_preserves_inst_wf:
  !fn. EVERY inst_wf (fn_insts fn) ==>
    EVERY inst_wf (fn_insts (function_map_transform
      (block_map_transform ao_handle_offset_inst) fn))
Proof
  rpt strip_tac >>
  simp[fn_insts_def, function_map_transform_def] >>
  `EVERY (\bb. EVERY inst_wf bb.bb_instructions)
     (MAP (block_map_transform ao_handle_offset_inst) fn.fn_blocks)` suffices_by
    simp[fn_insts_blocks_every] >>
  irule phase1_preserves_inst_wf_blocks >>
  fs[fn_insts_def, fn_insts_blocks_every]
QED

(* ===== Phase 1 preserves iszero no-label property ===== *)

Triviality fn_insts_blocks_map_transform[local]:
  !blocks f.
    fn_insts_blocks (MAP (block_map_transform f) blocks) =
    MAP f (fn_insts_blocks blocks)
Proof
  Induct >> simp[fn_insts_blocks_def, block_map_transform_def]
QED

Theorem ao_phase1_preserves_iszero_no_label:
  !fn.
    EVERY (\inst. inst.inst_opcode = ISZERO ==>
       EVERY (\op. get_label op = NONE) inst.inst_operands) (fn_insts fn) ==>
    EVERY (\inst. inst.inst_opcode = ISZERO ==>
       EVERY (\op. get_label op = NONE) inst.inst_operands)
      (fn_insts (function_map_transform
        (block_map_transform ao_handle_offset_inst) fn))
Proof
  simp[fn_insts_def, function_map_transform_def,
       fn_insts_blocks_map_transform] >>
  PURE_REWRITE_TAC[listTheory.EVERY_MAP] >>
  simp[listTheory.EVERY_MEM, combinTheory.o_DEF] >>
  rpt strip_tac >>
  Cases_on `x.inst_opcode = ADD` >- (
    gvs[ao_handle_offset_inst_def, LET_THM] >>
    rpt (FULL_CASE_TAC >> gvs[])) >>
  gvs[ao_handle_offset_inst_not_add] >> res_tac
QED

val _ = export_theory();
