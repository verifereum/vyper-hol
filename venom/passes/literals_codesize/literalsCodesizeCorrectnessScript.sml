(*
 * Literals Codesize — Correctness Statement
 *
 * The transform preserves semantics: NOT(NOT(x)) = x and
 * (x >>> tz) <<< tz = x when trailing zeros are correct.
 *)

Theory literalsCodesizeCorrectness
Ancestors
  literalsCodesizeProofs literalsCodesizeDefs
  venomWf venomInst passSimulationProps passSimulationDefs

Theorem lit_codesize_function_correct:
  !ctx fn s.
    fn_inst_wf fn ==>
    pass_correct (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (\fuel. run_blocks fuel ctx fn s)
      (\fuel. run_blocks fuel ctx (lit_codesize_function fn) s)
Proof
  ACCEPT_TAC lit_codesize_function_correct_proof
QED

(* ===== Structural helpers for lit_codesize_inst ===== *)

Triviality lci_preserves_id:
  !inst. (lit_codesize_inst inst).inst_id = inst.inst_id
Proof
  rw[lit_codesize_inst_def] >> rpt CASE_TAC >> simp[]
QED

Triviality lci_terminator_identity:
  !inst. is_terminator inst.inst_opcode ==> lit_codesize_inst inst = inst
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> ASSIGN` by
    (Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  simp[lit_codesize_inst_def]
QED

Triviality lci_non_term:
  !inst. ~is_terminator inst.inst_opcode ==>
         ~is_terminator (lit_codesize_inst inst).inst_opcode
Proof
  rw[lit_codesize_inst_def] >>
  rpt CASE_TAC >> gvs[is_terminator_def]
QED

Triviality lci_phi:
  !inst. inst.inst_opcode = PHI ==>
         (lit_codesize_inst inst).inst_opcode = PHI
Proof
  simp[lit_codesize_inst_def]
QED

Triviality lci_non_phi:
  !inst. inst.inst_opcode <> PHI ==>
         (lit_codesize_inst inst).inst_opcode <> PHI
Proof
  rw[lit_codesize_inst_def] >> rpt CASE_TAC >> gvs[]
QED

Triviality lci_preserves_outputs:
  !inst. (lit_codesize_inst inst).inst_outputs = inst.inst_outputs
Proof
  rw[lit_codesize_inst_def] >> rpt CASE_TAC >> simp[]
QED

Triviality fn_insts_blocks_flat:
  !l. fn_insts_blocks l = FLAT (MAP (\bb. bb.bb_instructions) l)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

Triviality lci_insts_outputs_eq:
  !l. FLAT (MAP (\i. i.inst_outputs) (MAP lit_codesize_inst l)) =
      FLAT (MAP (\i. i.inst_outputs) l)
Proof
  Induct >> simp[lci_preserves_outputs]
QED

Triviality lci_outputs_blocks_eq:
  !bbs. FLAT (MAP (\i. i.inst_outputs)
    (fn_insts_blocks (MAP (block_map_transform lit_codesize_inst) bbs))) =
    FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))
Proof
  Induct >> simp[fn_insts_blocks_def, block_map_transform_def,
                  lci_insts_outputs_eq]
QED

(* ===== Obligations ===== *)

Theorem lit_codesize_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (lit_codesize_function fn)
Proof
  simp[ssa_form_def, fn_insts_def, lit_codesize_function_def,
       function_map_transform_def, lci_outputs_blocks_eq]
QED

Theorem lit_codesize_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (lit_codesize_function fn)
Proof
  rpt strip_tac >> simp[lit_codesize_function_def] >>
  irule map_transform_preserves_wf >>
  simp[lci_preserves_id, lci_terminator_identity,
       lci_non_term, lci_phi, lci_non_phi]
QED
