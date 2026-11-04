Theory algebraicOptSsaDiagnostic
Ancestors
  algebraicOptDefs algebraicOptOutputShapeProofs venomInst
Libs
  listTheory

(* These equations diagnose partial pattern matching, not a counterexample:
   ARB is a fixed unspecified constant and must not be chosen freely. *)
Theorem ao_empty_comparator:
  inst.inst_operands = [] ==>
  ao_opt_comparator dfg ra lbl idx fr inst = (ARB : instruction list)
Proof
  simp[ao_opt_comparator_def]
QED

Theorem ao_empty_gt_peephole:
  inst.inst_operands = [] /\ inst.inst_outputs <> [] /\
  inst.inst_opcode = GT ==>
  ao_peephole_inst dfg ra lbl idx fr inst = (ARB : instruction list)
Proof
  simp[ao_peephole_inst_def, ao_empty_comparator]
QED

Theorem ao_empty_gt_transform:
  inst.inst_operands = [] /\ inst.inst_outputs <> [] /\
  inst.inst_opcode = GT ==>
  ao_transform_inst dfg ra lbl idx targets fr inst =
  MAP ao_post_flip_inst (ARB : instruction list)
Proof
  strip_tac >>
  `ao_resolve_iszero_inst targets inst = inst` by
    simp[ao_resolve_iszero_inst_def, instruction_component_equality] >>
  `ao_pre_flip_inst inst = inst` by simp[ao_pre_flip_inst_def] >>
  simp[ao_transform_inst_def, ao_opt_producer_def, ao_empty_gt_peephole]
QED
