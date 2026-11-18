Theory concretizeAssignProps
Ancestors
  concretizeStepStructure concretizeMemLocDefs venomInst list

Theorem ptr_forwarding_assign_interval:
  EVERY (\i. i.inst_opcode = ASSIGN) xs ==>
  FILTER (\i. i.inst_opcode <> NOP)
    (MAP (concretize_inst_with_positions p) xs) = xs
Proof
  Induct_on `xs` >> simp[] >> rpt strip_tac >>
  simp[concretize_positions_unchanged]
QED
