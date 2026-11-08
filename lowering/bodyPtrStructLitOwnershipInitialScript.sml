Theory bodyPtrStructLitOwnershipInitial
Ancestors bodyPtrStructLitCompilerOwnership vyperCompiler loweringShapeDefs list

Theorem initial_compile_state_insts:
  state_insts (initial_compile_state entry) = []
Proof
  simp[initial_compile_state_def, state_insts_def, all_blocks_def]
QED

Theorem initial_compile_state_alloc_writers_unique:
  alloc_writers_unique (initial_compile_state entry)
Proof
  simp[alloc_writers_unique_def, initial_compile_state_insts]
QED
