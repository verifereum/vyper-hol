Theory bodyPtrStructLitOwnershipExtraction
Ancestors bodyPtrStructLitCompilerOwnership vyperCompiler loweringShapeDefs list
  venomInst unitShapeDefs loweringPackageInsts

Theorem extract_context_with_internals_alloc_writers_unique:
  extract_context_with_internals entry internals st = SOME (ctx,data) /\
  lookup_function name ctx.ctx_functions = SOME func /\
  alloc_writers_unique st ==>
  !i j x. MEM i (fn_insts func) /\ MEM j (fn_insts func) /\
    i.inst_opcode = ALLOCA /\ MEM x i.inst_outputs /\
    MEM x j.inst_outputs ==> i = j
Proof
  strip_tac >> drule extract_context_with_internals_inst_subset >>
  simp[] >> strip_tac >>
  gvs[alloc_writers_unique_def] >> metis_tac[]
QED

Theorem install_immutable_reservation_functions:
  (install_immutable_reservation n ctx).ctx_functions = ctx.ctx_functions
Proof
  simp[install_immutable_reservation_def]
QED
