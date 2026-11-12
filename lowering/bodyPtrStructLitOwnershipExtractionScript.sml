Theory bodyPtrStructLitOwnershipExtraction
Ancestors bodyPtrStructLitCompilerOwnership vyperCompiler loweringShapeDefs list
  venomInst unitShapeDefs

Theorem split_blocks_at_partition:
  !blocks label prefix suffix.
    split_blocks_at label blocks = SOME (prefix,suffix) ==>
    blocks = prefix ++ suffix
Proof
  Induct >> simp[split_blocks_at_def] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem package_internal_blocks_subset:
  !descriptors blocks entry_blocks functions.
    package_internal_blocks descriptors blocks = SOME (entry_blocks,functions) ==>
    (!bb. MEM bb entry_blocks ==> MEM bb blocks) /\
    (!func bb. MEM func functions /\ MEM bb func.fn_blocks ==> MEM bb blocks)
Proof
  Induct >- simp[package_internal_blocks_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[package_internal_blocks_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule split_blocks_at_partition >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[mk_internal_function_metadata, MEM_APPEND] >> metis_tac[]
QED

Theorem extract_context_with_internals_inst_subset:
  extract_context_with_internals entry internals st = SOME (ctx,data) /\
  lookup_function name ctx.ctx_functions = SOME func ==>
  !i. MEM i (fn_insts func) ==> MEM i (state_insts st)
Proof
  simp[extract_context_with_internals_def, GSYM all_blocks_def,
       AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule lookup_function_MEM >>
  simp[mk_venom_context_def] >> strip_tac >>
  drule package_internal_blocks_subset >> strip_tac >>
  gvs[fn_insts_def, mk_raw_function_def, MEM_fn_insts_blocks_iff,
      state_insts_def, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

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
