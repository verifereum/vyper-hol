Theory loweringPackageInsts
Ancestors vyperCompiler loweringShapeDefs list venomInst unitShapeDefs

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

Theorem extract_context_with_internals_every:
  extract_context_with_internals entry internals st = SOME (ctx,data) /\
  EVERY P (state_insts st) ==>
  EVERY (\func. EVERY P (fn_insts func)) ctx.ctx_functions
Proof
  simp[extract_context_with_internals_def, GSYM all_blocks_def,
       AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule package_internal_blocks_subset >> strip_tac >>
  gvs[mk_venom_context_def, fn_insts_def, mk_raw_function_def,
      EVERY_MEM, MEM_fn_insts_blocks_iff, state_insts_def, MEM_FLAT,
      MEM_MAP] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem extract_context_with_internals_inst_subset:
  extract_context_with_internals entry internals st = SOME (ctx,data) /\
  lookup_function name ctx.ctx_functions = SOME func ==>
  !i. MEM i (fn_insts func) ==> MEM i (state_insts st)
Proof
  strip_tac >>
  `EVERY (\i. MEM i (state_insts st)) (state_insts st)` by simp[EVERY_MEM] >>
  drule_all extract_context_with_internals_every >>
  drule lookup_function_MEM >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem initial_compile_state_insts:
  state_insts (initial_compile_state entry) = []
Proof
  simp[initial_compile_state_def, state_insts_def, all_blocks_def]
QED

Theorem every_state_insts_initial:
  EVERY P (state_insts (initial_compile_state entry))
Proof
  simp[initial_compile_state_insts]
QED
