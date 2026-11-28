Theory ctorDeployMemoryRunMemEntryLabel
Ancestors
  ctorDeployMemoryRunMemEntryBoundary ctorGeneratorShape vyperCompiler
  loweringShapeProps loweringShapeDefs venomInst list
  loweringShapeSource supportedProgram supportedNames compileVyper
  ctorDeployDefs e2eDeployDefs context ctorDeployLoweringCode compileEnv
  ctorDeployEntryLabels intCallLookup deployUnitProducers

Theorem ctor_checked_package_head:
  !ds bb bs p fs.
    package_internal_blocks ds (bb::bs) = SOME (p,fs) /\
    ~MEM bb.bb_label (MAP FST ds) ==>
    ?p'. p = bb::p'
Proof
  Cases >> rw[package_internal_blocks_def] >>
  PairCases_on `h` >>
  gvs[package_internal_blocks_def, split_blocks_at_def, AllCaseEqs()]
QED

Theorem ctor_checked_run_entry_label:
  !has_constructor rpolicy runtime_bc imm args data_size internals cenv ss
   pay nr nkey trans u fn.
  run_deploy_lowering has_constructor rpolicy runtime_bc imm args data_size
    internals cenv ss pay nr nkey trans "__deploy" = SOME u /\
  ~MEM "__deploy" (MAP FST (internal_fn_descriptors internals)) /\
  lookup_function "__deploy" u.cu_context.ctx_functions = SOME fn ==>
  fn_entry_label fn = SOME "__deploy"
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `compile_generate_deploy has_constructor (LENGTH runtime_bc)
    imm args data_size internals cenv ss pay nr nkey trans
    (initial_compile_state "__deploy")` >>
  rename1 `_ = (x, st1)` >> Cases_on `x` >>
  drule compile_deploy_first_block >> strip_tac >>
  qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_deploy_lowering_def, extract_context_with_internals_def,
       GSYM all_blocks_def] >>
  gvs[AllCaseEqs()] >> strip_tac >>
  gvs[] >> drule ctor_checked_package_head >> simp[] >> strip_tac >>
  gvs[install_immutable_reservation_def, mk_venom_context_def,
      lookup_function_def, FIND_thm, mk_raw_function_def,
      fn_entry_label_def, entry_block_def]
QED

Theorem ctor_checked_source_run:
  !tops rpolicy runtime_bc unit.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME unit /\
    supported_program tops /\ supported_program_deploy tops ==>
    ?has_constructor imm args internals cenv ss pay nr nkey trans.
      run_deploy_lowering has_constructor rpolicy runtime_bc imm args 0
        internals cenv ss pay nr nkey trans "__deploy" = SOME unit /\
      EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internals) /\
      ALL_DISTINCT (MAP FST (internal_fn_descriptors internals))
Proof
  rpt gen_tac >> simp[lower_vyper_deploy_unit_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> rpt strip_tac >>
  first_x_assum (irule_at Any) >>
  Cases_on `ctor_fn` >> gvs[internal_fn_descriptors_def] >>
  rename1 `classify_functions tops = (exts, ints, fb, SOME cf)` >>
  qmatch_goalsub_abbrev_tac `internal_fn_descriptors packages` >>
  drule_all deploy_order_internals_ok >> strip_tac >>
  qspecl_then [`tops`, `rpolicy.rpol_target`, `T`, `K global_nonreentrant_slot`,
    `T`, `imm_len tops`, `order_internals (deploy_internal_order (SOME cf) ints) ints`,
    `packages`] mp_tac deploy_internal_package_labels >>
  simp[Abbr `packages`, GSYM immSectionDeadTheory.imm_len_def]
QED

Theorem ctor_checked_run_member_entry_label[local]:
  run_deploy_lowering has_constructor rpolicy runtime_bc imm args data_size
    internals cenv ss pay nr nkey trans "__deploy" = SOME u /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internals) /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors internals)) /\
  MEM fn u.cu_context.ctx_functions ==>
  fn_entry_label fn = SOME fn.fn_name
Proof
  strip_tac >>
  drule run_deploy_lowering_context_ok >> strip_tac >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) u.cu_context.ctx_functions)` by
    fs[lowering_context_ok_def, ctx_fn_names_def] >>
  drule_all lookup_function_distinct_mem >> strip_tac >>
  Cases_on `fn.fn_name = "__deploy"`
  >- (asm_rewrite_tac[] >> irule ctor_checked_run_entry_label >>
      goal_assum (drule_at Any) >> simp[] >>
      gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
      res_tac >> gvs[internal_label_ok_def]) >>
  qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_deploy_lowering_def, extract_context_with_internals_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[AllCaseEqs(), install_immutable_reservation_def, mk_venom_context_def,
      mk_raw_function_def] >>
  drule package_internal_blocks_metadata >>
  strip_tac >>
  `?desc. MEM desc (internal_fn_descriptors internals) /\
          internal_fn_matches_descriptor desc fn` by
    (fs[LIST_REL_EL_EQN, MEM_EL] >> metis_tac[]) >>
  PairCases_on `desc` >> drule_all package_internal_blocks_mem >>
  strip_tac >> fs[internal_fn_matches_descriptor_def] >>
  `mk_internal_function desc0 fbs desc1 desc2 = fn` by
    (drule_at (Pat `ALL_DISTINCT _`) lookup_function_distinct_mem >>
     disch_then (qspec_then `mk_internal_function desc0 fbs desc1 desc2` mp_tac) >>
     gvs[mk_internal_function_metadata, lookup_function_def, FIND_thm]) >>
  qpat_x_assum `mk_internal_function _ _ _ _ = fn` (SUBST_ALL_TAC o SYM) >>
  Cases_on `fbs` >> gvs[mk_internal_function_metadata, fn_entry_label_def, entry_block_def]
QED

Theorem ctor_checked_member_entry_label:
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
  supported_program tops /\ supported_program_deploy tops /\
  MEM fn dunit.cu_context.ctx_functions ==>
  fn_entry_label fn = SOME fn.fn_name
Proof
  strip_tac >> drule_all ctor_checked_source_run >> strip_tac >>
  irule ctor_checked_run_member_entry_label >> metis_tac[]
QED

Theorem ctor_checked_entry_label_from_lowering:
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
  supported_program tops /\ supported_program_deploy tops /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn ==>
  fn_entry_label fn = SOME "__deploy"
Proof
  strip_tac >> drule_all ctor_checked_source_run >> strip_tac >>
  `~MEM "__deploy" (MAP FST (internal_fn_descriptors internals))` by
    (gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
     res_tac >> gvs[internal_label_ok_def]) >>
  drule ctor_checked_run_entry_label >> simp[]
QED

Theorem ctor_checked_deploy_entry_label:
  !tops rpolicy runtime_bc dunit fn lbl.
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
  supported_program tops /\ supported_program_deploy tops /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==> lbl = "__deploy"
Proof
  rpt strip_tac >> drule_all ctor_checked_entry_label_from_lowering >> simp[]
QED

Theorem ctor_checked_task_entry_cursor:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx fn lbl.
  deploy_phases policy tops (deploy_bc,runtime_bc)
    (rpolicy,dunit,dout,prog,cplan) /\
  deploy_source_ok tops am tx /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  lbl = (initial_compile_state "__deploy").cs_current_bb /\
  LENGTH (initial_compile_state "__deploy").cs_current_insts = 0
Proof
  rpt gen_tac >> simp[deploy_phases_def, deploy_source_ok_def] >>
  strip_tac >> drule_all ctor_checked_deploy_entry_label >>
  simp[initial_compile_state_def]
QED
