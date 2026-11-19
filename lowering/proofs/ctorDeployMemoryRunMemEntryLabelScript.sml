Theory ctorDeployMemoryRunMemEntryLabel
Ancestors
  ctorDeployMemoryRunMemEntryBoundary ctorGeneratorShape vyperCompiler
  loweringShapeProps loweringShapeDefs venomInst list
  loweringShapeSource supportedProgram supportedNames compileVyper
  ctorDeployDefs e2eDeployDefs context ctorDeployShape compileEnv

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
  !has_constructor rpolicy runtime_bc imm args data_size internals cenv body
   pay nr nkey trans u fn.
  run_deploy_lowering has_constructor rpolicy runtime_bc imm args data_size
    internals cenv body pay nr nkey trans "__deploy" = SOME u /\
  (has_constructor ==>
    cenv_static_ok cenv /\ cenv.ce_return_pc = NONE /\
    ~supported_stmts_expr_exists expr_shape_root body /\
    EVERY internal_fn_shape_ok internals /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internals)) /\
  ~MEM "__deploy" (MAP FST (internal_fn_descriptors internals)) /\
  lookup_function "__deploy" u.cu_context.ctx_functions = SOME fn ==>
  fn_entry_label fn = SOME "__deploy"
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `~supported_stmts_expr_exists expr_shape_root ss` >>
  Cases_on `compile_generate_deploy has_constructor (LENGTH runtime_bc)
    imm args data_size internals cenv ss pay nr nkey trans
    (initial_compile_state "__deploy")` >>
  rename1 `_ = (x, st1)` >> Cases_on `x` >>
  drule_all compile_generate_deploy_shape >> strip_tac >>
  Cases_on `entry_blocks` >> gvs[] >>
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
      (has_constructor ==>
        cenv_static_ok cenv /\ cenv.ce_return_pc = NONE /\
        ~supported_stmts_expr_exists expr_shape_root ss) /\
      (~has_constructor ==> internals = []) /\
      EVERY internal_fn_shape_ok internals /\
      EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internals)
Proof
  rpt gen_tac >> simp[lower_vyper_deploy_unit_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> rpt strip_tac >>
  first_x_assum (irule_at Any) >>
  Cases_on `ctor_fn` >> gvs[internal_fn_descriptors_def] >>
  rename1 `classify_functions tops = (ext_fns, int_fns, fb_fn, SOME cf)` >>
  `SND (SND (SND (classify_functions tops))) = SOME cf` by simp[] >>
  drule_all package_constructor_shape_ok >> strip_tac >> simp[] >>
  `ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
                   (FST (SND (classify_functions tops))))`
    by metis_tac[supported_names_internal_names_distinct,
                 supported_program_names, supported_declaration_names_unique] >>
  qspecl_then [`tops`, `T`] mp_tac internal_descriptors_ok >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  gs[GSYM MAP_MAP_o, internal_fn_descriptors_set_internal_package_target,
     internal_fn_descriptors_MAP_package_internal_fn, EVERY_MAP] >>
  simp[EVERY_MEM] >> rpt strip_tac
  >- (irule package_internal_fn_ctor_shape_ok >> gs[]) >>
  fs[EVERY_MEM]
QED

Theorem ctor_checked_deploy_entry_label:
  !tops rpolicy runtime_bc dunit fn lbl.
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
  supported_program tops /\ supported_program_deploy tops /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==> lbl = "__deploy"
Proof
  rpt strip_tac >> drule_all ctor_checked_source_run >> strip_tac >>
  `~MEM "__deploy" (MAP FST (internal_fn_descriptors internals))` by
    (gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
     res_tac >> gvs[internal_label_ok_def]) >>
  drule ctor_checked_run_entry_label >> simp[]
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
