Theory runtimeSymSrcGroupedPackages
Ancestors
  runtimeSymSrcPackageTransport runtimeSymSrcModuleDispatch
  supportedProgram supportedDecls loweringShapeProps compileVyper list pair
  runtimeSymSrcInterfaces

Theorem runtime_sym_external_no_defaults:
  supported_program tops /\
  MEM (mut,nr,rr,name,args,defaults,ret,fbody) (FST (classify_functions tops)) ==>
  defaults = []
Proof
  strip_tac >> drule classify_functions_external_source >> strip_tac >>
  drule_all supported_program_declaration >>
  simp[supported_function_header_contract, NULL_EQ]
QED

Theorem runtime_sym_packaged_group_provenance:
  supported_program tops ==>
  EVERY (runtime_sym_group
    (\p. MEM p (MAP (set_external_package_target target o
      package_external_fn tops trans keys) (FST (classify_functions tops))))
    (\c. F) (\spec. F))
    (MAP (package_external_group tops target trans keys)
      (FST (classify_functions tops)))
Proof
  strip_tac >> simp[EVERY_MAP, EVERY_MEM] >> qx_gen_tac `e` >>
  PairCases_on `e` >> strip_tac >>
  drule_all runtime_sym_external_no_defaults >> strip_tac >> gvs[] >>
  simp[package_external_group_no_defaults, runtime_sym_group_def,
       compute_selector_def, runtime_sym_label_def, MEM_MAP] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem runtime_sym_singleton_groups_generator:
  EVERY (runtime_sym_group P (\c. F) (\spec. F)) groups /\
  (!p s u s'. P p /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_external_fn_bodies [p] s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_internal_fn_bodies ints s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!ce pay nr key tr view stmts ret s u s'.
    fb = SOME (ce,pay,nr,key,tr,view,stmts,ret) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_fallback_body ce pay nr key tr view stmts ret s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_generate_grouped_runtime groups ints fb s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  irule runtime_sym_generate_grouped_runtime >>
  goal_assum (drule_at Any) >>
  qexistsl [`\spec. F`, `P`, `\c. F`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (match_mp_tac runtime_sym_external_jobs >> asm_rewrite_tac[] >> simp[]) >>
  rpt gen_tac >> strip_tac >> irule runtime_sym_external_groups >>
  rewrite_tac[] >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[]
QED

Theorem runtime_sym_packaged_grouped_generator:
  supported_program tops /\
  (!p s u s'.
    MEM p (MAP (set_external_package_target target o
      package_external_fn tops trans keys) (FST (classify_functions tops))) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_external_fn_bodies [p] s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_internal_fn_bodies ints s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!ce pay nr key tr view stmts ret s u s'.
    fb = SOME (ce,pay,nr,key,tr,view,stmts,ret) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_fallback_body ce pay nr key tr view stmts ret s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_generate_grouped_runtime
      (MAP (package_external_group tops target trans keys)
        (FST (classify_functions tops))) ints fb s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >>
  match_mp_tac (Q.INST [`P` |->
    `\p. MEM p (MAP (set_external_package_target target o
      package_external_fn tops trans keys) (FST (classify_functions tops)))`]
    runtime_sym_singleton_groups_generator) >>
  BETA_TAC >> asm_rewrite_tac[] >> irule runtime_sym_packaged_group_provenance >>
  asm_rewrite_tac[]
QED
