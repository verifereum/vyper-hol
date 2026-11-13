Theory runtimeSymSrcRuntimeBoundary
Ancestors
  runtimeSymSrcPackageTransport runtimeSymSrcModuleArgs
  runtimeSymSrcModuleBodies runtimeSymSrcInternalFunction
  runtimeSymSrcFunctionLists runtimeSymSrcModuleDispatch
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmissionProbe vyperCompiler compileVyper
  list loweringShapeDefs compileEnv venomInst
  runtimeSymSrcOrdinaryPackages runtimeSymSrcGroupedPackages loweringShapeProps
  runtimeSymSrcInterfaces

Theorem runtime_sym_initial:
  EVERY P (state_insts (initial_compile_state entry))
Proof
  simp[state_insts_def, all_blocks_def, initial_compile_state_def]
QED

Theorem runtime_sym_run_lowering:
  (!s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_generate_runtime sels exts ints fb Linear bc mb db ei s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  run_lowering sels exts ints fb rp bc mb db ei entry = SOME unit ==>
  !fn. MEM fn unit.cu_context.ctx_functions ==>
    EVERY runtime_sym_inst (fn_insts fn)
Proof
  simp[run_lowering_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[AllCaseEqs(), lowering_policy_ok_def] >>
  `EVERY runtime_sym_inst (state_insts st1)` by
    (metis_tac[runtime_sym_initial]) >>
  drule_all runtime_sym_extract >> simp[]
QED

Theorem runtime_sym_run_grouped_lowering:
  (!s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_generate_grouped_runtime groups ints fb s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  run_grouped_lowering groups ints fb rp entry = SOME unit ==>
  !fn. MEM fn unit.cu_context.ctx_functions ==>
    EVERY runtime_sym_inst (fn_insts fn)
Proof
  simp[run_grouped_lowering_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  `EVERY runtime_sym_inst (state_insts st1)` by
    (metis_tac[runtime_sym_initial]) >>
  drule_all runtime_sym_extract >> simp[]
QED

Theorem runtime_sym_selectors:
  !sources tenv. EVERY (\(sel,lbl,tz). runtime_sym_label lbl)
    (build_selectors tenv sources)
Proof
  Induct >> simp[build_selectors_def] >> gen_tac >> PairCases_on `h` >>
  simp[build_selectors_def, compute_selector_def] >> simp[runtime_sym_label_def]
QED

Theorem runtime_sym_fallback_classified_body:
  supported_program tops /\ ~program_reads_self_code tops /\
  (!bindings ce lc ty ss. runtime_sym_stmts_contract tops bindings compile_stmts ce lc ty ss) /\
  set_fallback_package_target target
    (package_fallback_fn tops trans keys (FST (SND (SND (classify_functions tops))))) =
    SOME (ce,pay,nr,key,tr,view,stmts,ret) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_fallback_body ce pay nr key tr view stmts ret s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `FST (SND (SND (classify_functions tops)))`
  >- simp[package_fallback_fn_def, set_fallback_package_target_def] >>
  PairCases_on `x` >> Cases_on `u` >> strip_tac >>
  drule_at (Pat `set_fallback_package_target _ _ = _`) runtime_sym_fallback_package_body >>
  simp[] >> disch_then irule >> qexists `s` >> simp[]
QED

Theorem runtime_sym_runtime_boundary:
  (!bindings ce lc ty ss. runtime_sym_stmts_contract tops bindings compile_stmts ce lc ty ss) /\
  (!n s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer n s = (b,s') ==> EVERY runtime_sym_inst (state_insts s') /\
    ~is_label_operand b.buf_operand) /\
  (!ce args off s u s'. runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_decode_args ce args off CALLDATALOAD (Lit 0w) 4 s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!n s v s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_fixed_region_with_id n s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand (SND v).buf_operand) /\
  supported_program tops /\ ~program_reads_self_code tops /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit ==>
  !fn. MEM fn unit.cu_context.ctx_functions ==>
    EVERY runtime_sym_inst (fn_insts fn)
Proof
  strip_tac >>
  drule supported_program_no_external_defaults >> strip_tac >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def] >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[AllCaseEqs(), EVERY_MEM, EXISTS_MEM] >>
  drule_at (Pat `run_lowering _ _ _ _ _ _ _ _ _ _ = _`) runtime_sym_run_lowering >>
  disch_then assume_tac >> rpt gen_tac >> strip_tac >>
  rewrite_tac[GSYM EVERY_MEM] >> first_x_assum irule >> simp[] >>
  rpt gen_tac >> strip_tac >> irule runtime_sym_generate_runtime >>
  goal_assum (drule_at Any) >> simp[runtime_sym_selectors] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule runtime_sym_fallback_classified_body >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >>
      gvs[GSYM EVERY_MEM] >> goal_assum (drule_at Any)) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule runtime_sym_external_classified_bodies >>
      conj_tac
      >- (rpt gen_tac >> Cases_on `u` >>
          gvs[GSYM EVERY_MEM] >> first_assum MATCH_ACCEPT_TAC) >>
      conj_tac
      >- (gvs[GSYM EVERY_MEM] >> first_assum MATCH_ACCEPT_TAC) >>
      goal_assum (drule_at Any) >> simp[] >>
      qexists `K global_nonreentrant_slot` >> qexists `ext_fns` >>
      qexists `rpolicy.rpol_target` >> qexists `tops` >> qexists `T` >> simp[]) >>
  rpt gen_tac >> strip_tac >> irule runtime_sym_internal_classified_bodies >>
  conj_tac
  >- (gvs[GSYM EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (gvs[GSYM EVERY_MEM] >> first_assum MATCH_ACCEPT_TAC) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists `F` >> qexists `0` >> qexists `K global_nonreentrant_slot` >>
  qexists `int_fns` >> qexists `rpolicy.rpol_target` >>
  qexists `tops` >> qexists `T` >> simp[]
QED
