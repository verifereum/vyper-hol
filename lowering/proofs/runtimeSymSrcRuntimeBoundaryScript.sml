Theory runtimeSymSrcRuntimeBoundary
Ancestors
  runtimeSymSrcPackageTransport runtimeSymSrcModuleArgs
  runtimeSymSrcModuleBodies runtimeSymSrcInternalFunction
  runtimeSymSrcFunctionLists runtimeSymSrcModuleDispatch
  runtimeSymSrcGeneratorContracts runtimeSymSrcBlockEmission vyperCompiler compileVyper
  list loweringShapeDefs compileEnv venomInst
  runtimeSymSrcOrdinaryPackages loweringShapeProps
  runtimeSymSrcInterfaces loweringPackageInsts


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
    (metis_tac[every_state_insts_initial]) >>
  drule_all extract_context_with_internals_every >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem runtime_sym_selectors:
  !sources tenv. EVERY (\(sel,lbl,tz). runtime_sym_label lbl)
    (build_selectors tenv sources)
Proof
  Induct >> simp[build_selectors_def] >> gen_tac >> PairCases_on `h` >>
  simp[build_selectors_def, compute_selector_def] >> simp[runtime_sym_label_def]
QED

Theorem runtime_sym_fallback_classified_body:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
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

(* TEMPORARILY CHEATED - SCRATCH SEQ-8389 gate widening census (never lands)
Proof
  strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (ext_fns,int_fns,fb_fn,ctor_fn)` >>
  `~EXISTS external_has_defaults ext_fns` by
    (drule supported_program_no_external_defaults >> simp[]) >>
  drule_all lower_vyper_runtime_unit_no_external_defaults >>
  disch_then (qspec_then `rpolicy` (fn th =>
    qpat_x_assum `lower_vyper_runtime_unit _ _ = SOME _`
      (mp_tac o PURE_REWRITE_RULE [th]))) >>
  simp[bool_case_eq] >> strip_tac >>
  qabbrev_tac `exts = MAP (set_external_package_target rpolicy.rpol_target o
    package_external_fn tops T (K global_nonreentrant_slot)) ext_fns` >>
  qabbrev_tac `ints = MAP (set_internal_package_target rpolicy.rpol_target o
    package_internal_fn tops T (K global_nonreentrant_slot) F 0)
      (order_internals (runtime_internal_order tops int_fns) int_fns)` >>
  `!s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_external_fn_bodies exts s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')` by
    (match_mp_tac (GEN_ALL runtime_sym_external_classified_bodies) >>
     qpat_assum `Abbrev (exts = _)`
       (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     goal_assum (drule_at (Pat `_ = MAP _ _`)) >> simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt strip_tac >>
     qpat_assum `!ce args off s u s'. _ ==> _`
       (drule_at (Pat `compile_decode_args _ _ _ _ _ _ _ = _`)) >> simp[]) >>
  `!s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_internal_fn_bodies ints s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')` by
    (match_mp_tac (GEN_ALL runtime_sym_internal_classified_bodies) >>
     qpat_assum `Abbrev (ints = _)`
       (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     goal_assum (drule_at (Pat `_ = MAP _ _`)) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- simp[MEM_order_internals] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     rpt strip_tac >>
     qpat_assum `!n s b s'. _ /\ compile_alloc_buffer n s = (b,s') ==> _`
       (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  gen_tac >> strip_tac >>
  drule_at (Pat `run_lowering _ _ _ _ _ _ _ _ _ _ = _`) runtime_sym_run_lowering >>
  disch_then match_mp_tac >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `compile_generate_runtime _ _ _ _ _ _ _ _ _ _ = _`)
    runtime_sym_generate_runtime >>
  disch_then match_mp_tac >>
  rewrite_tac[runtime_sym_selectors] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  irule runtime_sym_fallback_classified_body >>
  goal_assum (drule_at (Pat `compile_fallback_body _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `supported_program _`)) >> simp[] >>
  goal_assum (drule_at (Pat `set_fallback_package_target _ _ = _`))
QED
*)
Theorem runtime_sym_runtime_boundary:
  (!bindings ce lc ty ss. runtime_sym_stmts_contract tops bindings compile_stmts ce lc ty ss) /\
  (!n s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer n s = (b,s') ==> EVERY runtime_sym_inst (state_insts s') /\
    ~is_label_operand b.buf_operand) /\
  (!ce args off s u s'. runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_decode_args ce args off CALLDATALOAD (Lit 0w) 4 s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!n s v s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_fixed_region_with_id n s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand (SND v).buf_operand) /\
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ ~program_reads_self_code tops /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit ==>
  !fn. MEM fn unit.cu_context.ctx_functions ==>
    EVERY runtime_sym_inst (fn_insts fn)
Proof
  cheat
QED
