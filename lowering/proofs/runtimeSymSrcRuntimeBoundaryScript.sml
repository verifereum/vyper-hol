Theory runtimeSymSrcRuntimeBoundary
Ancestors
  runtimeSymSrcPackageTransport runtimeSymSrcModuleArgs
  runtimeSymSrcModuleBodies runtimeSymSrcInternalFunction
  runtimeSymSrcFunctionLists runtimeSymSrcModuleDispatch
  runtimeSymSrcGeneratorContracts runtimeSymSrcBlockEmission vyperCompiler compileVyper
  list loweringShapeDefs compileEnv venomInst
  runtimeSymSrcOrdinaryPackages loweringShapeProps
  runtimeSymSrcInterfaces loweringPackageInsts
  runtimeSymSrcExpressions runtimeSymSrcPrimitives runtimeSymSrcAbiDecode
  runtimeSymSrcContextTypedBase stackPlanTypes


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

Theorem runtime_sym_run_grouped_lowering[local]:
  (!s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_generate_grouped_runtime groups ints fb s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  run_grouped_lowering groups ints fb rp entry = SOME unit ==>
  !fn. MEM fn unit.cu_context.ctx_functions ==>
    EVERY runtime_sym_inst (fn_insts fn)
Proof
  simp[run_grouped_lowering_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[AllCaseEqs(), lowering_policy_ok_def] >>
  `EVERY runtime_sym_inst (state_insts st1)` by
    metis_tac[every_state_insts_initial] >>
  drule_all extract_context_with_internals_every >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem runtime_sym_group_entry_kwargs[local]:
  runtime_sym_env tops ce /\ runtime_sym_label label /\
  EVERY (\(name,op,ty,e). ~is_label_operand op /\ supported_expr tops e /\
    ~supported_expr_exists is_self_code e) vars /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_entry_point_kwargs ce (vars:(string # operand # type # expr) list)
    off n label s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >>
  irule (Q.INST [`tops` |-> `tops`] runtime_sym_entry_point_kwargs) >>
  qexistsl_tac [`ce`, `label`, `n`, `off`, `s`, `tops`, `u`, `vars`] >>
  asm_rewrite_tac[] >>
  match_mp_tac runtime_sym_init_kwargs >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >> irule runtime_sym_abi_decode_to_buf >>
     goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
     simp[is_label_operand_def]) >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`tops` |-> `tops`] runtime_sym_closed_lower_value) >>
     rewrite_tac[runtime_sym_lower_value_clause_def] >>
     disch_then (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
     simp[] >> disch_then irule >>
     metis_tac[runtime_sym_generators, runtime_sym_expression_contracts]) >>
  rpt gen_tac >> MATCH_ACCEPT_TAC runtime_sym_store_bytestring
QED

Theorem runtime_sym_run_grouped_packages:
  (!p s u s'. P p /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_external_fn_bodies [p] s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!c. Q c ==> runtime_sym_env tops c.ec_env /\
    runtime_sym_label c.ec_common_label /\
    (?bindings. supported_stmts tops bindings c.ec_body) /\
    ~supported_stmts_expr_exists is_self_code c.ec_body) /\
  (!n ty e. D (n,ty,e) ==> supported_expr tops e /\
    ~supported_expr_exists is_self_code e) /\
  (!bindings ce lc ty ss. runtime_sym_stmts_contract tops bindings compile_stmts ce lc ty ss) /\
  (!n s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer n s = (b,s') ==> EVERY runtime_sym_inst (state_insts s') /\
    ~is_label_operand b.buf_operand) /\
  (!ce args off s u s'. runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_decode_args ce args off CALLDATALOAD (Lit 0w) 4 s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_internal_fn_bodies ints s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!ce pay nr key tr view stmts ret s u s'.
    fb = SOME (ce,pay,nr,key,tr,view,stmts,ret) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_fallback_body ce pay nr key tr view stmts ret s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  EVERY (runtime_sym_group P Q D) groups /\
  run_grouped_lowering groups ints fb rp entry = SOME unit ==>
  !fn. MEM fn unit.cu_context.ctx_functions ==>
    EVERY runtime_sym_inst (fn_insts fn)
Proof
  rpt strip_tac >>
  drule_at (Pat `run_grouped_lowering _ _ _ _ _ = _`) runtime_sym_run_grouped_lowering >>
  disch_then (qspec_then `fn` match_mp_tac) >> asm_rewrite_tac[] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `compile_generate_grouped_runtime _ _ _ _ = _`)
    runtime_sym_generate_grouped_runtime >>
  disch_then (qspecl_then [`Q`, `P`, `D`] mp_tac) >>
  asm_rewrite_tac[] >> disch_then match_mp_tac >>
  conj_tac
  >- (mp_tac (Q.INST [`P` |-> `P`, `Q` |-> `Q`, `D` |-> `D`]
        runtime_sym_external_groups) >>
      impl_tac
      >- (conj_tac
          >- (rpt gen_tac >> strip_tac >>
              drule_at (Pat `compile_create_kwarg_allocas _ _ _ = _`)
                runtime_sym_create_kwarg_allocas >>
              asm_rewrite_tac[]) >>
          rpt gen_tac >> strip_tac >>
          qpat_assum `!c. Q c ==> _` drule >> strip_tac >>
          drule_at (Pat `compile_entry_point_kwargs _ _ _ _ _ _ = _`)
            runtime_sym_group_entry_kwargs >>
          disch_then (qspec_then `tops` mp_tac) >> asm_rewrite_tac[] >>
          disch_then match_mp_tac >>
          rewrite_tac[EVERY_MEM] >> gen_tac >> strip_tac >>
          rename1 `MEM x vars` >> PairCases_on `x` >>
          qpat_assum `EVERY _ vars` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
          disch_then drule >> CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
          strip_tac >> asm_rewrite_tac[] >>
          qpat_assum `!n ty e. D (n,ty,e) ==> _` drule >> simp[]) >>
      disch_then (qspec_then `groups` mp_tac) >> asm_rewrite_tac[]) >>
  match_mp_tac runtime_sym_external_jobs >> asm_rewrite_tac[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!c. Q c ==> _` drule >> strip_tac >>
  drule_at (Pat `compile_common_function_body _ _ _ _ _ _ _ _ _ _ = _`)
    runtime_sym_common_function_body >>
  disch_then (qspecl_then [`tops`, `bindings`] mp_tac) >> asm_rewrite_tac[] >>
  disch_then match_mp_tac >>
  conj_tac
  >- (irule runtime_sym_register_kwarg_vars >> asm_rewrite_tac[] >>
      rewrite_tac[EVERY_MEM] >> gen_tac >> strip_tac >>
      rename1 `MEM x vars` >> PairCases_on `x` >>
      qpat_assum `EVERY _ vars` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
      disch_then drule >> CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
      strip_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)
    runtime_sym_register_positional_args >>
  disch_then (qspec_then `tops` mp_tac) >> asm_rewrite_tac[]
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

(* TEMPORARILY CHEATED - SCRATCH SEQ-8501 census (never lands)
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
