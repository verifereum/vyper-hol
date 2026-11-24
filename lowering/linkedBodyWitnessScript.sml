(* The checked linked fixture reaches the body gate in both modes. *)
Theory linkedBodyWitness
Ancestors
  e2eModsWitness e2eModsDefs e2eDeployModsDefs entryModuleLocations
  bodyInvSplit bodyCallSupport compileUnit typedCopyDomain
  supportedProgram supportedDecls supportedStmts vyperContext vyperInterpreter
  vyperTypeContractStaticMaps vyperTypeContract vyperTypeCallGraph
  vyperTypeCallStackSoundness vyperTypeCallGraphSoundness vyperTypeContractContext
  constSubst vyperTypeConstantFold
  vyperOriginFold supportedTypes supportedStmtTraverse pair
  alist finite_map list combin
Libs
  computeLib finite_mapLib intReduce cv_transLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset intReduce.add_int_compset

(* Native CV evaluation supplies the fixture's selector hashes. *)
val () = computeLib.add_funs (map cv_eval [
  ``function_selector "bar" []``,
  ``function_selector "get_x" []``,
  ``function_selector "locked_get_x" []``])

val reduce_fold = DEPTH_CONV (fn tm =>
  if is_comb tm andalso same_const (rator tm) ``origin_fold_value``
  then cv_eval tm else NO_CONV tm)
val linked_mods_normalized =
  CONV_RULE (RAND_CONV (reduce_fold THENC EVAL)) linked_witness_mods_def

val eval_linked_fixture = REWRITE_CONV [linked_mods_normalized] THENC EVAL
Triviality linked_witness_headers:
  EVERY (supported_module_headers o SND) linked_witness_mods
Proof
  simp[linked_mods_normalized, supported_module_headers_def,
       supported_module_declaration_header_def, supported_declaration_header_def,
       supported_function_return_def] >>
  EVAL_TAC >>
  simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def,
       wordsTheory.dimindex_8, wordsTheory.dimindex_32]
QED
val linked_witness_main_support = EQT_ELIM (eval_linked_fixture
  ``supported_program (main_module linked_witness_mods) /\
    supported_program_deploy (main_module linked_witness_mods)``)
val linked_witness_struct_fields = eval_linked_fixture
  ``make_struct_fields_map_mods linked_witness_mods``

Theorem linked_witness_imported_constructor:
  ?tops. ALOOKUP linked_witness_mods (SOME 2) = SOME tops /\
    supported_linked_callee T tops (SOME 2,"__init__") /\
    ~supported_linked_callee F tops (SOME 2,"__init__")
Proof
  simp[linked_mods_normalized, ALOOKUP_def] >> EVAL_TAC
QED

Triviality linked_witness_lowering:
  !deploy. ?p unit.
    if deploy then
      ?rbc. lower_vyper_deploy_unit_mods linked_witness_mods
        linked_witness_exports p rbc = SOME unit
    else lower_vyper_runtime_unit_mods linked_witness_mods
      linked_witness_exports p = SOME unit
Proof
  mp_tac (cj 2 linked_witness_deploy_premises) >>
  simp[compile_vyper_mods_def, compile_vyper_with_mods_def, AllCaseEqs()] >>
  rpt strip_tac >> Cases_on `deploy` >> metis_tac[]
QED

Triviality linked_witness_distinct_modules:
  IS_SOME (ALOOKUP linked_witness_mods NONE) /\
  ALL_DISTINCT (MAP FST linked_witness_mods) /\
  ALL_DISTINCT (contract_keys toplevel_vtype_keys_toplevel linked_witness_mods)
Proof
  EVAL_TAC
QED

Triviality linked_witness_closed_bodies:
  !in_deploy src tops vis mut nr raw name args dflts ret ss.
    ALOOKUP linked_witness_mods src = SOME tops /\
    MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops ==>
    function_mutability_ok linked_witness_mods vis mut nr dflts ss /\
    (in_deploy /\ vis = Deploy ==> EVERY (supported_value_type tops o SND) args) /\
    supported_declaration_body tops (FunctionDecl vis mut nr raw name args dflts ret ss) /\
    (in_deploy ==> supported_deploy_declaration tops (FunctionDecl vis mut nr raw name args dflts ret ss)) /\
    (check_function_body_in_mode in_deploy vis ==>
      EVERY (\call. ?callee.
        ALOOKUP linked_witness_mods (FST call) = SOME callee /\
        supported_linked_callee in_deploy callee call)
        (function_int_calls dflts ss))
Proof
  rpt gen_tac >> Cases_on `src` >> Cases_on `in_deploy` >>
  simp[linked_mods_normalized, ALOOKUP_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[check_function_body_in_mode_def] >> EVAL_TAC >>
  simp[] >> EVAL_TAC
QED

Theorem linked_witness_contract_inv:
  ALOOKUP cx.sources cx.txn.target = SOME linked_witness_mods /\
  cx.nonreentrant_slot = SOME global_nonreentrant_slot /\
  layouts_agree_mods linked_witness_mods linked_witness_exports am tx ==>
  !src. ?ctx ce. contract_inv linked_witness_mods linked_witness_exports ctx ce cx /\
    ce.ce_module = src
Proof
  strip_tac >> gen_tac >>
  qspec_then `cx.in_deploy` strip_assume_tac linked_witness_lowering >>
  qabbrev_tac `ce = build_compile_env_unit linked_witness_mods src
      (if cx.in_deploy then Deploy else External) Nonpayable ""
      [] NoneT [] T with ce_target := p.rpol_target` >>
  qexistsl [`unit.cu_context`, `ce`] >>
  `acyclic_struct_metadata ce.ce_struct_fields` by
    simp[Abbr `ce`, build_compile_env_unit_def, pairTheory.ELIM_UNCURRY,
         linked_witness_struct_fields, acyclic_struct_metadata_def,
         finite_mapTheory.FEVERY_FEMPTY] >>
  `immutable_section_layout_mods linked_witness_mods ce` by
    (irule unit_module_locations_immutable_layout >>
     simp[Abbr `ce`, build_compile_env_unit_def, pairTheory.ELIM_UNCURRY,
          linked_witness_distinct_modules] >>
     metis_tac[]) >>
  simp[contract_inv_def, cenv_module_pins_mods_def, Abbr `ce`,
       build_compile_env_unit_def, get_tenv_def, pairTheory.ELIM_UNCURRY, LET_THM,
       linked_witness_distinct_modules, GSYM contract_keys_def] >>
  rpt conj_tac
  >- (qx_genl_tac [`module_src`, `tops`] >> strip_tac >>
      `MEM (module_src,tops) linked_witness_mods` by
        (drule_then ACCEPT_TAC ALOOKUP_MEM) >>
      `supported_module_headers tops` by
        (mp_tac linked_witness_headers >> simp[EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
      simp[] >> conj_tac
      >- (strip_tac >>
          `main_module linked_witness_mods = tops` by
            (simp[main_module_def] >> BasicProvers.every_case_tac >> gvs[]) >>
          metis_tac[linked_witness_main_support]) >>
      irule vyperTypeContractTheory.contract_keys_module_distinct >>
      qexists_tac `linked_witness_mods` >> simp[linked_witness_distinct_modules])
  >- (qexistsl [`p`, `unit`] >> simp[])
  >- (strip_tac >> EVAL_TAC)
  >- (simp[linked_body_calls_resolved_def] >>
      metis_tac[linked_witness_closed_bodies])
  >- (Cases_on `cx.in_deploy` >> simp[])
  >- (rpt strip_tac >> metis_tac[linked_witness_closed_bodies])
  >- (rpt strip_tac >> metis_tac[linked_witness_closed_bodies])
  >> fs[]
QED

(* These are the support and resolution premises at the entry boundary.
   The frame and return hypotheses belong to the simulation of that entry. *)
Theorem linked_witness_entry_support:
  ALOOKUP linked_witness_mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops /\
  (vis = Deploy \/ vis = External) /\
  (vis = Deploy ==> cx.in_deploy) /\
  ALOOKUP cx.sources cx.txn.target = SOME linked_witness_mods /\
  cx.nonreentrant_slot = SOME global_nonreentrant_slot /\
  layouts_agree_mods linked_witness_mods linked_witness_exports am tx /\
  cx.stk = [(src,name)] /\
  context_function_live cx (src,name) /\
  check_contract cx.in_deploy cx.layouts cx.txn.target linked_witness_mods =
    SOME art ==>
  (?ctx ce. contract_inv linked_witness_mods linked_witness_exports ctx ce cx /\
    module_body_inv linked_witness_mods src tops ce cx) /\
  supported_stmts tops (args ++ supported_stmts_bindings T ss ++
    supported_stmts_bindings F ss) ss /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) ss ==>
    EXISTS (occurs_abi_decode_target target o SND) linked_witness_mods) /\
  (?env'. type_stmts (function_entry_env art linked_witness_mods src vis args)
    ret (subst_consts_stmts_mods (consts_env_mods linked_witness_mods) ss) = SOME env') /\
  call_evaluation_safe cx (int_calls_stmts ss) /\
  EVERY (\call. ?callee.
    ALOOKUP linked_witness_mods (FST call) = SOME callee /\
    supported_linked_callee cx.in_deploy callee call)
    (function_int_calls dflts ss)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qspec_then `src` strip_assume_tac) linked_witness_contract_inv >>
  `check_function_body_in_mode cx.in_deploy vis` by
    metis_tac[check_function_body_in_mode_def] >>
  drule_all_then (qspec_then `cx.in_deploy` strip_assume_tac)
    linked_witness_closed_bodies >>
  `function_live cx.layouts cx.txn.target linked_witness_mods
      (live_functions cx.layouts cx.txn.target linked_witness_mods) (src,name)` by
    (qpat_assum `context_function_live cx (src,name)`
       (mp_tac o REWRITE_RULE [context_function_live_def]) >>
     qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME linked_witness_mods`
       (fn sources => simp[NoAsms, sources])) >>
  drule_all_then assume_tac check_contract_function_body_MEM >>
  `MEM (src,tops) linked_witness_mods` by metis_tac[ALOOKUP_MEM] >>
  rpt conj_tac
  >- (qexistsl [`ctx`, `ce`] >> simp[module_body_inv_def])
  >- (Cases_on `vis` >> gvs[supported_declaration_body_def,
        supported_deploy_declaration_def, supported_function_body_def, LET_THM,
        APPEND_ASSOC])
  >- (rpt strip_tac >>
      simp[EXISTS_MEM, occurs_abi_decode_target_def,
           declaration_abi_decode_target_def] >>
      qexists_tac `(src,tops)` >> simp[] >>
      qexists_tac `FunctionDecl vis mut nr raw name args dflts ret ss` >>
      simp[declaration_abi_decode_target_def])
  >- fs[check_function_body_def, LET_THM, optionTheory.IS_SOME_EXISTS]
  >- (`calls_follow_call_graph (contract_call_edges linked_witness_mods)
          (src,name) (int_calls_stmts ss)` by
        (simp[NoAsms, calls_follow_call_graph_def, EVERY_MEM, call_edge_rel_def] >>
         rpt strip_tac >> irule contract_call_edges_function >>
         qexistsl [`args`, `ss`, `dflts`, `mut`, `nr`, `raw`, `ret`, `tops`, `vis`] >>
         simp[function_int_calls_def]) >>
      `cx = cx with stk := [(src,name)]` by
        simp[vyperContextTheory.evaluation_context_component_equality] >>
      pop_assum SUBST1_TAC >>
      irule checked_contract_call_evaluation_safe_singleton >>
      qexistsl [`art`, `cx.layouts`, `linked_witness_mods`] >> simp[])
  >> simp[]
QED
