Theory extRetSignatureFramePtr
Ancestors
  memoryLocalRhsProps vyperTypeInvariants vyperTypeContractStaticMaps
  compileVyper supportedNames finite_map e2eDefs vyperContext vyperInterpreter
  returnMetadataPtr bodySim

val _ = Parse.hide "body";

Theorem same_module_signature_return_map:
  ALL_DISTINCT (supported_function_names tops) /\ ~cx.in_deploy /\
  get_module_code cx NONE = SOME tops /\ fn_sigs_consistent env.fn_sigs cx /\
  FLOOKUP env.fn_sigs (NONE,name) = SOME sig ==>
  build_func_return_type tops name = sig.ret_ty
Proof
  strip_tac >>
  qpat_x_assum `fn_sigs_consistent _ _` mp_tac >>
  simp[fn_sigs_consistent_def] >>
  disch_then drule >> strip_tac >> gvs[] >>
  drule lookup_callable_function_F_SOME_MEM >> strip_tac >>
  irule build_func_return_type_distinct >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem initial_signature_namespace:
  source_deployment_rel tops am tx /\
  fn_sigs_consistent env.fn_sigs
    (initial_evaluation_context am.sources am.layouts tx NONE) /\
  FLOOKUP env.fn_sigs (src,name) = SOME sig ==>
  src = NONE
Proof
  strip_tac >>
  qpat_x_assum `fn_sigs_consistent _ _` mp_tac >>
  simp[fn_sigs_consistent_def] >> disch_then drule >> strip_tac >>
  gvs[source_deployment_rel_def, get_module_code_def,
      initial_evaluation_context_def] >>
  Cases_on `src` >> gvs[]
QED

Theorem initial_signature_return_map:
  ALL_DISTINCT (supported_function_names tops) /\
  source_deployment_rel tops am tx /\
  fn_sigs_consistent env.fn_sigs
    (initial_evaluation_context am.sources am.layouts tx NONE) /\
  FLOOKUP env.fn_sigs (src,name) = SOME sig ==>
  build_func_return_type tops (nsid_to_string (src,name)) = sig.ret_ty
Proof
  strip_tac >> drule_all initial_signature_namespace >> strip_tac >>
  gvs[compileEnvTheory.nsid_to_string_def] >>
  irule same_module_signature_return_map >> conj_tac >- simp[] >>
  qexistsl [`initial_evaluation_context am.sources am.layouts tx NONE`, `env`] >>
  simp[initial_evaluation_context_def] >>
  gvs[source_deployment_rel_def, get_module_code_def,
      initial_evaluation_context_def]
QED

Theorem external_frame_function_return_map:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, body)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next ==>
  next.ce_func_return_type = build_func_return_type tops
Proof
  strip_tac >>
  `cenv0.ce_func_return_type = build_func_return_type tops` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[package_external_fn_def, set_external_package_target_def] >>
     Cases_on `ret = NoneT` >>
     simp[update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
          build_compile_env_ce_func_return_type] >> strip_tac >>
     gvs[build_compile_env_ce_func_return_type]) >>
  drule_all register_same_frame_metadata >>
  simp[compileEnvTheory.compile_env_component_equality]
QED

Theorem external_frame_signature_return_map:
  supported_program tops /\ source_deployment_rel tops am tx /\
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, body)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\
  expr_sim_inv next
    (initial_evaluation_context am.sources am.layouts tx NONE) env es /\
  FLOOKUP env.fn_sigs id = SOME sig ==>
  next.ce_func_return_type (nsid_to_string id) = sig.ret_ty
Proof
  strip_tac >> drule_all external_frame_function_return_map >> strip_tac >>
  gvs[] >> PairCases_on `id` >>
  irule initial_signature_return_map >>
  conj_tac
  >- (drule supportedProgramTheory.supported_program_names >>
      simp[supportedNamesTheory.supported_declaration_names_def]) >>
  qexistsl [`am`, `env`, `tx`] >> simp[] >>
  gvs[exprSimHypsDefsTheory.expr_sim_inv_def, env_consistent_def,
      env_context_consistent_def]
QED
