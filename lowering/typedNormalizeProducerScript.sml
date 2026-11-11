(* Metadata at the actual external Return frame, after argument registration. *)
Theory typedNormalizeProducer
Ancestors
  typedCopyProducer structFieldsProps entryStateRel bodySim allocLimitsProps
  e2eDefs compileEnv compileVyper moduleLowering vyperInterpreter vyperContext

Theorem external_package_struct_fields:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, fbody)) =
    (lbl, cenv, pos_args, min_cds, payable, nr', key, ut, iv, fbody', rt) ==>
  cenv.ce_struct_fields = make_struct_fields_map tops
Proof
  Cases_on `ret = NoneT` >>
  simp[package_external_fn_def, set_external_package_target_def,
       update_cenv_ret_abi_def, update_cenv_nonreentrant_def,
       build_compile_env_ce_struct_fields] >>
  strip_tac >> gvs[build_compile_env_ce_struct_fields]
QED

Theorem external_registered_struct_fields:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, fbody)) =
    (lbl, cenv0, pos_args, min_cds, payable, nr', key, ut, iv, fbody', rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv, sa) ==>
  cenv.ce_struct_fields = make_struct_fields_map tops
Proof
  strip_tac >> drule external_package_struct_fields >> strip_tac >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `cenv = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem checked_return_frame_metadata:
  supported_program tops /\ source_typing_ok tops am tx /\
  cenv.ce_struct_fields = make_struct_fields_map tops ==>
  acyclic_struct_metadata cenv.ce_struct_fields /\
  (!ty tv. evaluate_type (type_env tops) ty = SOME tv ==>
     type_memory_bytes cenv ty = type_memory_size tv)
Proof
  strip_tac >> fs[source_typing_ok_def] >> conj_tac
  >- metis_tac[supported_checked_struct_metadata_acyclic] >>
  rpt strip_tac >> irule make_struct_fields_map_memory_size >>
  simp[] >> metis_tac[checked_contract_struct_args_unique]
QED

Theorem same_frame_return_metadata:
  same_frame cenv c /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  (!ty tv. evaluate_type tenv ty = SOME tv ==>
     type_memory_bytes cenv ty = type_memory_size tv) ==>
  acyclic_struct_metadata c.ce_struct_fields /\
  (!ty tv. evaluate_type tenv ty = SOME tv ==>
     type_memory_bytes c ty = type_memory_size tv)
Proof
  strip_tac >>
  `c.ce_struct_fields = cenv.ce_struct_fields` by
    (fs[same_frame_def, compile_env_component_equality]) >>
  conj_tac >- simp[] >> rpt strip_tac >>
  qpat_x_assum `!ty tv. _` drule >>
  drule type_memory_bytes_frame >> simp[]
QED

Theorem initial_return_frame_metadata:
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  cenv.ce_struct_fields = make_struct_fields_map tops ==>
  acyclic_struct_metadata cenv.ce_struct_fields /\
  (!ty tv.
     evaluate_type
       (get_tenv (initial_evaluation_context am.sources am.layouts tx NONE))
       ty = SOME tv ==>
     type_memory_bytes cenv ty = type_memory_size tv)
Proof
  strip_tac >>
  `get_tenv (initial_evaluation_context am.sources am.layouts tx NONE) =
     type_env tops` by
    (fs[source_deployment_rel_def, get_tenv_def,
        initial_evaluation_context_def, type_env_all_modules_def,
        type_env_def, finite_mapTheory.FUNION_FEMPTY_2]) >>
  drule_all checked_return_frame_metadata >> simp[]
QED
