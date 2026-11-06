Theory extRetEvaluatedStaticPtr
Ancestors extRetStaticPlanSelectionPtr extRetStaticCapacityPtr
  extRetStaticBoundedConsumerPtr extRetTypedStaticConsumerPtr
  structFieldsProps retAbiPlanProps vyperABI vyperContext
  returnMetadataPtr compileEnv compileVyper
  extRetStaticStmtPtr extRetSomeComposePtr extRetNormalEvidencePtr
  extRetCopyInputsPtr bodyPtrDefs exprOperandVar stmtSimReturn
  loweringPosts gasSummaryComposePtr typedCopyPtr

val _ = Parse.hide "body";

Theorem evaluated_static_map_props[local]:
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  evaluate_type (type_env tops) ret = SOME tv /\
  ~is_abi_dynamic (make_struct_fields_map tops) ret ==>
  ~is_dynamic (vyper_to_abi_type (type_env tops) ret) /\
  abi_size_bound (make_struct_fields_map tops) ret = type_memory_size tv
Proof
  strip_tac >>
  `sfields_tenv_consistent (make_struct_fields_map tops) (type_env tops)` by
    simp[make_struct_fields_map_consistent] >>
  `!k a. FLOOKUP (type_env tops) k = SOME (StructArgs a) ==> FST k = NONE` by
    (rw[type_env_def] >> drule type_env_for_module_struct_mem >> rw[] >> simp[]) >>
  drule (cj 1 abi_props_vyper) >>
  disch_then (qspec_then `make_struct_fields_map tops` mp_tac) >>
  simp[] >> strip_tac >>
  drule (cj 1 evaluated_abi_dynamic) >> strip_tac >>
  `~is_dynamic (vyper_to_abi_type (type_env tops) ret)` by metis_tac[] >>
  drule_all evaluated_static_abi_memory_size >> simp[]
QED

Theorem external_frame_evaluated_static_metadata:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, body)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\ source_typing_ok tops am tx /\
  evaluate_type (type_env tops) ret = SOME tv /\ ret <> NoneT /\
  ~is_abi_dynamic next.ce_struct_fields ret ==>
  next.ce_ret_enc_info = AbiCopy (type_memory_size tv) /\
  next.ce_max_return_size = type_memory_size tv /\
  ~is_dynamic (vyper_to_abi_type (type_env tops) ret)
Proof
  strip_tac >>
  drule_all external_frame_struct_fields >> strip_tac >>
  drule source_typing_distinct_type_keys >> strip_tac >>
  `~is_abi_dynamic (make_struct_fields_map tops) ret` by metis_tac[] >>
  drule_all evaluated_static_map_props >> strip_tac >>
  drule_all external_frame_type_memory_bytes >> strip_tac >>
  drule_all external_frame_static_copy_selection >> strip_tac >>
  drule_all register_same_frame_metadata >>
  simp[compile_env_component_equality] >> strip_tac >>
  qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
  simp[package_external_fn_def, set_external_package_target_def,
       update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
       build_compile_env_ce_struct_fields] >> strip_tac >>
  gvs[compile_env_component_equality]
QED

Theorem external_frame_evaluated_static_stmt_frag_ptr:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, fbody)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut', view, fbody', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\ source_typing_ok tops am tx /\
  evaluate_type (type_env tops) ret = SOME tv /\ ret <> NoneT /\
  ~is_abi_dynamic next.ce_struct_fields ret /\
  get_tenv cx = type_env tops /\ expr_type e = ret /\
  lowered_value_type next e = ret /\ ~is_word_type ret /\
  next.ce_return_pc = NONE /\ ~next.ce_raw_return /\
  next.ce_nonreentrant = (F,nkey,ut,iv) /\
  expr_sim_inv next cx env es /\ well_typed_expr env e /\
  call_evaluation_safe cx (int_calls_expr e) /\
  expr_sim_ptr d ctx PG func next cx ret e es ==>
  stmt_frag_ptr d ctx PG func cx lctx (\v es gt r. T) next
    (stmt_env next lctx ret (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >>
  drule_all external_frame_evaluated_static_metadata >> strip_tac >>
  rw[stmt_frag_ptr_def] >>
  drule external_return_static_copy_stmt_parts >> simp[] >>
  disch_then drule_all >> strip_tac >>
  drule_at (Pat `lower_value _ _ _ _ _ = _`) compile_lower_value_var >>
  simp[] >> disch_then assume_tac >>
  drule return_forced_admissible >> strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_ptr_def] >>
  disch_then (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  dxrule gas_outcome_ptr_normal_evidence >> strip_tac >>
  drule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)
    external_return_some_outcome_ptr >>
  disch_then irule >> rpt gen_tac >> strip_tac >> gvs[] >>
  `ptr_val_ok cx (expr_type e) v op G1 tn1 t` by fs[] >>
  drule_all expr_post_ptr_return_inputs >> strip_tac >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by fs[] >>
  drule_all external_return_forced_value_typed >> strip_tac >>
  `expr_val_at next cx (expr_type e) sa' sm ee v op t` by fs[expr_post_def] >>
  drule_at (Pat `compile_external_return _ _ _ _ _ _ _ _ _ _ = _`)
    compile_external_return_static_copy_equal_gas_path_ptr >>
  simp[] >> disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then drule_all >> simp[]
QED
