Theory bodyPtrTypeBuiltinsBodyTyping
Ancestors bodySim exprSimHypsDefs memoryLocalRhsProps vyperTypeEvalSoundness
  vyperTypeExprSoundness vyperTypeInvariants vyperTypeSystem vyperInterpreter
  vyperState vyperAST exprLowering compileEnv valueTypingMemoryProps
  abiTypeBoundProps
Libs monadsyntax

Theorem body_frame_signature_well_formed:
  expr_sim_inv cenv cx env es /\ FLOOKUP env.fn_sigs id = SOME sig ==>
  well_formed_type env.type_defs sig.ret_ty
Proof
  strip_tac >>
  `env_consistent env cx es /\ functions_well_typed cx` by
    gvs[expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx /\ fn_sigs_consistent env.fn_sigs cx` by
    (qpat_x_assum `env_consistent _ _ _` mp_tac >>
     simp[env_consistent_def, env_context_consistent_def]) >>
  Cases_on `id` >>
  qpat_assum `fn_sigs_consistent _ _` mp_tac >>
  pure_rewrite_tac[fn_sigs_consistent_def] >>
  disch_then drule >> strip_tac >>
  `IS_SOME (FLOOKUP env.fn_sigs (q,r))` by simp[] >>
  drule_all callable_body_typing_from_env_consistent >>
  simp[] >> strip_tac >> simp[well_formed_type_def]
QED

Theorem body_internal_annotation_eval:
  !cx a b id args drv.
  eval_expr cx (Call a (IntCall id) args drv) =
  eval_expr cx (Call b (IntCall id) args drv)
Proof
  rpt gen_tac >> Cases_on `id` >> once_rewrite_tac[evaluate_def] >> REFL_TAC
QED

Theorem body_internal_read_signature_typed:
  expr_body_pre cenv cx env (Call ann (IntCall id) args drv) es /\
  FLOOKUP env.fn_sigs id = SOME sig /\
  (do r <- eval_expr cx (Call ann (IntCall id) args drv);
      read_result cx r od) es = (INL v,ee) ==>
  value_runtime_typed env sig.ret_ty v
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `well_formed_type env.type_defs sig.ret_ty` by
    (drule_all body_frame_signature_well_formed >> simp[]) >>
  `well_typed_expr env (Call sig.ret_ty (IntCall id) args drv)` by
    (Cases_on `id` >>
     gvs[expr_body_pre_def, well_typed_expr_def, type_widens_to_def] >>
     metis_tac[]) >>
  `(do r <- eval_expr cx (Call sig.ret_ty (IntCall id) args drv);
      read_result cx r od) es = (INL v,ee)` by
    metis_tac[body_internal_annotation_eval] >>
  drule_at (Pat `bind _ _ _ = _`) eval_expr_read_type_sound >>
  disch_then (qspec_then `env` mp_tac) >>
  gvs[expr_body_pre_def, expr_sim_inv_def, vyperTypeCallGraphTheory.int_calls_expr_def, expr_type_def]
QED

Theorem body_runtime_signature_return:
  body_inv tops ctx cenv cx /\ ~cx.in_deploy /\
  expr_sim_inv cenv cx env es /\ FLOOKUP env.fn_sigs (NONE,id) = SOME sig ==>
  cenv.ce_func_return_type id = sig.ret_ty
Proof
  strip_tac >>
  `fn_sigs_consistent env.fn_sigs cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?fm nr args dflts body.
     lookup_callable_function F id tops = SOME (fm,nr,args,dflts,sig.ret_ty,body)` by
    (qpat_assum `fn_sigs_consistent _ _` mp_tac >>
     pure_rewrite_tac[fn_sigs_consistent_def] >> disch_then drule >> strip_tac >>
     gvs[body_inv_def] >> simp[SF SFY_ss]) >>
  drule vyperTypeContractStaticMapsTheory.lookup_callable_function_F_SOME_MEM >>
  strip_tac >>
  `ALL_DISTINCT (supported_function_names tops)` by
    (gvs[body_inv_def] >>
     metis_tac[supportedProgramTheory.supported_program_names,
               supportedNamesTheory.supported_declaration_names_unique]) >>
  `build_func_return_type tops id = sig.ret_ty` by
    (irule build_func_return_type_distinct >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  gvs[body_inv_def]
QED

Theorem body_runtime_internal_lowered_typed:
  body_inv tops ctx cenv cx /\ ~cx.in_deploy /\
  expr_body_pre cenv cx env (Call ann (IntCall id) args drv) es /\
  (do r <- eval_expr cx (Call ann (IntCall id) args drv);
      read_result cx r od) es = (INL v,ee) ==>
  value_runtime_typed env (lowered_value_type cenv (Call ann (IntCall id) args drv)) v
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es /\
   well_typed_expr env (Call ann (IntCall id) args drv)` by
    gvs[expr_body_pre_def] >>
  `FST id = NONE` by
    gvs[expr_body_pre_def, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  `?sig. FLOOKUP env.fn_sigs id = SOME sig` by
    (Cases_on `id` >> gvs[well_typed_expr_def, optionTheory.IS_SOME_EXISTS]) >>
  drule_all body_internal_read_signature_typed >>
  Cases_on `id` >> gvs[] >>
  drule_all body_runtime_signature_return >> simp[lowered_value_type_def, nsid_to_string_def]
QED

Theorem body_bytes_literal_lowered_typed:
  expr_body_pre cenv cx env (Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) es /\
  (do r <- eval_expr cx (Literal (BaseT (BytesT (Dynamic n))) (BytesL bs));
      read_result cx r od) es = (INL v,ee) ==>
  value_runtime_typed env (BaseT (BytesT (Dynamic (LENGTH bs)))) v
Proof
  strip_tac >>
  gvs[Once evaluate_def, bind_def, return_def, read_result_def,
      vyperValueOperationTheory.evaluate_literal_def] >>
  gvs[expr_body_pre_def, well_typed_expr_def, well_typed_literal_def,
      well_formed_type_def, vyperValueTheory.evaluate_type_def] >>
  simp[value_runtime_typed_def, vyperValueTheory.evaluate_type_def,
       vyperTypingTheory.value_has_type_def, vyperValueTheory.compatible_bound_def] >>
  gvs[vyperValueTheory.type_slot_size_def, vyperValueTheory.compatible_bound_def] >>
  imp_res_tac exprSimHypsTheory.word_size_monotone >> decide_tac
QED

Theorem body_string_literal_lowered_typed:
  expr_body_pre cenv cx env (Literal (BaseT (StringT n)) (StringL str)) es /\
  (do r <- eval_expr cx (Literal (BaseT (StringT n)) (StringL str));
      read_result cx r od) es = (INL v,ee) ==>
  value_runtime_typed env (BaseT (StringT (LENGTH str))) v
Proof
  strip_tac >>
  gvs[Once evaluate_def, bind_def, return_def, read_result_def,
      vyperValueOperationTheory.evaluate_literal_def] >>
  gvs[expr_body_pre_def, well_typed_expr_def, well_typed_literal_def,
      well_formed_type_def, vyperValueTheory.evaluate_type_def] >>
  simp[value_runtime_typed_def, vyperValueTheory.evaluate_type_def,
       vyperTypingTheory.value_has_type_def, vyperValueTheory.compatible_bound_def] >>
  gvs[vyperValueTheory.type_slot_size_def, vyperValueTheory.compatible_bound_def] >>
  imp_res_tac exprSimHypsTheory.word_size_monotone >> decide_tac
QED

Theorem body_abi_encode_lowered_typed:
  expr_body_pre cenv cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  (do r <- eval_expr cx (TypeBuiltin ann (AbiEncode ensure mid) target args);
      read_result cx r od) es = (INL v,ee) ==>
  value_runtime_typed env
    (lowered_value_type cenv (TypeBuiltin ann (AbiEncode ensure mid) target args)) v
Proof
  strip_tac >>
  drule exprSimHypsTheory.abi_encode_lowered_well_typed_coherent >> strip_tac >>
  drule_at (Pat `bind _ _ _ = _`) exprSimHypsTheory.type_builtin_read_annotation_typed >>
  simp[] >> disch_then irule >> gvs[expr_body_pre_def] >>
  qexists_tac `cenv` >> simp[]
QED

Theorem body_runtime_read_lowered_typed:
  !cenv e tops ctx cx env es v ee.
  body_inv tops ctx cenv cx /\ ~cx.in_deploy /\ expr_body_pre cenv cx env e es /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) ==>
  value_runtime_typed env (lowered_value_type cenv e) v
Proof
  recInduct lowered_value_type_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> simp[lowered_value_type_def] >>
      drule_all body_string_literal_lowered_typed >> simp[])
  >- (rpt gen_tac >> strip_tac >> simp[lowered_value_type_def] >>
      drule_all body_bytes_literal_lowered_typed >> simp[])
  >- (rpt gen_tac >> strip_tac >> drule_all body_abi_encode_lowered_typed >> simp[])
  >- (rpt gen_tac >> strip_tac >> drule_all body_runtime_internal_lowered_typed >> simp[]) >>
  rpt gen_tac >> strip_tac >> simp[lowered_value_type_def] >>
  drule_all exprSimHypsTheory.memory_rhs_read_annotation_typed >> simp[]
QED

Theorem body_runtime_source_lowered_bytestring:
  !cenv e tops ctx cx env es.
  body_inv tops ctx cenv cx /\ ~cx.in_deploy /\ expr_body_pre cenv cx env e es /\
  is_bytestring_type (expr_type e) ==>
  is_bytestring_type (lowered_value_type cenv e)
Proof
  recInduct lowered_value_type_ind >> rpt strip_tac >>
  gvs[lowered_value_type_def, vyperASTTheory.expr_type_def, is_bytestring_type_def] >>
  `expr_sim_inv cenv cx env es /\
   well_typed_expr env (Call v4 (IntCall func_id) v5 v6)` by
    gvs[expr_body_pre_def] >>
  `FST func_id = NONE` by
    gvs[expr_body_pre_def, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  Cases_on `func_id` >> gvs[] >>
  gvs[well_typed_expr_def, optionTheory.IS_SOME_EXISTS] >>
  drule_all body_runtime_signature_return >> simp[nsid_to_string_def] >>
  metis_tac[type_widens_to_def, compileEnvTheory.arg_type_fits_bytestring_source]
QED

Theorem body_runtime_source_read_lowered_layout:
  body_inv tops ctx cenv cx /\ ~cx.in_deploy /\ expr_body_pre cenv cx env e es /\
  is_bytestring_type (expr_type e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) ==>
  is_bytestring_type (lowered_value_type cenv e) /\
  ?tv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
       value_has_type tv v /\
       type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv
Proof
  strip_tac >> conj_tac
  >- (drule_all body_runtime_source_lowered_bytestring >> simp[]) >>
  drule_all body_runtime_read_lowered_typed >> strip_tac >>
  irule memory_rhs_runtime_layout >> qexistsl_tac [`env`,`es`] >>
  gvs[expr_body_pre_def]
QED
