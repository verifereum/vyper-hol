(* Capacity at the compiler's unmodified VV tag, and the live copy size. *)
Theory createBlueprintRawCopyLayoutMods
Ancestors
  createBlueprintRawCopyLayout createExprSizeExitDefsMods
  exprBodyPreProps exprReasonOperand exprSimIfExp exprSimHyps
  immutableDeployPhysicalSource abiEncodeArgsCase valueCopyBytes
  valueEncodingTyping vyperValue vyperTypeSystem
  exprSimHypsDefs exprSimProps context compileEnv
  createCtorMaterializePhysicalMods bodySimStmtFacts vyperTypeEvalCaseProofs
  vyperTypeExprSoundness exprSimIfExpCompat exprSimSource allocLimits
  valueLoadProps exprLowering

Theorem create_blueprint_raw_copy_layout_mods:
  expr_type e = BaseT (BytesT (Dynamic k)) /\
  expr_body_pre_mods mods ce cx env e es /\
  compile_expr ce (expr_type e) e ca = (vv,cm) /\
  bind (eval_expr cx e) (read_result cx) es = (INL (BytesV bytes),ee) ==>
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  value_has_type (BaseTV (BytesT (Dynamic k))) (BytesV bytes) /\
  ?p q.
    lowered_value_type ce e = BaseT (BytesT (Dynamic p)) /\
    vv_type vv = BaseT (BytesT (Dynamic q)) /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) =
      SOME (BaseTV (BytesT (Dynamic p))) /\
    evaluate_type (get_tenv cx) (vv_type vv) =
      SOME (BaseTV (BytesT (Dynamic q))) /\
    value_has_type (BaseTV (BytesT (Dynamic p))) (BytesV bytes) /\
    value_has_type (BaseTV (BytesT (Dynamic q))) (BytesV bytes) /\
    val_wf (BaseTV (BytesT (Dynamic p))) (BytesV bytes) /\
    val_wf (BaseTV (BytesT (Dynamic q))) (BytesV bytes) /\
    type_memory_bytes ce (vv_type vv) = type_memory_size (BaseTV (BytesT (Dynamic q))) /\
    type_memory_size (BaseTV (BytesT (Dynamic q))) < 2 ** 64 /\
    type_memory_size (BaseTV (BytesT (Dynamic q))) + 64 < dimword (:256) /\
    val_store_size (BaseTV (BytesT (Dynamic p))) (BytesV bytes) =
      val_store_size (BaseTV (BytesT (Dynamic q))) (BytesV bytes) /\
    val_store_size (BaseTV (BytesT (Dynamic p))) (BytesV bytes) <=
      type_memory_size (BaseTV (BytesT (Dynamic p))) /\
    val_store_size (BaseTV (BytesT (Dynamic q))) (BytesV bytes) <=
      type_memory_size (BaseTV (BytesT (Dynamic q)))
Proof
  strip_tac >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  drule expr_sim_inv_mods_env >> strip_tac >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  drule_all (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >> strip_tac >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
     SOME (BaseTV (BytesT (Dynamic k))) /\
   value_has_type (BaseTV (BytesT (Dynamic k))) (BytesV bytes)` by
    (gvs[value_runtime_typed_def] >>
     drule evaluate_type_base_identity >> strip_tac >> gvs[]) >>
  drule_all ctor_physical_bound_read_type_mods >> strip_tac >>
  drule expr_body_pre_mods_well_typed >> strip_tac >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    metis_tac[env_consistent_var_type_evaluates, well_formed_type_def] >>
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
       ce.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    metis_tac[expr_sim_inv_mods_return_type] >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    fs[expr_sim_inv_mods_def] >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    (drule_all ifexp_lowered_type_classify >> strip_tac >>
     gvs[ifexp_arg_type_fits_refl] >> PairCases_on `fid` >>
     gvs[well_typed_expr_def, lowered_value_type_def, vyperASTTheory.expr_type_def] >>
     first_x_assum (drule_then SUBST1_TAC) >> fs[type_widens_to_def]) >>
  `?p. lowered_value_type ce e = BaseT (BytesT (Dynamic p))` by
    (qpat_x_assum `arg_type_fits _ _` mp_tac >> simp[] >>
     Cases_on `lowered_value_type ce e` >> simp[arg_type_fits_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[arg_type_fits_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> simp[arg_type_fits_def]) >>
  pop_assum strip_assume_tac >>
  `tv = BaseTV (BytesT (Dynamic p))` by
    (qpat_x_assum `evaluate_type _ (lowered_value_type ce e) = _` mp_tac >>
     asm_rewrite_tac[] >> metis_tac[valueLoadPropsTheory.evaluate_type_base_identity]) >>
  `type_memory_bytes ce (expr_type e) < 2 ** 64` by
    (`type_alloc_ok ce (expr_type e)` by
       metis_tac[expr_body_pre_mods_def, alloc_limits_expr_type_alloc_ok] >>
     gvs[type_alloc_ok_def, is_word_type_def]) >>
  `type_memory_bytes ce (lowered_value_type ce e) <= type_memory_bytes ce (expr_type e)` by
    (irule (cj 1 abi_args_fits_memory_bytes) >> simp[]) >>
  `vv_type vv = expr_type e \/ vv_type vv = lowered_value_type ce e` by
    (`reason_uniform_shape compile_expr ce (expr_type e) e` by
       (irule compile_expr_reason_uniform >> qexists `env` >> fs[expr_sim_inv_mods_def]) >>
     pop_assum (strip_assume_tac o REWRITE_RULE [reason_uniform_shape_def]) >>
     qpat_x_assum `!sa vv sb. _ ==> reason_result_shape _ _ _` (drule_then assume_tac) >>
     Cases_on `vv` >> gvs[reason_result_shape_def, vv_type_def]) >>
  `!n. type_memory_bytes ce (BaseT (BytesT (Dynamic n))) =
       type_memory_size (BaseTV (BytesT (Dynamic n)))` by
    simp[compileEnvTheory.type_memory_bytes_def, valueEncodingTheory.type_memory_size_def,
         vfmConstantsTheory.word_size_def] >>
  `type_memory_size (BaseTV (BytesT (Dynamic k))) < 2 ** 64 /\
   type_memory_size (BaseTV (BytesT (Dynamic p))) < 2 ** 64` by
    (gvs[] >> decide_tac) >>
  gvs[wordsTheory.dimword_def, value_has_type_val_wf, val_store_size_le] >>
  simp[val_store_size_def] >> decide_tac
QED
