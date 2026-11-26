(* The raw snapshot uses the actual VV tag; the source read may use a
   different dynamic-bytes capacity. *)
Theory bodyCreateBlueprintRawTypeMods
Ancestors
  bodyCopyReadPhysicalTypeMods exprBodyPreProps exprReasonOperand
  exprSimHyps abiEncodeArgsCase typeLayoutProps abiValueEncoding
  valueEncodingTyping vyperTyping vyperTypeSystem words compileEnv context
  exprSimHypsDefs exprSimProps allocLimits valueEncoding loweringPosts

Theorem blueprint_raw_read_tag_mods:
  expr_body_pre_mods mods ce cx env e es /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) ==>
  post_value_type ce e = expr_type e /\
  evaluate_type (get_tenv cx) (post_value_type ce e) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  value_has_type (BaseTV (BytesT (Dynamic cap))) v /\
  ~is_word_type (vv_type vv) /\
  ?bs lk dk.
    v = BytesV bs /\ LENGTH bs < 2 ** 64 /\
    lowered_value_type ce e = BaseT (BytesT (Dynamic lk)) /\
    vv_type vv = BaseT (BytesT (Dynamic dk)) /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) =
      SOME (BaseTV (BytesT (Dynamic lk))) /\
    evaluate_type (get_tenv cx) (vv_type vv) =
      SOME (BaseTV (BytesT (Dynamic dk))) /\
    value_has_type (BaseTV (BytesT (Dynamic lk))) v /\
    value_has_type (BaseTV (BytesT (Dynamic dk))) v /\
    LENGTH bs <= lk /\ LENGTH bs <= dk /\
    val_wf (BaseTV (BytesT (Dynamic lk))) v /\
    val_wf (BaseTV (BytesT (Dynamic dk))) v /\
    type_memory_bytes ce (lowered_value_type ce e) =
      type_memory_size (BaseTV (BytesT (Dynamic lk))) /\
    type_memory_bytes ce (vv_type vv) = type_memory_size (BaseTV (BytesT (Dynamic dk))) /\
    0 < type_memory_bytes ce (lowered_value_type ce e) /\
    type_memory_bytes ce (lowered_value_type ce e) < 2 ** 64 /\
    0 < type_memory_bytes ce (vv_type vv) /\
    type_memory_bytes ce (vv_type vv) < 2 ** 64 /\
    val_store_size (BaseTV (BytesT (Dynamic lk))) v =
      val_store_size (BaseTV (BytesT (Dynamic dk))) v
Proof
  strip_tac >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  `post_value_type ce e = expr_type e` by simp[is_bytestring_type_def] >>
  drule_all copy_read_physical_type_gas_obs_mods >>
  disch_then (strip_assume_tac o cj 3) >>
  `pt = BaseTV (BytesT (Dynamic cap))` by
    metis_tac[evaluate_type_base_result] >>
  `?bs. v = BytesV bs /\ LENGTH bs <= cap` by
    (Cases_on `v` >> gvs[value_has_type_def]) >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  drule expr_body_pre_mods_well_typed >> strip_tac >>
  drule_all copy_lowered_fits_mods >> strip_tac >>
  `?lk. lowered_value_type ce e = BaseT (BytesT (Dynamic lk))` by
    (qpat_x_assum `arg_type_fits _ (expr_type e)` mp_tac >> simp[] >>
     Cases_on `lowered_value_type ce e` >> simp[arg_type_fits_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[arg_type_fits_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> simp[arg_type_fits_def]) >>
  `rt = BaseTV (BytesT (Dynamic lk))` by metis_tac[evaluate_type_base_result] >>
  `type_memory_bytes ce (expr_type e) < 2 ** 64` by
    (`alloc_limits_expr ce e` by fs[expr_body_pre_mods_def] >>
     drule alloc_limits_expr_type_alloc_ok >> simp[type_alloc_ok_def]) >>
  `type_memory_bytes ce (lowered_value_type ce e) < 2 ** 64` by
    (`type_memory_bytes ce (lowered_value_type ce e) <= type_memory_bytes ce (expr_type e)` by
       metis_tac[cj 1 abi_args_fits_memory_bytes] >>
     decide_tac) >>
  `type_memory_bytes ce (expr_type e) = type_memory_size pt` by
    (fs[] >> metis_tac[type_memory_bytes_base_evaluated]) >>
  `type_memory_size (BaseTV (BytesT (Dynamic cap))) < 2 ** 64` by metis_tac[] >>
  `LENGTH bs < 2 ** 64` by
    (qspec_then `cap` assume_tac le_word_size_mul >>
     qpat_x_assum `type_memory_size (BaseTV (BytesT (Dynamic cap))) < _` mp_tac >>
     simp[type_memory_size_def,NoAsms] >> decide_tac) >>
  `vv_type vv = expr_type e \/ vv_type vv = lowered_value_type ce e` by
    (`reason_uniform_shape compile_expr ce (expr_type e) e` by
       (irule compile_expr_reason_uniform >> qexists `env` >> fs[expr_sim_inv_mods_def]) >>
     pop_assum (strip_assume_tac o REWRITE_RULE [reason_uniform_shape_def]) >>
     qpat_x_assum `!sa vv sb. _ ==> reason_result_shape _ _ _` (drule_then assume_tac) >>
     Cases_on `vv` >> gvs[reason_result_shape_def,vv_type_def]) >>
  `val_wf (BaseTV (BytesT (Dynamic cap))) v /\
   val_wf (BaseTV (BytesT (Dynamic lk))) v` by
    metis_tac[cj 1 value_has_type_val_wf] >>
  Cases_on `vv_type vv = expr_type e` >>
  gvs[is_word_type_def,value_has_type_def,type_memory_size_def,val_store_size_def]
QED
