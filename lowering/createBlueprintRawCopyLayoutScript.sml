(* Capacity at the compiler's unmodified VV tag, and the live copy size. *)
Theory createBlueprintRawCopyLayout
Ancestors
  exprBodyPreProps exprReasonOperand exprSimIfExp exprSimHyps
  immutableDeployPhysicalSource abiEncodeArgsCase valueCopyBytes
  valueEncodingTyping vyperValue vyperTypeSystem
  exprSimHypsDefs exprSimProps context compileEnv

Theorem create_blueprint_raw_copy_layout:
  expr_type e = BaseT (BytesT (Dynamic k)) /\
  expr_body_pre ce cx env e es /\
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
  drule expr_body_pre_static_facts >> strip_tac >>
  drule_all (SRULE [SF ETA_ss] ifexp_body_pre_read_typed) >> strip_tac >>
  `tvt = BaseTV (BytesT (Dynamic k))` by
    (qpat_x_assum `evaluate_type _ (expr_type e) = _` mp_tac >>
     rw[evaluate_type_def] >> gvs[]) >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all expr_body_pre_copy_ok >> strip_tac >>
  drule_all (SRULE [SF ETA_ss] immutable_rhs_physical_typed) >> strip_tac >>
  drule expr_body_pre_lowered_fits >> strip_tac >>
  `?p. lowered_value_type ce e = BaseT (BytesT (Dynamic p))` by
    (qpat_x_assum `arg_type_fits _ (expr_type e)` mp_tac >> simp[] >>
     Cases_on `lowered_value_type ce e` >> simp[arg_type_fits_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[arg_type_fits_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> simp[arg_type_fits_def]) >>
  pop_assum strip_assume_tac >>
  `stv = BaseTV (BytesT (Dynamic p))` by
    (qpat_x_assum `evaluate_type _ (lowered_value_type ce e) = _` mp_tac >>
     rw[evaluate_type_def] >> gvs[]) >>
  `type_memory_bytes ce (lowered_value_type ce e) <=
   type_memory_bytes ce (expr_type e)` by metis_tac[abi_args_fits_memory_bytes] >>
  `type_memory_size tvt + 64 < dimword (:256) /\
   type_memory_size stv < 2 ** 64 /\
   type_memory_size stv + 64 < dimword (:256)` by
    (gvs[wordsTheory.dimword_def] >> decide_tac) >>
  `val_wf tvt (BytesV bytes)` by metis_tac[value_has_type_val_wf] >>
  `val_store_size stv (BytesV bytes) = val_store_size tvt (BytesV bytes)` by
    (irule bytestring_val_store_size_eq >> simp[] >>
     qexistsl [`lowered_value_type ce e`, `expr_type e`, `get_tenv cx`] >>
     simp[is_bytestring_type_def]) >>
  `vv_type vv = expr_type e \/ vv_type vv = lowered_value_type ce e` by
    (`reason_uniform_shape compile_expr ce (expr_type e) e` by
       (irule compile_expr_reason_uniform >> qexists `env` >>
        fs[expr_sim_inv_def]) >>
     pop_assum (strip_assume_tac o REWRITE_RULE [reason_uniform_shape_def]) >>
     qpat_x_assum `!sa vv sb. _ ==> reason_result_shape _ _ _`
       (drule_then assume_tac) >>
     Cases_on `vv` >> gvs[reason_result_shape_def, vv_type_def]) >>
  gvs[val_store_size_le]
QED
