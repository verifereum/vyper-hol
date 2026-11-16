Theory createCtorTuplePhysical
Ancestors
  exprPtrUnwrapStorageShape exprSimConvert loweringPosts exprSimProps exprLowering
  abiEncodeArgsSim placeRelayoutRawSource

Theorem ctor_capture_unequal_types_value:
  eval_expr cx e es_eval = (INL raw,es_child) /\
  post_value_type ce e <> lowered_value_type ce e ==>
  ?v. raw = Value v
Proof
  Cases_on `e` >> simp[lowered_value_type_def, post_value_type_def]
  >- metis_tac[exprSimPropsTheory.eval_expr_literal_value]
  >- metis_tac[exprLoweringPropsTheory.eval_expr_builtin_value]
  >- metis_tac[exprSimConvertTheory.eval_expr_type_builtin_value] >>
  rename1 `Call ann tgt args drv` >> Cases_on `tgt` >>
  simp[lowered_value_type_def, post_value_type_def] >>
  PairCases_on `p` >> metis_tac[placeRelayoutRawSourceTheory.internal_call_delayed_read]
QED

Theorem ctor_capture_lowered_transport:
  !ce cx env e es_eval es_child es_capture raw value ca cb vv origin endpoint s.
    expr_body_pre ce cx env e es_eval /\
    compile_expr ce (expr_type e) e ca = (vv,cb) /\
    eval_expr cx e es_eval = (INL raw,es_child) /\
    read_result cx raw es_capture = (INL value,es_capture) /\
    (~is_word_type (expr_type e) ==>
      ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
           value_has_type tv value /\ val_wf tv value) /\
    vv_holds ce cx (post_value_type ce e) raw vv es_capture s /\
    vv_at ce cx (post_value_type ce e) origin endpoint es_capture raw vv s ==>
    vv_holds ce cx (lowered_value_type ce e) raw vv es_capture s /\
    vv_at ce cx (lowered_value_type ce e) origin endpoint es_capture raw vv s
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `post_value_type ce e = lowered_value_type ce e` >- gvs[] >>
  `?v. raw = Value v` by metis_tac[ctor_capture_unequal_types_value] >>
  Cases_on `vv`
  >- (gvs[vv_holds_def, vv_at_def] >>
      metis_tac[abi_args_rel_lowered_transport, abi_args_at_lowered_transport]) >>
  rename1 `LocatedValue vt p` >>
  `p.ptr_location = LocMemory` by
    (spose_not_then assume_tac >>
     drule_all compile_nonmemory_lowered_value_type >>
     metis_tac[post_value_type_lowered]) >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits] >>
  `~is_word_type (expr_type e)` by
    (spose_not_then assume_tac >>
     `lowered_value_type ce e = expr_type e` suffices_by
       metis_tac[post_value_type_lowered] >>
     metis_tac[abiEncodeArgsSimTheory.abi_args_word_fits_eq]) >>
  `is_bytestring_type (post_value_type ce e) /\
   is_bytestring_type (lowered_value_type ce e)` by
    metis_tac[abiEncodeMaterializeTheory.materialize_post_lowered_classify] >>
  `~is_word_type (post_value_type ce e) /\
   ~is_word_type (lowered_value_type ce e)` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `expr_val_rel cx (post_value_type ce e) value p.ptr_operand s` by
    (gvs[vv_holds_def, expr_val_rel_def] >> metis_tac[]) >>
  `expr_val_at ce cx (post_value_type ce e) origin endpoint es_capture value p.ptr_operand s` by
    metis_tac[vv_at_memory_val_at] >>
  `expr_val_rel cx (lowered_value_type ce e) value p.ptr_operand s /\
   expr_val_at ce cx (lowered_value_type ce e) origin endpoint es_capture value p.ptr_operand s` by
    metis_tac[abi_args_rel_lowered_transport, abi_args_at_lowered_transport] >>
  gvs[vv_holds_def, vv_at_def, expr_val_rel_def, expr_val_at_def] >>
  metis_tac[]
QED
