(* Word snapshots reuse the original compiled value's unwrap path. *)
Theory bodyFullExtCallRequestSnapshotWord
Ancestors
  bodyFullExtCallRequestSnapshot exprSimHypsDefs exprSimHyps
  aggregateEvaluatedLayout loweringPosts exprLowering context compileEnv

Theorem extcall_request_word_snapshot_unwrap:
  expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  vv_holds ce cx (post_value_type ce e) tv vv ee s /\
  is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) vv)) ==>
  compile_snapshot_vv ce F (ext_call_arg_value (lowered_value_type ce e) vv) =
    comp_bind (unwrap_value ce vv)
      (\op. comp_return
        (StackValue (vv_type (ext_call_arg_value (lowered_value_type ce e) vv)) op))
Proof
  strip_tac >> Cases_on `vv`
  >- gvs[ext_call_arg_value_def, compile_snapshot_vv_def] >>
  rename1 `LocatedValue tag p` >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `is_word_type (expr_type e)` by
    (gvs[ext_call_arg_value_def, vv_type_def] >>
     metis_tac[arg_type_fits_word_type]) >>
  gvs[vv_holds_def, ext_call_arg_value_def, vv_type_def,
      compile_snapshot_vv_def, unwrap_value_def,
      is_bytestring_type_def, is_word_type_def] >>
  Cases_on `expr_type e` >> gvs[is_bytestring_type_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[is_bytestring_type_def, is_word_type_def] >>
  rename1 `BytesT bs` >> Cases_on `bs` >>
  gvs[is_bytestring_type_def, is_word_type_def]
QED
