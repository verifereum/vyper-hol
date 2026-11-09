Theory extRetStaticFrameConsumerPtr
Ancestors
  extRetStaticFrameMetadataPtr extRetStaticReservedPtr loweringPosts

Theorem external_frame_equal_static_copy_stmt_frag_ptr:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, fbody)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut', view, fbody', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\ source_typing_ok tops am tx /\
  assignable_type (type_env tops) ret /\ ret <> NoneT /\
  next.ce_ret_enc_info = AbiCopy m /\
  get_tenv cx = type_env tops /\ expr_type e = ret /\
  lowered_value_type next e = ret /\ ~is_word_type ret /\
  next.ce_return_pc = NONE /\ ~next.ce_raw_return /\
  next.ce_nonreentrant = (F,nkey,ut,iv) /\
  m <= next.ce_max_return_size /\ next.ce_max_return_size < dimword (:256) /\
  expr_sim_inv next cx env es /\ well_typed_expr env e /\
  call_evaluation_safe cx (int_calls_expr e) /\
  expr_sim_ptr d ctx PG func next cx ret e es ==>
  stmt_frag_ptr d ctx PG func cx lctx (\v es gt r. T) next
    (stmt_env next lctx ret (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >> drule_all external_frame_abicopy_layout >> strip_tac >>
  `post_value_type next e = expr_type e` by
    (irule post_value_type_lowered >> simp[]) >>
  irule external_return_static_copy_stmt_frag_ptr_reserved >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED
