Theory extRetTypedStaticConsumerPtr
Ancestors staticTypeFitsPtr typedCopyPtr extRetStaticBoundedConsumerPtr

Theorem typed_abi_static_return_annotation:
  !cenv cx env es ret e (sf : string |-> ('a # type # 'b) list).
    expr_sim_inv cenv cx env es /\
    IS_SOME (type_stmt env ret (Return (SOME e))) /\
    ~is_abi_dynamic sf ret ==>
    expr_type e = ret
Proof
  rpt strip_tac >> Cases_on `expr_type e = ret` >> simp[] >>
  drule_all typed_return_normalization_inputs >> strip_tac >>
  drule (cj 1 static_arg_type_fits) >>
  disch_then (qspec_then `sf` mp_tac) >> simp[]
QED

Theorem external_frame_typed_static_copy_stmt_frag_ptr_bounded:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, fbody)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut', view, fbody', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\ source_typing_ok tops am tx /\
  assignable_type (type_env tops) ret /\ ret <> NoneT /\
  next.ce_ret_enc_info = AbiCopy m /\
  get_tenv cx = type_env tops /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  ~is_abi_dynamic next.ce_struct_fields ret /\
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
  `expr_type e = ret` by
    (drule_all typed_abi_static_return_annotation >> simp[]) >>
  irule external_frame_equal_static_copy_stmt_frag_ptr_bounded >>
  simp[] >> metis_tac[]
QED
