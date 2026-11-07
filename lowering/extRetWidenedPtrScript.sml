Theory extRetWidenedPtr
Ancestors
  bodyPtrDefs stmtSimDefs compileEnv compileVyper vyperContext e2eDefs

(* RESIDUAL (s3-ptr Decision 10): the external frame's valued Return whose
   lowered value type differs from the expression's own type.  That happens
   only for a widened internal call: Return's normalize branch reads the value
   at lowered_value_type, while expr_sim_ptr/expr_vv_sim_ptr give ptr_vv_ok at
   expr_type e, and the two layouts differ (see
   extRetWidenedCallEvidence$nested_call_return_endpoint_incompatible).
   The posts-interface change (post_value_type) is meant to close it. *)
Theorem external_frame_ret_widened_ptr:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, F, rr, name, args, defaults, ret, fbody)) =
    (lbl, cenv0, pos, cds, payable, nr, key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\ source_typing_ok tops am tx /\
  get_tenv cx = type_env tops /\
  expr_sim_inv next cx env es /\
  stmt_exprs_ok next (Return (SOME e)) /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  expr_sim_ptr d ctx PG func next cx (expr_type e) e es /\
  expr_vv_sim_ptr d ctx PG func next cx (expr_type e) e es /\
  lowered_value_type next e <> expr_type e ==>
  stmt_frag_ptr d ctx PG func cx lctx (\v es gt r. T) next
    (stmt_env next lctx ret (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  cheat
QED
