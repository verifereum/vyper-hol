(* An exempt source error starts at an actual compiled TypeBuiltin and
   retains its normal child's complete postcondition and target landing. *)
Theory gasExemptOrigin
Ancestors
  gasNormalPrefix typeBuiltinSource gasSummary e2eDefs
  exprLowering exprLoweringProps vyperInterpreter vyperContext vyperState
  vyperValue vyperAST

Definition gas_exempt_origin_def:
  gas_exempt_origin memory tops (ctx, func) source (es, s0)
    marks (err, ee) t <=>
    ?cenv cx out_ty ann tb ty e sa sb sc vv op v.
      source = ignore_bind (eval_expr cx (TypeBuiltin ann tb ty [e]))
                           (return ()) /\
      compile_expr cenv out_ty (TypeBuiltin ann tb ty [e]) sa = (vv, sb) /\
      fn_has_code sa sb func /\
      gas_value_prefix memory (ctx, func, cenv, cx) (expr_type e, e)
        (sa, sc, op) (es, s0) marks (v, ee, t) /\
      evaluate_type_builtin cx tb ty [expr_type e] [v] = INR err /\
      ?unwrap. tb = AbiDecode unwrap /\
        err = RuntimeError "abi_decode invalid" /\
        ?target_ty. occurs_abi_decode_target target_ty tops /\
          is_dynamic (vyper_to_abi_type (type_env tops) target_ty)
End

Theorem gas_exempt_origin_execution:
  gas_exempt_origin memory tops (ctx, func) source (es, s0)
    marks (err, ee) t ==>
  gas_marked_exec memory (ctx, func) source (es, s0)
    marks (INR (Error err)) ee (OK t)
Proof
  rw[gas_exempt_origin_def] >>
  fs[gas_value_prefix_def, gas_marked_exec_def] >>
  gen_tac >> first_x_assum (qspec_then `tail` assume_tac) >>
  drule_all (SIMP_RULE (srw_ss()) [type_builtin_args_length_ok_def]
    (Q.SPECL [`cx`, `ann`, `AbiDecode unwrap`, `ty`, `e`]
      eval_type_builtin_singleton_error)) >>
  simp[ignore_bind_def, bind_def]
QED

Theorem gas_exempt_origin_classified:
  gas_exempt_origin memory tops (ctx, func) source (es, s0)
    marks (err, ee) t ==>
  unspecified_behaviour_exempt tops err
Proof
  rw[gas_exempt_origin_def] >>
  simp[unspecified_behaviour_exempt_def] >> metis_tac[]
QED
