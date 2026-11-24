(* The full origin for the singleton source unit. *)
Theory gasExemptOrigin
Ancestors
  gasExemptOriginMods sourceExemptMods e2eDefs gasNormalPrefix gasSummary
  selfdestructHalt supportedProgram exprLowering exprLoweringProps
  vyperInterpreter vyperContext vyperState vyperValue vyperABI vyperAST

Definition gas_exempt_origin_singleton_def:
  gas_exempt_origin memory tops p source start marks out endpoint <=>
    gas_exempt_origin_mods memory [(NONE,tops)] p source start marks out endpoint
End

Theorem gas_exempt_origin_def:
  gas_exempt_origin memory tops (ctx, func) source (es, s0)
    marks (err, ee) t <=>
    (?(H : (bool # bytes32 # type_value) list # num list)
      cenv cx out_ty ann tb ty e sa sb sc vv op v.
      source = ignore_bind (eval_expr cx (TypeBuiltin ann tb ty [e]))
                           (return ()) /\
      compile_expr cenv out_ty (TypeBuiltin ann tb ty [e]) sa = (vv, sb) /\
      fn_has_code sa sb func /\
      gas_value_prefix H memory (ctx, func, cenv, cx) (expr_type e, e)
        (sa, sc, op) (es, s0) marks (v, ee, t) /\
      evaluate_type_builtin cx tb ty [expr_type e] [v] = INR err /\
      ?unwrap. tb = AbiDecode unwrap /\
        err = RuntimeError "abi_decode invalid" /\
        ?target_ty. occurs_abi_decode_target target_ty tops /\
          is_dynamic (vyper_to_abi_type (type_env tops) target_ty)) \/
    (?(H : (bool # bytes32 # type_value) list # num list)
      cenv cx out_ty ann e dflt sa sb sc vv op v a.
      source = ignore_bind
        (eval_expr cx (Call ann SelfDestructTarget [e] dflt)) (return ()) /\
      compile_expr cenv out_ty (Call ann SelfDestructTarget [e] dflt) sa =
        (vv, sb) /\
      fn_has_code sa sb func /\
      gas_value_prefix H memory (ctx, func, cenv, cx) (expr_type e, e)
        (sa, sc, op) (es, s0) marks (v, ee, t) /\
      dest_AddressV v = SOME a /\ ~cx.txn.is_static /\
      selfdestruct_overflows cx a ee.accounts /\
      err = RuntimeError "transfer_value recipient overflow")
Proof
  simp[gas_exempt_origin_singleton_def, gas_exempt_origin_mods_def,
       unspecified_behaviour_exempt_mods_singleton, unspecified_behaviour_exempt_def]
QED

Theorem gas_exempt_origin_from_mem:
  gas_exempt_origin T tops p source start marks out endpoint ==>
  gas_exempt_origin memory tops p source start marks out endpoint
Proof
  simp[gas_exempt_origin_singleton_def,
       gas_exempt_origin_from_mem_mods]
QED

Theorem gas_exempt_origin_execution:
  gas_exempt_origin memory tops (ctx, func) source (es, s0)
    marks (err, ee) t ==>
  gas_marked_exec memory (ctx, func) source (es, s0)
    marks (INR (Error err)) ee (OK t)
Proof
  rewrite_tac[gas_exempt_origin_singleton_def] >>
  MATCH_ACCEPT_TAC gas_exempt_origin_execution_mods
QED

Theorem gas_exempt_origin_classified:
  gas_exempt_origin memory tops (ctx, func) source (es, s0)
    marks (err, ee) t ==>
  unspecified_behaviour_exempt tops err
Proof
  rewrite_tac[gas_exempt_origin_singleton_def,
              GSYM unspecified_behaviour_exempt_mods_singleton] >>
  MATCH_ACCEPT_TAC gas_exempt_origin_classified_mods
QED
