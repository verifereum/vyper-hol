(* An exempt source error starts at an actual compiled TypeBuiltin and
   retains its normal child's complete postcondition and target landing. *)
Theory gasExemptOriginMods
Ancestors
  gasNormalPrefix typeBuiltinSource selfdestructHalt gasSummary sourceExemptMods
  exprLowering exprLoweringProps vyperInterpreter vyperContext vyperState
  vyperValue vyperAST

Definition gas_exempt_origin_mods_def:
  gas_exempt_origin_mods memory mods (ctx, func) source (es, s0)
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
        unspecified_behaviour_exempt_mods mods (RuntimeError "abi_decode invalid")) \/
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
End

Theorem gas_exempt_origin_from_mem_mods:
  gas_exempt_origin_mods T mods p source start marks out endpoint ==>
  gas_exempt_origin_mods memory mods p source start marks out endpoint
Proof
  PairCases_on `p` >> PairCases_on `start` >> PairCases_on `out` >>
  simp[gas_exempt_origin_mods_def, gasNormalPrefixTheory.gas_value_prefix_def] >>
  metis_tac[gas_marked_exec_from_mem]
QED

Theorem gas_exempt_origin_execution_mods:
  gas_exempt_origin_mods memory mods (ctx, func) source (es, s0)
    marks (err, ee) t ==>
  gas_marked_exec memory (ctx, func) source (es, s0)
    marks (INR (Error err)) ee (OK t)
Proof
  rw[gas_exempt_origin_mods_def] >>
  fs[gas_value_prefix_def, gas_marked_exec_def] >>
  gen_tac >> first_x_assum (qspec_then `tail` assume_tac)
  >- (drule_all (SIMP_RULE (srw_ss()) [type_builtin_args_length_ok_def]
        (Q.SPECL [`cx`, `ann`, `AbiDecode unwrap`, `ty`, `e`]
          eval_type_builtin_singleton_error)) >>
      simp[ignore_bind_def, bind_def]) >>
  drule eval_selfdestruct_overflow >>
  disch_then (qspecl_then [`a`, `ann`, `dflt`] mp_tac) >>
  (impl_tac >- fs[]) >>
  simp[ignore_bind_def, bind_def]
QED

Theorem gas_exempt_origin_classified_mods:
  gas_exempt_origin_mods memory mods (ctx, func) source (es, s0)
    marks (err, ee) t ==>
  unspecified_behaviour_exempt_mods mods err
Proof
  rw[gas_exempt_origin_mods_def] >>
  simp[unspecified_behaviour_exempt_mods_def]
QED
