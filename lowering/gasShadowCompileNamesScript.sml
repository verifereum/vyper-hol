(* Word staging and callback-free name fast paths. *)
Theory gasShadowCompileNames
Ancestors
  gasShadowCompileLiteral gasShadowCompileConvert gasShadowCompileBase
  gasShadowState exprLowering builtinMath compileEnv emitHelper vyperAST venomInst

Theorem gas_shadow_compiles_store_words:
  !buf_op vals offset.
    gas_shadow_compiles (compile_store_words buf_op vals offset)
      (compile_store_words buf_op vals offset)
Proof
  qid_spec_tac `offset` >> Induct_on `vals` >> rpt gen_tac >>
  once_rewrite_tac[compile_store_words_def] >>
  simp[comp_ignore_bind_def, gas_shadow_compiles_return] >>
  Cases_on `offset = 0` >> simp[] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_return, gas_shadow_compiles_emit_void]
       >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_invert:
  gas_shadow_compiles (compile_invert v ty cenv) (compile_invert v ty cenv)
Proof
  Cases_on `ty` >> simp[compile_invert_def, LET_THM]
QED

Theorem as_stack_val_action[local]:
  (\s. as_stack_val ty (f s)) =
  (\s. let (x,s1) = f s in (StackValue ty x,s1))
Proof
  simp[FUN_EQ_THM] >> gen_tac >> Cases_on `f s` >> simp[as_stack_val_def]
QED

Theorem gas_shadow_compiles_as_stack_val:
  gas_shadow_compiles f g ==>
  gas_shadow_compiles (\s. as_stack_val ty (f s)) (\s. as_stack_val ty (g s))
Proof
  rewrite_tac[as_stack_val_action] >>
  MATCH_ACCEPT_TAC gas_shadow_compiles_map_result
QED

Theorem gas_shadow_compiles_addmod_names:
  gas_shadow_compiles (compile_addmod_names cenv ret_ty aty a bty b mty m)
    (compile_addmod_names cenv ret_ty aty a bty b mty m)
Proof
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  pure_rewrite_tac[compile_addmod_names_def] >>
  pure_rewrite_tac[LET_THM] >>
  ho_match_mp_tac (PURE_REWRITE_RULE [LET_THM] gas_shadow_compiles_pair) >>
  conj_tac >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
               simp[gas_shadow_compiles_name_vv]) >>
  gen_tac >> BETA_TAC >>
  ntac 5 (ho_match_mp_tac (PURE_REWRITE_RULE [LET_THM] gas_shadow_compiles_pair) >>
          conj_tac >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
                       simp[gas_shadow_compiles_name_vv, gas_shadow_compiles_unwrap_value]) >>
          gen_tac >> BETA_TAC) >>
  irule gas_shadow_compiles_as_stack_val >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[compile_addmod_def, comp_ignore_bind_def, gas_shadow_compiles_bind,
       gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_mulmod_names:
  gas_shadow_compiles (compile_mulmod_names cenv ret_ty aty a bty b mty m)
    (compile_mulmod_names cenv ret_ty aty a bty b mty m)
Proof
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  pure_rewrite_tac[compile_mulmod_names_def, LET_THM] >>
  ntac 6 (ho_match_mp_tac (PURE_REWRITE_RULE [LET_THM] gas_shadow_compiles_pair) >>
          conj_tac >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
                       simp[gas_shadow_compiles_name_vv, gas_shadow_compiles_unwrap_value]) >>
          gen_tac >> BETA_TAC) >>
  irule gas_shadow_compiles_as_stack_val >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[compile_mulmod_def, comp_ignore_bind_def, gas_shadow_compiles_bind,
       gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_powmod256_names:
  gas_shadow_compiles (compile_powmod256_names cenv ret_ty aty a bty b)
    (compile_powmod256_names cenv ret_ty aty a bty b)
Proof
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  pure_rewrite_tac[compile_powmod256_names_def, LET_THM] >>
  ntac 4 (ho_match_mp_tac (PURE_REWRITE_RULE [LET_THM] gas_shadow_compiles_pair) >>
          conj_tac >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
                       simp[gas_shadow_compiles_name_vv, gas_shadow_compiles_unwrap_value]) >>
          gen_tac >> BETA_TAC) >>
  irule gas_shadow_compiles_as_stack_val >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[compile_pow_mod256_def]
QED
