Theory entryDispatcherCode
Ancestors
  entryBuiltinCode entryAggregateCode entryValueCode entryArithmeticCode entryLocationValueCode
  entryCodePredicate entryContextCodePredicate exprLowering supportedExprForms
  entryEncoderCode entryDecoderRecursiveCode builtinAbi builtinSimple

Theorem entry_code_comparison_hash[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_bytestring_hash p)
Proof
  simp[compile_bytestring_hash_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_op]
QED

Theorem entry_code_dispatch_array[local]:
  (!e et. MEM e args ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn cenv et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_builtin_dispatch_body cfn cenv ret_ty ty (MakeArray o' b) args)
Proof
  strip_tac >> rw[entry_preserves_code_def] >> Cases_on `o'` >>
  gvs[compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[oneline as_ptr_val_def, AllCaseEqs()] >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_alloc_buffer)
  >~ [`compile_make_tuple _ _ _ _ _ _ _ = _`]
  >- (drule entry_code_make_tuple >>
      disch_then (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th))) >>
  drule entry_code_make_array >>
  disch_then (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th))
QED


Theorem entry_code_dispatch_env[local]:
  supported_builtin_form tops ret_ty (Env e) args ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_builtin_dispatch_body cfn cenv ret_ty ty (Env e) args)
Proof
  simp[supported_builtin_form_def] >> strip_tac >> gvs[] >>
  rw[entry_preserves_code_def, compile_builtin_dispatch_body_def, as_stack_val_def] >>
  Cases_on `compile_env_var e st` >> gvs[as_stack_val_def] >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_env_var)
QED

Theorem entry_code_dispatch_hash[local]:
  (!et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn cenv et a)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_builtin_dispatch_body cfn cenv ret_ty ty Sha256 [a])
Proof
  strip_tac >>
  `entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (lower_value cfn cenv (expr_type a) a)` by
    (irule entry_code_lower_value >> simp[]) >>
  rw[entry_preserves_code_def, compile_builtin_dispatch_body_def] >>
  Cases_on `is_bytestring_type (expr_type a)` >> gvs[] >>
  TRY (Cases_on `expr_type a` >> gvs[compileEnvTheory.is_bytestring_type_def] >>
       TRY (rename1 `expr_type a = BaseT bt` >> Cases_on `bt` >>
            gvs[compileEnvTheory.is_bytestring_type_def] >>
            TRY (rename1 `expr_type a = BaseT (BytesT bd)` >>
                 Cases_on `bd` >> gvs[compileEnvTheory.is_bytestring_type_def]))) >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[oneline as_stack_val_def, AllCaseEqs()] >>
  qpat_assum `entry_preserves_code _ (lower_value _ _ _ _)`
    (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th)) >>
  map_every (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th))
    (CONJUNCTS entry_code_hash_builtins)
QED

Theorem entry_code_bytestring_src[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_bytestring_src p)
Proof
  simp[builtinBytesTheory.compile_bytestring_src_def] >>
  ntac 2 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op] >> gen_tac >> BETA_TAC) >>
  simp[entry_code_return]
QED

(* TEMPORARILY CHEATED - SCRATCH SEQ-8501 census (never lands)
Proof
  Cases_on `bi` >> simp[supported_builtin_form_def] >> rpt strip_tac
  >~ [`compile_builtin_dispatch_body _ _ _ _ (MakeArray _ _) _`]
  >- (irule entry_code_dispatch_array >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Env _) _`]
  >- (irule entry_code_dispatch_env >> simp[supported_builtin_form_def] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ CalldataLen _`]
  >- (rw[entry_preserves_code_def, compile_builtin_dispatch_body_def,
          compile_builtin_calldatasize_def] >>
      Cases_on `emit_op CALLDATASIZE [] st` >> gvs[as_stack_val_def] >>
      imp_res_tac (SRULE [entry_preserves_code_def]
        (Q.INST [`opc` |-> `CALLDATASIZE`] entry_code_emit_op))) >>
  namedCases_on `args` ["", "a rest"] >> gvs[] >>
  namedCases_on `rest` ["", "b rest2"] >> gvs[]
  >>~- ([`compile_builtin_dispatch_body _ _ _ _ _ [a]`],
    irule entry_code_dispatch_unary >> simp[supported_builtin_form_def] >> metis_tac[]) >>
  namedCases_on `rest2` ["", "c rest3"] >> gvs[]
  >>~- ([`compile_builtin_dispatch_body _ _ _ _ _ [a;b]`],
    irule entry_code_dispatch_binary >> simp[supported_builtin_form_def] >> metis_tac[]) >>
  namedCases_on `rest3` ["", "d rest4"] >> gvs[]
  >>~- ([`compile_builtin_dispatch_body _ _ _ _ _ [a;b;c]`],
    irule entry_code_dispatch_ternary >> simp[supported_builtin_form_def] >> metis_tac[]) >>
  Cases_on `rest4` >> gvs[] >>
  irule entry_code_dispatch_quaternary >> simp[supported_builtin_form_def] >> metis_tac[]
QED
*)
Theorem entry_code_builtin_dispatch_body:
  supported_builtin_form tops ret_ty bi args /\
  (!e et. MEM e args ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn cenv et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_builtin_dispatch_body cfn cenv ret_ty ty bi args)
Proof
  cheat
QED

Theorem entry_code_dispatch_abi_encode[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (lower_abi_encode ensure mid src info maxlen)
Proof
  Cases_on `mid` >>
  simp[lower_abi_encode_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_emit_op, entry_code_emit_void,
            entry_code_encode_to_buf, entry_code_return, entry_code_bind] >>
    rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_return] >> rpt IF_CASES_TAC >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_emit_void]
QED

Theorem entry_code_dispatch_abi_decode[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (lower_abi_decode src info lo hi sz)
Proof
  simp[lower_abi_decode_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- (simp[entry_code_emit_op, entry_code_emit_void, entry_code_alloc_buffer,
             entry_code_decode_to_buf, entry_code_return] >>
        rpt IF_CASES_TAC >>
        rpt (irule entry_code_bind >> reverse conj_tac
          >- simp[entry_code_emit_op, entry_code_emit_void] >>
          rpt gen_tac >> BETA_TAC) >> simp[entry_code_emit_void]) >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]
QED

Theorem entry_code_dispatch_convert[local]:
  (!et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn cenv et a)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_type_builtin_dispatch_body cfn cenv vv_ty ty Convert ret_ty [a])
Proof
  strip_tac >>
  `!et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (lower_value cfn cenv et a)` by
    (gen_tac >> irule entry_code_lower_value >> simp[]) >>
  rw[entry_preserves_code_def, compile_type_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `!et. entry_preserves_code _ (lower_value _ _ et _)`
    (qspec_then `expr_type a` (fn th =>
      imp_res_tac (SRULE [entry_preserves_code_def] th))) >>
  rpt IF_CASES_TAC >> gvs[] >>
  Cases_on `ret_ty` >>
  gvs[oneline as_stack_val_def, exprBopLoweringTheory.as_ptr_val_pair,
      AllCaseEqs()] >>
  map_every (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th))
    [entry_code_type_convert, entry_code_bytestring_widen_copy] >>
  qmatch_goalsub_abbrev_tac `SND result` >>
  Cases_on `result` >> fs[markerTheory.Abbrev_def] >> metis_tac[]
QED

Theorem entry_code_dispatch_type_constant[local]:
  supported_type_builtin_form tops vv_ty tb ret_ty [] ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_type_builtin_dispatch_body cfn cenv vv_ty ty tb ret_ty [])
Proof
  Cases_on `tb` >> simp[supported_type_builtin_form_def] >>
  rpt strip_tac >>
  rw[entry_preserves_code_def, compile_type_builtin_dispatch_body_def] >>
  rpt IF_CASES_TAC >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_builtin_empty_complex) >>
  gvs[AllCaseEqs()]
QED

Theorem entry_code_dispatch_type_abi[local]:
  (!et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn cenv et a)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_type_builtin_dispatch_body cfn cenv vv_ty ty (AbiEncode F (SOME mid)) ret_ty [a]) /\
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_type_builtin_dispatch_body cfn cenv vv_ty ty (AbiDecode F) ret_ty [a])
Proof
  strip_tac >>
  `entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (lower_value cfn cenv (expr_type a) a)` by
    (irule entry_code_lower_value >> simp[]) >>
  conj_tac >>
  rw[entry_preserves_code_def, compile_type_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[oneline as_ptr_val_def, AllCaseEqs()] >>
  rpt IF_CASES_TAC >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[oneline as_ptr_val_def, AllCaseEqs()] >>
  qpat_x_assum `!et. entry_preserves_code _ (cfn cenv et _)`
    (qspec_then `expr_type a` (fn th =>
      imp_res_tac (SRULE [entry_preserves_code_def] th))) >>
  qpat_x_assum `entry_preserves_code _ (lower_value _ _ _ _)`
    (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th)) >>
  map_every (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th))
    [entry_code_unwrap_value, entry_code_alloc_buffer,
     Q.INST [`opc` |-> `MSTORE`] entry_code_emit_void,
     entry_code_dispatch_abi_encode, entry_code_dispatch_abi_decode] >>
  rpt (qpat_x_assum `!x. _` kall_tac) >> gvs[]
QED

Theorem entry_code_dispatch_extract32[local]:
  (!e et. MEM e [a;b] ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn cenv et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_type_builtin_dispatch_body cfn cenv vv_ty ty Extract32 ret_ty [a;b])
Proof
  strip_tac >>
  `!e et. MEM e [a;b] ==> entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (lower_value cfn cenv et e)` by
    (rpt strip_tac >> irule entry_code_lower_value >> simp[]) >>
  rw[entry_preserves_code_def, compile_type_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[oneline as_stack_val_def, AllCaseEqs()] >>
  qpat_x_assum `!e et. _ ==> entry_preserves_code _ (lower_value _ _ _ _)`
    (fn th => map_every (fn e =>
      imp_res_tac (SRULE [entry_preserves_code_def,listTheory.MEM] (Q.SPEC e th))) [`a`,`b`]) >>
  map_every (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th))
    [entry_code_bytestring_src, entry_code_extract32_load,
     entry_code_expr_clamp_basetype] >> gvs[]
QED

