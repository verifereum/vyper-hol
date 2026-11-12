Theory entryCallCode
Ancestors
  entryAggregateCode entryValueCode entryLocationValueCode entryTypedCopyCode
  entryCodePredicate entryContextCodePredicate exprLowering
  entryEncoderCode entryDecoderRecursiveCode builtinSimple emitHelper supportedExprs

Theorem entry_code_store_multi_results:
  !ops off. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (store_multi_results buf ops off)
Proof
  Induct_on `ops` >- simp[store_multi_results_def, entry_code_return] >>
  rpt gen_tac >> simp[store_multi_results_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 2 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >> rpt gen_tac >> BETA_TAC) >> simp[]
QED

Theorem entry_code_extcall_store_values:
  !vals off. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_extcall_store_values cenv vals buf off)
Proof
  Induct_on `vals` >- simp[compile_extcall_store_values_def, entry_code_return] >>
  Cases_on `h` >> rpt gen_tac >>
  simp[compile_extcall_store_values_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 2 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_unwrap_value] >> rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac
  >- (rpt IF_CASES_TAC >> simp[entry_code_emit_void, entry_code_store_bytestring]) >>
  simp[]
QED

Theorem entry_code_stage_intcall_args:
  !vals flags tys. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_stage_intcall_args cenv vals flags tys)
Proof
  Induct_on `vals` >- simp[compile_stage_intcall_args_def, entry_code_return] >>
  rpt gen_tac >> namedCases_on `flags` ["", "flag fs"]
  >- (simp[compile_stage_intcall_args_def] >>
      irule entry_code_bind >> reverse conj_tac >- simp[entry_code_unwrap_value] >>
      rpt gen_tac >> BETA_TAC >> irule entry_code_bind >> simp[entry_code_return]) >>
  Cases_on `tys`
  >- (simp[compile_stage_intcall_args_def] >>
      irule entry_code_bind >> reverse conj_tac >- simp[entry_code_unwrap_value] >>
      rpt gen_tac >> BETA_TAC >> irule entry_code_bind >> simp[entry_code_return]) >>
  Cases_on `flag` >> simp[compile_stage_intcall_args_def] >>
  simp[compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_unwrap_value, entry_code_alloc_buffer] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_return] >>
  irule entry_code_bind >> reverse conj_tac
  >- (rpt IF_CASES_TAC >> simp[entry_code_emit_void, entry_code_store_memory,
        entry_code_store_bytestring] >> irule entry_code_bind >>
      simp[entry_code_store_bytestring, entry_code_return]) >>
  rpt gen_tac >> BETA_TAC >> irule entry_code_bind >> simp[entry_code_return]
QED

Theorem entry_code_ext_call_kwarg:
  (!ce ty. entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce ty e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_ext_call_kwarg cfn cenv rt k e)
Proof
  strip_tac >> simp[compile_ext_call_kwarg_def] >> IF_CASES_TAC >> simp[] >>
  (irule entry_code_bind >> reverse conj_tac
   >- simp[entry_code_lower_value] >>
   rpt gen_tac >> BETA_TAC >> simp[entry_code_return] >>
   irule entry_code_bind >> simp[entry_code_materialize_vv, entry_code_return])
QED

Theorem entry_code_ext_call_kwargs:
  !es ks. (!e ce ty. MEM e es ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce ty e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_ext_call_kwargs cfn cenv rt ks es)
Proof
  Induct_on `es` >- (Cases_on `ks` >> simp[compile_ext_call_kwargs_def, entry_code_return]) >>
  rpt gen_tac >> strip_tac >> Cases_on `ks`
  >- simp[compile_ext_call_kwargs_def, entry_code_return] >>
  gvs[] >> simp[compile_ext_call_kwargs_def] >>
  irule entry_code_bind >> reverse conj_tac >- simp[entry_code_ext_call_kwarg] >>
  gen_tac >> PairCases_on `x` >> simp[] >>
  irule entry_code_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> PairCases_on `x` >> simp[entry_code_return]
QED

Theorem entry_code_extcodesize_check[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_extcodesize_check addr)
Proof
  simp[compile_extcodesize_check_def, compileEnvTheory.comp_ignore_bind_def] >>
  irule entry_code_bind >> simp[entry_code_emit_op, entry_code_emit_void]
QED

Theorem entry_code_return_value_decode[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_return_value_decode mn mx)
Proof
  `!a b c. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_select a b c)` by
    (rpt gen_tac >> simp[compile_select_def] >>
     rpt (irule entry_code_bind >> reverse conj_tac
       >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
     simp[entry_code_emit_op]) >>
  simp[compile_return_value_decode_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_op]
QED

Theorem entry_code_default_return_path[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_default_return_path cenv rt dt buf result default_op addr skip mn mx info)
Proof
  simp[compile_default_return_path_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- (simp[entry_code_emit_op, entry_code_emit_void, entry_code_emit_inst,
             entry_code_new_block, entry_code_fresh_label, entry_code_store_memory,
             entry_code_return_value_decode, entry_code_decode_to_buf] >>
        IF_CASES_TAC >> simp[entry_code_return, entry_code_extcodesize_check]) >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]
QED

Theorem entry_code_external_call_kwargs:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_external_call_kwargs cenv addr vals tys memsz abisz mid retsz
      minsz retmem static value gas skip hasdef def rt dt einfo dinfo)
Proof
  `!dst. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (if vals = [] then comp_return () else
        do tmp <- compile_alloc_buffer memsz;
           compile_extcall_store_values cenv (ZIP (vals,tys)) tmp.buf_operand 0;
           p <- emit_op ADD [dst; Lit 32w];
           compile_abi_encode_to_buf p tmp.buf_operand einfo;
           comp_return () od)` by
    (rpt gen_tac >> IF_CASES_TAC >> simp[entry_code_return,
       compileEnvTheory.comp_ignore_bind_def] >>
     rpt (irule entry_code_bind >> reverse conj_tac
       >- simp[entry_code_alloc_buffer, entry_code_extcall_store_values,
               entry_code_emit_op, entry_code_encode_to_buf] >>
       rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]) >>
  `!p n. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (do emit_void RETURNDATACOPY [p; Lit 0w; n]; emit_inst REVERT [p; n] [] od)` by
    (rpt gen_tac >> simp[compileEnvTheory.comp_ignore_bind_def] >>
     irule entry_code_bind >> simp[entry_code_emit_void, entry_code_emit_inst]) >>
  fs[compileEnvTheory.comp_ignore_bind_def] >>
  simp[compile_external_call_kwargs_def, compileEnvTheory.comp_ignore_bind_def] >>
  let
    val boundaries = [entry_code_extcall_store_values, entry_code_encode_to_buf,
      entry_code_return, entry_code_emit_op,
      entry_code_emit_void, entry_code_emit_inst, entry_code_fresh_label,
      entry_code_new_block, entry_code_alloc_buffer, entry_code_extcodesize_check,
      entry_code_return_value_decode, entry_code_decode_to_buf,
      entry_code_default_return_path];
    fun preserve_tac g =
      (FIRST [FIRST_PROVE [simp boundaries],
        irule entry_code_bind >> reverse conj_tac
          >- preserve_tac >> rpt gen_tac >> BETA_TAC >> preserve_tac,
        IF_CASES_TAC >> preserve_tac]) g;
  in preserve_tac end
QED

Theorem entry_code_fresh_vars[local]:
  !n. entry_preserves_code P (fresh_vars n)
Proof
  Induct >> simp[fresh_vars_def, entry_code_return] >>
  irule entry_code_bind >> reverse conj_tac >- simp[entry_code_fresh_var] >>
  rpt gen_tac >> BETA_TAC >> irule entry_code_bind >> simp[entry_code_return]
QED

Theorem entry_code_emit_multi_op[local]:
  opc <> DALLOCA ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (emit_multi_op opc ops n)
Proof
  strip_tac >> simp[emit_multi_op_def, compileEnvTheory.comp_ignore_bind_def] >>
  irule entry_code_bind >> reverse conj_tac >- simp[entry_code_fresh_vars] >>
  rpt gen_tac >> BETA_TAC >> irule entry_code_bind >>
  simp[entry_code_emit_inst, entry_code_return]
QED

Theorem entry_code_intcall:
  (!e ce et. MEM e args ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_call cfn cenv ret_ty ty (IntCall fid) args default_ret)
Proof
  strip_tac >> rw[entry_preserves_code_def, compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  `entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (compile_multi_vvs cfn cenv args)` by simp[entry_code_multi_vvs] >>
  fs[entry_preserves_code_def] >>
  `entry_code_pred (\i. i.inst_opcode <> DALLOCA) st1` by metis_tac[] >>
  rpt IF_CASES_TAC >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_alloc_buffer) >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_stage_intcall_args) >>
  imp_res_tac (SRULE [entry_preserves_code_def] (Q.INST [`opc` |-> `INVOKE`] entry_code_emit_op)) >>
  imp_res_tac (SRULE [entry_preserves_code_def] (Q.INST [`opc` |-> `INVOKE`] entry_code_emit_multi_op)) >>
  imp_res_tac (SRULE [entry_preserves_code_def] (Q.INST [`opc` |-> `INVOKE`] entry_code_emit_void)) >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_store_multi_results) >>
  gvs[] >> metis_tac[]
QED

Theorem entry_code_extcall:
  (!e ce et. MEM e args ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_call cfn cenv ret_ty ty (ExtCall static skip (fname, tys, rt) opts)
      args default_ret)
Proof
  strip_tac >> Cases_on `args`
  >- (rw[entry_preserves_code_def, compile_call_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      imp_res_tac (SRULE [entry_preserves_code_def]
        (Q.INST [`opc` |-> `INVALID`] entry_code_emit_inst))) >>
  rw[entry_preserves_code_def, compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  `entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (lower_value cfn cenv (BaseT AddressT) h)` by
    (irule entry_code_lower_value >> simp[]) >>
  `entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_multi_vvs cfn cenv (TAKE (LENGTH tys) t))` by
    (irule entry_code_multi_vvs >> metis_tac[rich_listTheory.MEM_TAKE]) >>
  `entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_ext_call_kwargs cfn cenv rt opts (DROP (LENGTH tys) t))` by
    (irule entry_code_ext_call_kwargs >> metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
  fs[entry_preserves_code_def] >>
  qpat_x_assum `!e ce et. e = h \/ MEM e t ==> _` kall_tac >>
  `entry_code_pred (\i. i.inst_opcode <> DALLOCA) st3` by metis_tac[] >>
  Cases_on `gas_opt` >> fs[optionTheory.option_case_def] >>
  rpt IF_CASES_TAC >> fs[] >>
  imp_res_tac (SRULE [entry_preserves_code_def]
    (Q.INST [`opc` |-> `GAS`] entry_code_emit_op)) >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_external_call_kwargs) >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  IF_CASES_TAC >> simp[] >> strip_tac >>
  rpt (qpat_x_assum `!x. _` kall_tac) >> metis_tac[]
QED

Theorem entry_code_send:
  (!e ce et. MEM e args ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_call cfn cenv ret_ty ty (Send hasgas) args default_ret)
Proof
  strip_tac >> Cases_on `args`
  >- (rw[entry_preserves_code_def, compile_call_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      imp_res_tac (SRULE [entry_preserves_code_def]
        (Q.INST [`opc` |-> `INVALID`] entry_code_emit_inst))) >>
  Cases_on `t`
  >- (rw[entry_preserves_code_def, compile_call_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      imp_res_tac (SRULE [entry_preserves_code_def]
        (Q.INST [`opc` |-> `INVALID`] entry_code_emit_inst))) >>
  rw[entry_preserves_code_def, compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  `!e et. MEM e (h::h'::t') ==>
     entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
       (lower_value cfn cenv et e)` by
    (rpt strip_tac >> irule entry_code_lower_value >> gvs[]) >>
  qpat_x_assum `!e ce et. _ ==> _` kall_tac >>
  fs[entry_preserves_code_def] >>
  Cases_on `t'` >> gvs[] >>
  gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac (SRULE [entry_preserves_code_def]
    (Q.INST [`opc` |-> `INVALID`] entry_code_emit_inst)) >>
  imp_res_tac (SRULE [entry_preserves_code_def]
    (Q.INST [`opc` |-> `CALL`] entry_code_emit_op)) >>
  imp_res_tac (SRULE [entry_preserves_code_def]
    (Q.INST [`opc` |-> `ASSERT`] entry_code_emit_void)) >>
  metis_tac[]
QED

Theorem entry_code_supported_call:
  supported_effect_expr tops (Call source_ty ct args default_ret) /\
  (!e ce et. MEM e args ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_call cfn cenv ret_ty ty ct args default_ret)
Proof
  Cases_on `ct` >> Cases_on `default_ret` >>
  simp[supported_effect_expr_def] >> rpt strip_tac
  >~ [`compile_call _ _ _ _ (IntCall _) _ _`]
    >- (irule entry_code_intcall >> simp[])
  >~ [`compile_call _ _ _ _ (ExtCall _ _ p _) _ _`]
    >- (PairCases_on `p` >> irule entry_code_extcall >> simp[]) >>
  irule entry_code_send >> simp[]
QED
