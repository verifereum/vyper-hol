(* Encoder lengths are literals or variables already produced by the encoder. *)
Theory abiEncoderResultLive
Ancestors
  abiEncoder abiDecoderReentry emitHelperProps exprLoweringProps
  compileEnv emitHelper venomInst list words

Theorem abi_encode_complex_result_live:
  compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,st') ==>
  abi_decoder_operand_live st'.cs_next_var out
Proof
  Cases_on `infos` >- simp[Once compile_abi_encode_child_def, comp_return_def, abi_decoder_operand_live_def] >>
  rename1 `AbiComplex (info::infos)` >>
  Cases_on `EXISTS (\(_,_,_,dyn). dyn) (info::infos)` >>
  asm_simp_tac bool_ss [Once compile_abi_encode_child_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  FIRST [drule abi_decoder_operand_live_emit >> simp[abi_decoder_operand_live_def],
    simp[abi_decoder_operand_live_def]]
QED

Theorem abi_encode_result_live:
  compile_abi_encode_to_buf dst src ei st = (out,st') ==>
  abi_decoder_operand_live st'.cs_next_var out
Proof
  Cases_on `ei` >> strip_tac >>
  FIRST [rename1 `compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,st')` >>
    drule abi_encode_complex_result_live >> simp[], ALL_TAC] >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_abi_encode_child_def, compile_abi_encode_static_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  FIRST [drule abi_decoder_operand_live_emit >> simp[abi_decoder_operand_live_def],
    simp[abi_decoder_operand_live_def]]
QED

Theorem abi_encode_static_info_result_live:
  compile_abi_encode_static_info dst src ei st = (out,st') ==>
  abi_decoder_operand_live st'.cs_next_var out
Proof
  Cases_on `ei` >>
  simp_tac bool_ss [compile_abi_encode_static_info_def, compile_abi_encode_static_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[abi_decoder_operand_live_def]
QED
