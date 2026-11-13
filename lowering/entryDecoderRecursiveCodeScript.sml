Theory entryDecoderRecursiveCode
Ancestors
  entryCodePredicate entryContextCodePredicate entryDecoderCode abiEncoder

Theorem entry_code_decoder_copy[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (case opc of
       CALLDATALOAD => emit_void CALLDATACOPY ops
     | DLOAD => emit_void DLOADBYTES ops
     | _ => emit_void MCOPY ops)
Proof
  Cases_on `opc` >> simp[entry_code_emit_void]
QED

Theorem entry_code_dec_addr[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_dec_addr base_op p)
Proof
  rw[compile_abi_dec_addr_def, entry_code_return, entry_code_emit_op]
QED

Theorem entry_code_range_check[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_decode_range_check start_op end_op hi_op)
Proof
  rewrite_tac[compile_abi_decode_range_check_def] >>
  rpt (irule entry_code_bind >> simp[entry_code_emit_op] >> gen_tac) >>
  simp[entry_code_emit_void]
QED

fun dec_code_tac g =
  FIRST [
    FIRST (map (fn th => irule th >> asm_simp_tac (srw_ss()) [entry_code_clamp_basetype] >> NO_TAC)
      [entry_code_return, entry_code_emit_op, entry_code_emit_void,
       entry_code_alloc_buffer, entry_code_range_check, entry_code_decoder_copy,
       entry_code_dec_addr, entry_code_decode_static, entry_code_clamp_basetype,
       entry_code_getelemptr_abi, entry_code_decode_dyn_elem_ptr,
       entry_code_fresh_label, entry_code_emit_inst, entry_code_new_block]),
    irule entry_code_bind >> rpt conj_tac >> rpt gen_tac >> BETA_TAC >> dec_code_tac,
    IF_CASES_TAC >> dec_code_tac,
    first_assum (fn th => irule th >> fs[] >> NO_TAC)] g;

Theorem entry_code_decoder_mutual[local]:
  (!dst src load_opc base_op hi info.
    load_opc <> DALLOCA ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_abi_decode_to_buf dst src load_opc base_op hi info)) /\
  (!dst src load_opc base_op hi elems ao vo.
    load_opc <> DALLOCA ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_abi_decode_complex_elems dst src load_opc base_op hi elems ao vo)) /\
  (!dst src load_opc base_op hi ei asz msz ip cnt.
    load_opc <> DALLOCA ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_abi_decode_dyn_loop dst src load_opc base_op hi ei asz msz ip cnt))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >>
  conj_tac >- suspend "prim" >>
  conj_tac >- suspend "bytes" >>
  conj_tac >- suspend "array" >>
  conj_tac >- suspend "complex" >>
  conj_tac >- suspend "nil" >>
  conj_tac >- suspend "cons" >>
  suspend "loop"
QED

Resume entry_code_decoder_mutual[prim]:
  rpt strip_tac >>
  pure_once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp[compileEnvTheory.comp_ignore_bind_def, LET_THM] >>
  dec_code_tac
QED

Resume entry_code_decoder_mutual[bytes]:
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  pure_once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp[compileEnvTheory.comp_ignore_bind_def, LET_THM] >>
  dec_code_tac
QED

Resume entry_code_decoder_mutual[array]:
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!can_bulk_copy. _` (assume_tac o SRULE []) >>
  pure_once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp[compileEnvTheory.comp_ignore_bind_def, LET_THM] >>
  dec_code_tac
QED

Resume entry_code_decoder_mutual[complex]:
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  rpt (qpat_x_assum `!static_sz. _` (assume_tac o SRULE [])) >>
  Cases_on `hi = Lit 0w` >> rpt BasicProvers.VAR_EQ_TAC >>
  pure_once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp[compileEnvTheory.comp_ignore_bind_def, LET_THM] >>
  dec_code_tac
QED

Resume entry_code_decoder_mutual[nil]:
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> simp[Once compile_abi_decode_to_buf_def, entry_code_return]
QED

Resume entry_code_decoder_mutual[cons]:
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> gvs[] >>
  simp[Once compile_abi_decode_to_buf_def, compileEnvTheory.comp_ignore_bind_def] >>
  irule entry_code_bind >> reverse conj_tac
  >- simp[entry_code_getelemptr_abi] >> gen_tac >> BETA_TAC >>
  irule entry_code_bind >> reverse conj_tac
  >- simp[entry_code_emit_op] >> gen_tac >> BETA_TAC >>
  irule entry_code_bind >> simp[arithmeticTheory.ADD_COMM]
QED

Resume entry_code_decoder_mutual[loop]:
  rpt strip_tac >> gvs[] >>
  pure_once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp[compileEnvTheory.comp_ignore_bind_def, LET_THM] >>
  dec_code_tac
QED

Finalise entry_code_decoder_mutual

Theorem entry_code_decode_to_buf:
  load_opc <> DALLOCA ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_decode_to_buf dst src load_opc base_op hi info)
Proof
  metis_tac[entry_code_decoder_mutual]
QED

Theorem entry_code_decode_complex_elems:
  load_opc <> DALLOCA ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_decode_complex_elems dst src load_opc base_op hi elems ao vo)
Proof
  metis_tac[entry_code_decoder_mutual]
QED

Theorem entry_code_decode_dyn_loop:
  load_opc <> DALLOCA ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_decode_dyn_loop dst src load_opc base_op hi ei asz msz ip cnt)
Proof
  metis_tac[entry_code_decoder_mutual]
QED
