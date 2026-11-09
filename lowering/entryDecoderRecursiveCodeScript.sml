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

Theorem entry_code_decoder_mutual[local]:
  (!dst src load_opc hi info.
    load_opc <> DALLOCA ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_abi_decode_to_buf dst src load_opc (Lit 0w) hi info)) /\
  (!dst src load_opc hi elems ao vo.
    load_opc <> DALLOCA ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_abi_decode_complex_elems dst src load_opc (Lit 0w) hi elems ao vo)) /\
  (!dst src load_opc hi ei asz msz ip cnt.
    load_opc <> DALLOCA ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_abi_decode_dyn_loop dst src load_opc (Lit 0w) hi ei asz msz ip cnt))
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
  simp[Once compile_abi_decode_to_buf_def,
       entry_code_decode_static, entry_code_clamp_basetype]
QED

Resume entry_code_decoder_mutual[bytes]:
  rpt strip_tac >>
  pure_once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp[compileEnvTheory.comp_ignore_bind_def] >>
  ntac 4 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >> rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac
  >- (Cases_on `hi = Lit 0w` >>
      simp[entry_code_return, compileEnvTheory.comp_ignore_bind_def] >>
      ntac 4 (irule entry_code_bind >> reverse conj_tac
        >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
      simp[entry_code_emit_void]) >>
  simp[entry_code_decoder_copy]
QED

Resume entry_code_decoder_mutual[array]:
  rpt strip_tac >>
  pure_once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp[compileEnvTheory.comp_ignore_bind_def] >>
  ntac 4 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac
  >- (Cases_on `hi = Lit 0w` >>
      simp[entry_code_return, compileEnvTheory.comp_ignore_bind_def] >>
      ntac 5 (irule entry_code_bind >> reverse conj_tac
        >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
      simp[entry_code_emit_void]) >>
  rpt gen_tac >> BETA_TAC >>
  ntac 2 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >>
  Cases_on `~elem_is_dyn /\ ~dec_info_needs_clamp ei`
  >- (gvs[] >>
      ntac 3 (irule entry_code_bind >> reverse conj_tac
        >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
      simp[entry_code_decoder_copy]) >>
  gvs[compileEnvTheory.comp_ignore_bind_def] >>
  (irule entry_code_bind >> reverse conj_tac
   >- simp[entry_code_alloc_buffer] >> gen_tac >> BETA_TAC >>
   irule entry_code_bind >> simp[entry_code_emit_void])
QED

Resume entry_code_decoder_mutual[complex]:
  rpt strip_tac >> Cases_on `hi = Lit 0w` >> gvs[] >>
  simp[Once compile_abi_decode_to_buf_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 4 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >> simp[]
QED

Resume entry_code_decoder_mutual[nil]:
  simp[Once compile_abi_decode_to_buf_def, entry_code_return]
QED

Resume entry_code_decoder_mutual[cons]:
  rpt strip_tac >> gvs[] >>
  simp[Once compile_abi_decode_to_buf_def, compileEnvTheory.comp_ignore_bind_def] >>
  irule entry_code_bind >> reverse conj_tac
  >- simp[entry_code_getelemptr_abi] >> gen_tac >> BETA_TAC >>
  irule entry_code_bind >> reverse conj_tac
  >- simp[entry_code_emit_op] >> gen_tac >> BETA_TAC >>
  irule entry_code_bind >> simp[arithmeticTheory.ADD_COMM]
QED

Resume entry_code_decoder_mutual[loop]:
  rpt strip_tac >> gvs[] >>
  simp[Once compile_abi_decode_to_buf_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 15 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_fresh_label, entry_code_emit_inst,
            entry_code_new_block, entry_code_emit_op] >>
    rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac
  >- (Cases_on `dec_info_needs_offset ei` >>
      simp[entry_code_decode_dyn_elem_ptr, entry_code_return]) >>
  gen_tac >> BETA_TAC >>
  ntac 8 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void,
            entry_code_emit_inst, entry_code_new_block] >>
    rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_return]
QED

Finalise entry_code_decoder_mutual

Theorem entry_code_decode_to_buf:
  load_opc <> DALLOCA ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_decode_to_buf dst src load_opc (Lit 0w) hi info)
Proof
  metis_tac[entry_code_decoder_mutual]
QED

Theorem entry_code_decode_complex_elems:
  load_opc <> DALLOCA ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_decode_complex_elems dst src load_opc (Lit 0w) hi elems ao vo)
Proof
  metis_tac[entry_code_decoder_mutual]
QED

Theorem entry_code_decode_dyn_loop:
  load_opc <> DALLOCA ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_decode_dyn_loop dst src load_opc (Lit 0w) hi ei asz msz ip cnt)
Proof
  metis_tac[entry_code_decoder_mutual]
QED
