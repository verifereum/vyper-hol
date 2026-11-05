Theory exprSimAbiDecodeCertificate
Ancestors
  exprSimAbiDecodePrims exprSimAbiDecodeTrace abiEncoder builtinAbi
  compileEnv emitHelper context venomInst

Theorem decode_certificate_copy:
  decode_certificate
    (case opc of
       CALLDATALOAD => emit_void CALLDATACOPY [d; s; n]
     | DLOAD => emit_void DLOADBYTES [d; s; n]
     | _ => emit_void MCOPY [d; s; n])
Proof
  Cases_on `opc` >> simp[decode_certificate_emit_void]
QED

Theorem decode_certificate_switch_bind:
  decode_certificate f ==>
  decode_certificate (comp_bind (new_block l) (\_. f))
Proof
  simp[GSYM comp_ignore_bind_def, decode_certificate_new_block]
QED

Theorem decode_certificate_mutual:
  (!dst src opc bop hi info.
    decode_certificate (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  (!dst src opc bop hi elems ao vo.
    decode_certificate (compile_abi_decode_complex_elems dst src opc bop hi elems ao vo)) /\
  (!dst src opc bop hi info abi_sz mem_sz ip cnt.
    decode_certificate (compile_abi_decode_dyn_loop dst src opc bop hi info abi_sz mem_sz ip cnt))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >>
  rpt conj_tac >> rpt gen_tac
  >- (once_rewrite_tac[compile_abi_decode_to_buf_def] >>
      match_mp_tac decode_certificate_bind >>
      simp[decode_certificate_abi_dec_addr] >> gen_tac >>
      irule decode_certificate_abi_decode_static >>
      simp[decode_certificate_abi_clamp_basetype])
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- (once_rewrite_tac[compile_abi_decode_to_buf_def] >> simp[decode_certificate_return])
  >- suspend "elems"
  >> suspend "loop"
QED

Resume decode_certificate_mutual[bytes]:
  Cases_on `hi = Lit 0w` >> Cases_on `bop = Lit 0w` >>
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp[LET_THM, comp_ignore_bind_def] >>
  rpt (pure_rewrite_tac[comp_bind_assoc] >> BETA_TAC >>
       match_mp_tac decode_certificate_bind >> conj_tac
       >- simp[decode_certificate_abi_dec_addr,
               decode_certificate_abi_decode_range_check, decode_certificate_emit_op,
               decode_certificate_emit_void, decode_certificate_return]
       >> gen_tac >> BETA_TAC) >>
  simp[decode_certificate_copy, decode_certificate_emit_void]
QED

Resume decode_certificate_mutual[array]:
  strip_tac >> Cases_on `hi = Lit 0w` >> Cases_on `bop = Lit 0w` >>
  Cases_on `~elem_is_dyn /\ ~dec_info_needs_clamp info` >>
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> asm_rewrite_tac[] >>
  gvs[] >> rewrite_tac[comp_ignore_bind_def] >>
  rpt (pure_rewrite_tac[comp_bind_assoc] >> BETA_TAC >>
       match_mp_tac decode_certificate_bind >> conj_tac
       >- simp[decode_certificate_abi_dec_addr,
               decode_certificate_abi_decode_range_check, decode_certificate_emit_op,
               decode_certificate_emit_void, decode_certificate_return,
               decode_certificate_alloc_buffer]
       >> gen_tac >> BETA_TAC) >>
  simp[decode_certificate_copy, decode_certificate_emit_void]
QED

Resume decode_certificate_mutual[complex]:
  strip_tac >> Cases_on `hi = Lit 0w` >> gvs[] >>
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp[LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac decode_certificate_bind >> conj_tac
       >- simp[decode_certificate_abi_decode_range_check,
               decode_certificate_emit_op] >> gen_tac >> BETA_TAC) >> simp[]
QED

Resume decode_certificate_mutual[elems]:
  strip_tac >> gvs[] >> once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp[LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac decode_certificate_bind >> conj_tac
       >- simp[decode_certificate_getelemptr_abi, decode_certificate_emit_op]
       >> gen_tac >> BETA_TAC) >> simp[]
QED

Resume decode_certificate_mutual[loop]:
  strip_tac >> gvs[] >> Cases_on `dec_info_needs_offset info` >>
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp[LET_THM, comp_ignore_bind_def] >>
  ntac 3
    (rpt (match_mp_tac decode_certificate_bind >> conj_tac
          >- simp[decode_certificate_fresh_label, decode_certificate_emit_inst,
                  decode_certificate_emit_op, decode_certificate_emit_void,
                  decode_certificate_abi_dec_addr,
                  decode_certificate_abi_decode_dyn_elem_ptr,
                  decode_certificate_return]
          >> gen_tac >> BETA_TAC) >>
     match_mp_tac decode_certificate_switch_bind) >>
  simp[decode_certificate_return]
QED

Finalise decode_certificate_mutual

Theorem decode_certificate_to_buf:
  decode_certificate (compile_abi_decode_to_buf dst src opc bop hi info)
Proof
  metis_tac[decode_certificate_mutual]
QED

Theorem decode_certificate_lower:
  decode_certificate (lower_abi_decode data di mn mx msz)
Proof
  Cases_on `mn = mx` >>
  simp[lower_abi_decode_def, comp_ignore_bind_def] >>
  rpt (pure_rewrite_tac[comp_bind_assoc] >> BETA_TAC >>
       match_mp_tac decode_certificate_bind >> conj_tac
       >- simp[decode_certificate_emit_op, decode_certificate_emit_void,
               decode_certificate_alloc_buffer, decode_certificate_to_buf,
               decode_certificate_return]
       >> gen_tac >> BETA_TAC) >>
  simp[decode_certificate_return]
QED
