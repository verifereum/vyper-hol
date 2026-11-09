Theory extcallReturnDecoderRelabel
Ancestors
  extcallReturnCompileRelabel abiEncoder context compileEnv
  exprSimAbiGasBridge emitHelper

val transport_simps = [return_compile_transport_return,
  return_compile_transport_bind, return_compile_transport_ignore_bind,
  return_compile_transport_emit_op, return_compile_transport_emit_void,
  return_compile_transport_emit_inst, return_compile_transport_fresh_label,
  return_compile_transport_new_block_ignore];

val transport_db = fn th =>
  ho_match_mp_tac return_compile_transport_bind >>
  (conj_tac >- simp [th]) >> gen_tac;

val transport_binds = rpt
  (ho_match_mp_tac return_compile_transport_bind >>
   (conj_tac >- simp transport_simps) >> gen_tac);

Theorem return_transport_dec_addr:
  return_compile_transport sa L ids (compile_abi_dec_addr base_op pos)
Proof
  rw[compile_abi_dec_addr_def] >> simp transport_simps
QED

Theorem return_transport_range_check:
  return_compile_transport sa L ids (compile_abi_decode_range_check src e hi)
Proof
  rewrite_tac[compile_abi_decode_range_check_def] >>
  transport_binds >> simp transport_simps
QED

Theorem return_transport_alloc_buffer:
  return_compile_transport sa L ids (compile_alloc_buffer sz)
Proof
  simp ([compile_alloc_buffer_def] @ transport_simps)
QED

Theorem return_transport_clamp:
  !c v. return_compile_transport sa L ids (compile_abi_clamp_basetype v c)
Proof
  Cases >> simp ([compile_abi_clamp_basetype_def,
    compile_abi_int_clamp_def, compile_abi_bytes_clamp_def] @ transport_simps) >>
  rpt gen_tac >> TRY (IF_CASES_TAC) >>
  transport_binds >> simp transport_simps
QED

Theorem return_transport_static:
  (!v. return_compile_transport sa L ids (clamp v)) ==>
  return_compile_transport sa L ids (compile_abi_decode_static src dst opc clamp)
Proof
  strip_tac >> simp ([compile_abi_decode_static_def] @ transport_simps)
QED

Theorem return_transport_getelemptr:
  return_compile_transport sa L ids
    (compile_getelemptr_abi src dyn off opc base_op hi)
Proof
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >>
  simp[compile_getelemptr_abi_def] >>
  transport_db return_compile_transport_emit_op >>
  simp transport_simps >>
  transport_db return_transport_dec_addr >>
  transport_binds >> simp transport_simps
QED

Theorem return_transport_dyn_elem_ptr:
  return_compile_transport sa L ids
    (compile_abi_decode_dyn_elem_ptr opc base_op src data hi sz)
Proof
  Cases_on `hi = Lit 0w` >>
  rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >>
  transport_db return_transport_dec_addr >>
  transport_binds >> simp transport_simps >>
  ho_match_mp_tac return_compile_transport_ignore_bind >> conj_tac
  >- (transport_binds >>
      ho_match_mp_tac return_compile_transport_ignore_bind >> conj_tac
      >- simp transport_simps >>
      transport_binds >> simp[return_transport_range_check]) >>
  simp transport_simps
QED

val decoder_transport_simps = transport_simps @
  [return_transport_dec_addr, return_transport_range_check,
   return_transport_alloc_buffer, return_transport_clamp,
   return_transport_static, return_transport_getelemptr,
   return_transport_dyn_elem_ptr];

(* Syntax-directed monadic composition; no semantic execution search. *)
fun transport_close g =
  (FIRST [simp decoder_transport_simps >> NO_TAC,
    ho_match_mp_tac return_compile_transport_new_block_ignore >> transport_close,
    ho_match_mp_tac return_compile_transport_ignore_bind >>
      conj_tac >> transport_close,
    ho_match_mp_tac return_compile_transport_bind >>
      conj_tac >> rpt gen_tac >> transport_close]) g;

Theorem return_transport_decoder_mutual:
  (!dst src opc base_op hi info.
    return_compile_transport sa L ids
      (compile_abi_decode_to_buf dst src opc base_op hi info)) /\
  (!dst src opc base_op hi elems ao vo.
    return_compile_transport sa L ids
      (compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo)) /\
  (!dst src opc base_op hi ei asz msz ip cnt.
    return_compile_transport sa L ids
      (compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac)
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "nil"
  >- suspend "cons"
  >> suspend "loop"
QED

Resume return_transport_decoder_mutual[word]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> transport_close
QED
Resume return_transport_decoder_mutual[bytes]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  ho_match_mp_tac return_compile_transport_bind >> conj_tac
  >- (IF_CASES_TAC >> simp decoder_transport_simps >> transport_close) >>
  gen_tac >> transport_db return_transport_dec_addr >>
  ntac 3 (transport_db return_compile_transport_emit_op) >>
  ho_match_mp_tac return_compile_transport_ignore_bind >> conj_tac
  >- simp decoder_transport_simps >>
  ho_match_mp_tac return_compile_transport_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp decoder_transport_simps >> transport_close) >>
  IF_CASES_TAC
  >- (Cases_on `opc` >> simp decoder_transport_simps) >>
  transport_close
QED
Resume return_transport_decoder_mutual[array]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  ho_match_mp_tac return_compile_transport_bind >> conj_tac
  >- (IF_CASES_TAC >> simp decoder_transport_simps >> transport_close) >>
  gen_tac >> transport_db return_transport_dec_addr >>
  ntac 3 (transport_db return_compile_transport_emit_op) >>
  ho_match_mp_tac return_compile_transport_ignore_bind >> conj_tac
  >- simp decoder_transport_simps >>
  ho_match_mp_tac return_compile_transport_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp decoder_transport_simps >> transport_close) >>
  transport_db return_compile_transport_emit_op >>
  ho_match_mp_tac return_compile_transport_ignore_bind >> conj_tac
  >- simp decoder_transport_simps >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC
  >- (ntac 2 (transport_db return_compile_transport_emit_op) >>
      transport_db return_transport_dec_addr >>
      transport_db return_compile_transport_emit_op >>
      Cases_on `opc` >> simp decoder_transport_simps) >>
  transport_db return_transport_alloc_buffer >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  ho_match_mp_tac return_compile_transport_ignore_bind >> conj_tac
  >- simp decoder_transport_simps >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED
Resume return_transport_decoder_mutual[complex]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  IF_CASES_TAC >> transport_close
QED
Resume return_transport_decoder_mutual[nil]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >> transport_close
QED
Resume return_transport_decoder_mutual[cons]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> transport_close
QED
Resume return_transport_decoder_mutual[loop]:
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  Cases_on `dec_info_needs_offset ei` >>
  gvs[] >> transport_close
QED
Finalise return_transport_decoder_mutual
