(* All recursive encoder actions preserve their containing CFG prefixes. *)
Theory abiEncoderAppend
Ancestors
  abiEncoder abiDecoderAppend fragExec compileEnv emitHelper venomInst context list

val encode_append_simps =
  [cs_appends_return, cs_appends_prims, cs_appends_emit_helpers,
   cs_appends_abi_alloc_buffer, LET_THM];

fun encode_append_tac extra g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss()) (extra @ encode_append_simps)],
    first_x_assum (fn th => FIRST_PROVE [irule (SRULE[] th) >> asm_simp_tac (srw_ss()) []]),
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- encode_append_tac extra >> rpt gen_tac >> encode_append_tac extra,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> encode_append_tac extra,
    IF_CASES_TAC >> fs[] >> encode_append_tac extra]) g;

Theorem cs_appends_abi_encode_static:
  cs_appends (compile_abi_encode_static dst src)
Proof
  rewrite_tac [compile_abi_encode_static_def] >> encode_append_tac []
QED

Theorem cs_appends_abi_encode_static_info:
  !dst src ei. cs_appends (compile_abi_encode_static_info dst src ei)
Proof
  rpt gen_tac >> Cases_on `ei` >> rewrite_tac [compile_abi_encode_static_info_def] >>
  simp_tac (srw_ss()) [cs_appends_abi_encode_static] >> encode_append_tac []
QED

Theorem cs_appends_abi_encode_static_loop:
  cs_appends (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
Proof
  rewrite_tac [compile_abi_encode_dyn_static_loop_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> encode_append_tac [cs_appends_abi_encode_static_info]
QED

(* Remove the let-bound size/flag witnesses introduced by compiler induction. *)
Theorem abi_encoder_complex_append_bindings:
  (!size flag ptr alloc. size = total /\ flag = dynamic /\ flag /\ ptr = alloc.buf_operand ==> P ptr) /\
  (!size flag. size = total /\ flag = dynamic /\ ~flag ==> P (Lit 0w)) ==>
  (!alloc. dynamic ==> P alloc.buf_operand) /\ (~dynamic ==> P (Lit 0w))
Proof
  strip_tac >> conj_tac
  >- (qx_gen_tac `alloc` >> strip_tac >>
      qpat_x_assum `!size flag ptr alloc. _`
        (qspecl_then [`total`, `T`, `alloc.buf_operand`, `alloc`] mp_tac) >> asm_simp_tac bool_ss []) >>
  strip_tac >> qpat_x_assum `!size flag. _` (qspecl_then [`total`, `F`] mp_tac) >>
  asm_simp_tac bool_ss []
QED

Theorem cs_appends_abi_encode_mutual:
  (!dst src ei dyn off ptr. cs_appends (compile_abi_encode_child dst src ei dyn off ptr)) /\
  (!dst src ei. cs_appends (compile_abi_encode_to_buf dst src ei)) /\
  (!dst src infos so ho ptr. cs_appends (compile_abi_encode_complex_elems dst src infos so ho ptr)) /\
  (!dst src ei asz msz len. cs_appends (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt (disch_then strip_assume_tac) >> ONCE_REWRITE_TAC [compile_abi_encode_child_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  TRY (drule_all abi_encoder_complex_append_bindings >> strip_tac) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  encode_append_tac [cs_appends_abi_encode_static, cs_appends_abi_encode_static_loop]
QED

Theorem cs_extends_abi_encode:
  compile_abi_encode_to_buf dst src ei st = (out,st') ==> cs_extends st st'
Proof
  metis_tac[cj 2 cs_appends_abi_encode_mutual, cs_appends_def]
QED

Theorem cs_extends_abi_encode_child:
  compile_abi_encode_child dst src ei dyn off dyn_ptr st = (out,st') ==> cs_extends st st'
Proof
  metis_tac[cj 1 cs_appends_abi_encode_mutual, cs_appends_def]
QED
