(* Encoder allocation syntax, using the shared code certificate. *)
Theory exprExtRequestEncoderCode
Ancestors
  abiDecoderCode abiEncoderAppend abiEncoder compileEnv emitHelper

val encoder_code_simps =
  [abi_decoder_code_return, abi_decoder_code_emit_op,
   abi_decoder_code_emit_void, abi_decoder_code_emit_inst,
   abi_decoder_code_fresh_label, abi_decoder_code_new_block,
   abi_decoder_code_alloc_buffer, LET_THM];

fun encoder_code_tac extra g =
  (rpt gen_tac >> simp_tac pure_ss [LET_THM] >> BETA_TAC >> FIRST [FIRST_PROVE [asm_simp_tac (srw_ss()) (extra @ encoder_code_simps)],
    first_x_assum (fn th => FIRST_PROVE
      [irule (SRULE[] th) >> asm_simp_tac (srw_ss()) []]),
    ho_match_mp_tac abi_decoder_code_bind >> conj_tac
      >- encoder_code_tac extra >> rpt gen_tac >> encoder_code_tac extra,
    ho_match_mp_tac abi_decoder_code_ignore_bind >> conj_tac >> encoder_code_tac extra,
    IF_CASES_TAC >> fs[] >> encoder_code_tac extra]) g;

Theorem extrequest_encoder_code_static:
  !st. abi_decoder_code st (SND (compile_abi_encode_static dst src st))
Proof
  rewrite_tac[compile_abi_encode_static_def] >> encoder_code_tac []
QED

Theorem extrequest_encoder_code_static_info:
  !dst src ei st. abi_decoder_code st
    (SND (compile_abi_encode_static_info dst src ei st))
Proof
  rpt gen_tac >> Cases_on `ei` >>
  rewrite_tac[compile_abi_encode_static_info_def] >>
  encoder_code_tac [extrequest_encoder_code_static]
QED

Theorem extrequest_encoder_code_static_loop:
  !st. abi_decoder_code st
    (SND (compile_abi_encode_dyn_static_loop dst src ei asz msz len st))
Proof
  rewrite_tac[compile_abi_encode_dyn_static_loop_def] >>
  encoder_code_tac [extrequest_encoder_code_static_info]
QED

Theorem extrequest_encoder_code_mutual:
  (!dst src ei dyn off ptr st. abi_decoder_code st
     (SND (compile_abi_encode_child dst src ei dyn off ptr st))) /\
  (!dst src ei st. abi_decoder_code st
     (SND (compile_abi_encode_to_buf dst src ei st))) /\
  (!dst src infos so ho ptr st. abi_decoder_code st
     (SND (compile_abi_encode_complex_elems dst src infos so ho ptr st))) /\
  (!dst src ei asz msz len st. abi_decoder_code st
     (SND (compile_abi_encode_dyn_loop dst src ei asz msz len st)))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt (disch_then strip_assume_tac) >>
  ONCE_REWRITE_TAC[compile_abi_encode_child_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  TRY (drule_all abi_encoder_complex_append_bindings >> strip_tac) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  encoder_code_tac [extrequest_encoder_code_static,
    extrequest_encoder_code_static_loop]
QED
