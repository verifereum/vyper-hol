(* The complete ABI encoder extends the compiler fragment and both counters. *)
Theory abiBuiltinEncodeAppend
Ancestors
  abiBuiltinEncodeCode abiEncoderAppend abiEncoderCounters abiDecoderAppend
  fragExec compileEnv words list arithmetic

Theorem lower_abi_encode_extends:
  lower_abi_encode ensure method_id_opt src info maxlen st = (out,final) ==>
  cs_extends st final /\ st.cs_next_var <= final.cs_next_var /\
  st.cs_next_id <= final.cs_next_id
Proof
  strip_tac >> drule lower_abi_encode_trace >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `cs_extends st ready /\ cs_extends body_end final` by
    (conj_tac >> irule cs_extends_same_block >> asm_simp_tac bool_ss []) >>
  drule cs_extends_abi_encode >> strip_tac >>
  `cs_extends st body_end` by
    (irule cs_extends_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss []) >>
  `cs_extends st final` by
    (irule cs_extends_trans >> qexists_tac `body_end` >> asm_simp_tac bool_ss []) >>
  Cases_on `method_id_opt` >> asm_simp_tac (srw_ss()) [] >> decide_tac
QED
