(* Bridge existing typed tuple-argument representations to complete encoder
   sources for words, flags and dynamic Bytes/String values. *)
Theory abiTupleEncodeSourceInput
Ancestors
  abiTupleEncodeInput abiTupleProps abiEncoderWordSource abiEncoderSourceInput abiEncoderInput
  abiDecoderReentry compileEnv exprLowering valueEncoding vyperABI vyperTyping
  contractABI venomState venomExecSemantics words list arithmetic

Theorem abi_tuple_encode_base_source_input:
  is_word_type (BaseT bt) /\
  abi_tuple_inputs ce [(op,BaseT bt)] [BaseTV bt] [v] s lo hi /\
  value_has_type (BaseTV bt) v /\ vyper_to_abi_base bt v = SOME av /\
  has_type (vyper_base_to_abi_type bt) av /\ ~is_dynamic (vyper_base_to_abi_type bt) /\
  static_length (vyper_base_to_abi_type bt) = 32 /\ abi_decoder_operand_live next op ==>
  abi_tuple_encode_input sf ce (BaseT bt) (vyper_base_to_abi_type bt) av op next lo hi s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_tuple_inputs _ _ _ _ _ _ _` mp_tac >>
  asm_simp_tac bool_ss [abi_tuple_inputs_singleton, abi_tuple_input_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH (enc (vyper_base_to_abi_type bt) av) = 32` by
    (drule_all (cj 1 enc_has_static_length) >> simp[]) >>
  drule_all abi_encoder_base_source_word >> strip_tac >>
  asm_simp_tac bool_ss [abi_tuple_encode_input_def] >>
  qexists_tac `typed_val_to_w256 (BaseTV bt) v` >> asm_simp_tac bool_ss []
QED

Theorem abi_tuple_encode_flag_source_input:
  abi_tuple_inputs ce [(op,FlagT nsid)] [FlagTV m] [FlagV k] s lo hi /\
  has_type (Uint 256) (NumV k) /\ abi_decoder_operand_live next op ==>
  abi_tuple_encode_input sf ce (FlagT nsid) (Uint 256) (NumV k) op next lo hi s
Proof
  strip_tac >> qpat_x_assum `abi_tuple_inputs _ _ _ _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [abi_tuple_inputs_singleton, abi_tuple_input_def, is_word_type_def] >>
  strip_tac >> asm_simp_tac (srw_ss()) [abi_tuple_encode_input_def, is_word_type_def,
    abi_encoder_flag_source_word, is_dynamic_def, static_length_def]
QED

Theorem abi_tuple_encode_nonword_source_input:
  ~is_word_type ty /\ type_memory_bytes ce ty < dimword (:256) /\ abi_decoder_operand_live next op /\
  eval_operand op s = SOME source_word /\
  source_cap <= type_memory_bytes ce ty /\
  abi_encoder_input (type_to_abi_enc_info sf ce ty) at av (w2n source_word) source_cap s.vs_memory /\
  (w2n source_word+source_cap <= lo \/ hi <= w2n source_word) ==>
  abi_tuple_encode_input sf ce ty at av op next lo hi s
Proof
  strip_tac >> asm_simp_tac bool_ss [abi_tuple_encode_input_def] >>
  qexistsl_tac [`w2n source_word`, `source_cap`] >>
  asm_simp_tac (srw_ss()) [n2w_w2n, w2n_lt]
QED

Theorem abi_tuple_encode_nonword_source_input_full:
  ~is_word_type ty /\ type_memory_bytes ce ty < dimword (:256) /\ abi_decoder_operand_live next op /\
  eval_operand op s = SOME source_word /\
  abi_encoder_input (type_to_abi_enc_info sf ce ty) at av (w2n source_word)
    (type_memory_bytes ce ty) s.vs_memory /\
  (w2n source_word+type_memory_bytes ce ty <= lo \/ hi <= w2n source_word) ==>
  abi_tuple_encode_input sf ce ty at av op next lo hi s
Proof
  strip_tac >>
  mp_tac (Q.INST [`source_cap` |-> `type_memory_bytes ce ty`]
    abi_tuple_encode_nonword_source_input) >> simp[]
QED

Theorem abi_tuple_encode_bytes_source_input:
  abi_tuple_inputs ce [(op,BaseT (BytesT (Dynamic n)))]
    [BaseTV (BytesT (Dynamic n))] [vyperValue$BytesV bs] s lo hi /\
  value_has_type (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) /\
  n < dimword (:256) /\ abi_decoder_operand_live next op ==>
  abi_tuple_encode_input sf ce (BaseT (BytesT (Dynamic n)))
    (vyper_to_abi_type env (BaseT (BytesT (Dynamic n)))) (contractABI$BytesV bs) op next lo hi s
Proof
  strip_tac >> qpat_x_assum `abi_tuple_inputs _ _ _ _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [abi_tuple_inputs_singleton, abi_tuple_input_def, is_word_type_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `?p. eval_operand op s = SOME p /\ _`
    (qx_choose_then `source_word` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `abi_encoder_input (type_to_abi_enc_info sf ce (BaseT (BytesT (Dynamic n))))
    (vyper_to_abi_type env (BaseT (BytesT (Dynamic n)))) (contractABI$BytesV bs)
    (w2n source_word) (type_memory_bytes ce (BaseT (BytesT (Dynamic n)))) s.vs_memory` by
    (drule_all abi_encoder_bytes_source_input >> simp[]) >>
  `~is_word_type (BaseT (BytesT (Dynamic n)))` by simp[is_word_type_def] >>
  qpat_assum `!p. eval_operand op s = SOME p ==> _` (fn sep =>
    qpat_assum `eval_operand op s = SOME source_word` (fn evaluated =>
      assume_tac (MATCH_MP (Q.SPEC `source_word` sep) evaluated))) >>
  drule_all abi_tuple_encode_nonword_source_input_full >> simp[]
QED

Theorem abi_tuple_encode_string_source_input:
  abi_tuple_inputs ce [(op,BaseT (StringT n))] [BaseTV (StringT n)] [StringV chars] s lo hi /\
  value_has_type (BaseTV (StringT n)) (StringV chars) /\
  n < dimword (:256) /\ abi_decoder_operand_live next op ==>
  abi_tuple_encode_input sf ce (BaseT (StringT n))
    (vyper_to_abi_type env (BaseT (StringT n)))
    (contractABI$BytesV (MAP (n2w o ORD) chars)) op next lo hi s
Proof
  strip_tac >> qpat_x_assum `abi_tuple_inputs _ _ _ _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [abi_tuple_inputs_singleton, abi_tuple_input_def, is_word_type_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `?p. eval_operand op s = SOME p /\ _`
    (qx_choose_then `source_word` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `abi_encoder_input (type_to_abi_enc_info sf ce (BaseT (StringT n)))
    (vyper_to_abi_type env (BaseT (StringT n))) (contractABI$BytesV (MAP (n2w o ORD) chars))
    (w2n source_word) (type_memory_bytes ce (BaseT (StringT n))) s.vs_memory` by
    (drule_all abi_encoder_string_source_input >> simp[]) >>
  `~is_word_type (BaseT (StringT n))` by simp[is_word_type_def] >>
  qpat_assum `!p. eval_operand op s = SOME p ==> _` (fn sep =>
    qpat_assum `eval_operand op s = SOME source_word` (fn evaluated =>
      assume_tac (MATCH_MP (Q.SPEC `source_word` sep) evaluated))) >>
  drule_all abi_tuple_encode_nonword_source_input_full >> simp[]
QED
