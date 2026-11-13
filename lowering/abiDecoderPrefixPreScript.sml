(* Prefix observation establishes the existing recursive decoder input at an
   arbitrary child address. The source need not be a standalone Bytes object. *)
Theory abiDecoderPrefixPre
Ancestors
  abiCanonicalHeadSize abiDecoderCoherence abiDecoderTypedContract abiDecoderReentry
  abiDecoderContract vyperABI contractABI valueEncoding compileEnv venomState words list arithmetic

Theorem abi_decode_source_prefix_window:
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\ n <= LENGTH bs ==>
  mem_bytes_at sb n (abi_decode_source opc s) = TAKE n bs
Proof
  strip_tac >> mp_tac (Q.INST [`off` |-> `0`] abi_decode_source_window) >> simp[]
QED

Theorem abi_decoder_pre_from_prefix:
  abi_decoder_metadata ce env ty tv di av v /\
  abi_decoder_reservation (abi_decoder_entry_floor st) last b cap s /\
  abi_decoder_ranges opc base_op hi src dst src_base sb (LENGTH bs) d (type_memory_bytes ce ty) b cap s /\
  mem_bytes_at (src_base + sb) (LENGTH bs) (abi_decode_source opc s) = bs /\
  LENGTH (enc (vyper_to_abi_type env ty) av) <= LENGTH bs /\
  TAKE (LENGTH (enc (vyper_to_abi_type env ty) av)) bs = enc (vyper_to_abi_type env ty) av /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var hi ==>
  abi_decoder_pre ce env ty tv di av v st last src dst opc base_op hi src_base sb d b cap
    (abi_decoder_prune_vars st.cs_next_var s)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand src s = SOME (n2w sb)` by fs[abi_decoder_ranges_def] >>
  `abi_decoder_ranges opc base_op hi src dst src_base sb (LENGTH (enc (vyper_to_abi_type env ty) av))
    d (type_memory_bytes ce ty) b cap s` by
    (irule (SRULE [] (Q.INST [`delta` |-> `0`] abi_decoder_child_ranges)) >>
     conj_tac >- simp[] >>
     qexistsl_tac [`LENGTH (bs:word8 list)`, `src`] >> simp[]) >>
  `mem_bytes_at (src_base + sb) (LENGTH (enc (vyper_to_abi_type env ty) av)) (abi_decode_source opc s) =
    enc (vyper_to_abi_type env ty) av` by
    (drule abi_decode_source_prefix_window >>
     disch_then (qspec_then `LENGTH (enc (vyper_to_abi_type env ty) av)` mp_tac) >>
     simp[]) >>
  drule_all abi_decoder_pre_prune >> simp[]
QED

Theorem abi_decoder_recursive_pre_from_prefix:
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
  abi_decoder_reservation (abi_decoder_entry_floor st) last b cap s /\
  abi_decoder_ranges opc base_op hi src dst src_base sb (LENGTH bs) d (type_memory_bytes ce ty) b cap s /\
  mem_bytes_at (src_base + sb) (LENGTH bs) (abi_decode_source opc s) = bs /\
  LENGTH (enc (vyper_to_abi_type env ty) av) <= LENGTH bs /\
  TAKE (LENGTH (enc (vyper_to_abi_type env ty) av)) bs = enc (vyper_to_abi_type env ty) av /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var hi ==>
  abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
    st last src dst opc base_op hi src_base sb d b cap (abi_decoder_prune_vars st.cs_next_var s)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_pre_from_prefix >> simp[abi_decoder_recursive_pre_def]
QED
