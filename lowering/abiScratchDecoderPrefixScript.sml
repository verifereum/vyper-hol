(* Existing scalar execution can use a derived empty reservation at the frontier.
   Actual bytes determine the readable prefix; no canonical whole-input equality is assumed. *)
Theory abiScratchDecoderPrefix
Ancestors
  vyperABIValid abiScratchDecoderRanges abiScratchDecoderContract abiDecoderValidContract abiDecoderPrefixPre
  abiDecoderDynamic abiDecoderCoherence abiDecoderTypedContract abiDecoderContract
  abiDecoderReentry abiValidStatic abiDecodeRanges compileEnv valueEncoding vyperABI contractABI
  venomState words list rich_list

Theorem abi_scratch_decoder_static_prefix:
  ~is_dynamic at /\ valid_enc at bs /\ abi_member_head_size at <= LENGTH bs ==>
  LENGTH (enc at (dec at bs)) <= LENGTH bs /\
  TAKE (LENGTH (enc at (dec at bs))) bs = enc at (dec at bs)
Proof
  strip_tac >>
  `static_length at <= LENGTH bs` by
    (qpat_x_assum `abi_member_head_size at <= LENGTH bs` mp_tac >>
     asm_simp_tac bool_ss [abi_member_head_size_def]) >>
  drule abi_static_prefix_static >> simp_tac bool_ss [abi_static_prefix_def] >>
  disch_then (qspec_then `bs` mp_tac) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  asm_simp_tac (srw_ss()) [LENGTH_TAKE_EQ, TAKE_TAKE_MIN, Excl "enc_def", Excl "dec_def"]
QED

Theorem abi_scratch_decoder_static_pre:
  abi_scratch_decoder_input ce env sf ty tv bs v st src dst opc hi sb d first last b cap s /\
  abi_decoder_budget first last b cap s /\ ~is_dynamic (vyper_to_abi_type env ty) ==>
  abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty)
    (dec (vyper_to_abi_type env ty) bs) v st st.cs_next_id src dst opc hi sb d
    s.vs_alloca_next 0 (abi_decoder_prune_vars st.cs_next_var s)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_input_point >> strip_tac >>
  `abi_decoder_reservation st.cs_next_id st.cs_next_id s.vs_alloca_next 0 s` by
    (mp_tac abi_scratch_decoder_point_reservation >> asm_simp_tac bool_ss []) >>
  `vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
   abi_member_head_size (vyper_to_abi_type env ty) <= LENGTH bs` by
    fs[abi_scratch_decoder_input_def, abi_member_head_size_def,
      Excl "vyper_decode_valid_enc_def", Excl "dec_def"] >>
  `valid_enc (vyper_to_abi_type env ty) bs` by
    (irule vyper_decode_valid_enc_static >> simp[]) >>
  drule_all abi_scratch_decoder_static_prefix >> strip_tac >>
  mp_tac (Q.INST [`last` |-> `st.cs_next_id`, `b` |-> `s.vs_alloca_next`, `cap` |-> `0:num`]
    abi_decoder_valid_pre_prefix) >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_word_pre:
  type_to_abi_dec_info (sf:string |-> (string # vyperAST$type # num) list) ce ty = DecPrimWord clamp /\
  abi_scratch_decoder_input ce env sf ty tv bs v st src dst opc hi sb d first last b cap s /\
  abi_decoder_budget first last b cap s ==>
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp)
    (dec (vyper_to_abi_type env ty) bs) v st st.cs_next_id src dst opc hi sb d
    s.vs_alloca_next 0 (abi_decoder_prune_vars st.cs_next_var s)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_scratch_decoder_input_def] >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  `~is_dynamic (vyper_to_abi_type env ty)` by
    (qpat_assum `type_to_abi_dec_info sf ce ty = DecPrimWord clamp` (fn eq =>
       qpat_x_assum `abi_decoder_dynamic _ = _` (mp_tac o PURE_REWRITE_RULE [eq])) >>
     simp_tac (srw_ss()) [abi_decoder_dynamic_def]) >>
  drule_all abi_scratch_decoder_static_pre >> asm_simp_tac bool_ss []
QED
