(* Metadata, rather than a fresh standalone source gate, bounds decoded byte
   payloads even when a child's actual suffix exceeds its own size bound. *)
Theory abiDecoderValidBytesInput
Ancestors
  abiDecoderValidContract abiDecoderValidBytes abiDecoderBytes abiDecoderBytesTyped
  abiDecoderString abiDecoderTypedContract abiDecoderContract abiDecoderCoherence
  abiDecoderReentry abiDecoderArrayInitReentry abiValidBytesUnwrap
  compileEnv valueEncoding vyperABI vyperValue contractABI
  venomState words list arithmetic

Theorem abi_decoder_dynamic_bytes_value:
  dec (Bytes NONE) bs = contractABI$BytesV (TAKE (abi_head_word bs) (DROP 32 bs)) /\
  dec String bs = contractABI$BytesV (TAKE (abi_head_word bs) (DROP 32 bs))
Proof
  simp_tac bool_ss [dec_def, GSYM abi_head_word_def, LET_THM]
QED

Theorem abi_decoder_valid_bytes_metadata:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  abi_decoder_metadata ce env ty tv di (dec (vyper_to_abi_type env ty) bs) v ==>
  ?at payload. vyper_to_abi_type env ty = at /\ (at = Bytes NONE \/ at = String) /\
    dec at bs = contractABI$BytesV payload /\ LENGTH payload <= n /\
    (!mem d. val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d mem /\
      val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d mem ==>
      val_in_memory tv v d mem)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qexistsl_tac [`vyper_to_abi_type env ty`, `TAKE (abi_head_word bs) (DROP 32 bs)`] >>
  gvs[abi_decoder_metadata_def, abi_decoder_dynamic_bytes_value, LET_THM, abi_to_vyper_def,
      compatible_bound_def, evaluate_type_def, AllCaseEqs(),
      Excl "dec_def", Excl "valid_enc_def"]
QED

Theorem abi_decoder_valid_bytes_input:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  abi_decoder_valid_pre ce env sf ty tv bs v st src dst opc hi sb d b cap initial ==>
  ?at payload. abi_decoder_valid_bytes_pre n at bs payload st src dst opc hi sb d
      (abi_decoder_prune_vars st.cs_next_var initial) /\
    type_to_abi_dec_info sf ce ty = DecBytestring n /\
    type_memory_bytes ce ty = abi_decode_bytes_copy_size n /\
    (!mem. val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d mem /\
      val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d mem ==>
      val_in_memory tv v d mem)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (INST_TYPE [alpha |-> ``:string``, beta |-> ``:num``] abi_valid_bytes_lowering) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_decoder_valid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_pre_def]) >>
  drule_all abi_decoder_valid_bytes_metadata >>
  disch_then (qx_choose_then `at` (qx_choose_then `payload`
    (MAP_EVERY assume_tac o CONJUNCTS))) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  mp_tac (cj 3 abi_decoder_bytes_copy_size) >> strip_tac >>
  `n < dimword (:256)` by gvs[] >>
  `abi_decoder_valid_bytes_pre n at bs payload st src dst opc hi sb d
     (abi_decoder_prune_vars st.cs_next_var initial)` by
    (asm_simp_tac bool_ss [abi_decoder_valid_bytes_pre_def, abi_decoder_prune_fresh,
      abi_decoder_prune_eval, abi_decoder_prune_source] >>
     gvs[Excl "valid_enc_def", Excl "dec_def", Excl "enc_def"]) >>
  qexistsl_tac [`at`, `payload`] >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >> first_x_assum irule >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_VALID_BYTES_INPUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid bytes child input not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderValidBytesInput");
