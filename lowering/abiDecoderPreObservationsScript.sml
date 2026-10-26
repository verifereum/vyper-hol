(* Recover actual-state observations from a pruned recursive decoder precondition.
   TOP-LEVEL: abi_decoder_pre_observations. *)
Theory abiDecoderPreObservations
Ancestors
  abiDecoderCoherence abiDecoderTypedContract abiDecoderReentry
  abiDecoderPrimitiveArrayReentryInit abiDecoderContract
  compileEnv valueEncoding vyperABI contractABI venomState words list

Theorem abi_decoder_pre_observations:
  abi_decoder_recursive_pre ce env sf ty tv di av v st last src dst opc hi sb d b cap
    (abi_decoder_prune_vars st.cs_next_var initial) ==>
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
  abi_decoder_reservation st.cs_next_id last b cap initial /\
  abi_decoder_ranges opc hi src dst sb (LENGTH (enc (vyper_to_abi_type env ty) av))
    d (type_memory_bytes ce ty) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) (abi_decode_source opc initial) =
    enc (vyper_to_abi_type env ty) av /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi
Proof
  strip_tac >> qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def]) >>
  drule abi_decoder_pre_pruned_operands >> strip_tac >>
  qpat_assum `abi_decoder_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_pre_def]) >>
  `abi_decoder_ranges opc hi src dst sb (LENGTH (enc (vyper_to_abi_type env ty) av))
    d (type_memory_bytes ce ty) b cap initial` by
    (qpat_x_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     asm_simp_tac bool_ss [abi_decoder_prune_ranges]) >>
  asm_simp_tac bool_ss [] >> fs[abi_decoder_prune_source, abi_decoder_prune_reservation, Excl "enc_def"]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_PRE_OBSERVATIONS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI precondition observations not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderPreObservations");
