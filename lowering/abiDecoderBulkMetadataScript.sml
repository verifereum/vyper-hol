(* Static dynamic-array descriptor sizes derived from recursive coherence. *)
Theory abiDecoderBulkMetadata
Ancestors
  abiDecoderCoherence abiDecoderLayout abiStaticLayoutProps
  exprLowering compileEnv vyperTyping vyperValue valueEncoding
  abiDecodeRanges contractABI words

Theorem abi_decoder_bulk_metadata:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  DecDynArray ei abi_sz mem_sz F maxn =
    type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) /\
  ~dec_info_needs_clamp ei ==>
  static_layout_compatible ce env ty tv /\
  ei = type_to_abi_dec_info sf ce ty /\
  abi_sz = type_memory_size tv /\ mem_sz = type_memory_size tv /\
  maxn < dimword (:256) /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = 32 + maxn * mem_sz
Proof
  strip_tac >>
  qpat_x_assum `DecDynArray _ _ _ _ _ = _` mp_tac >>
  simp[Once type_to_abi_dec_info_def] >> strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by
    gvs[abi_decoder_coherent_array_iff] >>
  `static_layout_compatible ce env ty tv` by
    (drule_all abi_decoder_unclamped_static_layout >> simp[]) >>
  drule static_layout_compatible_properties >> strip_tac >>
  `abi_decoder_header ce env ty tv` by
    (drule abi_decoder_coherent_header >> simp[]) >>
  `evaluate_type env (ArrayT ty (Dynamic maxn)) =
   SOME (ArrayTV tv (Dynamic maxn))` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  mp_tac (Q.SPECL [`env`, `ArrayT ty (Dynamic maxn)`, `ArrayTV tv (Dynamic maxn)`]
    (cj 1 evaluate_type_well_formed)) >>
  simp[well_formed_type_value_def] >> strip_tac >>
  gvs[abi_decoder_header_def, abi_member_head_size_def, type_memory_bytes_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_BULK_METADATA_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder bulk metadata not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderBulkMetadata");
