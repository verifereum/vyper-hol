(* Canonical source and post-copy layout for static-element dynamic arrays. *)
Theory abiDecoderBulkContract
Ancestors
  abiStaticDynarrayLayout abiCanonicalArrays abiStaticAggregateProps
  abiStaticLayoutProps abiStaticPrimitiveProps valueEncoding vyperABI vyperTyping
  contractABI byte words arithmetic list rich_list

Theorem abi_bulk_contract_dimindex[simp,local]: dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem static_dynarray_encoding:
  ~is_dynamic ty ==>
  enc (Array NONE ty) (ListV avs) =
    word_to_bytes (n2w (LENGTH avs) : bytes32) T ++ FLAT (MAP (enc ty) avs)
Proof
  strip_tac >>
  `enc (Array NONE ty) (ListV avs) = enc_number (Uint 256) (NumV (LENGTH avs)) ++
    enc (Array (SOME (LENGTH avs)) ty) (ListV avs)` by
    (pure_rewrite_tac[canonical_array_tuple] >> simp[]) >>
  asm_simp_tac bool_ss [enc_static_array, enc_number_def]
QED

Theorem static_dynarray_source_windows:
  static_layout_compatible ce env ty tv /\ all_have_type tv vs /\
  vyper_to_abi_same env ty vs = SOME avs /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs))) source =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) ==>
  mem_word_at sb source = n2w (LENGTH vs) /\
  mem_bytes_at (sb + 32) (LENGTH vs * type_memory_size tv) source =
    FLAT (MAP (enc (vyper_to_abi_type env ty)) avs)
Proof
  strip_tac >> drule static_layout_compatible_properties >> strip_tac >>
  drule_all static_same_canonical_layout >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `mem_bytes_at sb _ source = _` mp_tac >>
  asm_simp_tac bool_ss [static_dynarray_encoding] >> strip_tac >>
  drule mem_bytes_at_append_parts >> strip_tac >>
  gvs[mem_word_at_bytes, word_of_bytes_word_to_bytes,
      dividesTheory.divides_def, Excl "enc_def"]
QED

Theorem static_dynarray_copied_layout:
  static_layout_compatible ce env ty tv /\ all_have_type tv vs /\
  vyper_to_abi_same env ty vs = SOME avs /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs))) source =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  mem_word_at d mem = n2w (LENGTH vs) /\
  mem_bytes_at (d + 32) (LENGTH vs * type_memory_size tv) mem =
    mem_bytes_at (sb + 32) (LENGTH vs * type_memory_size tv) source ==>
  val_in_memory (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) d mem
Proof
  strip_tac >> drule_all static_dynarray_source_windows >> strip_tac >>
  `mem_bytes_at (d + 32) (LENGTH vs * type_memory_size tv) mem =
    FLAT (MAP (enc (vyper_to_abi_type env ty)) avs)` by asm_rewrite_tac[] >>
  mp_tac static_dynarray_canonical_layout >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_BULK_CONTRACT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder bulk contract not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderBulkContract");
