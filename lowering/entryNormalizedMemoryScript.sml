(* Transport decoder-normalized memory without identifying sparse values. *)
Theory entryNormalizedMemory
Ancestors
  entryAbiMemoryTransport abiDecoderLayout abiDecoderValidContract
  abiDecoderTypedContract valueEncoding vyperABI vyperTyping
  vyperTypeValues vyperValue vyperValueOperation

Theorem entry_decoder_normalized_memory:
  abi_decoder_coherent ce env sf ty tv /\
  evaluate_type env ty = SOME tv /\
  has_type (vyper_to_abi_type env ty) av /\
  value_has_type tv v /\ value_has_type tv nv /\
  vyper_to_abi env ty v = SOME av /\
  abi_to_vyper env ty av = SOME nv /\ val_in_memory tv nv p mem ==>
  val_in_memory tv v p mem
Proof
  strip_tac >> drule_all abi_decoder_typed_conversion >> strip_tac >>
  metis_tac[entry_common_conversion_memory]
QED

Theorem entry_valid_pre_original_memory:
  abi_decoder_valid_pre ce env sf ty tv bs nv st src dst opc hi sb d b cap initial /\
  value_has_type tv v /\
  vyper_to_abi env ty v = SOME (dec (vyper_to_abi_type env ty) bs) /\
  val_in_memory tv nv p mem ==>
  val_in_memory tv v p mem
Proof
  simp_tac bool_ss [abi_decoder_valid_pre_def, abi_decoder_metadata_def] >>
  rpt strip_tac >> irule entry_decoder_normalized_memory >> metis_tac[]
QED

Theorem entry_dynamic_normalized_memory_probe[local]:
  abi_decoder_coherent ce FEMPTY sf (BaseT (BytesT (Dynamic 4))) (BaseTV (BytesT (Dynamic 4))) /\
  val_in_memory (BaseTV (BytesT (Dynamic 4))) (vyperValue$BytesV [1w;2w]) p mem ==>
  val_in_memory (BaseTV (BytesT (Dynamic 4))) (vyperValue$BytesV [1w;2w]) p mem
Proof
  strip_tac >> irule entry_decoder_normalized_memory >>
  qexistsl_tac [`contractABI$BytesV [1w;2w]`, `ce`, `FEMPTY`,
                `vyperValue$BytesV [1w;2w]`, `sf`, `BaseT (BytesT (Dynamic 4))`] >>
  asm_simp_tac bool_ss [] >> EVAL_TAC
QED

Theorem entry_nested_sparse_normalized_memory_probe[local]:
  abi_decoder_coherent ce FEMPTY sf
    (ArrayT (ArrayT (BaseT (UintT 256)) (Fixed 1)) (Fixed 1))
    (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1)) (Fixed 1)) /\
  val_in_memory (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1)) (Fixed 1))
    (ArrayV (SArrayV [(0, ArrayV (SArrayV [(0, vyperValue$IntV 1)]))])) p mem ==>
  val_in_memory (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1)) (Fixed 1))
    (ArrayV (SArrayV [(0, ArrayV (SArrayV [(0, vyperValue$IntV 1)]))])) p mem
Proof
  strip_tac >> irule entry_decoder_normalized_memory >>
  qexistsl_tac [`ListV [ListV [NumV 1]]`, `ce`, `FEMPTY`,
    `ArrayV (SArrayV [(0, ArrayV (SArrayV [(0, vyperValue$IntV 1)]))]))`, `sf`,
    `ArrayT (ArrayT (BaseT (UintT 256)) (Fixed 1)) (Fixed 1)`] >>
  asm_simp_tac bool_ss [] >> EVAL_TAC
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then () else raise Fail "entry normalized memory inherited admission"
  end) [entry_decoder_normalized_memory, entry_valid_pre_original_memory,
        entry_dynamic_normalized_memory_probe, entry_nested_sparse_normalized_memory_probe];
