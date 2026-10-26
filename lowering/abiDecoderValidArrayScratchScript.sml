(* Recursive child effects preserve actual input bytes and the decoded prefix. *)
Theory abiDecoderValidArrayScratch
Ancestors
  abiDecoderValidArrayMemory abiDecoderArrayScratch abiDecoderArrayPrefix abiDecoderFrame
  abiDecoderFrameCompose abiDecoderContract valueEncodingProps valueEncodingProofs
  valueEncodingTyping valueEncoding vyperTyping venomState contractABI words list rich_list arithmetic

Theorem abi_decoder_valid_array_child_advance:
  abi_decoder_valid_array_memory opc bs tv vs sb d j before /\ j < LENGTH vs /\
  all_have_type tv vs /\
  val_in_memory tv (EL j vs) (d + 32 + j * type_memory_size tv) after.vs_memory /\
  abi_decode_footprint_frame fp before after /\
  abi_footprint_disjoint d 32 fp /\
  abi_footprint_disjoint (d + 32) (j * type_memory_size tv) fp /\
  abi_decode_source_opcode opc /\
  (opc = MLOAD ==>
    abi_footprint_disjoint sb (LENGTH bs) fp) ==>
  abi_decoder_valid_array_memory opc bs tv vs sb d (SUC j) after
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_valid_array_memory _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_array_memory_def]) >>
  `LENGTH (TAKE j vs) = j /\ all_have_type tv (TAKE j vs)` by
    (fs[all_have_type_EVERY, Excl "enc_def"] >> simp[EVERY_TAKE]) >>
  `elems_in_memory (TAKE j vs ++ [EL j vs]) (d + 32) tv after.vs_memory` by
    (irule abi_decode_footprint_frame_append_element >>
     asm_simp_tac bool_ss [] >>
     qexistsl_tac [`before`, `fp`] >> asm_simp_tac bool_ss []) >>
  `mem_word_at d after.vs_memory = mem_word_at d before.vs_memory` by
    (drule_all abi_decode_footprint_frame_mload >>
     simp[GSYM mem_word_at_eq_mload]) >>
  `mem_bytes_at sb (LENGTH bs) (abi_decode_source opc after) =
   mem_bytes_at sb (LENGTH bs) (abi_decode_source opc before)` by
    (irule abi_decode_footprint_frame_source_window >> asm_simp_tac bool_ss [] >>
     qexists_tac `fp` >>
     asm_simp_tac bool_ss []) >>
  `SUC j <= LENGTH vs` by decide_tac >>
  asm_simp_tac bool_ss [abi_decoder_valid_array_memory_def, TAKE_SUC, TAKE1_DROP]
QED

Theorem abi_decoder_valid_array_child_scratch_advance:
  abi_decoder_valid_array_memory opc bs tv vs sb d j before /\ j < LENGTH vs /\
  all_have_type tv vs /\
  val_in_memory tv (EL j vs) (d + 32 + j * type_memory_size tv) after.vs_memory /\
  abi_decode_footprint_frame
    [(d + 32 + j * type_memory_size tv,type_memory_size tv);(b,cap)] before after /\
  d + 32 + j * type_memory_size tv + type_memory_size tv <= d + outsz /\
  (d + outsz <= b \/ b + cap <= d) /\ abi_decode_source_opcode opc /\
  (opc = MLOAD ==>
    abi_footprint_disjoint sb (LENGTH bs)
      [(d,outsz);(b,cap)]) ==>
  abi_decoder_valid_array_memory opc bs tv vs sb d (SUC j) after
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `d <= d + 32 + j * type_memory_size tv` by
    (pure_rewrite_tac [GSYM ADD_ASSOC] >> irule LESS_EQ_ADD) >>
  `abi_footprint_disjoint d 32
      [(d + 32 + j * type_memory_size tv,type_memory_size tv);(b,cap)] /\
   abi_footprint_disjoint (d + 32) (j * type_memory_size tv)
      [(d + 32 + j * type_memory_size tv,type_memory_size tv);(b,cap)]` by
    (irule abi_decoder_array_prefix_footprint >> qexists_tac `outsz` >>
     asm_simp_tac bool_ss []) >>
  irule abi_decoder_valid_array_child_advance >>
  asm_simp_tac bool_ss [] >>
  qexistsl_tac [`before`,
    `[(d + 32 + j * type_memory_size tv,type_memory_size tv);(b,cap)]`] >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  irule abi_decoder_child_footprint_disjoint >>
  qexistsl_tac [`d`, `outsz`] >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_VALID_ARRAY_SCRATCH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid array prefix scratch not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderValidArrayScratch");
