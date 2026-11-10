(* Source-success builtin input with physical scratch resources after output allocation. *)
Theory abiScratchDecodeInput
Ancestors
  abiScratchDecoderContract abiScratchFootprint abiDecoderFootprint abiBuiltinValidInput abiBuiltinSource
  abiBuiltinDecodeSetup abiBuiltinAllocation abiBuiltinSetupReach abiDecoderReentry abiDecoderReadableTypes abiDecoderCoherence
  abiDecoderTypedContract abiDecoderContract abiDecoderAllocation abiDecodeRanges vyperABIValid
  vyperABI contractABI compileEnv valueEncoding valueEncodingDefs valueEncodingProps venomState words list

Definition abi_scratch_decode_resources_def:
  abi_scratch_decode_resources st first last min_size max_size outsz cnt p d b cap s <=>
    min_size <= cnt /\ cnt <= max_size /\ max_size < dimword (:256) /\
    p + 32 + cnt < dimword (:256) /\ d + outsz < dimword (:256) /\
    ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
        d = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) =
        SOME (d,outsz)) /\
    first <= abi_builtin_decode_output_site st min_size max_size + 2 /\
    let allocated = abi_builtin_allocate_state
      (abi_builtin_decode_output_site st min_size max_size) outsz s in
    abi_decoder_budget first last b cap allocated /\
    abi_footprint_disjoint d outsz
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap allocated) /\
    abi_footprint_disjoint (p + 32) cnt
      ((d,outsz)::abi_decoder_child_scratch (abi_decoder_ids first last) b cap allocated)
End

Definition abi_scratch_decode_pre_def:
  abi_scratch_decode_pre ce env sf ty tv bs v st first last data min_size max_size p d b cap s <=>
    abi_decoder_coherent ce env sf ty tv /\
    abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
      (dec (vyper_to_abi_type env ty) bs) v /\
    vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
    (is_dynamic (vyper_to_abi_type env ty) \/
      static_length (vyper_to_abi_type env ty) <= LENGTH bs) /\
    val_in_memory (BaseTV (BytesT (Dynamic (LENGTH bs)))) (vyperValue$BytesV bs) p s.vs_memory /\
    eval_operand data s = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var data /\
    abi_scratch_decode_resources st first last min_size max_size (type_memory_bytes ce ty)
      (LENGTH bs) p d b cap s
End

Theorem abi_scratch_decode_source:
  abi_scratch_decode_pre ce env sf ty tv bs v st first last data min_size max_size p d b cap s ==>
  mload p s = n2w (LENGTH bs) /\ mem_bytes_at (p + 32) (LENGTH bs) s.vs_memory = bs
Proof
  simp_tac bool_ss [abi_scratch_decode_pre_def] >> strip_tac >>
  fs[val_in_memory_def, mem_word_at_eq_mload]
QED

Theorem abi_scratch_decode_pre_from_source:
  abi_decoder_coherent ce env sf ty tv /\
  evaluate_abi_decode env ty bs = INL v /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) p s.vs_memory /\
  eval_operand data s = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var data /\
  abi_scratch_decode_resources st first last min_size max_size (type_memory_bytes ce ty)
    (LENGTH bs) p d b cap s ==>
  abi_scratch_decode_pre ce env sf ty tv bs v st first last data min_size max_size p d b cap s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_source_metadata >> strip_tac >>
  drule evaluate_abi_decode_vyper_valid_enc >> strip_tac >>
  drule vyper_valid_enc_static_length_lower >> strip_tac >>
  asm_simp_tac bool_ss [abi_scratch_decode_pre_def] >>
  fs[vyper_valid_enc_def, val_in_memory_def, Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"]
QED

(* Physical observations after actual builtin setup; positions are relative. *)
Theorem abi_scratch_decode_ranges:
  abi_scratch_decode_resources st first last min_size max_size outsz cnt p d b cap initial /\
  abi_builtin_allocation_frame next (abi_builtin_decode_output_site st min_size max_size)
    outsz initial prepared /\
  eval_operand base_op prepared = SOME (n2w (p + 32)) /\
  eval_operand dst prepared = SOME (n2w d) /\
  eval_operand hi prepared = SOME (n2w cnt) ==>
  abi_scratch_decoder_ranges MLOAD base_op hi (Lit 0w) dst (p + 32) 0 cnt d outsz first last b cap prepared
Proof
  simp_tac bool_ss [abi_scratch_decode_resources_def, LET_THM] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_child_scratch (abi_decoder_ids first last) b cap prepared =
    abi_decoder_child_scratch (abi_decoder_ids first last) b cap
      (abi_builtin_allocate_state (abi_builtin_decode_output_site st min_size max_size) outsz initial)` by
    fs[abi_builtin_allocation_frame_def, abi_decoder_child_scratch_def] >>
  asm_simp_tac (srw_ss()) [abi_scratch_decoder_ranges_def, abi_decode_source_opcode_def] >>
  conj_tac >- simp[eval_operand_def] >>
  disj2_tac >> qexists_tac `cnt` >> simp[]
QED

Theorem abi_scratch_decode_pre_ready:
  abi_builtin_decode_setup data min_size max_size (type_memory_bytes ce ty) st = (ops,ready) /\
  abi_scratch_decode_pre ce env sf ty tv bs v st first last data min_size max_size p d b cap initial /\
  abi_builtin_allocation_frame st.cs_next_var (abi_builtin_decode_output_site st min_size max_size)
    (type_memory_bytes ce ty) initial prepared /\
  eval_operand (FST ops) prepared = SOME (n2w d) /\
  eval_operand (FST (SND ops)) prepared = SOME (n2w (p + 32)) /\
  eval_operand (SND (SND ops)) prepared = SOME (n2w (LENGTH bs)) ==>
  first <= abi_decoder_entry_floor ready /\ abi_decoder_budget first last b cap prepared /\
  abi_scratch_decoder_input ce env sf ty tv bs v ready (Lit 0w) (FST ops)
    MLOAD (FST (SND ops)) (SND (SND ops)) (p + 32) 0 d first last b cap prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_decode_setup_live >> strip_tac >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  drule_all abi_scratch_decode_source >> strip_tac >>
  qpat_assum `abi_scratch_decode_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decode_pre_def]) >>
  qpat_assum `abi_scratch_decode_resources _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_scratch_decode_resources_def, LET_THM]) >>
  `first <= abi_decoder_entry_floor ready` by fs[abi_decoder_entry_floor_def] >>
  `abi_decoder_budget first last b cap prepared` by
    (drule abi_builtin_allocation_frame_budget >> simp[]) >>
  drule_all abi_scratch_decode_ranges >> strip_tac >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  asm_simp_tac (srw_ss()) [abi_scratch_decoder_input_def, abi_decode_source_def,
    abi_decoder_operand_live_def]
QED
