(* Pure actual-source data premises for the emitted recursive array loop. *)
Theory abiScratchDecoderLoopContext
Ancestors
  abiScratchDecoderContract abiScratchDecoderTransport abiScratchEncoderContract
  abiScratchDecoderArrayMemory
  abiDecoderValidArrayValues abiDecoderRecursiveArrayFacts abiDecoderRecursiveLoopContext
  abiDecoderCoherence abiDecoderTypedContract abiDecoderEffect abiDecoderProtectedScratch
  abiDecoderAllocation abiDecoderFrame abiDecoderContract abiDecoderLoop abiDecoderReentry
  abiDecodeRanges compileEnv valueEncoding vyperABI vyperValue contractABI venomState
  words list arithmetic

Definition abi_scratch_decoder_loop_data_def:
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc hi_op ip src dst
      sb d slot first last b cap next initial <=>
    abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
    abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
      (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
      (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
    valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\
    (is_dynamic (vyper_to_abi_type env ty) ==>
      !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
    abi_scratch_decoder_ranges opc hi_op src dst sb
      (LENGTH bs)
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) first last b cap initial /\
    abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
    abi_decoder_operand_live next hi_op /\ abi_decoder_operand_live next ip /\
    eval_operand ip initial = SOME (n2w slot) /\ slot < dimword (:256)
End

Theorem abi_scratch_decoder_loop_data_facts:
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc hi_op ip src dst
    sb d slot first last b cap next initial ==>
  32 <= LENGTH bs /\ abi_head_word bs = LENGTH vs /\ all_have_type tv vs /\ LENGTH vs <= maxn /\
  LENGTH vs < dimword (:256) /\ type_memory_size tv = type_memory_bytes ce ty /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = 32 + maxn * type_memory_size tv
Proof
  simp_tac bool_ss [abi_scratch_decoder_loop_data_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_dynarray_values >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_coherent_array_capacity >> strip_tac >>
  `LENGTH vs < dimword (:256)` by decide_tac >>
  asm_simp_tac bool_ss [Once type_memory_bytes_def]
QED

Theorem abi_scratch_decoder_loop_slot_separation:
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc hi_op ip src dst
    sb d slot first last b cap next initial /\
  abi_scratch_effect first last lo hi next limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial s /\
  first <= lo /\ hi <= last /\ first <= site /\ site < last /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) ==>
  (slot + 32 <= d \/ d + 32 + LENGTH vs * type_memory_size tv <= slot) /\
  (opc = MLOAD ==> sb + LENGTH bs <= slot \/
    slot + 32 <= sb)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_decoder_loop_data_facts >> strip_tac >>
  qpat_assum `abi_scratch_decoder_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_loop_data_def]) >>
  drule_all abi_scratch_decoder_ranges_effect >> strip_tac >>
  drule_all abi_scratch_decoder_slot_separation >> strip_tac >>
  `LENGTH vs * type_memory_size tv <= maxn * type_memory_size tv`
    by simp[LE_MULT_RCANCEL] >>
  `d + 32 + LENGTH vs * type_memory_size tv <=
    d + type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    (qpat_x_assum `LENGTH vs * type_memory_size tv <= _` mp_tac >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  conj_tac >- decide_tac >> asm_simp_tac bool_ss []
QED
