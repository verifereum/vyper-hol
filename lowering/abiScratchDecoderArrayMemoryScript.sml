(* Physical child writes preserve actual source bytes and the initialized array prefix. *)
Theory abiScratchDecoderArrayMemory
Ancestors
  abiScratchDecoderContract abiScratchDecoderSubwindow abiScratchEncoderContract
  abiScratchEffectFrame abiScratchFootprint abiEncoderArrayFrame
  abiDecoderValidArrayScratch abiDecoderValidArrayMemory abiDecoderArrayScratch
  abiDecoderFootprint abiDecoderAllocation abiDecoderFrame abiDecoderContract
  abiDecodeRanges valueEncoding vyperTyping venomState words list arithmetic

Theorem abi_scratch_array_prefix_disjoint:
  abi_footprint_disjoint d outsz fp /\ d + 32 + used + sz <= d + outsz ==>
  abi_footprint_disjoint d 32 ((d + 32 + used,sz)::fp) /\
  abi_footprint_disjoint (d + 32) used ((d + 32 + used,sz)::fp)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_footprint_disjoint d 32 fp /\ abi_footprint_disjoint (d + 32) used fp` by
    (conj_tac >> irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`d`, `outsz`] >> asm_simp_tac bool_ss [] >> decide_tac) >>
  asm_simp_tac arith_ss [abi_scratch_disjoint_cons]
QED

Theorem abi_scratch_decoder_array_child_advance:
  abi_decoder_valid_array_memory opc bs tv vs sb d j s /\ j < LENGTH vs /\
  all_have_type tv vs /\
  val_in_memory tv (EL j vs) (d + 32 + j * type_memory_size tv) t.vs_memory /\
  abi_scratch_effect first last lo hi next limit_st
    (d + 32 + j * type_memory_size tv) (type_memory_size tv) b cap s t /\
  first <= lo /\ hi <= last /\
  abi_scratch_decoder_ranges opc hi_op src dst sb (LENGTH bs) d outsz first last b cap s /\
  d + 32 + j * type_memory_size tv + type_memory_size tv <= d + outsz ==>
  abi_decoder_valid_array_memory opc bs tv vs sb d (SUC j) t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_effect_frame >> strip_tac >>
  qpat_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_ranges_def]) >>
  drule_all abi_scratch_array_prefix_disjoint >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  irule abi_decoder_valid_array_child_advance >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`s`, `(d + 32 + j * type_memory_size tv,type_memory_size tv)::
    abi_decoder_child_scratch (abi_decoder_ids first last) b cap s`] >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  irule abi_scratch_disjoint_output_subwindow >>
  qexistsl_tac [`d`, `outsz`] >> asm_simp_tac arith_ss []
QED

Theorem abi_scratch_decoder_slot_separation:
  abi_scratch_decoder_ranges opc hi src dst sb len d outsz first last b cap s /\
  first <= site /\ site < last /\ FLOOKUP s.vs_allocas site = SOME (slot,32) ==>
  (d + outsz <= slot \/ slot + 32 <= d) /\
  (opc = MLOAD ==> sb + len <= slot \/ slot + 32 <= sb)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `MEM (slot,32) (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_scratch_registered_member >> simp_tac (srw_ss()) [] >> qexists_tac `site` >>
     asm_simp_tac (srw_ss()) [abi_decoder_ids_def]) >>
  qpat_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_ranges_def]) >>
  conj_tac
  >- (qpat_x_assum `abi_footprint_disjoint d outsz _`
        (qspecl_then [`slot`, `32`] mp_tac o PURE_REWRITE_RULE [abi_footprint_disjoint_def]) >>
      asm_simp_tac bool_ss []) >>
  strip_tac >> qpat_x_assum `opc = MLOAD ==> _` (fn th => drule_all th) >>
  simp_tac bool_ss [abi_scratch_disjoint_cons] >>
  disch_then (fn th => mp_tac (CONJUNCT2 th)) >>
  simp_tac bool_ss [abi_footprint_disjoint_def] >>
  disch_then (qspecl_then [`slot`, `32`] mp_tac) >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_ARRAY_MEMORY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical array memory preservation not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderArrayMemory");

