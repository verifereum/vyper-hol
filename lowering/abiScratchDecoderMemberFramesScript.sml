(* Preserve parent observations and completed members through physical child writes. *)
Theory abiScratchDecoderMemberFrames
Ancestors
  abiScratchDecoderContract abiScratchDecoderTransport abiScratchEncoderContract
  abiScratchEffectFrame abiScratchEffectWiden abiScratchEffectCompose abiScratchFootprint
  abiDecoderMemberFrames abiDecoderAllocation abiDecoderFootprint abiDecoderFrame
  abiDecoderReentry abiDecoderContract abiDecoderTypedContract abiDecodeRanges
  compileEnv valueEncoding vyperTyping venomState words list arithmetic

Theorem abi_scratch_decoder_member_after_head:
  abi_scratch_decoder_ranges opc hi_op src dst sb (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
    (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty) b cap initial after_head /\
  first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi_op /\ st.cs_next_var <= end_st.cs_next_var ==>
  abi_scratch_decoder_ranges opc hi_op src dst sb (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) first last b cap after_head /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc after_head) = bs /\
  fresh_vars_wrt limit_st after_head /\ abi_decoder_budget first last b cap after_head /\
  abi_decoder_operand_live end_st.cs_next_var src /\ abi_decoder_operand_live end_st.cs_next_var dst /\
  abi_decoder_operand_live end_st.cs_next_var hi_op
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap initial after_head` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d + SUM (MAP (type_memory_bytes ce) pretys)`, `end_st.cs_next_id`,
       `st.cs_next_id`, `st.cs_next_var`, `type_memory_bytes ce ty`] >>
     asm_simp_tac arith_ss [MAP_APPEND, MAP, SUM_APPEND, SUM]) >>
  drule_all abi_scratch_decoder_ranges_effect >> strip_tac >>
  drule_all abi_scratch_decoder_source_effect >> strip_tac >>
  `abi_decoder_operand_live end_st.cs_next_var src /\ abi_decoder_operand_live end_st.cs_next_var dst /\
   abi_decoder_operand_live end_st.cs_next_var hi_op` by
    (rpt conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  fs[abi_scratch_effect_def]
QED

Theorem abi_scratch_decoder_suffix_preserves_head:
  val_in_memory tv v cell s.vs_memory /\ value_has_type tv v /\
  abi_scratch_effect first last lo hi next limit_st
    (cell + type_memory_size tv) restsz b cap s t /\
  first <= lo /\ hi <= last /\
  abi_footprint_disjoint cell (type_memory_size tv)
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) ==>
  val_in_memory tv v cell t.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_effect_frame >> strip_tac >>
  `abi_footprint_disjoint cell (type_memory_size tv)
    ((cell + type_memory_size tv,restsz)::
      abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    asm_simp_tac arith_ss [abi_scratch_disjoint_cons] >>
  irule abi_decoder_value_frame >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`(cell + type_memory_size tv,restsz)::
    abi_decoder_child_scratch (abi_decoder_ids first last) b cap s`, `s`] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_member_effects_compose:
  abi_scratch_effect first last lo mid_id next limit_st cell headsz b cap s middle /\
  abi_scratch_effect first last mid_id hi tail_next limit_st
    (cell + headsz) tailsz b cap middle t /\
  first <= lo /\ hi <= last /\ lo <= mid_id /\ mid_id <= hi /\ next <= tail_next ==>
  abi_scratch_effect first last lo hi next limit_st cell (headsz + tailsz) b cap s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_scratch_effect first last lo hi next limit_st cell (headsz + tailsz) b cap s middle` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`cell`, `mid_id`, `lo`, `next`, `headsz`] >>
     asm_simp_tac arith_ss []) >>
  `abi_scratch_effect first last lo hi next limit_st cell (headsz + tailsz) b cap middle t` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`cell + headsz`, `hi`, `mid_id`, `tail_next`, `tailsz`] >>
     asm_simp_tac arith_ss []) >>
  irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >> qexists_tac `middle` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_MEMBER_FRAMES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical member framing not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderMemberFrames");

