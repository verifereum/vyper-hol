(* Preserve canonical sources and decoded members through later child effects.
   TOP-LEVEL: abi_decoder_member_frame_source, abi_decoder_suffix_preserves_head.
   Helper: typed values are preserved outside an arbitrary write footprint. *)
Theory abiDecoderMemberFrames
Ancestors
  abiDecoderEffect abiDecoderArrayScratch abiDecoderFrame abiDecoderTypedContract
  abiDecoderRecursiveArrayIteration abiDecoderReentry
  abiDecoderContract valueEncodingTyping valueEncodingProps valueEncoding
  vyperTyping venomState words list arithmetic

Theorem abi_decoder_value_frame:
  val_in_memory tv v d s.vs_memory /\ value_has_type tv v /\
  abi_decode_footprint_frame fp s t /\ abi_footprint_disjoint d (type_memory_size tv) fp ==>
  val_in_memory tv v d t.vs_memory
Proof
  strip_tac >> drule_all (cj 1 value_has_type_val_wf) >> strip_tac >>
  drule_all abi_decode_footprint_frame_slice >> strip_tac >>
  mp_tac (Q.SPECL [`tv`, `v`, `d`, `type_memory_size tv`, `s.vs_memory`, `t.vs_memory`]
    val_in_memory_mem_agree) >> asm_simp_tac bool_ss [LESS_EQ_REFL]
QED

Theorem abi_decoder_member_frame_source:
  abi_decoder_effect first last lo hi next limit_st cell sz b cap s t /\
  abi_decoder_ranges opc hi_op src dst sb len d outsz b cap s /\
  d <= cell /\ cell + sz <= d + outsz ==>
  mem_bytes_at sb len (abi_decode_source opc t) = mem_bytes_at sb len (abi_decode_source opc s)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  irule abi_decode_footprint_frame_source_window >> asm_simp_tac bool_ss [] >>
  qexists_tac `[(cell,sz);(b,cap)]` >> asm_simp_tac bool_ss [] >> strip_tac >>
  irule abi_decoder_child_footprint_disjoint >> qexistsl_tac [`d`, `outsz`] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_decoder_suffix_preserves_head:
  val_in_memory tv v cell s.vs_memory /\ value_has_type tv v /\
  abi_decoder_effect first last lo hi next limit_st
    (cell + type_memory_size tv) restsz b cap s t /\
  (cell + type_memory_size tv + restsz <= b \/ b + cap <= cell) ==>
  val_in_memory tv v cell t.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_footprint_disjoint cell (type_memory_size tv)
    [(cell + type_memory_size tv,restsz);(b,cap)]` by
    (simp[abi_footprint_disjoint_def] >> decide_tac) >>
  irule abi_decoder_value_frame >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`[(cell + type_memory_size tv,restsz);(b,cap)]`, `s`] >>
  fs[abi_decoder_effect_def]
QED

Theorem abi_decoder_member_observations:
  abi_decoder_effect first last lo hi next limit_st cell sz b cap before after /\
  abi_decoder_ranges opc hi_op src dst sb len d outsz b cap before /\
  d <= cell /\ cell + sz <= d + outsz /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi_op /\ next <= new_next /\
  mem_bytes_at sb len (abi_decode_source opc before) = bytes ==>
  abi_decoder_ranges opc hi_op src dst sb len d outsz b cap after /\
  mem_bytes_at sb len (abi_decode_source opc after) = bytes /\
  fresh_vars_wrt limit_st after /\ abi_decoder_budget first last b cap after /\
  abi_decoder_operand_live new_next src /\ abi_decoder_operand_live new_next dst /\
  abi_decoder_operand_live new_next hi_op
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_effect_ranges >> strip_tac >>
  drule_all abi_decoder_member_frame_source >> strip_tac >>
  `abi_decoder_operand_live new_next src /\ abi_decoder_operand_live new_next dst /\
   abi_decoder_operand_live new_next hi_op` by
    (rpt conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  fs[abi_decoder_effect_def]
QED

Theorem abi_decoder_member_effects_compose:
  abi_decoder_effect first last lo mid_id next limit_st cell headsz b cap s middle /\
  abi_decoder_effect first last mid_id hi tail_next limit_st
    (cell + headsz) tailsz b cap middle t /\
  lo <= mid_id /\ mid_id <= hi /\ next <= tail_next ==>
  abi_decoder_effect first last lo hi next limit_st cell (headsz + tailsz) b cap s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_effect first last lo hi next limit_st cell (headsz + tailsz) b cap s middle` by
    (mp_tac (Q.INST [`child_lo` |-> `lo:num`, `child_hi` |-> `mid_id:num`,
      `child_next` |-> `next:num`, `child_d` |-> `cell:num`, `child_sz` |-> `headsz:num`,
      `d` |-> `cell:num`, `sz` |-> `headsz + tailsz`, `t` |-> `middle:venom_state`]
      abi_decoder_effect_widen) >> asm_simp_tac arith_ss []) >>
  `abi_decoder_effect first last lo hi next limit_st cell (headsz + tailsz) b cap middle t` by
    (mp_tac (Q.INST [`child_lo` |-> `mid_id:num`, `child_hi` |-> `hi:num`,
      `child_next` |-> `tail_next:num`, `child_d` |-> `cell + headsz`, `child_sz` |-> `tailsz:num`,
      `d` |-> `cell:num`, `sz` |-> `headsz + tailsz`, `s` |-> `middle:venom_state`]
      abi_decoder_effect_widen) >> asm_simp_tac arith_ss []) >>
  drule_all abi_decoder_effect_trans >> simp[]
QED
