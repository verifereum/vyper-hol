Theory abiScratchChild
Ancestors
  abiScratchFrameCompose abiScratchEncoderContract abiScratchFootprint abiEncoderChildFrames
  abiDecoderDynamicLoopSetup abiDecoderFootprint abiDecoderFrame venomState finite_map pred_set
  list arithmetic abiScratchEffect abiEncoderChildSuffixReach abiDecoderArrayInitExec
  abiDecoderAllocation abiDecoderReentry compileEnv valueEncoding contractABI words
  abiEncoderChildEffect abiDecoderProtectedScratch abiDecoderContract abiDecoderLoop
  abiScratchInput abiEncoderInput abiEncoderChildContext abiEncoderChildCode abiEncoderArrayTail
  abiEncoderAddressReach fragExec emitHelperProps emitHelper venomInst rich_list
Libs monadsyntax

(* ===== Frame ===== *)

(* One precise frame for setup, recursive encoding and parent bookkeeping.
   TOP-LEVEL: abi_scratch_dynamic_child_frame keeps the head and encoded tail
   windows separate and charges the cursor store to its actual owned site. *)

Theorem abi_scratch_dynamic_child_frame:
  abi_decoder_address_frame next initial ready /\
  abi_scratch_effect first last child_lo child_hi child_next limit_st q len b cap ready encoded /\
  FINITE ids /\ ids SUBSET abi_decoder_ids first last /\
  abi_decoder_ids child_lo child_hi SUBSET ids /\ site IN ids /\
  FLOOKUP encoded.vs_allocas site = SOME (slot,32) /\
  abi_decode_footprint_frame [(h,32);(slot,32)] encoded actual ==>
  abi_decode_footprint_frame
    ([(h,32);(q,len)] ++ abi_decoder_child_scratch ids b cap initial) initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `abi_scratch_evolution ids b cap ready encoded` by
    (drule_all abi_scratch_evolution_subset >> simp[]) >>
  `abi_decode_footprint_frame
    ([(q,len)] ++ abi_decoder_child_scratch ids b cap ready) ready encoded` by
    (irule abi_scratch_frame_subset_append >> asm_simp_tac bool_ss [] >>
     qexists_tac `abi_decoder_ids child_lo child_hi` >> simp[]) >>
  `abi_decode_footprint_frame
    ([(h,32);(q,len)] ++ abi_decoder_child_scratch ids b cap ready) ready encoded` by
    (simp_tac bool_ss [APPEND] >> irule abi_encoder_frame_extra_window >> gvs[APPEND]) >>
  `MEM (slot,32) (abi_decoder_child_scratch ids b cap encoded)` by
    (irule abi_scratch_registered_member >> asm_simp_tac bool_ss [] >>
     qexists_tac `site` >> simp[]) >>
  `abi_decode_footprint_frame
    ([(h,32);(q,len)] ++ abi_decoder_child_scratch ids b cap encoded) encoded actual` by
    (irule abi_decode_footprint_frame_weaken >> qexists_tac `[(h,32);(slot,32)]` >>
     asm_simp_tac bool_ss [] >> simp[] >> rpt gen_tac >> strip_tac >|
     [qexistsl_tac [`h`, `32`] >> simp[], qexistsl_tac [`slot`, `32`] >> simp[]]) >>
  `abi_decode_footprint_frame
    ([(h,32);(q,len)] ++ abi_decoder_child_scratch ids b cap ready) encoded actual` by
    (drule_all abi_scratch_frame_advance_append >> simp[]) >>
  `abi_decode_footprint_frame
    ([(h,32);(q,len)] ++ abi_decoder_child_scratch ids b cap ready) ready actual` by
    (irule abi_decode_footprint_frame_trans >> qexists_tac `encoded` >> simp[]) >>
  `abi_decoder_child_scratch ids b cap ready = abi_decoder_child_scratch ids b cap initial` by
    fs[abi_decoder_address_frame_def, abi_decoder_child_scratch_def] >>
  irule abi_encoder_frame_after_address >> qexistsl_tac [`next`, `ready`] >> gvs[APPEND]
QED

(* ===== Effect ===== *)

(* Compose setup, recursive child execution and cursor bookkeeping.
   TOP-LEVEL: abi_scratch_child_effect derives one enclosing precise effect;
   Helper: abi_scratch_child_operands chains the three register frames. *)

Theorem abi_scratch_child_operands:
  !next child_next suffix_st initial ready encoded actual first last child_lo child_hi
    limit_st q len b cap out h slot off.
  abi_decoder_address_frame next initial ready /\
  abi_scratch_effect first last child_lo child_hi child_next limit_st q len b cap ready encoded /\
  abi_encoder_child_suffix_post out suffix_st limit_st h slot off len encoded actual /\
  next <= child_next /\ next <= suffix_st.cs_next_var ==>
  !op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> rpt gen_tac >> strip_tac >>
  `abi_decoder_operand_live child_next op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  `abi_decoder_operand_live suffix_st.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  `eval_operand op ready = SOME w` by fs[abi_decoder_address_frame_def] >>
  `eval_operand op encoded = SOME w` by
    (drule_all abi_scratch_effect_operand >> simp[]) >>
  qpat_assum `abi_encoder_child_suffix_post _ _ _ _ _ _ _ _ _`
    (qspecl_then [`op`, `w`] mp_tac o List.last o CONJUNCTS o
      PURE_REWRITE_RULE [abi_encoder_child_suffix_post_def]) >> simp[]
QED

Theorem abi_scratch_child_effect:
  abi_decoder_address_frame next initial ready /\
  abi_scratch_effect first last child_lo child_hi child_next limit_st q len b cap ready encoded /\
  abi_encoder_child_suffix_post out suffix_st limit_st h slot off len encoded actual /\
  first <= lo /\ hi <= last /\ lo <= child_lo /\ child_hi <= hi /\
  next <= child_next /\ next <= suffix_st.cs_next_var /\
  site IN abi_decoder_ids lo hi /\ FLOOKUP encoded.vs_allocas site = SOME (slot,32) /\
  d <= h /\ h+32 <= d+sz /\ d <= q /\ q+len <= d+sz ==>
  abi_scratch_effect first last lo hi next limit_st d sz b cap initial actual /\
  abi_decode_footprint_frame
    ([(h,32);(q,len)] ++ abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial)
    initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_ids lo hi SUBSET abi_decoder_ids first last /\
   abi_decoder_ids child_lo child_hi SUBSET abi_decoder_ids lo hi` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `FINITE (abi_decoder_ids lo hi)` by simp[] >>
  `abi_decode_footprint_frame [(h,32);(slot,32)] encoded actual` by
    fs[abi_encoder_child_suffix_post_def] >>
  `abi_decode_footprint_frame
    ([(h,32);(q,len)] ++ abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial)
    initial actual` by
    (drule_all (Q.INST [`ids` |-> `abi_decoder_ids lo hi`] abi_scratch_dynamic_child_frame) >> simp[]) >>
  `abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial) initial actual` by
    (irule abi_decode_footprint_frame_weaken >>
     qexists_tac `[(h,32);(q,len)] ++ abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial` >>
     asm_simp_tac bool_ss [] >> simp[] >> qx_genl_tac [`p`, `n`] >> strip_tac >|
     [qexistsl_tac [`d`, `sz`] >> simp[], qexistsl_tac [`d`, `sz`] >> simp[],
      qexistsl_tac [`p`, `n`] >> simp[]]) >>
  `!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w` by
    (mp_tac (Q.SPECL [`next`, `child_next`, `suffix_st`, `initial`, `ready`, `encoded`, `actual`,
       `first`, `last`, `child_lo`, `child_hi`, `limit_st`, `q`, `len`, `b`, `cap`, `out`, `h`,
       `slot`, `off`] abi_scratch_child_operands) >>
     impl_tac >- asm_simp_tac bool_ss [] >> simp[]) >>
  `(abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual <=>
    abi_scratch_evolution (abi_decoder_ids first last) b cap ready encoded)` by
    (irule abi_scratch_evolution_transport >>
     fs[abi_decoder_address_frame_def, abi_encoder_child_suffix_post_def]) >>
  `(abi_decoder_budget first last b cap actual <=> abi_decoder_budget first last b cap encoded)` by
    (irule abi_decoder_budget_transport >> fs[abi_encoder_child_suffix_post_def]) >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  qpat_assum `abi_encoder_child_suffix_post _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_child_suffix_post_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `!id. id < lo \/ hi <= id ==> FLOOKUP actual.vs_allocas id = FLOOKUP initial.vs_allocas id` by
    (rpt gen_tac >> strip_tac >> `id < child_lo \/ child_hi <= id` by decide_tac >>
     asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [abi_scratch_effect_def] >> gvs[] >> first_assum ACCEPT_TAC
QED

(* ===== Finish ===== *)

(* Actual post-child stores use physical separation from the parent cursor.
   TOP-LEVEL: abi_scratch_child_finish preserves encoded tail bytes, writes
   the head offset and advances the registered cursor with a two-store frame. *)

Theorem abi_scratch_child_finish:
  abi_encode_child_suffix head dyn_ptr offset child_len st = (out,st') /\ fn_has_code st st' func /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  eval_operand offset initial = SOME (n2w off) /\ eval_operand child_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ abi_decoder_operand_live st.cs_next_var child_len /\
  mem_bytes_at (d+off) len initial.vs_memory = bytes /\
  d <= h /\ h+32 <= d+off /\ off+len <= output_size /\ d+output_size < dimword (:256) /\
  abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_decoder_budget first last b cap initial /\ site IN abi_decoder_ids first last /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+off) len actual.vs_memory = bytes /\
    mem_word_at h actual.vs_memory = n2w off /\
    mem_word_at slot actual.vs_memory = n2w (off+len) /\
    eval_operand out actual = SOME (n2w len) /\ FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
    abi_encoder_child_suffix_post out st limit_st h slot off len initial actual /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `b+cap < dimword (:256)` by fs[abi_decoder_budget_def] >>
  `h < dimword (:256) /\ slot < dimword (:256) /\ h+32 <= d+output_size` by decide_tac >>
  `MEM (slot,32) (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    (irule abi_scratch_registered_member >> asm_simp_tac (srw_ss()) [] >>
     qexists_tac `site` >> simp[]) >>
  qpat_assum `abi_footprint_disjoint d output_size _`
    (qspecl_then [`slot`, `32`] mp_tac o REWRITE_RULE [abi_footprint_disjoint_def]) >>
  asm_simp_tac bool_ss [] >> disch_then assume_tac >>
  mp_tac (Q.INST [`p` |-> `slot:num`] abi_encode_child_suffix_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  mp_tac (Q.INST [`q` |-> `d+off`, `offset` |-> `off:num`] abi_encoder_child_suffix_output) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  `(abi_decoder_budget first last b cap actual <=> abi_decoder_budget first last b cap initial)` by
    (irule abi_decoder_budget_transport >> fs[abi_encoder_child_suffix_post_def]) >>
  `initial.vs_alloca_next <= b+cap` by (drule abi_decoder_budget_frontier >> simp[]) >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual` by
    (qpat_assum `abi_encoder_child_suffix_post _ _ _ _ _ _ _ _ _`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_child_suffix_post_def]) >>
     rw[abi_scratch_evolution_def] >> gvs[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >> fs[abi_encoder_child_suffix_post_def]
QED

(* ===== Input ===== *)

(* Exact child destinations inherit their parent buffer's physical separation.
   TOP-LEVEL: abi_scratch_child_input_address selects a bounded output offset
   after the real register-only prefix, without a numeric arena exclusion. *)

Theorem abi_scratch_child_input_address:
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  abi_decoder_address_frame st.cs_next_var initial actual /\
  abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
  st.cs_next_var <= prepared.cs_next_var /\
  abi_decoder_operand_live prepared.cs_next_var child_dst /\
  eval_operand child_dst actual = SOME (n2w (d+off)) /\
  off+LENGTH (enc at av) <= output_size ==>
  abi_scratch_input ei at av prepared src child_dst sb source_cap (d+off)
    (LENGTH (enc at av)) first last b cap actual
Proof
  strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  `actual.vs_memory = initial.vs_memory` by fs[abi_decoder_address_frame_def] >>
  `abi_encoder_input ei at av sb source_cap actual.vs_memory` by simp[] >>
  `eval_operand src actual = SOME (n2w sb)` by fs[abi_decoder_address_frame_def] >>
  `abi_decoder_operand_live prepared.cs_next_var src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `sb <= sb /\ sb+source_cap <= sb+source_cap /\
   d <= d+off /\ d+off+LENGTH (enc at av) <= d+output_size` by decide_tac >>
  mp_tac (Q.INST [`parent_ei` |-> `ei:abi_enc_info`, `parent_at` |-> `at:abi_type`,
    `parent_av` |-> `av:abi_value`, `parent_src` |-> `src:operand`, `parent_dst` |-> `dst:operand`,
    `dst` |-> `child_dst:operand`, `child_sb` |-> `sb:num`, `child_cap` |-> `source_cap:num`,
    `child_d` |-> `d+off`, `child_size` |-> `LENGTH (enc at av)`] abi_scratch_input_regions) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> simp[]
QED

(* ===== Split ===== *)

(* Share the actual cursor-load/tail-address phase between members and arrays.
   TOP-LEVEL: abi_scratch_dynamic_child_split exposes the member's head ADD,
   existing array-tail setup, recursive encoder and cursor bookkeeping. *)

Theorem abi_scratch_child_prefix_phases:
  abi_encode_child_prefix dst ho dyn_ptr =
    do head <- emit_op ADD [dst;Lit (n2w ho)];
       tail <- abi_encode_array_tail dst dyn_ptr;
       return (head,FST tail,SND tail)
    od
Proof
  simp_tac bool_ss [FUN_EQ_THM, abi_encode_child_prefix_def, abi_encode_array_tail_def,
    comp_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_scratch_child_prefix_split:
  abi_encode_child_prefix dst ho dyn_ptr st = (ops,prepared) /\ fn_has_code st prepared func ==>
  ?head middle tail.
    emit_op ADD [dst;Lit (n2w ho)] st = (head,middle) /\
    abi_encode_array_tail dst dyn_ptr middle = (tail,prepared) /\
    ops = (head,FST tail,SND tail) /\
    fn_has_code st middle func /\ fn_has_code middle prepared func /\
    middle.cs_next_var = st.cs_next_var+1 /\ middle.cs_next_id = st.cs_next_id+1 /\
    abi_decoder_operand_live middle.cs_next_var head
Proof
  simp_tac bool_ss [abi_scratch_child_prefix_phases, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op ADD _ st = (head,middle)` >>
  rename1 `abi_encode_array_tail dst dyn_ptr middle = (tail,prepared)` >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  drule abi_encode_array_tail_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> drule abi_decoder_operand_live_emit >> strip_tac >>
  `cs_extends middle prepared` by (irule abi_encoder_straight_extends >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  simp[]
QED

Theorem abi_scratch_dynamic_child_split:
  compile_abi_encode_child dst src ei T ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func ==>
  ?head middle tail prepared child_len child_end.
    emit_op ADD [dst;Lit (n2w ho)] st = (head,middle) /\
    abi_encode_array_tail dst dyn_ptr middle = (tail,prepared) /\
    compile_abi_encode_to_buf (SND tail) src ei prepared = (child_len,child_end) /\
    abi_encode_child_suffix head dyn_ptr (FST tail) child_len child_end = (child_len,end_st) /\
    out = child_len /\
    fn_has_code st middle func /\ fn_has_code middle prepared func /\
    fn_has_code prepared child_end func /\ fn_has_code child_end end_st func /\
    middle.cs_next_var = st.cs_next_var+1 /\ middle.cs_next_id = st.cs_next_id+1 /\
    middle.cs_next_var <= end_st.cs_next_var /\ middle.cs_next_id <= end_st.cs_next_id /\
    abi_decoder_operand_live middle.cs_next_var head
Proof
  strip_tac >> drule_all abi_encoder_dynamic_child_context >> strip_tac >>
  drule_all abi_scratch_child_prefix_split >> strip_tac >>
  drule abi_encode_child_suffix_shape >> strip_tac >>
  qexistsl_tac [`head`, `middle`, `tail`, `prepared`, `child_len`, `child_end`] >>
  gvs[] >> decide_tac
QED
