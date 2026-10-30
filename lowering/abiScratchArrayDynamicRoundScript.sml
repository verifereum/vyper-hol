Theory abiScratchArrayDynamicRound
Ancestors
  abiScratchArraySpine abiEncoderArraySourceSpine abiScratchMemberAdapter abiEncoderMemberSpine
  abiEncoderMemberPhaseRaw abiEncoderExtendSim abiScratchArrayTail abiScratchEncoderRun
  abiScratchChild abiScratchEncoderContract abiScratchFootprint abiScratchEffect
  abiEncoderArrayTail abiEncoderChildCode abiEncoderChildSuffixReach abiDecoderDynamicLoopSetup
  abiDecoderAllocation abiDecoderFootprint abiDecoderFrame abiDecoderReentry abiDecoderContract
  abiDecoderLoop compileEnv valueEncoding contractABI venomState finite_map pred_set words list
  arithmetic abiScratchArrayPrepare abiScratchAfterAddress abiEncoderArrayDynamicMemory
  abiEncoderArrayBodyCode abiEncoderInput abiScratchPrefix abiScratchInput abiScratchSubset
  abiEncoderArrayPrefix abiScratchCursor abiEncoderArrayHeaderMemory abiEncoderMembersDefs
  valueEncodingProps abiScratchArrayBackedge abiEncoderArrayRound venomInst

(* Execute setup, the recursive child and bookkeeping in the containing CFG.
   TOP-LEVEL: abi_scratch_array_dynamic_tail_reach composes all three actual
   stages under the child induction hypothesis and returns one precise effect. *)
Theorem abi_scratch_array_dynamic_tail_reach:
  abi_scratch_encoder ei /\
  abi_encode_array_tail data_op dyn_ptr st = (ops,prepared) /\
  compile_abi_encode_to_buf (SND ops) src ei prepared = (child_len,child_end) /\
  abi_encode_child_suffix head dyn_ptr (FST ops) child_len child_end = (child_len,end_st) /\
  fn_has_code st prepared func /\ fn_has_code prepared child_end func /\ fn_has_code child_end end_st func /\
  abi_scratch_input ei at av st src data_op sb source_cap d output_size first last b cap initial /\
  abi_decoder_operand_live st.cs_next_var head /\ eval_operand head initial = SOME (n2w (d+ho)) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ ho+32 <= off /\ off+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= lo /\ lo <= site /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+off) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    mem_word_at (d+ho) actual.vs_memory = n2w off /\
    mem_word_at slot actual.vs_memory = n2w (off+LENGTH (enc at av)) /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
    eval_operand child_len actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_encoder_input ei at av sb source_cap actual.vs_memory /\
    abi_decode_footprint_frame
      ([(d+ho,32);(d+off,LENGTH (enc at av))] ++
        abi_decoder_child_scratch (abi_decoder_ids lo end_st.cs_next_id) b cap initial) initial actual /\
    abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_array_tail_code >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand data_op initial = SOME (n2w d) /\
    abi_decoder_operand_live st.cs_next_var data_op /\
    d+output_size < dimword (:256)` by fs[abi_scratch_input_def] >>
  `abi_encoder_spine_core_code func (ei,SND ops,src,prepared,child_end,child_len)` by
    fs[abi_encoder_spine_core_code_def] >>
  qabbrev_tac `Pre = \(e,dd,ss,p,en,op:operand) s.
    abi_scratch_encoder e /\ abi_scratch_input e at av p ss dd sb source_cap (d+off)
      (LENGTH (enc at av)) first last b cap s /\
    abi_decoder_budget first last b cap s /\ first <= p.cs_next_id /\ en.cs_next_id <= last /\
    en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
    abi_decoder_operand_live p.cs_next_var head /\
    abi_decoder_operand_live p.cs_next_var (FST ops) /\
    abi_decoder_operand_live p.cs_next_var dyn_ptr /\
    eval_operand head s = SOME (n2w (d+ho)) /\
    eval_operand (FST ops) s = SOME (n2w off) /\
    eval_operand dyn_ptr s = SOME (n2w slot) /\ first <= site /\ site < p.cs_next_id /\
    FLOOKUP s.vs_allocas site = SOME (slot,32) /\
    ~s.vs_halted /\ s.vs_current_bb = p.cs_current_bb /\ s.vs_inst_idx = LENGTH p.cs_current_insts` >>
  qabbrev_tac `Post = \(e:abi_enc_info,dd:operand,ss:operand,p,en,op) s t.
    mem_bytes_at (d+off) (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand op t = SOME (n2w (LENGTH (enc at av))) /\
    abi_encoder_input e at av sb source_cap t.vs_memory /\
    abi_scratch_effect first last p.cs_next_id en.cs_next_id p.cs_next_var
      limit_st (d+off) (LENGTH (enc at av)) b cap s t /\
    eval_operand head t = SOME (n2w (d+ho)) /\
    eval_operand (FST ops) t = SOME (n2w off) /\
    eval_operand dyn_ptr t = SOME (n2w slot) /\ FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    mload slot t = mload slot s /\ fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func s t` >>
  `!c ready. abi_encoder_spine_core_code func c /\ Pre c ready ==>
    ?encoded. Post c ready encoded /\ Post c ready encoded` by
    (rpt gen_tac >> PairCases_on `c` >>
     simp_tac (srw_ss()) [Abbr `Pre`, Abbr `Post`, abi_encoder_spine_core_code_def] >>
     rpt strip_tac >> irule abi_scratch_dynamic_child_core >>
     goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac []) >>
  `!ready. abi_encoder_member_phase_raw st prepared initial ready ==>
    Pre (ei,SND ops,src,prepared,child_end,child_len) ready` by
    (rpt strip_tac >> drule_all abi_scratch_array_prepare_raw_transport >> strip_tac >>
     fs[Abbr `Pre`, abi_decoder_address_frame_def] >> decide_tac) >>
  `!ready encoded. Post (ei,SND ops,src,prepared,child_end,child_len) ready encoded ==>
    abi_encoder_spine_cursor_input (head,dyn_ptr,FST ops,child_len,child_end,end_st,limit_st) encoded` by
    (simp_tac (srw_ss()) [Abbr `Post`, abi_encoder_spine_cursor_input_def] >>
     rpt strip_tac >> qexistsl_tac [`d+ho`, `slot`, `off`, `LENGTH (enc at av)`] >>
     asm_rewrite_tac [] >> decide_tac) >>
  drule_all abi_encoder_array_spine_dynamic_run >>
  disch_then (qx_choose_then `ready` (qx_choose_then `encoded` (qx_choose_then `actual` strip_assume_tac))) >>
  qpat_x_assum `Post _ _ _` mp_tac >> simp_tac (srw_ss()) [Abbr `Post`] >> strip_tac >>
  qpat_x_assum `abi_encoder_spine_call _ _ _ _` kall_tac >>
  qpat_x_assum `!c rr. _` kall_tac >>
  qpat_x_assum `!rr. abi_encoder_member_phase_raw _ _ _ _ ==> _` kall_tac >>
  qpat_x_assum `!rr uu. _` kall_tac >>
  qpat_x_assum `Abbrev (Pre = _)` kall_tac >>
  drule_all abi_scratch_array_prepare_raw_transport >> strip_tac >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap ready encoded` by fs[abi_scratch_effect_def] >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial encoded` by
    (drule_all abi_scratch_evolution_trans >> simp[]) >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap encoded)` by
    (mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`, `b` |-> `b:num`, `cap` |-> `cap:num`,
       `p` |-> `d:num`, `n` |-> `output_size:num`, `s` |-> `initial:venom_state`,
       `t` |-> `encoded:venom_state`] abi_scratch_disjoint_advance) >>
     impl_tac >- fs[abi_scratch_input_def] >> simp[]) >>
  `d <= d+ho /\ d+ho+32 <= d+off` by decide_tac >>
  drule_all abi_scratch_dynamic_finish_raw_transport >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `lo <= prepared.cs_next_id /\ child_end.cs_next_id <= end_st.cs_next_id /\
    st.cs_next_var <= prepared.cs_next_var /\
    site IN abi_decoder_ids lo end_st.cs_next_id /\
    d <= d+off /\ (d+off)+LENGTH (enc at av) <= d+output_size /\ d+ho+32 <= d+output_size` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  drule_all abi_scratch_child_effect >> strip_tac >>
  `abi_encoder_input ei at av sb source_cap actual.vs_memory` by
    (irule (Q.INST [`s` |-> `initial:venom_state`, `st` |-> `st:compile_state`,
       `dst` |-> `data_op:operand`, `lo` |-> `lo:num`, `hi` |-> `end_st.cs_next_id`]
       abi_scratch_effect_source) >>
     goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac []) >>
  drule abi_encode_array_tail_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st prepared)` by fs[EVERY_CONJ] >>
  drule_all abi_encoder_member_phase_extend_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_encoder_extend_sim_sim >> strip_tac >>
  qexists_tac `actual` >> fs[] >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `encoded` >> simp[]
QED

(* Complete actual dynamic-element body with physical scratch separation.
   TOP-LEVEL: abi_scratch_array_dynamic_body_reach composes the seven address
   instructions with recursive child execution and cursor bookkeeping.
   Helper: exact head/tail bounds are derived from complete typed array input. *)
Theorem abi_scratch_array_body_bounds:
  abi_encoder_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs) sb source_cap mem /\
  j < LENGTH avs /\ LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  off = LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) ==>
  has_type (Array NONE ty) (ListV avs) /\ is_dynamic ty /\ asz = abi_member_head_size ty /\
  32 <= output_size /\ j*asz+32 <= off /\ off+LENGTH (enc ty (EL j avs)) <= output_size-32
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_input (AbiDynArray _ _ _ _) _ _ _ _ _`
    (assume_tac o MATCH_MP abi_encoder_input_typed) >>
  drule_all abi_encoder_array_selected_input >> strip_tac >>
  `is_dynamic ty` by fs[] >> drule_all abi_encoder_array_child_bounds >> strip_tac >>
  gvs[Excl "enc_def"] >> decide_tac
QED

Theorem abi_scratch_array_dynamic_body_reach:
  abi_scratch_encoder ei /\ abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\ j < LENGTH avs /\
  off = LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+32+off) (LENGTH (enc ty (EL j avs))) actual.vs_memory = enc ty (EL j avs) /\
    mem_word_at (d+32+j*asz) actual.vs_memory = n2w off /\
    mem_word_at slot actual.vs_memory = n2w (off+LENGTH (enc ty (EL j avs))) /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\ eval_operand out actual = SOME (n2w j) /\
    abi_decode_footprint_frame
      ([(d+32+j*asz,32);(d+32+off,LENGTH (enc ty (EL j avs)))] ++
        abi_decoder_child_scratch (abi_decoder_ids site end_st.cs_next_id) b cap initial) initial actual /\
    abi_scratch_effect first last site end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_dynamic_body_context >> strip_tac >>
  `addressed.cs_next_var <= limit_st.cs_next_var /\ site < addressed.cs_next_id /\
   st.cs_next_var <= addressed.cs_next_var` by decide_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule_all abi_scratch_array_body_bounds >> strip_tac >>
  mp_tac (Q.INST [`prepared` |-> `addressed`, `active` |-> `T`] abi_scratch_array_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  drule abi_encode_array_addresses_shape >> strip_tac >>
  `abi_decoder_operand_live addressed.cs_next_var dyn_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand dyn_ptr ready = SOME (n2w slot) /\ mload slot ready = n2w off /\
   FLOOKUP ready.vs_allocas site = SOME (slot,32)` by
    fs[abi_decoder_address_frame_def, mload_def] >>
  mp_tac (Q.INST [`st` |-> `addressed`, `initial` |-> `ready:venom_state`,
    `src` |-> `SND (FST (coords:(operand # operand) # (operand # operand)))`,
    `data_op` |-> `FST (SND (coords:(operand # operand) # (operand # operand)))`,
    `head` |-> `SND (SND (coords:(operand # operand) # (operand # operand)))`,
    `at` |-> `ty:abi_type`, `av` |-> `EL j (avs:abi_value list)`, `ho` |-> `j*asz`,
    `sb` |-> `sb+32+j*msz`, `source_cap` |-> `msz:num`, `d` |-> `d+32`,
    `output_size` |-> `output_size-32`, `lo` |-> `site:num`] abi_scratch_array_dynamic_tail_reach) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready actual` >>
  `eval_operand (FST (FST coords)) actual = SOME (n2w j)` by
    (mp_tac (Q.INST [`op` |-> `FST (FST (coords:(operand # operand) # (operand # operand)))`,
       `w` |-> `n2w j:bytes32`, `s` |-> `ready:venom_state`, `t` |-> `actual:venom_state`,
       `next` |-> `addressed.cs_next_var`, `d` |-> `d+32`, `sz` |-> `output_size-32`,
       `lo` |-> `site:num`, `hi` |-> `end_st.cs_next_id`] abi_scratch_effect_operand) >>
     asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`ids` |-> `abi_decoder_ids site end_st.cs_next_id`, `next` |-> `st.cs_next_var`,
    `fp` |-> `[(d+32+j*asz,32);(d+32+off,LENGTH (enc ty (EL j avs)))]`]
    abi_scratch_frame_after_address) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`child_lo` |-> `site:num`, `child_hi` |-> `end_st.cs_next_id`,
    `child_next` |-> `addressed.cs_next_var`, `child_d` |-> `d+32`, `child_sz` |-> `output_size-32`,
    `hi` |-> `end_st.cs_next_id`, `next` |-> `st.cs_next_var`, `lo` |-> `site:num`,
    `sz` |-> `output_size:num`] abi_scratch_effect_after_address) >>
  impl_tac >- (asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >> disch_tac >>
  qexists_tac `actual` >> gvs[] >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> simp[]
QED

(* The real recursive body advances the complete output and source invariants.
   TOP-LEVEL: abi_scratch_array_dynamic_iteration extends the encoded prefix,
   updates the tail offset and retains complete source data and separation. *)
Theorem abi_scratch_array_dynamic_iteration:
  abi_scratch_encoder ei /\ abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\ j < LENGTH avs /\
  off = LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory /\
    abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
      st src dst sb source_cap d output_size first last b cap actual /\
    mem_word_at slot actual.vs_memory = n2w (LENGTH avs*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\ eval_operand out actual = SOME (n2w j) /\
    abi_scratch_effect first last site end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac abi_scratch_array_dynamic_body_reach >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule_all abi_scratch_array_body_bounds >> strip_tac >>
  `abi_decoder_ids site end_st.cs_next_id SUBSET abi_decoder_ids first last` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids site end_st.cs_next_id) b cap initial)` by
    (irule abi_scratch_disjoint_subset >> qexists_tac `abi_decoder_ids first last` >> simp[]) >>
  qpat_assum `asz = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  mp_tac (Q.INST [`fp` |-> `abi_decoder_child_scratch (abi_decoder_ids site end_st.cs_next_id) b cap initial`]
    abi_scratch_array_dynamic_step) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`ei` |-> `AbiDynArray ei (abi_member_head_size ty) msz T`,
    `at` |-> `Array NONE ty`, `av` |-> `ListV avs`, `sz` |-> `output_size:num`,
    `lo` |-> `site:num`, `hi` |-> `end_st.cs_next_id`, `next` |-> `st.cs_next_var`]
    abi_scratch_input_effect) >> impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  drule_all abi_encoder_array_tail_sum_suc >> disch_tac >>
  qexists_tac `actual` >> full_simp_tac bool_ss [ADD_ASSOC]
QED

(* Actual recursive body preservation at the loop's stable compiler entry.
   TOP-LEVEL: abi_scratch_array_dynamic_body_memory advances the output/tail
   while retaining the complete source contract and the registered index. *)
Theorem abi_scratch_array_dynamic_body_memory:
  abi_scratch_encoder ei /\ abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_encoder_cursor T ip index_site index_slot first lo owner_st j initial /\
  abi_encoder_cursor T dyn_ptr site slot first lo owner_st off initial /\ index_site < site /\
  off = LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) /\
  j < LENGTH avs /\ owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= st.cs_next_id /\
  abi_decoder_budget first last b cap initial /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
      owner_st src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory /\
    abi_encoder_cursor T ip index_site index_slot first lo owner_st j actual /\
    abi_encoder_cursor T dyn_ptr site slot first lo owner_st
      (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) actual /\
    eval_operand out actual = SOME (n2w j) /\
    abi_scratch_effect first last site end_st.cs_next_id owner_st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  qpat_assum `abi_encoder_cursor T dyn_ptr _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule_all abi_encode_array_dynamic_body_context >> strip_tac >>
  `site < st.cs_next_id /\ index_site < last /\ site < last /\ owner_st.cs_next_id <= last` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `cursor_op` |-> `ip:operand`, `off` |-> `j:num`,
    `site` |-> `index_site:num`, `slot` |-> `index_slot:num`, `s` |-> `initial:venom_state`] abi_encoder_cursor_bounds) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial` by
    (irule abi_scratch_input_mono >> qexists_tac `owner_st` >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live st.cs_next_var dyn_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `owner_st.cs_next_var` >> simp[]) >>
  mp_tac (Q.INST [`p` |-> `n2w index_slot:bytes32`] abi_scratch_array_dynamic_iteration) >>
  impl_tac >- asm_simp_tac (srw_ss()) [w2n_n2w, Excl "enc_def"] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `abi_scratch_effect first last site end_st.cs_next_id owner_st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `site`, `st.cs_next_var`, `output_size`] >> simp[]) >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `next` |-> `owner_st.cs_next_var`, `cursor_op` |-> `ip:operand`,
    `site` |-> `index_site:num`, `slot` |-> `index_slot:num`, `active` |-> `T`, `off` |-> `j:num`,
    `sz` |-> `output_size:num`, `owned_lo` |-> `site:num`, `owned_hi` |-> `end_st.cs_next_id`]
    abi_scratch_cursor_protected) >> impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `next` |-> `owner_st.cs_next_var`, `cursor_op` |-> `dyn_ptr:operand`,
    `active` |-> `T`, `sz` |-> `output_size:num`, `owned_lo` |-> `site:num`, `owned_hi` |-> `end_st.cs_next_id`,
    `next_off` |-> `LENGTH (avs:abi_value list)*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) (avs:abi_value list)))`]
    abi_scratch_cursor_registered) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL, GSYM mem_word_at_eq_mload] >> disch_tac >>
  mp_tac (Q.INST [`ei` |-> `AbiDynArray ei asz msz T`, `at` |-> `Array NONE ty`,
    `av` |-> `ListV avs`, `sz` |-> `output_size:num`,
    `st` |-> `owner_st`, `lo` |-> `site:num`, `hi` |-> `end_st.cs_next_id`,
    `next` |-> `owner_st.cs_next_var`] abi_scratch_input_effect) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* One actual dynamic body and backedge advances the complete array state.
   TOP-LEVEL: abi_scratch_array_dynamic_round composes recursive encoding and
   the index update into one physical effect and containing-function simulation. *)
Theorem abi_scratch_array_dynamic_round:
  abi_scratch_encoder ei /\ abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\
  lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = end_st.cs_current_insts ++ abi_decode_backedge_insts end_st.cs_next_id
    (STRING #"%" (toString st.cs_next_var)) (STRING #"%" (toString end_st.cs_next_var)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first lo owner_st j initial /\
  abi_encoder_cursor T dyn_ptr cursor_site cursor_slot first lo owner_st
    (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) initial /\
  site < cursor_site /\ j < LENGTH avs /\
  owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= st.cs_next_id /\
  abi_decoder_budget first last b cap initial /\ end_st.cs_next_id+3 <= last /\
  end_st.cs_next_var+1 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
      owner_st src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory /\
    abi_encoder_cursor T ip site slot first lo owner_st (SUC j) actual /\
    abi_encoder_cursor T dyn_ptr cursor_site cursor_slot first lo owner_st
      (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) actual /\
    abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_dynamic_body_context >> strip_tac >>
  drule abi_encode_array_dynamic_body_index >> disch_tac >>
  `owner_st.cs_next_id <= last /\ end_st.cs_next_id <= last /\
    end_st.cs_next_var <= limit_st.cs_next_var /\ end_st.cs_next_var < limit_st.cs_next_var /\
    owner_st.cs_next_var <= end_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`index_site` |-> `site:num`, `index_slot` |-> `slot:num`,
    `site` |-> `cursor_site:num`, `slot` |-> `cursor_slot:num`,
    `off` |-> `LENGTH (avs:abi_value list)*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE j (avs:abi_value list)))`]
    abi_scratch_array_dynamic_body_memory) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial encoded` >>
  qpat_assum `out = Var _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule abi_encoder_input_typed >> disch_tac >>
  `j <= LENGTH avs` by decide_tac >> drule_all abi_encoder_array_prefix_types >> strip_tac >>
  qpat_assum `abi_scratch_effect _ _ cursor_site end_st.cs_next_id _ _ _ _ _ _ initial encoded`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  mp_tac (Q.INST [`initial` |-> `encoded:venom_state`, `k` |-> `SUC j`, `n` |-> `LENGTH (avs:abi_value list)`,
    `off` |-> `LENGTH (avs:abi_value list)*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) (avs:abi_value list)))`,
    `prefix` |-> `end_st.cs_current_insts`, `id` |-> `end_st.cs_next_id`, `next` |-> `end_st.cs_next_var`,
    `iv` |-> `STRING #"%" (toString st.cs_next_var)`] abi_scratch_array_backedge_memory) >>
  impl_tac >- full_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func encoded actual` >>
  `first <= site` by fs[abi_encoder_cursor_def] >>
  `abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
    limit_st d output_size b cap initial encoded` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `cursor_site`, `owner_st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [] >> fs[abi_encoder_cursor_def] >> decide_tac) >>
  `abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
    limit_st d output_size b cap encoded actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `site+1`, `site`, `end_st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [] >> fs[abi_encoder_cursor_def] >> decide_tac) >>
  `abi_scratch_effect first last site (end_st.cs_next_id+3) owner_st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `encoded` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `encoded` >> simp[]
QED
