(* Rich array callbacks: the address phase, child and suffix retain their
   actual endpoints.  No loop or descriptor execution induction lives here. *)
Theory abiEncoderSharedArrayBody
Ancestors
  abiEncoderSharedArrayAddress abiEncoderSharedArrayStep abiEncoderSharedArrayTail
  abiEncoderSharedArrayRound abiEncoderSharedArrayHeader abiEncoderSharedArrayInput
  abiEncoderSharedInputEffect abiEncoderArrayDynamicCode abiEncoderArrayBodyCode
  abiEncoderSharedContract abiEncoderArrayCursor abiEncoderMembersDefs abiScratchEffect
  abiEncoderArrayFrame abiEncoderOpenInputFrame abiDecodeRanges venomMemDefs
  abiScratchEncoderContract abiScratchChild abiEncoderChildSuffixReach abiScratchSubset
  abiEncoderMemberSourceAdapter abiEncoderAdmissible
  abiEncoderOpenInput abiEncoderInput abiEncoderMemberSpine abiScratchFootprint
  abiDecoderDynamicLoopSetup abiDecoderAllocation abiDecoderFootprint abiDecoderReentry
  abiDecoderFrame abiEncoderSharedMemberContract abiEncoderMemberSpineCompat
  abiEncoderSharedArraySpine abiEncoderMemberPhaseRaw abiEncoderChildSuffix abiEncoderExtendSim abiScratchAfterAddress abiEncoderRegisteredEffect abiScratchCursor
  compileEnv valueEncoding valueEncodingProps venomState words list rich_list arithmetic

Theorem abi_encoder_shared_array_body_address:
  abi_encode_array_addresses ip src dst asz msz st = (coords,addressed) /\
  fn_has_code st addressed func /\
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first site st j initial /\
  abi_encoder_cursor active dp cursor_site cursor_slot first site st
    (LENGTH avs*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) initial /\
  addressed.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_budget first last b cap initial /\ st.cs_next_id <= last /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_member_phase_raw st addressed initial actual /\
    abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
      (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) actual /\
    abi_encoder_array_prefix ty avs j d actual.vs_memory /\
    abi_encoder_cursor T ip site slot first site st j actual /\
    abi_encoder_cursor active dp cursor_site cursor_slot first site st
      (LENGTH avs*abi_member_head_size ty+
        SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) actual /\
    eval_operand (FST (FST coords)) actual = SOME (n2w j) /\
    eval_operand (SND (FST coords)) actual = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) actual = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) actual = SOME (n2w (d+32+j*asz)) /\
    abi_decoder_operand_live addressed.cs_next_var (FST (FST coords)) /\
    abi_decoder_operand_live addressed.cs_next_var (SND (FST coords)) /\
    abi_decoder_operand_live addressed.cs_next_var (FST (SND coords)) /\
    abi_decoder_operand_live addressed.cs_next_var (SND (SND coords)) /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    abi_encoder_registered_effect ids outs initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    abi_encoder_extend_sim ctx func initial actual /\
    actual.vs_current_bb = addressed.cs_current_bb /\
    actual.vs_inst_idx = LENGTH addressed.cs_current_insts /\ ~actual.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
   abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst` by
    fs[abi_encoder_shared_input_def] >>
  `slot < dimword (:256) /\ eval_operand ip initial = SOME (n2w slot) /\
   mload slot initial = n2w j` by
    (drule_all abi_encoder_cursor_bounds >>
     fs[abi_encoder_cursor_def, mload_def]) >>
  `mload (w2n (n2w slot : bytes32)) initial = n2w j` by simp[w2n_n2w] >>
  drule_all abi_encoder_shared_array_address_reach >>
  disch_then (qspecl_then [`outs`,`ids`,`ctx`] (qx_choose_then `actual` strip_assume_tac)) >>
  `abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) actual` by
    (drule_all abi_encoder_shared_input_address >> simp[]) >>
  `abi_encoder_cursor T ip site slot first site st j actual /\
   abi_encoder_cursor active dp cursor_site cursor_slot first site st
    (LENGTH avs*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) actual` by
    (conj_tac >> irule abi_encoder_cursor_address >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`initial`,`st`] >> simp[]) >>
  `actual.vs_memory = initial.vs_memory /\ actual.vs_allocas = initial.vs_allocas /\
   actual.vs_alloca_next = initial.vs_alloca_next` by fs[abi_decoder_address_frame_def] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  qpat_x_assum `abi_decoder_budget _ _ _ _ initial` mp_tac >>
  pure_rewrite_tac [abi_decoder_budget_def, abi_decoder_missing_def] >>
  qpat_assum `actual.vs_allocas = _` (fn th => rewrite_tac [th]) >>
  qpat_assum `actual.vs_alloca_next = _` (fn th => rewrite_tac [th])
QED

(* The generated child operands are live at addressed, not at the parent
   entry.  Both source and destination windows are genuinely narrowed. *)
Theorem abi_encoder_shared_array_body_child_input[local]:
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) s /\
  j < LENGTH avs /\
  eval_operand child_src s = SOME (n2w (sb+32+j*msz)) /\
  eval_operand child_dst s = SOME (n2w q) /\
  abi_decoder_operand_live prepared.cs_next_var child_src /\
  abi_decoder_operand_live prepared.cs_next_var child_dst /\
  LENGTH (enc ty (EL j avs)) <= n /\ d <= q /\ q+n <= d+sz ==>
  abi_encoder_shared_input (ei,ty,EL j avs) (prepared,child_src,child_dst)
    (sb+32+j*msz,msz) (q,n) (first,last,b,cap) s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_shared_array_input_facts >> strip_tac >>
  qpat_assum `abi_encoder_shared_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  `sb+32+j*msz+msz <= sb+source_cap` by
    (`SUC j*msz <= LENGTH avs*msz` by simp[] >>
     pop_assum mp_tac >> pure_rewrite_tac [MULT_CLAUSES] >>
     simp_tac bool_ss [MULT_COMM] >> decide_tac) >>
  `regions_disjoint (sb+32+j*msz,msz) (q,n)` by
    (gvs[abi_encoder_zero_aware_separation] >> decide_tac) >>
  `abi_footprint_disjoint (sb+32+j*msz) msz
     (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_footprint_disjoint_subwindow >> qexistsl_tac [`sb`,`source_cap`] >>
     asm_rewrite_tac [] >> decide_tac) >>
  `abi_footprint_disjoint q n
     (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_footprint_disjoint_subwindow >> qexistsl_tac [`d`,`sz`] >>
     asm_rewrite_tac []) >>
  asm_simp_tac bool_ss [abi_encoder_shared_input_def] >> decide_tac
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared array body admission, axiom or hypothesis"
  end) [abi_encoder_shared_array_body_address,abi_encoder_shared_array_body_child_input];

(* The dynamic callback uses the actual address endpoint as the entry of the
   common tail driver.  These witnesses are also used for all post-observations. *)
Theorem abi_encoder_shared_array_dynamic_body_run_retained[local]:
  abi_encoder_shared ei /\
  abi_encode_array_dynamic_body ip dp src dst ei asz msz st = (out,en) /\
  fn_has_code st en func /\
  abi_encoder_shared_input (AbiDynArray ei asz msz T,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first site st j initial /\
  abi_encoder_cursor T dp cursor_site cursor_slot first site st
    (LENGTH avs*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) initial /\
  j < LENGTH avs /\ en.cs_next_id <= last /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_budget first last b cap initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?coords addressed ops prepared len ce address_ready ready encoded actual.
    abi_encode_array_addresses ip src dst asz msz st = (coords,addressed) /\
    abi_encode_array_tail (FST (SND coords)) dp addressed = (ops,prepared) /\
    compile_abi_encode_to_buf (SND ops) (SND (FST coords)) ei prepared = (len,ce) /\
    abi_encode_child_suffix (SND (SND coords)) dp (FST ops) len ce = (len,en) /\
    out = FST (FST coords) /\
    abi_encoder_member_phase_raw st addressed initial address_ready /\
    abi_encoder_member_phase_raw addressed prepared address_ready ready /\
    abi_encoder_shared_member_dynamic_post (ctx,func)
      (ty,EL j avs,sb+32+j*msz,msz,
        d+32+LENGTH avs*abi_member_head_size ty+
          SUM (MAP (abi_member_tail_size ty) (TAKE j avs)))
      (first,last,b,cap,limit_st)
      (SND (SND coords),FST ops,dp,d+32+j*asz,
        LENGTH avs*abi_member_head_size ty+
          SUM (MAP (abi_member_tail_size ty) (TAKE j avs)),cursor_slot,cursor_site)
      (ei,SND ops,SND (FST coords),prepared,ce,len) ready encoded /\
    abi_encoder_member_phase_raw ce en encoded actual /\
    abi_encoder_shared_input (AbiDynArray ei asz msz T,Array NONE ty,ListV avs)
      (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) address_ready /\
    abi_encoder_array_prefix ty avs j d address_ready.vs_memory /\
    abi_encoder_cursor T ip site slot first site st j address_ready /\
    abi_encoder_cursor T dp cursor_site cursor_slot first site st
      (LENGTH avs*abi_member_head_size ty+
        SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) address_ready /\
    abi_decoder_address_frame st.cs_next_var initial address_ready /\
    abi_encoder_registered_effect (abi_decoder_ids first last) [(d,sz)] initial address_ready /\
    (alloca_inv initial ==> alloca_inv address_ready) /\
    abi_encoder_extend_sim ctx func initial address_ready /\
    eval_operand out address_ready = SOME (n2w j) /\
    abi_decoder_operand_live addressed.cs_next_var out /\
    address_ready.vs_current_bb = addressed.cs_current_bb /\
    address_ready.vs_inst_idx = LENGTH addressed.cs_current_insts /\
    ~address_ready.vs_halted /\
    mem_bytes_at (d+32+LENGTH avs*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE j avs)))
      (LENGTH (enc ty (EL j avs))) actual.vs_memory = enc ty (EL j avs) /\
    mem_word_at (d+32+j*asz) actual.vs_memory =
      n2w (LENGTH avs*abi_member_head_size ty+
        SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) /\
    mem_word_at cursor_slot actual.vs_memory =
      n2w (LENGTH avs*abi_member_head_size ty+
        SUM (MAP (abi_member_tail_size ty) (TAKE j avs))+
        LENGTH (enc ty (EL j avs))) /\
    eval_operand (SND (FST coords)) address_ready = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) address_ready = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) address_ready = SOME (n2w (d+32+j*asz)) /\
    abi_decoder_operand_live addressed.cs_next_var (SND (FST coords)) /\
    abi_decoder_operand_live addressed.cs_next_var (FST (SND coords)) /\
    abi_decoder_operand_live addressed.cs_next_var (SND (SND coords)) /\
    fresh_vars_wrt limit_st address_ready /\
    abi_decoder_budget first last b cap address_ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_dynamic_body_context >>
  disch_then (qx_choose_then `coords` (qx_choose_then `addressed`
    (qx_choose_then `ops` (qx_choose_then `prepared`
      (qx_choose_then `len` (qx_choose_then `ce` strip_assume_tac)))))) >>
  `addressed.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_id <= last` by decide_tac >>
  drule_all abi_encoder_shared_array_body_address >>
  disch_then (qspecl_then [`[(d,sz)]`,`abi_decoder_ids first last`,`ctx`]
    (qx_choose_then `address_ready` strip_assume_tac)) >>
  qexistsl_tac [`coords`,`addressed`,`ops`,`prepared`,`len`,`ce`,`address_ready`] >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `abi_encode_array_dynamic_body _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `fn_has_code st en func` kall_tac >>
  qpat_x_assum `abi_encoder_shared_input _ _ _ _ _ initial` kall_tac >>
  qpat_x_assum `abi_encoder_array_prefix _ _ _ _ initial.vs_memory` kall_tac >>
  qpat_x_assum `abi_encoder_cursor T ip _ _ _ _ _ _ initial` kall_tac >>
  qpat_x_assum `abi_encoder_cursor T dp _ _ _ _ _ _ initial` kall_tac >>
  drule abi_encoder_shared_array_input_facts >> strip_tac >>
  `LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs` by
    (drule abi_encoder_structural_list_layout >> simp[]) >>
  `32+LENGTH avs*abi_member_head_size ty+
     SUM (MAP (abi_member_tail_size ty) avs) <= sz` by
    (drule abi_encoder_open_array_length >>
     fs[abi_encoder_shared_input_def]) >>
  `SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) +
     LENGTH (enc ty (EL j avs)) <= SUM (MAP (abi_member_tail_size ty) avs)` by
    (mp_tac (Q.ISPECL [`abi_member_tail_size ty`,`avs:abi_value list`,`j:num`]
       abi_encoder_prefix_sum_bound) >>
     asm_simp_tac bool_ss [abi_member_tail_size_def]) >>
  `abi_encoder_shared_input (ei,ty,EL j avs)
     (addressed,SND (FST coords),FST (SND coords)) (sb+32+j*msz,msz)
     (d+32,sz-32) (first,last,b,cap) address_ready` by
    (irule abi_encoder_shared_array_body_child_input >>
     asm_simp_tac bool_ss [] >>
     conj_tac >- decide_tac >>
     goal_assum (drule_at Any) >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `first <= cursor_site /\ cursor_site < last /\ cursor_slot < dimword (:256)` by
    (drule_all abi_encoder_cursor_bounds >> simp[]) >>
  `eval_operand dp address_ready = SOME (n2w cursor_slot) /\
   abi_decoder_operand_live addressed.cs_next_var dp /\
   mload cursor_slot address_ready = n2w
     (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) /\
   cursor_site < addressed.cs_next_id /\
   FLOOKUP address_ready.vs_allocas cursor_site = SOME (cursor_slot,32)` by
    (qpat_assum `abi_encoder_cursor T dp _ _ _ _ _ _ address_ready` mp_tac >>
     simp_tac bool_ss [abi_encoder_cursor_def] >> strip_tac >>
     asm_simp_tac bool_ss [] >> conj_tac
     >- (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
     decide_tac) >>
  `d+sz <= dimword (:256)` by fs[abi_encoder_shared_input_def] >>
  `d+32+j*asz < dimword (:256)` by
    (`abi_member_head_size ty = 32` by simp[abi_member_head_size_def] >>
     `SUC j*32 <= LENGTH avs*32` by simp[] >>
     fs[MULT_CLAUSES] >> decide_tac) >>
  `abi_encoder_spine_core_code func
     (ei,SND ops,SND (FST coords),prepared,ce,len)` by
    (simp_tac bool_ss [abi_encoder_spine_core_code_def] >> asm_rewrite_tac [] >>
     drule_all abi_encode_array_dynamic_body_child_phi >> simp[]) >>
  `LENGTH avs*abi_member_head_size ty+
     SUM (MAP (abi_member_tail_size ty) (TAKE j avs))+
     LENGTH (enc ty (EL j avs)) <= sz-32` by decide_tac >>
  `ce.cs_next_id <= last` by decide_tac >>
  drule_all abi_encoder_shared_array_tail_reach >>
  disch_then (qspec_then `ctx` (qx_choose_then `ready`
    (qx_choose_then `encoded` (qx_choose_then `actual` strip_assume_tac)))) >>
  `abi_footprint_disjoint d sz
     (abi_decoder_child_scratch (abi_decoder_ids first last) b cap address_ready)` by
    fs[abi_encoder_shared_input_def] >>
  `MEM (cursor_slot,32)
     (abi_decoder_child_scratch (abi_decoder_ids first last) b cap address_ready)` by
    (irule abi_scratch_registered_member >>
     simp[abi_decoder_ids_def] >> goal_assum (drule_at Any) >> simp[]) >>
  `d+sz <= cursor_slot \/ cursor_slot+32 <= d` by
    (qpat_x_assum `abi_footprint_disjoint d sz _` mp_tac >>
     simp_tac bool_ss [abi_footprint_disjoint_def] >>
     disch_then drule >> simp[]) >>
  `d+32+j*asz+32 <= d+32+
     (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs)))` by
    (`abi_member_head_size ty = 32` by simp[abi_member_head_size_def] >>
     `SUC j*32 <= LENGTH avs*32` by simp[] >>
     fs[MULT_CLAUSES] >> decide_tac) >>
  drule abi_encoder_shared_array_tail_observations >>
  disch_then (qspecl_then [`len`,`en`,`actual`] mp_tac) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >>
    qpat_x_assum `asz = _` SUBST_ALL_TAC >> decide_tac)) >> strip_tac >>
  qexistsl_tac [`ready`,`encoded`,`actual`] >>
  rule_assum_tac (PURE_REWRITE_RULE [ADD_ASSOC]) >>
  full_simp_tac bool_ss [ADD_ASSOC] >> metis_tac[]
QED

Theorem abi_encoder_shared_array_dynamic_body_run[local]:
  abi_encoder_shared ei /\
  abi_encode_array_dynamic_body ip dp src dst ei asz msz st = (out,en) /\
  fn_has_code st en func /\
  abi_encoder_shared_input (AbiDynArray ei asz msz T,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first site st j initial /\
  abi_encoder_cursor T dp cursor_site cursor_slot first site st
    (LENGTH avs*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) initial /\
  j < LENGTH avs /\ en.cs_next_id <= last /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_budget first last b cap initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?coords addressed ops prepared len ce address_ready ready encoded actual.
    abi_encode_array_addresses ip src dst asz msz st = (coords,addressed) /\
    abi_encode_array_tail (FST (SND coords)) dp addressed = (ops,prepared) /\
    compile_abi_encode_to_buf (SND ops) (SND (FST coords)) ei prepared = (len,ce) /\
    abi_encode_child_suffix (SND (SND coords)) dp (FST ops) len ce = (len,en) /\
    out = FST (FST coords) /\
    abi_encoder_member_phase_raw st addressed initial address_ready /\
    abi_encoder_member_phase_raw addressed prepared address_ready ready /\
    abi_encoder_shared_member_dynamic_post (ctx,func)
      (ty,EL j avs,sb+32+j*msz,msz,
        d+32+LENGTH avs*abi_member_head_size ty+
          SUM (MAP (abi_member_tail_size ty) (TAKE j avs)))
      (first,last,b,cap,limit_st)
      (SND (SND coords),FST ops,dp,d+32+j*asz,
        LENGTH avs*abi_member_head_size ty+
          SUM (MAP (abi_member_tail_size ty) (TAKE j avs)),cursor_slot,cursor_site)
      (ei,SND ops,SND (FST coords),prepared,ce,len) ready encoded /\
    abi_encoder_member_phase_raw ce en encoded actual /\
    abi_encoder_shared_input (AbiDynArray ei asz msz T,Array NONE ty,ListV avs)
      (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) address_ready /\
    abi_encoder_array_prefix ty avs j d address_ready.vs_memory /\
    abi_encoder_cursor T ip site slot first site st j address_ready /\
    abi_encoder_cursor T dp cursor_site cursor_slot first site st
      (LENGTH avs*abi_member_head_size ty+
        SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) address_ready /\
    abi_decoder_address_frame st.cs_next_var initial address_ready /\
    abi_encoder_registered_effect (abi_decoder_ids first last) [(d,sz)] initial address_ready /\
    (alloca_inv initial ==> alloca_inv address_ready) /\
    abi_encoder_extend_sim ctx func initial address_ready /\
    eval_operand out address_ready = SOME (n2w j) /\
    abi_decoder_operand_live addressed.cs_next_var out /\
    address_ready.vs_current_bb = addressed.cs_current_bb /\
    address_ready.vs_inst_idx = LENGTH addressed.cs_current_insts /\
    ~address_ready.vs_halted /\
    mem_bytes_at (d+32+LENGTH avs*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE j avs)))
      (LENGTH (enc ty (EL j avs))) actual.vs_memory = enc ty (EL j avs) /\
    mem_word_at (d+32+j*asz) actual.vs_memory =
      n2w (LENGTH avs*abi_member_head_size ty+
        SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) /\
    mem_word_at cursor_slot actual.vs_memory =
      n2w (LENGTH avs*abi_member_head_size ty+
        SUM (MAP (abi_member_tail_size ty) (TAKE j avs))+
        LENGTH (enc ty (EL j avs)))
Proof
  strip_tac >> drule_all abi_encoder_shared_array_dynamic_body_run_retained >>
  disch_then (qspec_then `ctx` (qx_choose_then `coords` (qx_choose_then `addressed`
    (qx_choose_then `ops` (qx_choose_then `prepared` (qx_choose_then `len`
      (qx_choose_then `ce` (qx_choose_then `address_ready` (qx_choose_then `ready`
        (qx_choose_then `encoded` (qx_choose_then `actual` strip_assume_tac))))))))))) >>
  qexistsl_tac [`coords`,`addressed`,`ops`,`prepared`,`len`,`ce`,`address_ready`,`ready`,`encoded`,`actual`] >>
  asm_rewrite_tac []
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "retained body run admission, axiom or hypothesis"
  end) [abi_encoder_shared_array_dynamic_body_run_retained];

val _ =
  let val th = abi_encoder_shared_array_dynamic_body_run
      val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared dynamic body run admission, axiom or hypothesis"
  end;

Theorem abi_encoder_shared_array_dynamic_body:
  abi_encoder_shared ei /\
  abi_encode_array_dynamic_body ip dp src dst ei asz msz st = (out,en) /\
  fn_has_code st en func /\
  abi_encoder_shared_input (AbiDynArray ei asz msz T,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first site st j initial /\
  abi_encoder_cursor T dp cursor_site cursor_slot first site st
    (LENGTH avs*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) initial /\
  site < cursor_site /\ j < LENGTH avs /\ en.cs_next_id <= last /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_budget first last b cap initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual.
    abi_encoder_shared_input (AbiDynArray ei asz msz T,Array NONE ty,ListV avs)
      (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) actual /\
    abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory /\
    abi_encoder_cursor T ip site slot first site st j actual /\
    abi_encoder_cursor T dp cursor_site cursor_slot first site st
      (LENGTH avs*abi_member_head_size ty+
        SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) actual /\
    eval_operand out actual = SOME (n2w j) /\
    abi_scratch_effect first last site en.cs_next_id st.cs_next_var limit_st
      d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids site en.cs_next_id) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    abi_encoder_extend_sim ctx func initial actual /\
    actual.vs_current_bb = en.cs_current_bb /\
    actual.vs_inst_idx = LENGTH en.cs_current_insts /\ ~actual.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_shared_array_dynamic_body_run_retained >>
  disch_then (qspec_then `ctx` (qx_choose_then `coords` (qx_choose_then `addressed`
    (qx_choose_then `ops` (qx_choose_then `prepared` (qx_choose_then `len`
      (qx_choose_then `ce` (qx_choose_then `address_ready` (qx_choose_then `ready`
        (qx_choose_then `encoded` (qx_choose_then `actual` strip_assume_tac))))))))))) >>
  qpat_assum `abi_encoder_shared_member_dynamic_post _ _ _ _ _ ready encoded`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE
      [abi_encoder_shared_member_dynamic_post_def,abi_encoder_spine_shared_post_def]) >>
  suspend "actual_callback"
QED

Resume abi_encoder_shared_array_dynamic_body[actual_callback]:
  drule_all abi_encode_array_dynamic_body_context >> strip_tac >>
  gvs[] >>
  drule abi_encoder_shared_array_input_facts >> strip_tac >>
  `LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs` by
    (drule abi_encoder_structural_list_layout >> simp[]) >>
  `32+LENGTH avs*abi_member_head_size ty+
     SUM (MAP (abi_member_tail_size ty) avs) <= sz` by
    (drule abi_encoder_open_array_length >> fs[abi_encoder_shared_input_def]) >>
  `SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) + LENGTH (enc ty (EL j avs)) <=
     SUM (MAP (abi_member_tail_size ty) avs)` by
    (mp_tac (Q.ISPECL [`abi_member_tail_size ty`,`avs:abi_value list`,`j:num`]
      abi_encoder_prefix_sum_bound) >> asm_simp_tac bool_ss [abi_member_tail_size_def]) >>
  `first <= cursor_site /\ cursor_site < last /\ cursor_slot < dimword (:256) /\
   first <= site /\ site < last /\ slot < dimword (:256)` by
    (imp_res_tac abi_encoder_cursor_bounds >> simp[]) >>
  drule abi_encoder_shared_member_dynamic_saved >> strip_tac >>
  `d+32+j*abi_member_head_size ty < dimword (:256)` by
    (`d+sz <= dimword (:256)` by fs[abi_encoder_shared_input_def] >>
     `SUC j*32 <= LENGTH avs*32` by simp[] >>
     fs[abi_member_head_size_def,MULT_CLAUSES] >> gvs[] >> decide_tac) >>
  `eval_operand dp address_ready = SOME (n2w cursor_slot) /\
   mload cursor_slot address_ready = n2w
    (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) /\
   cursor_site < addressed.cs_next_id /\
   FLOOKUP address_ready.vs_allocas cursor_site = SOME (cursor_slot,32)` by
    (fs[abi_encoder_cursor_def] >> gvs[] >> decide_tac) >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\
   abi_decoder_operand_live addressed.cs_next_var (FST (SND coords))` by
    (asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decoder_address_frame addressed.cs_next_var address_ready ready` by
    (drule_all abi_encoder_member_tail_transport >> simp[]) >>
  `abi_decoder_operand_live ce.cs_next_var dp` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >>
     fs[abi_encoder_cursor_def]) >>
  `abi_scratch_effect first last cursor_site en.cs_next_id addressed.cs_next_var limit_st
     d sz b cap address_ready actual /\
   abi_encoder_registered_effect (abi_decoder_ids cursor_site en.cs_next_id) [(d,sz)] address_ready actual /\
   (alloca_inv address_ready ==> alloca_inv actual)` by
    (qpat_assum `abi_encoder_shared_endpoint _ _ _ _ ready encoded`
       (mp_then Any mp_tac abi_encoder_array_spine_shared_effects) >>
     disch_then (fn th => qpat_assum `abi_encode_array_tail _ _ addressed = _`
       (mp_then Any mp_tac th)) >>
     disch_then (fn th => qpat_assum `abi_encode_child_suffix _ _ _ _ ce = _`
       (mp_then Any irule th)) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     asm_simp_tac bool_ss [] >>
     (conj_tac >- decide_tac) >>
     (conj_tac >- decide_tac) >>
     (conj_tac >- decide_tac) >>
     (conj_tac >- decide_tac) >>
     (conj_tac >- decide_tac) >>
     (conj_tac >- decide_tac) >>
     (conj_tac >- (qexists_tac `d+32` >> simp[])) >>
     (conj_tac >- (qexists_tac `d+32+j*abi_member_head_size ty` >> simp[] >>
       `SUC j*32 <= LENGTH avs*32` by simp[] >>
       fs[abi_member_head_size_def,MULT_CLAUSES] >> gvs[] >> decide_tac)) >>
     qexistsl_tac [`LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs))`,
       `cursor_site`,`cursor_slot`] >>
     asm_simp_tac bool_ss [abi_decoder_ids_def] >>
     full_simp_tac bool_ss [] >>
     (conj_tac >- (AP_TERM_TAC >> AP_TERM_TAC >> decide_tac)) >>
     simp[abi_decoder_ids_def] >> decide_tac) >>
  `abi_encoder_extend_sim ctx func address_ready actual` by
    (drule_all abi_encoder_array_spine_shared_sim >> simp[]) >>
  `abi_encoder_extend_sim ctx func initial actual` by
    (irule abi_encoder_extend_sim_trans >> qexists_tac `address_ready` >> simp[]) >>
  `abi_scratch_effect first last site en.cs_next_id st.cs_next_var limit_st
     d sz b cap initial actual` by
    (irule abi_scratch_effect_after_address >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_encoder_registered_effect (abi_decoder_ids site en.cs_next_id) [(d,sz)]
     initial address_ready` by
    (fs[abi_encoder_registered_effect_def,abi_decoder_address_frame_def]) >>
  `abi_encoder_registered_effect (abi_decoder_ids site en.cs_next_id) [(d,sz)]
     address_ready actual` by
    (irule abi_encoder_registered_effect_enlarge >>
     goal_assum (drule_at Any) >>
     simp[pred_setTheory.SUBSET_DEF,abi_decoder_ids_def] >> decide_tac) >>
  `abi_encoder_registered_effect (abi_decoder_ids site en.cs_next_id) [(d,sz)]
     initial actual` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `address_ready` >> simp[]) >>
  `abi_encoder_shared_input (AbiDynArray ei asz msz T,Array NONE ty,ListV avs)
     (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) actual` by
    (irule abi_encoder_shared_input_effect >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  `alloca_inv initial ==> alloca_inv actual` by metis_tac[] >>
  `abi_encoder_cursor T ip site slot first site st j actual` by
    (irule abi_scratch_cursor_protected >>
     qpat_assum `abi_scratch_effect _ _ cursor_site _ _ _ _ _ _ _ address_ready actual`
       (irule_at Any) >>
     goal_assum (drule_at Any) >>
     asm_simp_tac bool_ss [] >>
     fs[abi_encoder_shared_input_def] >> decide_tac) >>
  `FLOOKUP actual.vs_allocas cursor_site = SOME (cursor_slot,32)` by
    (drule_all abi_encoder_registered_effect_allocated >> simp[]) >>
  `SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs)) =
     SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) + LENGTH (enc ty (EL j avs))` by
    (simp[GSYM SNOC_EL_TAKE,MAP_SNOC,SUM_SNOC,abi_member_tail_size_def]) >>
  `abi_encoder_cursor T dp cursor_site cursor_slot first site st
     (LENGTH avs*abi_member_head_size ty+
       SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) actual` by
    (irule abi_scratch_cursor_registered >>
     qpat_assum `abi_scratch_effect _ _ site _ _ _ _ _ _ _ initial actual`
       (irule_at Any) >>
     qpat_assum `abi_encoder_cursor T dp _ _ _ _ _ _ initial` (irule_at Any) >>
     asm_simp_tac bool_ss [GSYM mem_word_at_eq_mload] >>
     (conj_tac >- (AP_TERM_TAC >> decide_tac)) >> decide_tac) >>
  `abi_encoder_child_suffix_post child_len ce limit_st
     (d+32+j*asz) cursor_slot
     (SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) + LENGTH avs*abi_member_head_size ty)
     (LENGTH (enc ty (EL j avs))) encoded actual` by
    (qpat_assum `abi_encode_child_suffix _ _ _ _ ce = _`
       (mp_then Any irule abi_encoder_spine_cursor_post) >>
     goal_assum (drule_at Any) >>
     asm_simp_tac bool_ss [] >>
     fs[abi_encoder_shared_endpoint_def,abi_scratch_effect_def]) >>
  `abi_scratch_effect first last prepared.cs_next_id ce.cs_next_id prepared.cs_next_var
     limit_st (d+(SUM (MAP (abi_member_tail_size ty) (TAKE j avs))+
       (LENGTH avs*abi_member_head_size ty+32))) (LENGTH (enc ty (EL j avs)))
     b cap ready encoded` by
    (drule abi_encoder_shared_endpoint_scratch >> simp[]) >>
  `abi_decode_footprint_frame
     ([(d+32+j*asz,32);
       (d+(SUM (MAP (abi_member_tail_size ty) (TAKE j avs))+
         (LENGTH avs*abi_member_head_size ty+32)),LENGTH (enc ty (EL j avs)))] ++
       abi_decoder_child_scratch (abi_decoder_ids cursor_site en.cs_next_id) b cap address_ready)
     address_ready actual` by
    (irule abi_scratch_dynamic_child_frame >>
     qpat_assum `abi_scratch_effect _ _ prepared.cs_next_id _ _ _ _ _ _ _ ready encoded`
       (irule_at Any) >>
     qpat_assum `abi_decoder_address_frame _ address_ready ready` (irule_at Any) >>
     qpat_assum `abi_encoder_child_suffix_post _ _ _ _ _ _ _ encoded actual`
       (assume_tac o cj 4 o PURE_REWRITE_RULE [abi_encoder_child_suffix_post_def]) >>
     goal_assum (drule_at Any) >>
     qexists_tac `cursor_site` >>
     asm_simp_tac bool_ss [] >>
     simp[abi_decoder_ids_def,pred_setTheory.SUBSET_DEF] >> decide_tac) >>
  `abi_footprint_disjoint d sz
     (abi_decoder_child_scratch (abi_decoder_ids cursor_site en.cs_next_id) b cap address_ready)` by
    (irule abi_scratch_disjoint_subset >> qexists_tac `abi_decoder_ids first last` >>
     fs[abi_encoder_shared_input_def,pred_setTheory.SUBSET_DEF,abi_decoder_ids_def] >> decide_tac) >>
  `!p n. d <= p /\ p+n <= d+sz ==>
     abi_footprint_disjoint p n
       (abi_decoder_child_scratch (abi_decoder_ids cursor_site en.cs_next_id) b cap address_ready)` by
    (rpt strip_tac >> irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`d`,`sz`] >> simp[]) >>
  `abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory` by
    (irule abi_encoder_open_array_dynamic_step >>
     qpat_assum `abi_decode_footprint_frame (_ ++ _) address_ready actual` (irule_at Any) >>
     qpat_assum `abi_encoder_array_prefix _ _ _ _ address_ready.vs_memory` (irule_at Any) >>
     asm_simp_tac bool_ss [] >>
     (conj_tac >-
       (qpat_x_assum `asz = _` SUBST_ALL_TAC >>
        qpat_assum `mem_word_at (d+_) actual.vs_memory = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp_tac bool_ss [AC ADD_ASSOC ADD_COMM,MULT_COMM])) >>
     (conj_tac >-
       (qpat_assum `mem_bytes_at _ _ actual.vs_memory = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp_tac bool_ss [AC ADD_ASSOC ADD_COMM])) >>
     simp_tac bool_ss [abi_footprint_disjoint_append,abi_scratch_disjoint_cons] >>
     `SUC j*32 <= LENGTH avs*32` by simp[] >>
     full_simp_tac bool_ss [abi_member_head_size_def] >>
     qpat_assum `is_dynamic ty` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
     asm_simp_tac (srw_ss()) [MULT_CLAUSES] >>
     rpt conj_tac
     >- decide_tac
     >- simp[abi_footprint_disjoint_def]
     >- (qpat_assum `!p n. _ ==> abi_footprint_disjoint p n _` irule >> decide_tac)
     >- decide_tac
     >- simp[abi_footprint_disjoint_def]
     >- (qpat_assum `!p n. _ ==> abi_footprint_disjoint p n _` irule >> decide_tac)
     >- decide_tac
     >- decide_tac
     >- simp[abi_footprint_disjoint_def]
     >> qpat_assum `!p n. _ ==> abi_footprint_disjoint p n _` irule >> decide_tac) >>
  `eval_operand (FST (FST coords)) actual = SOME (n2w j)` by
    (qpat_assum `abi_scratch_effect _ _ cursor_site _ _ _ _ _ _ _ address_ready actual`
       (mp_then Any irule abi_scratch_effect_operand) >>
     asm_simp_tac bool_ss []) >>
  `actual.vs_current_bb = en.cs_current_bb /\
   actual.vs_inst_idx = LENGTH en.cs_current_insts` by
    (qpat_assum `abi_encode_child_suffix _ _ _ _ ce = _`
       (mp_then Any irule abi_encoder_source_suffix_raw_control) >>
     goal_assum (drule_at Any) >> fs[abi_encoder_shared_endpoint_def]) >>
  `~actual.vs_halted` by
    (qpat_assum `abi_encoder_child_suffix_post _ _ _ _ _ _ _ encoded actual` mp_tac >>
     fs[abi_encoder_child_suffix_post_def,abi_encoder_shared_endpoint_def]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  qpat_assum `abi_encoder_cursor T dp _ _ _ _ _ _ actual` mp_tac >>
  qpat_assum `SUM (MAP _ (TAKE (SUC j) avs)) = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]
QED

Finalise abi_encoder_shared_array_dynamic_body

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared dynamic body admission, axiom or hypothesis"
  end) [abi_encoder_shared_array_dynamic_body];

Theorem abi_encoder_shared_array_static_body:
  abi_encoder_shared ei /\ abi_encoder_static_leaf ei /\
  abi_encode_array_static_body ip src dst ei asz msz st = (out,en) /\
  fn_has_code st en func /\
  abi_encoder_shared_input (AbiDynArray ei asz msz F,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first site st j initial /\
  abi_encoder_cursor F dp cursor_site cursor_slot first site st
    (LENGTH avs*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) initial /\
  j < LENGTH avs /\ en.cs_next_id <= last /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_budget first last b cap initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual.
    abi_encoder_shared_input (AbiDynArray ei asz msz F,Array NONE ty,ListV avs)
      (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) actual /\
    abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory /\
    abi_encoder_cursor T ip site slot first site st j actual /\
    abi_encoder_cursor F dp cursor_site cursor_slot first site st
      (LENGTH avs*abi_member_head_size ty+
        SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) actual /\
    eval_operand out actual = SOME (n2w j) /\
    abi_scratch_effect first last site en.cs_next_id st.cs_next_var limit_st
      d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids site en.cs_next_id) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    abi_encoder_extend_sim ctx func initial actual /\
    actual.vs_current_bb = en.cs_current_bb /\
    actual.vs_inst_idx = LENGTH en.cs_current_insts /\ ~actual.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_static_body_context >>
  disch_then (qx_choose_then `coords` (qx_choose_then `addressed`
    (qx_choose_then `ignored` strip_assume_tac))) >>
  `addressed.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_id <= last` by decide_tac >>
  drule_all abi_encoder_shared_array_body_address >>
  disch_then (qspecl_then [`[(d,sz)]`,`abi_decoder_ids first last`,`ctx`]
    (qx_choose_then `address_ready` strip_assume_tac)) >>
  qpat_x_assum `abi_encode_array_static_body _ _ _ _ _ _ _ = _` kall_tac >>
  drule abi_encoder_shared_array_input_facts >> strip_tac >>
  `~is_dynamic ty` by metis_tac[] >>
  `LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs` by
    (drule abi_encoder_structural_list_layout >> simp[]) >>
  `32+LENGTH avs*abi_member_head_size ty+
     SUM (MAP (abi_member_tail_size ty) avs) <= sz` by
    (drule abi_encoder_open_array_length >> fs[abi_encoder_shared_input_def]) >>
  `abi_encoder_layout_valid ty (EL j avs)` by
    (fs[LIST_REL_EL_EQN,EL_REPLICATE]) >>
  `LENGTH (enc ty (EL j avs)) = abi_member_head_size ty` by
    fs[abi_encoder_layout_valid_def,abi_member_head_size_def] >>
  `j*asz+LENGTH (enc ty (EL j avs)) <= LENGTH avs*asz` by
    (`SUC j*asz <= LENGTH avs*asz` by simp[] >>
     qpat_x_assum `SUC j*asz <= _` mp_tac >>
     asm_simp_tac bool_ss [MULT_CLAUSES,ADD_COMM]) >>
  `abi_encoder_shared_input (ei,ty,EL j avs)
     (addressed,SND (FST coords),SND (SND coords)) (sb+32+j*msz,msz)
     (d+32+j*asz,LENGTH (enc ty (EL j avs))) (first,last,b,cap) address_ready` by
    (irule abi_encoder_shared_array_body_child_input >>
     asm_simp_tac bool_ss [] >> (conj_tac >- simp[]) >>
     goal_assum (drule_at Any) >> qpat_x_assum `asz = _` SUBST_ALL_TAC >>
     full_simp_tac bool_ss [] >> decide_tac) >>
  qpat_assum `abi_encoder_static_leaf ei` (fn th =>
    qpat_assum `compile_abi_encode_static_info _ _ _ _ = _`
      (assume_tac o PURE_REWRITE_RULE [MATCH_MP abi_encode_static_info_agrees th])) >>
  `first <= addressed.cs_next_id` by
    (qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ initial` mp_tac >>
     simp_tac bool_ss [abi_encoder_cursor_def] >> strip_tac >> decide_tac) >>
  `?actual. abi_encoder_shared_endpoint (ctx,func) (addressed,en,ignored,limit_st)
     (first,last,b,cap) (ty,EL j avs,d+32+j*asz) address_ready actual` by
    (qpat_assum `abi_encoder_shared ei` (irule o PURE_REWRITE_RULE [abi_encoder_shared_def]) >>
     goal_assum (drule_at Any) >> asm_simp_tac bool_ss [] >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`sb+32+j*msz`,`msz`] >>
     qpat_x_assum `asz = _` SUBST_ALL_TAC >>
     qpat_assum `abi_encoder_shared_input (ei,ty,_) _ _ _ _ address_ready` mp_tac >>
     qpat_assum `LENGTH (enc ty (EL j avs)) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]) >>
  rename1 `abi_encoder_shared_endpoint (ctx,func) _ _ _ address_ready actual` >>
  suspend "static_finish"
QED

Resume abi_encoder_shared_array_static_body[static_finish]:
  qpat_assum `abi_encoder_shared_endpoint _ _ _ _ address_ready actual`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_endpoint_def]) >>
  `site <= st.cs_next_id /\ first <= site` by fs[abi_encoder_cursor_def] >>
  `d+32+j*asz+LENGTH (enc ty (EL j avs)) <= d+sz` by
    (qpat_x_assum `asz = _` SUBST_ALL_TAC >> full_simp_tac bool_ss [] >> decide_tac) >>
  `abi_encoder_extend_sim ctx func initial actual` by
    (irule abi_encoder_extend_sim_trans >> qexists_tac `address_ready` >> simp[]) >>
  `abi_scratch_effect first last site en.cs_next_id st.cs_next_var limit_st
     d sz b cap initial actual` by
    (irule abi_scratch_effect_after_address >>
     qpat_assum `abi_scratch_effect _ _ addressed.cs_next_id _ _ _ _ _ _ _ address_ready actual`
       (irule_at Any) >>
     goal_assum (drule_at Any) >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_encoder_registered_effect (abi_decoder_ids site en.cs_next_id) [(d,sz)]
     initial address_ready` by
    fs[abi_encoder_registered_effect_def,abi_decoder_address_frame_def] >>
  `abi_encoder_registered_effect (abi_decoder_ids site en.cs_next_id) [(d,sz)]
     address_ready actual` by
    (irule abi_encoder_registered_effect_enlarge >>
     goal_assum (drule_at Any) >>
     simp[pred_setTheory.SUBSET_DEF,abi_decoder_ids_def] >>
     qpat_x_assum `asz = _` SUBST_ALL_TAC >> full_simp_tac bool_ss [] >> decide_tac) >>
  `abi_encoder_registered_effect (abi_decoder_ids site en.cs_next_id) [(d,sz)]
     initial actual` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `address_ready` >> simp[]) >>
  `abi_encoder_shared_input (AbiDynArray ei asz msz F,Array NONE ty,ListV avs)
     (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) actual` by
    (irule abi_encoder_shared_input_effect >>
     qpat_assum `abi_scratch_effect _ _ site _ _ _ d sz _ _ initial actual` (irule_at Any) >>
     qpat_assum `abi_encoder_shared_input _ _ _ _ _ initial` (irule_at Any) >>
     simp[]) >>
  `alloca_inv initial ==> alloca_inv actual` by metis_tac[] >>
  `abi_encoder_cursor T ip site slot first site st j actual` by
    (irule abi_scratch_cursor_protected >>
     qpat_assum `abi_scratch_effect _ _ addressed.cs_next_id _ _ _ _ _ _ _ address_ready actual`
       (irule_at Any) >>
     qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ address_ready` (irule_at Any) >>
     asm_simp_tac bool_ss [] >>
     fs[abi_encoder_shared_input_def] >>
     qpat_x_assum `asz = _` SUBST_ALL_TAC >>
     fs[MULT_COMM,abi_encoder_cursor_def] >>
     qpat_assum `abi_footprint_disjoint (d + _) (LENGTH (enc ty (EL j avs))) _` mp_tac >>
     qpat_assum `LENGTH (enc ty (EL j avs)) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[AC ADD_ASSOC ADD_COMM]) >>
  `eval_operand out actual = SOME (n2w j)` by
    (qpat_assum `abi_scratch_effect _ _ addressed.cs_next_id _ _ _ _ _ _ _ address_ready actual`
       (mp_then Any irule abi_scratch_effect_operand) >> gvs[]) >>
  suspend "static_prefix"
QED

Resume abi_encoder_shared_array_static_body[static_prefix]:
  `abi_decode_footprint_frame
     ((d+32+j*asz,LENGTH (enc ty (EL j avs)))::
       abi_decoder_child_scratch (abi_decoder_ids first last) b cap address_ready)
     address_ready actual` by
    (qpat_assum `abi_scratch_effect _ _ addressed.cs_next_id _ _ _ _ _ _ _ address_ready actual`
       (mp_then Any mp_tac abi_scratch_effect_frame) >> simp[]) >>
  `!p n. d <= p /\ p+n <= d+sz ==>
     abi_footprint_disjoint p n
       (abi_decoder_child_scratch (abi_decoder_ids first last) b cap address_ready)` by
    (rpt strip_tac >> irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`d`,`sz`] >> fs[abi_encoder_shared_input_def]) >>
  `!xs. SUM (MAP (abi_member_tail_size ty) xs) = 0` by
    (Induct >> simp[abi_member_tail_size_def]) >>
  `abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory` by
    (irule abi_encoder_open_array_static_step >>
     qpat_assum `abi_decode_footprint_frame _ address_ready actual` (irule_at Any) >>
     qpat_assum `abi_encoder_array_prefix _ _ _ _ address_ready.vs_memory` (irule_at Any) >>
     asm_simp_tac bool_ss [] >>
     (conj_tac >-
       (qpat_assum `mem_bytes_at _ _ actual.vs_memory = _` mp_tac >>
        qpat_x_assum `asz = _` SUBST_ALL_TAC >>
        qpat_assum `LENGTH (enc ty (EL j avs)) = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[AC ADD_ASSOC ADD_COMM])) >>
     simp_tac bool_ss [abi_scratch_disjoint_cons] >>
     rpt conj_tac
     >- decide_tac
     >- (qpat_assum `!p n. _ ==> abi_footprint_disjoint p n _` irule >> decide_tac)
     >- decide_tac
     >- (qpat_assum `!p n. _ ==> abi_footprint_disjoint p n _` irule >>
         qpat_x_assum `asz = _` SUBST_ALL_TAC >>
         qpat_assum `32+LENGTH avs*abi_member_head_size ty+_ <= sz` mp_tac >>
         asm_simp_tac bool_ss [] >> decide_tac)
     >> simp[abi_footprint_disjoint_def] >>
     `SUC j * abi_member_head_size ty <= LENGTH avs * abi_member_head_size ty` by simp[] >>
     qpat_x_assum `SUC j * abi_member_head_size ty <= _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [MULT_CLAUSES] >> decide_tac) >>
  qexists_tac `actual` >> simp[abi_encoder_cursor_def]
QED

Finalise abi_encoder_shared_array_static_body

val _ =
  let val th = abi_encoder_shared_array_static_body
      val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared array static body admission, axiom or hypothesis"
  end;
