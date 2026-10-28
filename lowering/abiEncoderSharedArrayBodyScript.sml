(* Rich array callbacks: the address phase, child and suffix retain their
   actual endpoints.  No loop or descriptor execution induction lives here. *)
Theory abiEncoderSharedArrayBody
Ancestors
  abiEncoderSharedArrayAddress abiEncoderSharedArrayStep abiEncoderSharedArrayTail
  abiEncoderSharedArrayRound abiEncoderSharedArrayHeader abiEncoderSharedArrayInput
  abiEncoderSharedInputEffect abiEncoderArrayDynamicCode abiEncoderArrayBodyCode
  abiEncoderSharedContract abiEncoderArrayCursor abiEncoderMembersDefs abiScratchEffect
  abiEncoderArrayFrame abiEncoderOpenInputFrame abiDecodeRanges venomMemDefs
  abiDecoderDynamicLoopSetup abiDecoderAllocation abiDecoderFootprint abiDecoderReentry
  compileEnv valueEncoding venomState words list arithmetic

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
