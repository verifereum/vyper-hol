Theory abiEncoderMembersStep
Ancestors
  abiEncoderMembersDefs abiEncoderMembersInput abiEncoderInput abiEncoderChildInputs
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderContract compileEnv valueEncoding
  contractABI venomState words list arithmetic abiEncoderMembersContract abiEncoderTuple
  abiCanonicalWindows abiDecodeRanges abiDecoderEffect abiEncoderMemberSourceAdapter
  abiEncoderMemberSourceInterpret abiEncoderMemberSourceContract abiEncoderMemberCode
  abiDecoderLoop valueEncodingProps abiEncoderMember abiEncoderCorrect fragExec

(* Pure source invariants for the current child and the remaining compiler call. *)
Theorem abi_encoder_members_pre_cons:
  abi_encoder_members_pre ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    st src dst sb so d output_size b cap s ==>
  has_type ty av /\ has_types tys avs /\
  abi_sz = abi_member_head_size ty /\ dyn = is_dynamic ty /\
  abi_encoder_input ei ty av (sb+so) mem_sz s.vs_memory /\
  abi_encoder_members_pre infos tys avs st src dst sb (so+mem_sz) d output_size b cap s
Proof
  strip_tac >> qpat_x_assum `abi_encoder_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_pre_def]) >>
  drule abi_encoder_members_input_cons >> strip_tac >>
  `has_types tys avs` by (imp_res_tac abi_encoder_input_typed >> fs[Once has_type_def]) >>
  `abi_encoder_member_span ((ei,abi_sz,mem_sz,dyn)::infos) = mem_sz+abi_encoder_member_span infos`
    by simp[abi_encoder_member_span_def] >>
  asm_simp_tac bool_ss [abi_encoder_members_pre_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >> PURE_REWRITE_TAC [ADD_ASSOC] >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_encoder_members_child_buffer:
  abi_encoder_members_pre ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    st src dst sb so d output_size b cap initial /\
  abi_decoder_address_frame st.cs_next_var initial actual /\ st.cs_next_var <= prepared.cs_next_var /\
  abi_decoder_operand_live prepared.cs_next_var elem_src /\
  eval_operand elem_src actual = SOME (n2w (sb+so)) ==>
  abi_encoder_buffer_pre ei ty av prepared elem_src dst (sb+so) mem_sz d output_size b cap actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_pre_def]) >>
  drule abi_encoder_members_input_cons >> strip_tac >>
  `abi_encoder_member_span ((ei,abi_sz,mem_sz,dyn)::infos) = mem_sz+abi_encoder_member_span infos`
    by simp[abi_encoder_member_span_def] >>
  `actual.vs_memory = initial.vs_memory /\ eval_operand dst actual = SOME (n2w d)`
    by fs[abi_decoder_address_frame_def] >>
  `abi_decoder_operand_live prepared.cs_next_var dst` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  asm_simp_tac bool_ss [abi_encoder_buffer_pre_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >> PURE_REWRITE_TAC [ADD_ASSOC] >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

(* Canonical bounds and offsets needed by one recursive member step. *)
Theorem abi_encoder_members_layout:
  has_types (pre++ty::tys) (pvs++av::avs) /\ LENGTH pre = LENGTH pvs /\
  hl = head_lengths (pre++ty::tys) 0 /\ heads = SUM (MAP abi_member_head_size pre) /\
  tails = SUM (MAP2 abi_member_tail_size pre pvs) /\
  LENGTH (enc (Tuple (pre++ty::tys)) (ListV (pvs++av::avs))) <= output_size ==>
  has_types pre pvs /\ has_type ty av /\ has_types tys avs /\
  heads = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  tails = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  heads+abi_member_head_size ty <= hl /\ hl+tails <= output_size /\
  (~is_dynamic ty ==> heads+LENGTH (enc ty av) <= hl) /\
  (is_dynamic ty ==> heads+32 <= hl /\ hl+tails+LENGTH (enc ty av) <= output_size)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `has_types pre pvs /\ has_type ty av /\ has_types tys avs`
    by fs[has_types_append, has_type_def] >>
  `heads+abi_member_head_size ty <= hl` by
    simp[head_lengths_acc, MAP_APPEND, SUM_APPEND] >>
  `LENGTH (enc (Tuple (pre++ty::tys)) (ListV (pvs++av::avs))) =
    hl+tails+abi_member_tail_size ty av+SUM (MAP2 abi_member_tail_size tys avs)` by
    asm_simp_tac bool_ss [canonical_tuple_length, head_lengths_acc, MAP_APPEND, MAP2_APPEND,
      SUM_APPEND, MAP, MAP2, SUM, ADD_CLAUSES, AC ADD_COMM ADD_ASSOC] >>
  `~is_dynamic ty ==> LENGTH (enc ty av) = static_length ty` by
    (strip_tac >> irule (cj 1 enc_has_static_length) >> simp[]) >>
  Cases_on `is_dynamic ty` >>
  full_simp_tac bool_ss [abi_member_head_size_def, abi_member_tail_size_def,
    abi_tuple_heads_length, abi_tuple_tails_length] >> decide_tac
QED

Theorem abi_encoder_members_prefix_advance:
  has_types pre pvs /\ has_type ty av ==>
  has_types (pre++[ty]) (pvs++[av]) /\
  SUM (MAP abi_member_head_size (pre++[ty])) =
    SUM (MAP abi_member_head_size pre)+abi_member_head_size ty /\
  LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av]))) =
    LENGTH (FLAT (abi_tuple_tails pre pvs))+(if is_dynamic ty then LENGTH (enc ty av) else 0)
Proof
  strip_tac >> drule has_types_length >> strip_tac >>
  simp[has_types_append, has_type_def, MAP_APPEND, SUM_APPEND,
    abi_tuple_tails_append, abi_tuple_tails_def, FLAT_APPEND] >>
  Cases_on `is_dynamic ty` >> simp[]
QED

Theorem abi_encoder_members_inv_layout:
  abi_encoder_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial ==>
  has_type ty av /\ has_types tys avs /\ LENGTH pre = LENGTH pvs /\
  abi_sz = abi_member_head_size ty /\ dyn = is_dynamic ty /\
  ho = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  SUM (MAP2 abi_member_tail_size pre pvs) = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  ho+abi_sz <= hl /\ hl+SUM (MAP2 abi_member_tail_size pre pvs) <= output_size /\
  (~dyn ==> ho+LENGTH (enc ty av) <= hl) /\
  (dyn ==> ho+32 <= hl /\ hl+SUM (MAP2 abi_member_tail_size pre pvs)+LENGTH (enc ty av) <= output_size)
Proof
  strip_tac >> qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`] abi_encoder_members_pre_cons) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `LENGTH pre = LENGTH pvs` by (irule has_types_length >> asm_simp_tac bool_ss []) >>
  `has_types (pre++ty::tys) (pvs++av::avs)` by simp[has_types_append, has_type_def] >>
  mp_tac (Q.INST [`heads` |-> `ho:num`, `tails` |-> `SUM (MAP2 abi_member_tail_size pre pvs)`]
    abi_encoder_members_layout) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `ho = SUM _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qpat_assum `hl = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

(* Transfer successful child observations to the next member's pure invariant. *)
Theorem abi_encoder_members_after_child:
  abi_encoder_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual /\
  abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d actual.vs_memory /\
  abi_encoder_cursor active dyn_ptr site slot first lo end_st
    (hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))) actual /\
  st.cs_next_var <= end_st.cs_next_var /\ st.cs_next_id <= end_st.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  ~actual.vs_halted /\ actual.vs_current_bb = end_st.cs_current_bb /\
  actual.vs_inst_idx = LENGTH end_st.cs_current_insts ==>
  abi_encoder_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot first last lo
    end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  mp_tac (Q.INST [`infos` |-> `(ei,abi_sz,mem_sz,dyn)::infos`, `tys` |-> `ty::tys`,
    `avs` |-> `av::avs`, `hi` |-> `end_st.cs_next_id`] abi_encoder_members_pre_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`infos` |-> `(ei,abi_sz,mem_sz,dyn)::infos`, `tys` |-> `ty::tys`,
    `avs` |-> `av::avs`, `prepared` |-> `end_st`, `s` |-> `actual:venom_state`]
    abi_encoder_members_pre_mono) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`st` |-> `end_st`, `s` |-> `actual:venom_state`] abi_encoder_members_pre_cons) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac abi_encoder_members_prefix_advance >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  `first <= end_st.cs_next_id /\ lo <= end_st.cs_next_id` by decide_tac >>
  PURE_REWRITE_TAC [abi_encoder_members_inv_def, GSYM APPEND_ASSOC, APPEND] >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `active \/ EVERY _ _` mp_tac >> simp_tac (srw_ss()) [] >>
  rpt strip_tac >> asm_simp_tac bool_ss []
QED

(* Pure member invariant advancement at the shared generator's endpoint.
   This late interpretation layer deliberately does not generate execution. *)
Theorem abi_encoder_members_static_endpoint:
  compile_abi_encode_child dst elem_src ei F ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_members_inv ((ei,abi_sz,mem_sz,F)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_encoder_buffer_pre ei ty av st elem_src dst (sb+so) mem_sz d output_size b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_spine_child_output
    (abi_encoder_member_core_post (ctx,func) (ty,av,sb+so,mem_sz,d+ho)
      (first,last,b,cap,limit_st))
    (ei,F,dst,elem_src,ho,dyn_ptr,st,end_st,out) initial actual ==>
  abi_encoder_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot
    first last lo end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual /\
  abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  mp_tac (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `F`] abi_encoder_members_inv_layout)) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_encoder_child_bounds >> strip_tac >>
  `ho+LENGTH (enc ty av) <= output_size` by decide_tac >>
  drule_all abi_encoder_member_source_static_output >> strip_tac >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  drule_all abi_encoder_tuple_static_step >> strip_tac >>
  mp_tac (Q.INST [`off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`,
    `sz` |-> `output_size:num`] abi_encoder_cursor_static) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac abi_encoder_members_prefix_advance >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_encoder_cursor active dyn_ptr site slot first lo end_st
    (hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))) actual` by
    (qpat_assum `~is_dynamic ty` (fn dyn_th =>
       qpat_assum `LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av]))) = _`
         (fn th => PURE_REWRITE_TAC [SIMP_RULE bool_ss [dyn_th, ADD_CLAUSES] th])) >>
     first_assum ACCEPT_TAC) >>
  `abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  drule_all (Q.INST [`dyn` |-> `F`] abi_encoder_members_after_child) >> strip_tac >>
  asm_rewrite_tac []
QED

Theorem abi_encoder_members_dynamic_endpoint:
  compile_abi_encode_child dst elem_src ei T ho dyn_ptr st = (out,end_st) /\
  abi_encode_child_prefix dst ho dyn_ptr st = (ops,prepared) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_members_inv ((ei,abi_sz,mem_sz,T)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_encoder_buffer_pre ei ty av st elem_src dst (sb+so) mem_sz d output_size b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  off = hl+LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  abi_encoder_spine_child_output
    (abi_encoder_member_dynamic_post (ctx,func) (ty,av,sb+so,mem_sz,d+off)
      (first,last,b,cap,limit_st) (FST ops,FST (SND ops),dyn_ptr,d+ho,off,slot,site))
    (ei,T,dst,elem_src,ho,dyn_ptr,st,end_st,out) initial actual ==>
  abi_encoder_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot
    first last lo end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual /\
  abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  reverse (Cases_on `active`) >- simp[abi_encoder_members_inv_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  mp_tac (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `T`, `active` |-> `T`]
    abi_encoder_members_inv_layout)) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_encoder_child_bounds >> strip_tac >>
  qpat_assum `abi_encoder_cursor _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  `ho+32 <= off /\ off+LENGTH (enc ty av) <= output_size /\
    mload slot initial = n2w off` by fs[] >>
  drule_all abi_encoder_member_source_dynamic_output >> strip_tac >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  qpat_x_assum `abi_encoder_spine_child_output _ _ _ _` kall_tac >>
  qpat_x_assum `abi_encode_child_prefix _ _ _ _ = _` kall_tac >>
  mp_tac (Q.INST [`heads` |-> `ho:num`,
    `tails` |-> `LENGTH (FLAT (abi_tuple_tails pre pvs))`] abi_encoder_tuple_dynamic_step) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac abi_encoder_members_prefix_advance >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `mem_word_at slot actual.vs_memory = _`
    (assume_tac o PURE_REWRITE_RULE [mem_word_at_eq_mload]) >>
  mp_tac (Q.INST [`off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`,
    `next_off` |-> `hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))`,
    `sz` |-> `output_size:num`, `owned_lo` |-> `lo:num`, `owned_hi` |-> `end_st.cs_next_id`]
    abi_encoder_cursor_finish) >>
  impl_tac >- asm_simp_tac bool_ss [ADD_ASSOC] >> strip_tac >>
  drule_all (Q.INST [`dyn` |-> `T`, `active` |-> `T`] abi_encoder_members_after_child) >>
  strip_tac >> asm_rewrite_tac []
QED

(* The list interpretation keeps origin/initial fixed, rather than resetting
   its effect ledger to the most recent prepare state. *)
Theorem abi_encoder_members_origin_transport:
  abi_decoder_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial s /\
  abi_decode_sim ctx func initial s /\
  abi_decoder_address_frame st.cs_next_var s r /\ fresh_vars_wrt limit_st r /\
  abi_decoder_budget first last b cap s /\
  abi_decode_sim ctx func s r /\
  abi_decoder_effect first last lo ce.cs_next_id prepared.cs_next_var
    limit_st d sz b cap r u /\ abi_decode_sim ctx func r u /\
  origin.cs_next_var <= st.cs_next_var /\ origin.cs_next_var <= prepared.cs_next_var /\
  ce.cs_next_id <= hi ==>
  abi_decoder_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial u /\
  abi_decode_sim ctx func initial u
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_effect first last lo hi origin.cs_next_var limit_st d sz b cap s r` by
    (irule abi_decoder_address_effect >> asm_rewrite_tac [] >>
     qexists_tac `st.cs_next_var` >> asm_rewrite_tac []) >>
  `abi_decoder_effect first last lo hi origin.cs_next_var limit_st d sz b cap r u` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d`, `ce.cs_next_id`, `lo:num`, `prepared.cs_next_var`, `sz:num`] >>
     simp[]) >>
  conj_tac
  >- (irule abi_decoder_effect_trans >> qexists_tac `s` >> asm_rewrite_tac [] >>
      irule abi_decoder_effect_trans >> qexists_tac `r` >> asm_rewrite_tac []) >>
  irule abi_decode_sim_trans >> qexists_tac `s` >> asm_rewrite_tac [] >>
  irule abi_decode_sim_trans >> qexists_tac `r` >> asm_rewrite_tac []
QED

(* Execute a static child and retain the parent cursor for the remaining members. *)
Theorem abi_encoder_members_static_advance:
  abi_encoder_correct ei /\ compile_abi_encode_child dst elem_src ei F ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_members_inv ((ei,abi_sz,mem_sz,F)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_encoder_buffer_pre ei ty av st elem_src dst (sb+so) mem_sz d output_size b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. abi_encoder_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot
      first last lo end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual /\
    abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  mp_tac (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `F`] abi_encoder_members_inv_layout)) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_encoder_child_bounds >> strip_tac >>
  mp_tac (Q.INST [`heads` |-> `ho:num`, `tails` |-> `SUM (MAP2 abi_member_tail_size pre pvs)`,
    `src` |-> `elem_src`, `sb` |-> `sb+so`, `source_cap` |-> `mem_sz:num`]
    abi_encoder_static_member_step) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  mp_tac (Q.INST [`off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`,
    `sz` |-> `output_size:num`] abi_encoder_cursor_static) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac abi_encoder_members_prefix_advance >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_encoder_cursor active dyn_ptr site slot first lo end_st
    (hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))) actual` by
    (qpat_assum `~is_dynamic ty` (fn dyn_th =>
       qpat_assum `LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av]))) = _`
         (fn th => PURE_REWRITE_TAC [SIMP_RULE bool_ss [dyn_th, ADD_CLAUSES] th])) >>
     first_assum ACCEPT_TAC) >>
  `abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  mp_tac (Q.INST [`dyn` |-> `F`] abi_encoder_members_after_child) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* Execute a dynamic child and advance its parent cursor and remaining source invariant. *)
Theorem abi_encoder_members_dynamic_advance:
  abi_encoder_correct ei /\ compile_abi_encode_child dst elem_src ei T ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_members_inv ((ei,abi_sz,mem_sz,T)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_encoder_buffer_pre ei ty av st elem_src dst (sb+so) mem_sz d output_size b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. abi_encoder_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot
      first last lo end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual /\
    abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  reverse (Cases_on `active`) >- simp[abi_encoder_members_inv_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  mp_tac (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `T`, `active` |-> `T`]
    abi_encoder_members_inv_layout)) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_encoder_child_bounds >> strip_tac >>
  qpat_assum `abi_encoder_cursor _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  mp_tac (Q.INST [`heads` |-> `ho:num`, `tails` |-> `SUM (MAP2 abi_member_tail_size pre pvs)`,
    `off` |-> `hl+SUM (MAP2 abi_member_tail_size pre pvs)`,
    `src` |-> `elem_src`, `sb` |-> `sb+so`, `source_cap` |-> `mem_sz:num`]
    abi_encoder_dynamic_member_step) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  mp_tac abi_encoder_members_prefix_advance >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`,
    `next_off` |-> `hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))`,
    `sz` |-> `output_size:num`, `owned_lo` |-> `lo:num`, `owned_hi` |-> `end_st.cs_next_id`]
    abi_encoder_cursor_finish) >>
  impl_tac >- asm_simp_tac bool_ss [ADD_ASSOC] >> strip_tac >>
  mp_tac (Q.INST [`dyn` |-> `T`, `active` |-> `T`] abi_encoder_members_after_child) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* Both child branches establish the same next-member state and execution contract. *)
Theorem abi_encoder_members_child_advance:
  abi_encoder_correct ei /\ compile_abi_encode_child dst elem_src ei dyn ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_encoder_buffer_pre ei ty av st elem_src dst (sb+so) mem_sz d output_size b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. abi_encoder_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot
      first last lo end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual /\
    abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  Cases_on `dyn` >| [ACCEPT_TAC abi_encoder_members_dynamic_advance,
    ACCEPT_TAC abi_encoder_members_static_advance]
QED
