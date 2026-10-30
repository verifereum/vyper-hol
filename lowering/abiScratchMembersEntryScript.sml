Theory abiScratchMembersEntry
Ancestors
  abiScratchMembers abiScratchMemberStep abiScratchCursor abiScratchEncoderContract
  abiScratchEffect abiEncoderMembersDefs abiEncoderMembersStep abiEncoderMemberCode
  abiEncoderTuple abiCanonicalWindows abiDecoderDynamicLoopSetup abiDecoderFootprint
  abiDecoderReentry abiDecoderContract abiDecoderLoop compileEnv valueEncoding contractABI
  venomState words list arithmetic abiScratchMemberInterpret abiScratchPrefix abiScratchStatic
  valueEncodingProps abiScratchMembersIndex abiEncoderMemberPhaseExec abiEncoderMemberPhaseRaw
  abiEncoderMemberSpine abiScratchAddress abiEncoderInput

(* Complete one actual member and restore the recursive suffix invariant.
   TOP-LEVEL: static/dynamic advance use the child's precise effect to protect
   the remaining source, processed prefix and registered parent cursor. *)
Theorem abi_scratch_cursor_mono:
  abi_encoder_cursor active dyn_ptr site slot first lo st off s /\
  st.cs_next_var <= end_st.cs_next_var /\ st.cs_next_id <= end_st.cs_next_id ==>
  abi_encoder_cursor active dyn_ptr site slot first lo end_st off s
Proof
  Cases_on `active` >> simp_tac bool_ss [abi_encoder_cursor_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_operand_live end_st.cs_next_var dyn_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_scratch_members_static_advance:
  abi_scratch_encoder ei /\ compile_abi_encode_child dst elem_src ei F ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_members_inv ((ei,abi_sz,mem_sz,F)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_scratch_input ei ty av st elem_src dst (sb+so) mem_sz d output_size first last b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. abi_scratch_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot
      first last lo end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual /\
    abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  mp_tac (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `F`] abi_scratch_members_inv_layout)) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_encoder_child_bounds >> strip_tac >>
  mp_tac (Q.INST [`heads` |-> `ho:num`, `tails` |-> `SUM (MAP2 abi_member_tail_size pre pvs)`,
    `src` |-> `elem_src`, `sb` |-> `sb+so`, `source_cap` |-> `mem_sz:num`] abi_scratch_static_member_step) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `abi_encoder_cursor active dyn_ptr site slot first lo st
    (hl+LENGTH (FLAT (abi_tuple_tails pre pvs))) actual` by
    (reverse (Cases_on `active`) >- simp[abi_encoder_cursor_def] >>
     mp_tac (Q.INST [`active` |-> `T`, `cursor_op` |-> `dyn_ptr:operand`, `owned_lo` |-> `st.cs_next_id`,
       `owned_hi` |-> `end_st.cs_next_id`, `next` |-> `st.cs_next_var`,
       `off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`, `sz` |-> `output_size:num`]
       abi_scratch_cursor_protected) >>
     impl_tac >- (fs[abi_encoder_cursor_def, abi_scratch_input_def] >> decide_tac) >> simp[]) >>
  drule_all (Q.INST [`s` |-> `actual:venom_state`, `end_st` |-> `end_st:compile_state`]
    abi_scratch_cursor_mono) >> disch_tac >>
  mp_tac abi_encoder_members_prefix_advance >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_encoder_cursor active dyn_ptr site slot first lo end_st
    (hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))) actual` by
    (qpat_assum `~is_dynamic ty` (fn dyn_th =>
       qpat_assum `LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av]))) = _`
         (fn th => PURE_REWRITE_TAC [SIMP_RULE bool_ss [dyn_th, ADD_CLAUSES] th])) >>
     first_assum ACCEPT_TAC) >>
  `abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  mp_tac (Q.INST [`dyn` |-> `F`] abi_scratch_members_after_child) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_members_dynamic_advance:
  abi_scratch_encoder ei /\ compile_abi_encode_child dst elem_src ei T ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_scratch_members_inv ((ei,abi_sz,mem_sz,T)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_scratch_input ei ty av st elem_src dst (sb+so) mem_sz d output_size first last b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. abi_scratch_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot
      first last lo end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual /\
    abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  reverse (Cases_on `active`) >- simp[abi_scratch_members_inv_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  mp_tac (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `T`, `active` |-> `T`]
    abi_scratch_members_inv_layout)) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_encoder_child_bounds >> strip_tac >>
  qpat_assum `abi_encoder_cursor _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  mp_tac (Q.INST [`heads` |-> `ho:num`, `tails` |-> `SUM (MAP2 abi_member_tail_size pre pvs)`,
    `off` |-> `hl+SUM (MAP2 abi_member_tail_size pre pvs)`, `src` |-> `elem_src`,
    `sb` |-> `sb+so`, `source_cap` |-> `mem_sz:num`] abi_scratch_dynamic_member_step) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  mp_tac abi_encoder_members_prefix_advance >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`active` |-> `T`, `cursor_op` |-> `dyn_ptr:operand`,
    `off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`,
    `next_off` |-> `hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))`,
    `sz` |-> `output_size:num`, `owned_lo` |-> `lo:num`, `owned_hi` |-> `end_st.cs_next_id`,
    `next` |-> `st.cs_next_var`] abi_scratch_cursor_registered) >>
  impl_tac >- asm_simp_tac bool_ss [ADD_ASSOC, LESS_EQ_REFL] >> disch_tac >>
  drule_all (Q.INST [`s` |-> `actual:venom_state`, `end_st` |-> `end_st:compile_state`]
    abi_scratch_cursor_mono) >> disch_tac >>
  mp_tac (Q.INST [`dyn` |-> `T`, `active` |-> `T`] abi_scratch_members_after_child) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_members_child_advance:
  abi_scratch_encoder ei /\ compile_abi_encode_child dst elem_src ei dyn ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_scratch_input ei ty av st elem_src dst (sb+so) mem_sz d output_size first last b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. abi_scratch_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot
      first last lo end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual /\
    abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  Cases_on `dyn`
  >- (disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      drule_all abi_scratch_members_dynamic_advance >> disch_then (qspec_then `ctx` ACCEPT_TAC)) >>
  ACCEPT_TAC abi_scratch_members_static_advance
QED

(* Pure invariant transport at the common generator's supplied child endpoint. *)
Theorem abi_scratch_members_static_endpoint:
  compile_abi_encode_child dst elem_src ei F ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_members_inv ((ei,abi_sz,mem_sz,F)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_scratch_input ei ty av st elem_src dst (sb+so) mem_sz d output_size first last b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_spine_child_output
    (abi_scratch_member_core_post (ctx,func) (ty,av,sb+so,mem_sz,d+ho)
      (first,last,b,cap,limit_st))
    (ei,F,dst,elem_src,ho,dyn_ptr,st,end_st,out) initial actual ==>
  abi_scratch_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot
    first last lo end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual /\
  abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  drule (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `F`] abi_scratch_members_inv_layout)) >> strip_tac >>
  drule abi_encoder_child_bounds >> strip_tac >>
  `ho+LENGTH (enc ty av) <= output_size /\ first <= st.cs_next_id` by decide_tac >>
  drule_all abi_scratch_member_static_output >> strip_tac >>
  drule_all abi_scratch_input_owned_output >> disch_tac >>
  mp_tac (Q.INST [`fp` |-> `abi_decoder_child_scratch
    (abi_decoder_ids st.cs_next_id end_st.cs_next_id) b cap initial`,
    `heads` |-> `ho:num`, `tails` |-> `LENGTH (FLAT (abi_tuple_tails pre pvs))`]
    abi_scratch_tuple_static_step) >>
  impl_tac >- gvs[Excl "enc_def"] >> disch_tac >>
  `abi_encoder_cursor active dyn_ptr site slot first lo st
    (hl+LENGTH (FLAT (abi_tuple_tails pre pvs))) actual` by
    (reverse (Cases_on `active`) >- simp[abi_encoder_cursor_def] >>
     mp_tac (Q.INST [`active` |-> `T`, `cursor_op` |-> `dyn_ptr:operand`, `owned_lo` |-> `st.cs_next_id`,
       `owned_hi` |-> `end_st.cs_next_id`, `next` |-> `st.cs_next_var`,
       `off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`, `sz` |-> `output_size:num`]
       abi_scratch_cursor_protected) >>
     impl_tac >- (fs[abi_encoder_cursor_def, abi_scratch_input_def] >> decide_tac) >> simp[]) >>
  drule_all (Q.INST [`s` |-> `actual:venom_state`, `end_st` |-> `end_st:compile_state`]
    abi_scratch_cursor_mono) >> disch_tac >>
  mp_tac abi_encoder_members_prefix_advance >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_encoder_cursor active dyn_ptr site slot first lo end_st
    (hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))) actual` by
    (qpat_assum `~is_dynamic ty` (fn dyn_th =>
       qpat_assum `LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av]))) = _`
         (fn th => PURE_REWRITE_TAC [SIMP_RULE bool_ss [dyn_th, ADD_CLAUSES] th])) >>
     first_assum ACCEPT_TAC) >>
  `abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  drule_all (Q.INST [`dyn` |-> `F`] abi_scratch_members_after_child) >> strip_tac >>
  asm_rewrite_tac []
QED

Theorem abi_scratch_members_dynamic_endpoint:
  compile_abi_encode_child dst elem_src ei T ho dyn_ptr st = (out,end_st) /\
  abi_encode_child_prefix dst ho dyn_ptr st = (ops,prepared) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_members_inv ((ei,abi_sz,mem_sz,T)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_scratch_input ei ty av st elem_src dst (sb+so) mem_sz d output_size first last b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  off = hl+LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  abi_encoder_spine_child_output
    (abi_scratch_member_dynamic_post (ctx,func) (ty,av,sb+so,mem_sz,d+off)
      (first,last,b,cap,limit_st) (FST ops,FST (SND ops),dyn_ptr,d+ho,off,slot,site))
    (ei,T,dst,elem_src,ho,dyn_ptr,st,end_st,out) initial actual ==>
  abi_scratch_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot
    first last lo end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual /\
  abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  reverse (Cases_on `active`) >- simp[abi_scratch_members_inv_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  drule (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `T`, `active` |-> `T`]
    abi_scratch_members_inv_layout)) >> strip_tac >>
  drule abi_encoder_child_bounds >> strip_tac >>
  qpat_assum `abi_encoder_cursor _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  `ho+32 <= off /\ off+LENGTH (enc ty av) <= output_size /\
    mload slot initial = n2w off` by fs[] >>
  drule_all abi_scratch_member_dynamic_output_detailed >> strip_tac >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids lo end_st.cs_next_id) b cap initial)` by
    (irule abi_scratch_input_owned_output >>
     goal_assum (drule_at (Pat `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     asm_rewrite_tac []) >>
  `abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d actual.vs_memory` by
    (irule abi_scratch_tuple_dynamic_step >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`abi_decoder_child_scratch (abi_decoder_ids lo end_st.cs_next_id) b cap initial`,
       `initial`, `output_size`] >>
     gvs[Excl "enc_def"]) >>
  mp_tac abi_encoder_members_prefix_advance >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `mem_word_at slot actual.vs_memory = _`
    (assume_tac o PURE_REWRITE_RULE [mem_word_at_eq_mload]) >>
  mp_tac (Q.INST [`active` |-> `T`, `cursor_op` |-> `dyn_ptr:operand`,
    `off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`,
    `next_off` |-> `hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))`,
    `sz` |-> `output_size:num`, `owned_lo` |-> `lo:num`, `owned_hi` |-> `end_st.cs_next_id`,
    `next` |-> `st.cs_next_var`] abi_scratch_cursor_registered) >>
  impl_tac >- asm_simp_tac bool_ss [ADD_ASSOC, LESS_EQ_REFL] >> disch_tac >>
  drule_all (Q.INST [`s` |-> `actual:venom_state`, `end_st` |-> `end_st:compile_state`]
    abi_scratch_cursor_mono) >> disch_tac >>
  drule_all (Q.INST [`dyn` |-> `T`, `active` |-> `T`] abi_scratch_members_after_child) >>
  strip_tac >> asm_rewrite_tac []
QED

(* Universal transport at the shared generator's physical source-ADD endpoint. *)
Theorem abi_scratch_members_index_prepare:
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,dyn)::infos) (st,so,ho) (ty::tys,av::avs,pre,pvs) s /\
  abi_encoder_spine_cons_layout func limit_st last (dst,src,dp)
    (ei,az,mz,dyn,infos) (st,so,ho) (out,en) (elem_src,p,len,ce) /\
  hi <= last /\ abi_encoder_member_phase_raw st p s r ==>
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,dyn)::infos) (p,so,ho) (ty::tys,av::avs,pre,pvs) r /\
  abi_scratch_input ei ty av p elem_src dst (sb+so) mz d sz first last b cap r /\
  abi_decoder_address_frame st.cs_next_var s r /\ abi_decode_sim ctx func s r
Proof
  PairCases_on `target` >>
  simp_tac bool_ss [abi_scratch_members_index_def, abi_encoder_spine_cons_layout_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_members_prepare_raw_transport >> strip_tac >>
  `abi_decoder_budget first last b cap s /\ first <= lo /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts` by
    fs[abi_scratch_members_inv_def] >>
  `fresh_vars_wrt limit_st r` by fs[abi_scratch_members_inv_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_raw_sim)) >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `origin.cs_next_var <= p.cs_next_var` by decide_tac >>
  `abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap s r` by
    (drule_all abi_scratch_address_effect >> simp[]) >>
  `abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap s r` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`,`hi`,`lo:num`,`st.cs_next_var`,`sz:num`] >> simp[]) >>
  `abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial r` by
    (irule abi_scratch_effect_trans >> asm_rewrite_tac [] >> qexists_tac `s` >> asm_rewrite_tac []) >>
  `abi_decode_sim ctx func initial r` by
    (irule abi_decode_sim_trans >> qexists_tac `s` >> asm_rewrite_tac []) >>
  asm_rewrite_tac [] >> decide_tac
QED

Theorem abi_scratch_members_static_request:
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,F)::infos) (p,so,ho) (ty::tys,av::avs,pre,pvs) r /\
  abi_scratch_input ei ty av p elem_src dst (sb+so) mz d sz first last b cap r /\
  compile_abi_encode_child dst elem_src ei F ho dp p = (len,ce) /\
  fn_has_code p ce func /\
  (p.cs_blocks = ce.cs_blocks \/
    !bb. lookup_block ce.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  ce.cs_next_id <= last /\ ce.cs_next_var <= limit_st.cs_next_var ==>
  abi_encoder_spine_child_input func limit_st
    (abi_scratch_member_core_pre (ty,av,sb+so,mz,d+ho) (first,last,b,cap,limit_st))
    (abi_scratch_member_core_post (ctx,func) (ty,av,sb+so,mz,d+ho)
      (first,last,b,cap,limit_st))
    (ei,F,dst,elem_src,ho,dp,p,ce,len) r
Proof
  PairCases_on `target` >>
  simp_tac bool_ss [abi_scratch_members_index_def, EVERY_DEF, pairTheory.UNCURRY_DEF] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `F`] abi_scratch_members_inv_layout)) >> strip_tac >>
  `ho+LENGTH (enc ty av) <= sz` by decide_tac >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  `first <= p.cs_next_id` by decide_tac >>
  drule_all abi_scratch_member_static_input >> simp[]
QED

Theorem abi_scratch_members_dynamic_request:
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,T)::infos) (p,so,ho) (ty::tys,av::avs,pre,pvs) r /\
  abi_scratch_input ei ty av p elem_src dst (sb+so) mz d sz first last b cap r /\
  compile_abi_encode_child dst elem_src ei T ho dp p = (len,ce) /\
  abi_encode_child_prefix dst ho dp p = (ops,prepared) /\
  fn_has_code p ce func /\
  (p.cs_blocks = ce.cs_blocks \/
    !bb. lookup_block ce.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  ce.cs_next_id <= last /\ ce.cs_next_var <= limit_st.cs_next_var /\
  off = hl+LENGTH (FLAT (abi_tuple_tails pre pvs)) ==>
  abi_encoder_spine_child_input func limit_st
    (abi_scratch_member_dynamic_pre (ty,av,sb+so,mz,d+off) (first,last,b,cap,limit_st)
      (FST ops,FST (SND ops),dp,d+ho,off,slot,site))
    (abi_scratch_member_dynamic_post (ctx,func) (ty,av,sb+so,mz,d+off)
      (first,last,b,cap,limit_st) (FST ops,FST (SND ops),dp,d+ho,off,slot,site))
    (ei,T,dst,elem_src,ho,dp,p,ce,len) r
Proof
  PairCases_on `target` >>
  simp_tac bool_ss [abi_scratch_members_index_def, EVERY_DEF, pairTheory.UNCURRY_DEF] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `T`] abi_scratch_members_inv_layout)) >> strip_tac >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  `active` by fs[EVERY_DEF, pairTheory.UNCURRY_DEF] >>
  `ho+32 <= off /\ off+LENGTH (enc ty av) <= sz` by decide_tac >>
  `abi_decoder_operand_live p.cs_next_var dp /\
    eval_operand dp r = SOME (n2w slot) /\ mload slot r = n2w off /\
    first <= site /\ site < p.cs_next_id /\ FLOOKUP r.vs_allocas site = SOME (slot,32)` by
    (qpat_assum `active` (fn ath =>
       qpat_assum `abi_encoder_cursor _ _ _ _ _ _ _ _ _`
         (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def,ath])) >>
     asm_rewrite_tac []) >>
  drule_all abi_scratch_member_dynamic_input >> simp[]
QED

Theorem abi_scratch_members_static_exit:
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,F)::infos) (p,so,ho) (ty::tys,av::avs,pre,pvs) r /\
  abi_scratch_input ei ty av p elem_src dst (sb+so) mz d sz first last b cap r /\
  compile_abi_encode_child dst elem_src ei F ho dp p = (len,ce) /\
  fn_has_code p ce func /\
  (p.cs_blocks = ce.cs_blocks \/
    !bb. lookup_block ce.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  ce.cs_next_id <= last /\ ce.cs_next_id <= hi /\ hi <= last /\
  ce.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_spine_child_output
    (abi_scratch_member_core_post (ctx,func) (ty,av,sb+so,mz,d+ho)
      (first,last,b,cap,limit_st))
    (ei,F,dst,elem_src,ho,dp,p,ce,len) r u ==>
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target infos (ce,so+mz,ho+az) (tys,avs,pre++[ty],pvs++[av]) u
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_scratch_members_inv ((ei,az,mz,F)::infos) (ty::tys) (av::avs) pre pvs
    active dp site slot first last lo p limit_st src dst sb so ho d hl sz b cap r /\
    fresh_vars_wrt limit_st r` by
    (PairCases_on `target` >> fs[abi_scratch_members_index_def, abi_scratch_members_inv_def]) >>
  drule_all abi_scratch_members_static_endpoint >> strip_tac >>
  `p.cs_next_var <= ce.cs_next_var` by
    (drule abi_encoder_child_bounds >> simp[]) >>
  `abi_decoder_address_frame p.cs_next_var r r` by simp[abi_decoder_address_frame_def] >>
  `abi_decode_sim ctx func r r` by simp[abi_decode_sim_refl] >>
  irule abi_scratch_members_index_advance >>
  asm_rewrite_tac [] >> qexistsl_tac [`F`, `ei`, `p`, `r`, `r`, `p`] >>
  asm_rewrite_tac [] >> decide_tac
QED

Theorem abi_scratch_members_dynamic_exit:
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,T)::infos) (p,so,ho) (ty::tys,av::avs,pre,pvs) r /\
  abi_scratch_input ei ty av p elem_src dst (sb+so) mz d sz first last b cap r /\
  compile_abi_encode_child dst elem_src ei T ho dp p = (len,ce) /\
  abi_encode_child_prefix dst ho dp p = (ops,prepared) /\
  fn_has_code p ce func /\
  (p.cs_blocks = ce.cs_blocks \/
    !bb. lookup_block ce.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  ce.cs_next_id <= last /\ ce.cs_next_id <= hi /\ hi <= last /\
  ce.cs_next_var <= limit_st.cs_next_var /\
  off = hl+LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  abi_encoder_spine_child_output
    (abi_scratch_member_dynamic_post (ctx,func) (ty,av,sb+so,mz,d+off)
      (first,last,b,cap,limit_st) (FST ops,FST (SND ops),dp,d+ho,off,slot,site))
    (ei,T,dst,elem_src,ho,dp,p,ce,len) r u ==>
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target infos (ce,so+mz,ho+az) (tys,avs,pre++[ty],pvs++[av]) u
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_scratch_members_inv ((ei,az,mz,T)::infos) (ty::tys) (av::avs) pre pvs
    active dp site slot first last lo p limit_st src dst sb so ho d hl sz b cap r /\
    fresh_vars_wrt limit_st r` by
    (PairCases_on `target` >> fs[abi_scratch_members_index_def, abi_scratch_members_inv_def]) >>
  drule_all abi_scratch_members_dynamic_endpoint >> strip_tac >>
  `p.cs_next_var <= ce.cs_next_var` by
    (drule abi_encoder_child_bounds >> simp[]) >>
  `abi_decoder_address_frame p.cs_next_var r r` by simp[abi_decoder_address_frame_def] >>
  `abi_decode_sim ctx func r r` by simp[abi_decode_sim_refl] >>
  irule abi_scratch_members_index_advance >>
  asm_rewrite_tac [] >> qexistsl_tac [`T`, `ei`, `p`, `r`, `r`, `p`] >>
  asm_rewrite_tac [] >> decide_tac
QED
