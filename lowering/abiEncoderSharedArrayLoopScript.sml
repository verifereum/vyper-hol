(* Generated loop layout specialized to the fixed-owner shared ledger. *)
Theory abiEncoderSharedArrayLoop
Ancestors
  abiEncoderSharedArrayOwner abiEncoderSharedArrayRound abiEncoderSharedArrayHeader
  abiEncoderSharedArrayIndex abiEncoderArrayCursor abiEncoderArrayLoopCode abiEncoderArrayLoopHeader
  abiEncoderArrayBodyCode abiEncoderArrayBodyMemory abiEncoderArrayDynamicCode abiEncoderSharedContract
  abiEncoderMembersDefs abiEncoderExtendSim abiEncoderExtendControl abiDecoderLoop abiDecoderContract compileEnv venomState
  valueEncoding words list arithmetic

Theorem abi_encoder_shared_array_loop_header:
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\
  body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) (FST labels) j origin initial ==>
  ?ready. abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz)
    (if j < LENGTH avs then FST (SND labels) else SND (SND labels)) j origin ready /\
    abi_encoder_extend_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >>
  qpat_x_assum `?bb. lookup_block body_st.cs_current_bb _ = _ /\ _`
    (qx_choose_then `body_bb` strip_assume_tac) >>
  qpat_x_assum `?bb. lookup_block exit_st.cs_current_bb _ = _ /\ _`
    (qx_choose_then `exit_bb` strip_assume_tac) >>
  qpat_assum `body_st.cs_current_bb = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  qpat_assum `exit_st.cs_current_bb = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `owner_st.cs_next_id <= last /\ owner_st.cs_next_var+3 <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_encoder_shared_array_header_index >>
  disch_then (qx_choose_then `ready` strip_assume_tac) >>
  qexists_tac `ready` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_shared_array_loop_round_finish:
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) label j origin initial /\
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) encoded /\
  abi_encoder_array_prefix ty avs (SUC j) d encoded.vs_memory /\
  abi_encoder_cursor T ip site slot first site owner_st j encoded /\
  abi_encoder_cursor active dp cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) encoded /\
  abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap initial encoded /\
  abi_encoder_registered_effect (abi_decoder_ids site hi) [(d,sz)] initial encoded /\
  (alloca_inv initial ==> alloca_inv encoded) /\ abi_encoder_extend_sim ctx func initial encoded /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  encoded.vs_current_bb = body_end.cs_current_bb /\
  encoded.vs_inst_idx = LENGTH body_end.cs_current_insts /\ ~encoded.vs_halted /\
  out = Var (STRING #"%" (toString body_st.cs_next_var)) /\
  eval_operand out encoded = SOME (n2w j) /\ j < LENGTH avs /\
  owner_st.cs_next_var <= body_end.cs_next_var /\ body_end.cs_next_var < limit_st.cs_next_var /\
  owner_st.cs_next_id <= last /\ site < hi /\ hi <= last /\
  (active ==> site < cursor_site /\ cursor_site < last) ==>
  ?actual. abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) (FST labels) (SUC j) origin actual /\
    abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_array_loop_header_phi >>
  disch_then (qx_choose_then `hdr_bb` strip_assume_tac) >>
  qpat_x_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
    (assume_tac o List.last o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >>
  qmatch_asmsub_abbrev_tac `lookup_block body_end.cs_current_bb _ = SOME backedge_bb` >>
  `backedge_bb.bb_instructions = body_end.cs_current_insts ++
    abi_decode_backedge_insts body_end.cs_next_id (STRING #"%" (toString body_st.cs_next_var))
      (STRING #"%" (toString body_end.cs_next_var)) ip (FST labels)` by
    simp[Abbr `backedge_bb`] >>
  qpat_assum `out = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  qpat_assum `encoded.vs_current_bb = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th])) >>
  drule_all abi_encoder_shared_array_round_finish >>
  disch_then irule
QED

Theorem abi_encoder_shared_array_loop_static_step:
  abi_encoder_shared ei /\ abi_encoder_static_leaf ei /\
  abi_encode_array_static_body ip src dst ei asz msz body_st = (out,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\
  body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,F,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) (FST labels) j origin initial /\
  j < LENGTH avs ==>
  ?actual. abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,F,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) (FST labels) (SUC j) origin actual /\
    abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_shared_array_loop_header >>
  disch_then (qx_choose_then `ready` strip_assume_tac) >>
  fs[COND_CLAUSES] >>
  qpat_x_assum `abi_encoder_shared_array_index _ _ _ _ _ _ _ _ _ initial` kall_tac >>
  `fresh_vars_wrt limit_st ready /\ abi_decoder_budget first last b cap ready` by
    metis_tac[abi_encoder_shared_array_index_facts] >>
  `fn_has_code body_st body_end func /\
   body_st.cs_next_var = owner_st.cs_next_var+3 /\
   body_st.cs_next_id = owner_st.cs_next_id+5 /\
   body_st.cs_current_bb = FST (SND labels) /\ body_st.cs_current_insts = [] /\
   body_st.cs_next_var <= body_end.cs_next_var /\ body_st.cs_next_id <= body_end.cs_next_id` by
    fs[abi_encoder_array_loop_code_def] >>
  `abi_encoder_shared_input (AbiDynArray ei asz msz F,Array NONE ty,ListV avs)
     (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) ready /\
   abi_encoder_array_prefix ty avs j d ready.vs_memory /\
   abi_encoder_cursor T ip site slot first site owner_st j ready /\
   abi_encoder_cursor F dp cursor_site cursor_slot first site owner_st
     (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) ready /\
   ready.vs_current_bb = FST (SND labels) /\ ready.vs_inst_idx = 0 /\ ~ready.vs_halted` by
    fs[abi_encoder_shared_array_index_def] >>
  `site < owner_st.cs_next_id` by fs[abi_encoder_cursor_def] >>
  `owner_st.cs_next_var <= body_st.cs_next_var /\ owner_st.cs_next_id <= body_st.cs_next_id /\
   body_end.cs_next_id <= last /\ body_end.cs_next_var <= limit_st.cs_next_var /\
   ready.vs_current_bb = body_st.cs_current_bb /\
   ready.vs_inst_idx = LENGTH body_st.cs_current_insts` by (gvs[] >> decide_tac) >>
  drule_all abi_encoder_shared_array_static_body_owner >>
  disch_then (qspec_then `ctx` (qx_choose_then `encoded` strip_assume_tac)) >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap ready encoded /\
   abi_encoder_registered_effect (abi_decoder_ids site hi) [(d,sz)] ready encoded` by
    (irule abi_encoder_shared_array_owner_effects >>
     qpat_assum `abi_scratch_effect _ _ _ body_end.cs_next_id _ _ _ _ _ _ _ _`
       (irule_at Any) >> asm_simp_tac bool_ss [] >> decide_tac) >>
  drule abi_encode_array_static_body_index >> disch_tac >>
  `owner_st.cs_next_var <= body_end.cs_next_var /\ body_end.cs_next_var < limit_st.cs_next_var /\
   owner_st.cs_next_id <= last /\ site < hi` by decide_tac >>
  `?actual. abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,F,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) (FST labels) (SUC j) origin actual /\
    abi_encoder_extend_sim ctx func ready actual` by
    (drule_all (SRULE [] (Q.INST [`active` |-> `F`] abi_encoder_shared_array_loop_round_finish)) >>
     simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_encoder_extend_sim_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_shared_array_loop_dynamic_step:
  abi_encoder_shared ei /\
  abi_encode_array_dynamic_body ip dp src dst ei asz msz body_st = (out,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\
  body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,T,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) (FST labels) j origin initial /\
  j < LENGTH avs ==>
  ?actual. abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,T,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) (FST labels) (SUC j) origin actual /\
    abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_shared_array_loop_header >>
  disch_then (qx_choose_then `ready` strip_assume_tac) >>
  fs[COND_CLAUSES] >>
  qpat_x_assum `abi_encoder_shared_array_index _ _ _ _ _ _ _ _ _ initial` kall_tac >>
  `fresh_vars_wrt limit_st ready /\ abi_decoder_budget first last b cap ready` by
    metis_tac[abi_encoder_shared_array_index_facts] >>
  `fn_has_code body_st body_end func /\
   body_st.cs_next_var = owner_st.cs_next_var+3 /\
   body_st.cs_next_id = owner_st.cs_next_id+5 /\
   body_st.cs_current_bb = FST (SND labels) /\ body_st.cs_current_insts = [] /\
   body_st.cs_next_var <= body_end.cs_next_var /\ body_st.cs_next_id <= body_end.cs_next_id` by
    fs[abi_encoder_array_loop_code_def] >>
  `abi_encoder_shared_input (AbiDynArray ei asz msz T,Array NONE ty,ListV avs)
     (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) ready /\
   abi_encoder_array_prefix ty avs j d ready.vs_memory /\
   abi_encoder_cursor T ip site slot first site owner_st j ready /\
   abi_encoder_cursor T dp cursor_site cursor_slot first site owner_st
     (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) ready /\
   ready.vs_current_bb = FST (SND labels) /\ ready.vs_inst_idx = 0 /\ ~ready.vs_halted /\
   site < cursor_site` by
    fs[abi_encoder_shared_array_index_def] >>
  `site < owner_st.cs_next_id /\ cursor_site < owner_st.cs_next_id` by
    fs[abi_encoder_cursor_def] >>
  `owner_st.cs_next_var <= body_st.cs_next_var /\ owner_st.cs_next_id <= body_st.cs_next_id /\
   body_end.cs_next_id <= last /\ body_end.cs_next_var <= limit_st.cs_next_var /\
   ready.vs_current_bb = body_st.cs_current_bb /\
   ready.vs_inst_idx = LENGTH body_st.cs_current_insts` by (gvs[] >> decide_tac) >>
  drule_all abi_encoder_shared_array_dynamic_body_owner >>
  disch_then (qspec_then `ctx` (qx_choose_then `encoded` strip_assume_tac)) >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap ready encoded /\
   abi_encoder_registered_effect (abi_decoder_ids site hi) [(d,sz)] ready encoded` by
    (irule abi_encoder_shared_array_owner_effects >>
     qpat_assum `abi_scratch_effect _ _ _ body_end.cs_next_id _ _ _ _ _ _ _ _`
       (irule_at Any) >> asm_simp_tac bool_ss [] >> decide_tac) >>
  drule abi_encode_array_dynamic_body_index >> disch_tac >>
  `owner_st.cs_next_var <= body_end.cs_next_var /\ body_end.cs_next_var < limit_st.cs_next_var /\
   owner_st.cs_next_id <= last /\ site < hi /\ cursor_site < last` by decide_tac >>
  `?actual. abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,T,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) (FST labels) (SUC j) origin actual /\
    abi_encoder_extend_sim ctx func ready actual` by
    (drule_all (SRULE [] (Q.INST [`active` |-> `T`] abi_encoder_shared_array_loop_round_finish)) >>
     simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_encoder_extend_sim_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_shared_array_loop_finite:
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\
  body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) (FST labels) i origin initial /\
  (!j u. abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) (FST labels) j origin u /\ j < LENGTH avs ==>
    ?v. abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
      (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
      (first,last,hi,b,cap) (sb,source_cap,d,sz) (FST labels) (SUC j) origin v /\
      abi_encoder_extend_sim ctx func u v) ==>
  ?actual. abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) (SND (SND labels)) (LENGTH avs) origin actual /\
    abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `i <= LENGTH avs` by metis_tac[abi_encoder_shared_array_index_facts] >>
  irule abi_encoder_extend_finite_iteration >>
  qexistsl_tac [`LENGTH avs`,`i`] >>
  qexists_tac `\j u. abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) (FST labels) j origin u` >>
  simp_tac bool_ss [] >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  drule_all abi_encoder_shared_array_loop_header >> simp[]
QED

Theorem abi_encoder_shared_array_loop_run:
  abi_encoder_shared ei /\
  ((active = F /\ abi_encoder_static_leaf ei /\
    abi_encode_array_static_body ip src dst ei asz msz body_st = (out,body_end)) \/
   (active = T /\
    abi_encode_array_dynamic_body ip dp src dst ei asz msz body_st = (out,body_end))) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\
  body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) (FST labels) i origin initial ==>
  ?actual. abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) (SND (SND labels)) (LENGTH avs) origin actual /\
    abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!j u. abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) (FST labels) j origin u /\ j < LENGTH avs ==>
    ?v. abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
      (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
      (first,last,hi,b,cap) (sb,source_cap,d,sz) (FST labels) (SUC j) origin v /\
      abi_encoder_extend_sim ctx func u v` by
    (rpt strip_tac >> Cases_on `active` >> gvs[]
     >- (drule_all abi_encoder_shared_array_loop_dynamic_step >> simp[]) >>
     drule_all abi_encoder_shared_array_loop_static_step >> simp[]) >>
  drule_all abi_encoder_shared_array_loop_finite >> simp[]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared array loop admission, axiom or hypothesis"
  end) [abi_encoder_shared_array_loop_header, abi_encoder_shared_array_loop_round_finish,
    abi_encoder_shared_array_loop_static_step, abi_encoder_shared_array_loop_dynamic_step,
    abi_encoder_shared_array_loop_finite, abi_encoder_shared_array_loop_run];
