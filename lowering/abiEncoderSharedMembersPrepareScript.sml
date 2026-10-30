(* Open-source transport at the generator's supplied source-ADD endpoint. *)
Theory abiEncoderSharedMembersPrepare
Ancestors
  abiEncoderSharedMembersIndex abiEncoderSharedMembersInput abiEncoderSharedContract
  abiEncoderMemberPhaseExec abiEncoderMemberPhaseRaw abiEncoderMemberSourcePhase
  abiEncoderMemberPhaseEffect abiEncoderExtendSim abiEncoderMembersDefs abiEncoderMemberSpine
  abiEncoderRegisteredEffect abiScratchEffect
  abiEncoderAddressReach abiEncoderTuple abiScratchAddress abiScratchEncoderContract
  abiDecoderReentry abiDecoderAllocation abiDecoderDynamicLoopSetup emitHelperProps compileEnv valueEncoding
  venomState venomInst emitHelper words list arithmetic

Theorem abi_encoder_shared_members_prepare_raw_transport:
  emit_op ADD [src;Lit (n2w so)] st = (elem_src,prepared) /\
  abi_encoder_shared_members_inv ((ei,az,mz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dp site slot first last lo st limit_st
    src dst sb so ho d hl sz b cap initial /\
  prepared.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_member_phase_raw st prepared initial ready ==>
  abi_encoder_shared_members_inv ((ei,az,mz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dp site slot first last lo prepared limit_st
    src dst sb so ho d hl sz b cap ready /\
  abi_encoder_shared_input (ei,ty,av) (prepared,elem_src,dst) (sb+so,mz) (d,sz)
    (first,last,b,cap) ready /\
  abi_decoder_address_frame st.cs_next_var initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_shared_members_inv_layout >> strip_tac >>
  `LENGTH (enc ty av) <= sz` by (Cases_on `dyn` >> fs[] >> decide_tac) >>
  qpat_assum `abi_encoder_shared_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_members_inv_def]) >>
  `eval_operand src initial = SOME (n2w sb)` by fs[abi_encoder_shared_members_pre_def] >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> drule abi_decoder_operand_live_emit >> strip_tac >>
  `st.cs_next_var <= prepared.cs_next_var /\ st.cs_next_id <= prepared.cs_next_id` by decide_tac >>
  `eval_operand (Lit (n2w so)) initial = SOME (n2w so)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_transport)) >> strip_tac >>
  `eval_operand elem_src ready = SOME (n2w (sb+so))` by fs[word_add_n2w] >>
  `abi_encoder_shared_members_pre ((ei,az,mz,dyn)::infos) (ty::tys) (av::avs)
    prepared src dst sb so d sz first last b cap ready` by
    (irule abi_encoder_shared_members_pre_address >>
     qexistsl_tac [`initial`,`st`] >> asm_rewrite_tac []) >>
  drule_all abi_encoder_cursor_address >> strip_tac >>
  `abi_encoder_shared_input (ei,ty,av) (prepared,elem_src,dst) (sb+so,mz) (d,sz)
    (first,last,b,cap) ready` by
    (drule_all abi_encoder_shared_members_child_buffer >> simp[]) >>
  drule_all abi_scratch_address >>
  disch_then (qspecl_then [`abi_decoder_ids first last`, `[]`] strip_assume_tac) >>
  `abi_encoder_tuple_prefix hl pre pvs d ready.vs_memory` by
    (gvs[abi_decoder_address_frame_def, Excl "enc_def"]) >>
  qpat_assum `hl = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qpat_assum `ho = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  asm_simp_tac bool_ss [abi_encoder_shared_members_inv_def] >> decide_tac
QED

Theorem abi_encoder_shared_members_prepare_extend:
  emit_op ADD [src;Lit (n2w so)] st = (elem_src,p) /\ fn_has_code st p func /\
  abi_encoder_member_phase_raw st p s r /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_extend_sim ctx func s r
Proof
  strip_tac >> drule abi_encoder_emit_address_shape >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st p)` by
    (drule emitted_insts_emit_op >> strip_tac >> gvs[mk_inst_def, is_terminator_def]) >>
  drule_all abi_encoder_member_phase_extend_sim >> simp[]
QED

Theorem abi_encoder_shared_members_index_prepare:
  abi_encoder_shared_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,dyn)::infos) (st,so,ho) (ty::tys,av::avs,pre,pvs) s /\
  abi_encoder_spine_cons_layout func limit_st last (dst,src,dp)
    (ei,az,mz,dyn,infos) (st,so,ho) (out,en) (elem_src,p,len,ce) /\
  hi <= last /\ abi_encoder_member_phase_raw st p s r ==>
  abi_encoder_shared_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    target ((ei,az,mz,dyn)::infos) (p,so,ho) (ty::tys,av::avs,pre,pvs) r /\
  abi_encoder_shared_input (ei,ty,av) (p,elem_src,dst) (sb+so,mz) (d,sz) (first,last,b,cap) r
Proof
  PairCases_on `target` >>
  simp_tac bool_ss [abi_encoder_shared_members_index_def, abi_encoder_spine_cons_layout_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_shared_members_prepare_raw_transport >> strip_tac >>
  `abi_decoder_budget first last b cap s /\ first <= lo /\ fresh_vars_wrt limit_st s /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\ eval_operand src s = SOME (n2w sb)` by
    fs[abi_encoder_shared_members_inv_def, abi_encoder_shared_members_pre_def] >>
  `fresh_vars_wrt limit_st r` by fs[abi_encoder_shared_members_inv_def] >>
  `eval_operand (Lit (n2w so)) s = SOME (n2w so)` by simp[eval_operand_def] >>
  drule_all abi_encoder_shared_members_prepare_extend >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_registered)) >>
  disch_then (qspecl_then [`[(d,sz)]`,`abi_decoder_ids lo hi`] strip_assume_tac) >>
  `origin.cs_next_var <= p.cs_next_var` by decide_tac >>
  `abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap s r` by
    (drule_all abi_scratch_address_effect >> simp[]) >>
  `abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap s r` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`,`hi`,`lo:num`,`st.cs_next_var`,`sz:num`] >> simp[]) >>
  `abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial r` by
    (irule abi_scratch_effect_trans >> asm_rewrite_tac [] >> qexists_tac `s` >> asm_rewrite_tac []) >>
  `abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial r` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `s` >> asm_rewrite_tac []) >>
  `abi_encoder_extend_sim ctx func initial r` by
    (irule abi_encoder_extend_sim_trans >> qexists_tac `s` >> asm_rewrite_tac []) >>
  `alloca_inv initial ==> alloca_inv r` by metis_tac[] >>
  asm_rewrite_tac [] >> decide_tac
QED
