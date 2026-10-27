(* Universal transport at the shared generator's physical source-ADD endpoint. *)
Theory abiScratchMembersEntry
Ancestors
  abiScratchMembersIndex abiEncoderMemberPhaseExec abiEncoderMemberPhaseRaw
  abiEncoderMemberSpine abiScratchMembers abiScratchAddress abiScratchEffect
  abiEncoderMembersDefs abiEncoderInput abiDecoderLoop abiDecoderDynamicLoopSetup
  compileEnv venomState list arithmetic

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

val _ =
  if List.exists (fn name => List.exists (fn parent => parent = name) (Theory.ancestry "-"))
    ["abiScratchMembersCorrect", "abiScratchComplex", "abiScratchEncoderRecursive"]
  then raise Fail "scratch member entry imports a recursive execution owner" else ();

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "scratch member entry has an admission, axiom or hypothesis"
  end) [abi_scratch_members_index_prepare];
