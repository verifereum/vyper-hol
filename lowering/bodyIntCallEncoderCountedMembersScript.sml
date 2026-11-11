(* Physical member generation under a counted recursive child contract. *)
Theory bodyIntCallEncoderCountedMembers
Ancestors
  bodyIntCallEncoderCountedSpine abiScratchMembersInterpret abiScratchMembersIndex
  abiScratchMembersEntry abiScratchMemberContract abiEncoderMemberSpine
  abiScratchMembers abiScratchEffect abiDecoderLoop compileEnv venomState list
  abiEncoderMembersContract abiScratchEncoderContract abiEncoderMembersDefs
  fragGasPath venomExecSemantics

Theorem intcall_scratch_members_generate:
  (!y c r. abi_encoder_spine_core_code func c /\
    abi_scratch_members_child_pre (first,last,b,cap,limit_st) y c r ==>
    ?u. intcall_encoder_core_path ctx func c r u /\
      abi_scratch_members_child_post (ctx,func) (first,last,b,cap,limit_st) y c r u) /\
  hi <= last /\
  abi_encoder_spine_code func limit_st hi (dst,src,dp) infos (st,so,ho) (out,en) /\
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    (all_tys,all_avs,end_so,end_ho) infos (st,so,ho) x s ==>
  ?t. abi_encoder_member_spine (intcall_encoder_core_path ctx func)
      (dst,src,dp) infos (st,so,ho) (out,en) s t /\
    abi_scratch_members_inv [] [] [] all_tys all_avs active dp site slot first last lo
      en limit_st src dst sb end_so end_ho d hl sz b cap t /\
    abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial t /\
    abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  irule (SRULE [] (Q.INST [
    `child_pre` |-> `abi_scratch_members_child_pre (first,last,b,cap,limit_st)`,
    `child_post` |-> `abi_scratch_members_child_post (ctx,func) (first,last,b,cap,limit_st)`,
    `Post` |-> `\(out,en) t.
      abi_scratch_members_inv [] [] [] all_tys all_avs active dp site slot first last lo
        en limit_st src dst sb end_so end_ho d hl sz b cap t /\
      abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial t /\
      abi_decode_sim ctx func initial t`]
    (Q.ISPECL [
      `abi_scratch_members_index (ctx,func) (origin,initial)
        (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
        (all_tys,all_avs,end_so,end_ho)`,
      `\i (st:compile_state,so,ho) x (s:venom_state).
        abi_scratch_members_entry (ctx,func) (origin,initial)
          (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
          (all_tys,all_avs,end_so,end_ho) i (st,so,ho) x s`]
      (Q.GENL [`Inv`,`Entry`]
        (Q.INST [`last` |-> `hi`] abi_encoder_member_spine_generate))))) >>
  rpt conj_tac
  >- (rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      drule_all abi_scratch_members_entry_prepare >> simp[])
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC abi_scratch_members_entry_exit)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC abi_scratch_members_entry_input)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC abi_scratch_members_index_source)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC abi_scratch_members_empty_post) >>
  asm_rewrite_tac [] >> goal_assum (drule_at Any)
QED

(* The physical post and counted reachability use the generated endpoint. *)
Theorem intcall_scratch_members_counted:
  (!y c r. abi_encoder_spine_core_code func c /\
    abi_scratch_members_child_pre (first,last,b,cap,limit_st) y c r ==>
    ?u. intcall_encoder_core_path ctx func c r u /\
      abi_scratch_members_child_post (ctx,func) (first,last,b,cap,limit_st) y c r u) /\
  hi <= last /\
  abi_encoder_spine_code func limit_st hi (dst,src,dp) infos (st,so,ho) (out,en) /\
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    (all_tys,all_avs,end_so,end_ho) infos (st,so,ho) x s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t n. gas_path ctx func s n (OK t) /\
    abi_scratch_members_inv [] [] [] all_tys all_avs active dp site slot first last lo
      en limit_st src dst sb end_so end_ho d hl sz b cap t /\
    abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial t /\
    abi_decode_sim ctx func initial t
Proof
  strip_tac >> drule_all intcall_scratch_members_generate >> strip_tac >>
  drule_all intcall_encoder_counted_member_spine >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Preparing a child preserves its encoder tag, in both ABI branches. *)
Theorem intcall_encoder_child_input_restrict:
  P ei /\ abi_encoder_spine_child_input func limit_st pre post
    (ei,dyn,dst,src,ho,dp,st,en,out) s ==>
  abi_encoder_spine_child_input func limit_st
    (\c r. P (FST c) /\ pre c r) post (ei,dyn,dst,src,ho,dp,st,en,out) s
Proof
  Cases_on `dyn` >>
  simp_tac bool_ss [abi_encoder_spine_child_input_def] >>
  rpt strip_tac
  >- (qexistsl_tac [`ops`,`p`,`len`,`ce`,`d`,`slot`,`off`] >>
      asm_rewrite_tac [] >> simp[]) >>
  qexistsl_tac [`head`,`p`,`d`] >> asm_rewrite_tac [] >> simp[]
QED

(* A predicate ledger restricts recursion to the immediate encoder children. *)
Theorem intcall_scratch_members_restricted_generate:
  (!y ei cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_members_child_pre (first,last,b,cap,limit_st) y (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_members_child_post (ctx,func) (first,last,b,cap,limit_st)
        y (ei,cd,cs,cst,cen,co) r u) /\
  EVERY (\(ei,az,mz,dyn). P ei) infos /\ hi <= last /\
  abi_encoder_spine_code func limit_st hi (dst,src,dp) infos (st,so,ho) (out,en) /\
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    (all_tys,all_avs,end_so,end_ho) infos (st,so,ho) x s ==>
  ?t. abi_encoder_member_spine (intcall_encoder_core_path ctx func)
      (dst,src,dp) infos (st,so,ho) (out,en) s t /\
    abi_scratch_members_inv [] [] [] all_tys all_avs active dp site slot first last lo
      en limit_st src dst sb end_so end_ho d hl sz b cap t /\
    abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial t /\
    abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  irule (SRULE [] (Q.INST [
    `child_pre` |-> `\y c r. P (FST c) /\
      abi_scratch_members_child_pre (first,last,b,cap,limit_st) y c r`,
    `child_post` |-> `abi_scratch_members_child_post (ctx,func) (first,last,b,cap,limit_st)`,
    `Post` |-> `\(out,en) t.
      abi_scratch_members_inv [] [] [] all_tys all_avs active dp site slot first last lo
        en limit_st src dst sb end_so end_ho d hl sz b cap t /\
      abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial t /\
      abi_decode_sim ctx func initial t`]
    (Q.ISPECL [
      `\infos (st:compile_state,so,ho) x (s:venom_state).
        EVERY (\(ei,az,mz,dyn). P ei) infos /\
        abi_scratch_members_index (ctx,func) (origin,initial)
          (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
          (all_tys,all_avs,end_so,end_ho) infos (st,so,ho) x s`,
      `\(ei,az,mz,dyn,rest) (st:compile_state,so,ho) x (s:venom_state) child r y. P ei /\
        EVERY (\(ej,a,m,dyn). P ej) rest /\
        abi_scratch_members_entry (ctx,func) (origin,initial)
          (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
          (all_tys,all_avs,end_so,end_ho) (ei,az,mz,dyn,rest) (st,so,ho) x s child r y`]
      (Q.GENL [`Inv`,`Entry`]
        (Q.INST [`last` |-> `hi`] abi_encoder_member_spine_generate))))) >>
  conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC abi_scratch_members_empty_post) >>
  reverse conj_tac >- (asm_rewrite_tac [] >> goal_assum (drule_at Any)) >>
  qexists_tac `P` >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all abi_scratch_members_entry_prepare >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      drule_all abi_scratch_members_entry_exit >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      irule intcall_encoder_child_input_restrict >> simp[] >>
      drule_all abi_scratch_members_entry_input >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      drule_all abi_scratch_members_index_source >> simp[])
  >- (rpt gen_tac >> PairCases_on `c` >> simp[] >> metis_tac[]) >>
  asm_rewrite_tac [] >> goal_assum (drule_at Any)
QED

Theorem intcall_scratch_members_restricted_counted:
  (!y ei cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_members_child_pre (first,last,b,cap,limit_st) y (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_members_child_post (ctx,func) (first,last,b,cap,limit_st)
        y (ei,cd,cs,cst,cen,co) r u) /\
  EVERY (\(ei,az,mz,dyn). P ei) infos /\ hi <= last /\
  abi_encoder_spine_code func limit_st hi (dst,src,dp) infos (st,so,ho) (out,en) /\
  abi_scratch_members_index (ctx,func) (origin,initial)
    (first,last,lo,hi,b,cap,limit_st) (active,dp,site,slot,src,dst,sb,d,hl,sz)
    (all_tys,all_avs,end_so,end_ho) infos (st,so,ho) x s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t n. gas_path ctx func s n (OK t) /\
    abi_scratch_members_inv [] [] [] all_tys all_avs active dp site slot first last lo
      en limit_st src dst sb end_so end_ho d hl sz b cap t /\
    abi_scratch_effect first last lo hi origin.cs_next_var limit_st d sz b cap initial t /\
    abi_decode_sim ctx func initial t
Proof
  strip_tac >> drule_all intcall_scratch_members_restricted_generate >> strip_tac >>
  drule_all intcall_encoder_counted_member_spine >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Dispatching static/dynamic child requests retains the child's counted state. *)
Theorem intcall_scratch_members_counted_callback:
  (!value ei cd cs st en out r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,st,en,out) /\
    abi_scratch_member_core_pre value resources (ei,cd,cs,st,en,out) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,st,en,out) r u /\
      abi_scratch_member_core_post (ctx,func) value resources (ei,cd,cs,st,en,out) r u) ==>
  !y ei cd cs st en out r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,st,en,out) /\
    abi_scratch_members_child_pre resources y (ei,cd,cs,st,en,out) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,st,en,out) r u /\
      abi_scratch_members_child_post (ctx,func) resources y (ei,cd,cs,st,en,out) r u
Proof
  strip_tac >> rpt gen_tac >> PairCases_on `y` >> Cases_on `y0` >>
  simp_tac bool_ss [abi_scratch_members_child_pre_def,
    abi_scratch_members_child_post_def, abi_scratch_member_dynamic_pre_def,
    abi_scratch_member_dynamic_post_def] >>
  strip_tac >> first_x_assum (drule_all_then strip_assume_tac) >>
  goal_assum (drule_at Any) >> asm_rewrite_tac [abi_scratch_member_dynamic_pre_def]
QED

(* Initialize the ledger at any physical member invariant, including [] . *)
Theorem intcall_scratch_members_run:
  (!y ei cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_members_child_pre (first,last,b,cap,limit_st) y (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_members_child_post (ctx,func) (first,last,b,cap,limit_st)
        y (ei,cd,cs,cst,cen,co) r u) /\
  EVERY (\(ei,az,mz,dyn). P ei) infos /\
  EVERY (\(ei,az,mz,dyn). abi_scratch_encoder ei) infos /\ en.cs_next_id <= last /\
  abi_encoder_spine_code func limit_st en.cs_next_id (dst,src,dp) infos (st,so,ho) (out,en) /\
  abi_scratch_members_inv infos tys avs pre pvs active dp site slot first last lo
    st limit_st src dst sb so ho d hl sz b cap initial ==>
  ?t n. gas_path ctx func initial n (OK t) /\
    abi_scratch_members_inv [] [] [] (pre++tys) (pvs++avs) active dp site slot first last lo
      en limit_st src dst sb (so+abi_encoder_member_span infos)
      (ho+SUM (MAP (\(_,az,_,_). az) infos)) d hl sz b cap t /\
    abi_scratch_effect first last lo en.cs_next_id st.cs_next_var limit_st d sz b cap initial t /\
    abi_decode_sim ctx func initial t
Proof
  strip_tac >>
  drule_all (Q.INST [`hi` |-> `en.cs_next_id`] abi_scratch_members_index_initial) >>
  disch_then (qspecl_then [`func`,`en`,`ctx`] assume_tac) >>
  `~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts` by fs[abi_scratch_members_inv_def] >>
  drule_all intcall_scratch_members_restricted_counted >> simp[]
QED
