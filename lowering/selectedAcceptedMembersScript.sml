(* Accepted decoding of installed complex members on the real calldata. *)
Theory selectedAcceptedMembers
Ancestors
  selectedAcceptedInterfaces calldataExactMemberValues calldataMembersRawSubregion
  decoderMemberJointModular calldataEmptyArrayChild calldataSourceCorrespondence
  abiDecoderOffset abiDecoderDynamic abiDecoderMemberCons abiDecoderMemberCode abiDecoderComplexExecute
  abiDecoderContract abiDecoderFrame abiDecoderLoop fragExec venomExecSemantics venomInst
  fragGasPathMem fragGasOriginPtrLoop fragGasOriginPtrExec freshWrites
  vyperCalldata valueEncoding valueEncodingDefs valueEncodingTyping vyperTyping
  abiDecoderCoherence compileEnv exprLowering abiEncoder words finite_map list arithmetic
  venomMemDefs allocaFrontierBound allocaBudgetProps ptrDiscipline pred_set
  bodyPtrDefs abiDecoderReentry loweringStateRelDefs venomState

(* The addition uses a word literal, even if the mathematical head cursor
   does not fit in a word. The source also reduces that cursor modulo 2^256. *)
Theorem selected_member_source_decode[local]:
  abi_decoder_coherent ce env sf ty tv ==>
  cd_decode F s.vs_call_ctx.cc_calldata tv
    (w2n (if dec_info_needs_offset (type_to_abi_dec_info sf ce ty)
          then p + abi_decode_load CALLDATALOAD (p + n2w ao) s
          else p + n2w ao)) =
  cd_decode F s.vs_call_ctx.cc_calldata tv
    (cd_member_ptr F s.vs_call_ctx.cc_calldata tv (w2n p) ao)
Proof
  strip_tac >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- gvs[abi_decoder_empty_dynamic_translation,
         abi_decoder_coherent_array_iff, cd_decode_def] >>
  drule abi_decoder_coherent_dynamic >>
  drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def] >> rpt strip_tac >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) = tv_abi_dynamic tv` by
    metis_tac[abi_decoder_nonempty_offset, calldata_coherent_dynamic] >>
  `cd_member_ptr F s.vs_call_ctx.cc_calldata tv (w2n p) ao =
    cd_member_ptr F s.vs_call_ctx.cc_calldata tv (w2n p)
      (w2n (n2w ao : bytes32))` by
    simp[cd_member_ptr_def, cd_at_def, MOD_PLUS] >>
  metis_tac[calldata_member_pointer]
QED

Theorem selected_member_cons_trace[local]:
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    ((di,az,mz)::rest) ao vo st = ((),last) /\ fn_has_code st last fn ==>
  ?ops mid en.
    abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      (dec_info_needs_offset di) ao vo st = (ops,mid) /\
    compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w)
      di mid = ((),en) /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      rest (ao+az) (vo+mz) en = ((),last) /\
    fn_has_code st mid fn /\ fn_has_code mid en fn /\ fn_has_code en last fn /\
    st.cs_next_id <= mid.cs_next_id /\ mid.cs_next_id <= en.cs_next_id /\
    en.cs_next_id <= last.cs_next_id /\
    st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= en.cs_next_var /\
    en.cs_next_var <= last.cs_next_var
Proof
  rewrite_tac[abiDecoderMemberSetupTheory.abi_decode_complex_member_phases] >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_decode_member_setup _ _ _ _ _ _ _ _ st = (ops,mid)` >>
  rename1 `compile_abi_decode_to_buf _ _ _ _ _ di mid = ((),en)` >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  `fn_has_code st mid fn /\ fn_has_code mid en fn` by
    metis_tac[fn_has_code_split] >>
  simp[]
QED

Theorem selected_member_exit_phi[local]:
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    infos ao vo en = ((),last) /\ fn_has_code en last fn /\
  (last.cs_current_insts = [] ==> !bb.
      lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\ en.cs_current_insts = [] ==>
  !bb. lookup_block en.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  Cases_on `infos`
  >- (simp[Once compile_abi_decode_to_buf_def, comp_return_def] >> metis_tac[]) >>
  PairCases_on `h` >> strip_tac >>
  drule_all selected_member_cons_trace >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  `mid.cs_current_insts <> [] /\ phi_prefix_length mid.cs_current_insts = 0` by
    fs[phi_prefix_length_def, mk_inst_def] >>
  metis_tac[exprSimAbiDecodePhiBoundaryTheory.abi_decode_continuation_exit_phi]
QED

Theorem selected_fixed_source_list[local]:
  !n i cd t p nat.
    cd_decode_elems nat cd t p i n =
    cd_decode_list nat cd (REPLICATE n t) p (i * tv_abi_size t)
Proof
  Induct
  >- simp[cd_decode_def, rich_listTheory.REPLICATE] >>
  rpt gen_tac >>
  simp[Once cd_decode_def, rich_listTheory.REPLICATE] >>
  simp[Once cd_decode_def, LEFT_ADD_DISTRIB]
QED

(* The modular setup has no effect on the allocation frontier or replay map. *)
Theorem selected_setup_frontier[local]:
  r = s with <| vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx |> ==>
  (alloca_inv r <=> alloca_inv s) /\
  (alloca_frontier_inv ctx fn site r <=> alloca_frontier_inv ctx fn site s) /\
  (allocas_from lo r <=> allocas_from lo s)
Proof
  disch_then (fn th => pure_once_rewrite_tac [th]) >>
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_frontier_inv_def, remaining_alloca_budget_def, allocas_from_def]
QED

Theorem selected_member_setup_accepts[local]:
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty)) ao vo st = (ops,mid) /\
  abi_decoder_coherent ce env sf ty tv /\
  cd_decode F s.vs_call_ctx.cc_calldata tv
    (cd_member_ptr F s.vs_call_ctx.cc_calldata tv (w2n p) ao) = SOME x /\
  eval_operand (Var root) s = SOME (n2w d) /\
  eval_operand src s = SOME p /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
  ptr_covers G tn root s extent /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  vo + type_memory_size tv <= extent /\ d + extent < dimword (:256) /\
  mid.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  fn_has_code st mid fn /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?r H u q p'.
    r = s with <| vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx |> /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK r,H,u)) /\
    r.vs_current_bb = mid.cs_current_bb /\ r.vs_inst_idx = LENGTH mid.cs_current_insts /\
    fresh_vars_wrt limit r /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op r = eval_operand op s) /\
    abi_decoder_operand_live mid.cs_next_var (FST ops) /\
    abi_decoder_operand_live mid.cs_next_var (SND ops) /\
    SND ops = Var q /\ eval_operand (SND ops) r = SOME (n2w (d + vo)) /\
    eval_operand (FST ops) r = SOME p' /\
    cd_decode F r.vs_call_ctx.cc_calldata tv (w2n p') = SOME x /\
    ptr_covers H u q r (type_memory_size tv) /\
    op_taint u (FST ops) = {} /\ op_prov H (FST ops) = NONE /\
    (!name. not_fresh_at st name ==> FLOOKUP H name = FLOOKUP G name /\
      FLOOKUP u.t_var name = FLOOKUP tn.t_var name) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm
Proof
  strip_tac >>
  `lookup_var root s = SOME (n2w d)` by fs[eval_operand_def] >>
  `d < dimword (:256) /\ d + vo < dimword (:256)` by decide_tac >>
  `not_fresh_at st root /\ (!q. src = Var q ==> not_fresh_at st q)` by
    (Cases_on `src` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  drule_all calldata_member_setup_joint_modular >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `r.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `r = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >>
  qexistsl [`r`,`H`,`u`,`q`] >>
  goal_assum (drule_at Any) >>
  drule selected_member_source_decode >>
  disch_then (qspecl_then [`s`,`p`,`ao`] assume_tac) >>
  simp[] >> metis_tac[]
QED

Definition selected_member_frame_def:
  selected_member_frame st en (s,G,tn) (t,H,u) <=>
    t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_code = s.vs_code /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
    t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\
    t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
    t.vs_fmp = s.vs_fmp /\ t.vs_gas_readings = s.vs_gas_readings /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP s.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ en.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!name. not_fresh_at st name ==>
      FLOOKUP H name = FLOOKUP G name /\
      FLOOKUP u.t_var name = FLOOKUP tn.t_var name) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm
End

Definition selected_member_replays_def:
  selected_member_replays st en fn s <=>
  !id q k. st.cs_next_id <= id /\ id < en.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]
End

Theorem selected_member_frame_refl[local]:
  selected_member_frame st en (s,G,tn) (s,G,tn)
Proof
  simp[selected_member_frame_def]
QED

Theorem selected_member_frame_trans[local]:
  selected_member_frame st en (s,G,tn) (t,H,u) /\
  selected_member_frame en last (t,H,u) (v,J,z) /\
  st.cs_next_id <= en.cs_next_id /\ en.cs_next_id <= last.cs_next_id /\
  st.cs_next_var <= en.cs_next_var ==>
  selected_member_frame st last (s,G,tn) (v,J,z)
Proof
  simp[selected_member_frame_def] >> strip_tac >> simp[] >>
  `!id. id < st.cs_next_id \/ last.cs_next_id <= id ==>
     (id < st.cs_next_id \/ en.cs_next_id <= id) /\
     (id < en.cs_next_id \/ last.cs_next_id <= id)` by decide_tac >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
        abi_decoder_operand_live en.cs_next_var op` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `!name. not_fresh_at st name ==> not_fresh_at en name` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  metis_tac[SUBSET_TRANS]
QED

Theorem selected_member_replays_narrow[local]:
  selected_member_replays st last fn s /\
  st.cs_next_id <= mid.cs_next_id /\ en.cs_next_id <= last.cs_next_id ==>
  selected_member_replays mid en fn s
Proof
  rewrite_tac[selected_member_replays_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `st.cs_next_id <= id /\ id < last.cs_next_id` by decide_tac >>
  qpat_assum `!id q k. _ ==> k = 32 /\ _` irule >> metis_tac[]
QED

Theorem selected_member_replays_join[local]:
  selected_member_replays st en fn t /\ selected_member_replays en last fn t ==>
  selected_member_replays st last fn t
Proof
  rewrite_tac[selected_member_replays_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  Cases_on `id < en.cs_next_id` >>
  `st.cs_next_id <= id /\ id < en.cs_next_id \/
   en.cs_next_id <= id /\ id < last.cs_next_id` by decide_tac >>
  metis_tac[]
QED

Theorem selected_member_replays_outside[local]:
  selected_member_frame st en (s,G,tn) (t,H,u) /\
  selected_member_replays a b fn s /\
  (b.cs_next_id <= st.cs_next_id \/ en.cs_next_id <= a.cs_next_id) ==>
  selected_member_replays a b fn t
Proof
  rewrite_tac[selected_member_frame_def,selected_member_replays_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  `id < st.cs_next_id \/ en.cs_next_id <= id` by decide_tac >>
  `FLOOKUP s.vs_allocas id = SOME (q,k)` by metis_tac[] >>
  qpat_assum `!id q k. _ ==> k = 32 /\ _` (qspecl_then [`id`,`q`,`k`] mp_tac) >>
  metis_tac[LESS_EQ_TRANS]
QED
