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
       (fn th => pure_once_rewrite_tac [th]) >> simp[]) >>
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

Theorem selected_setup_frame[local]:
  r = s with <| vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx |> /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op r = eval_operand op s) /\
  (!name. not_fresh_at st name ==> FLOOKUP H name = FLOOKUP G name /\
    FLOOKUP u.t_var name = FLOOKUP tn.t_var name) /\
  u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
  u.t_imm = tn.t_imm ==>
  selected_member_frame st mid (s,G,tn) (r,H,u) /\
  abi_decode_footprint_frame fp s r
Proof
  strip_tac >>
  `r.vs_allocas = s.vs_allocas /\ r.vs_alloca_next = s.vs_alloca_next /\
   r.vs_memory = s.vs_memory /\ r.vs_call_ctx = s.vs_call_ctx /\
   r.vs_data_section = s.vs_data_section /\ r.vs_code = s.vs_code /\
   r.vs_accounts = s.vs_accounts /\ r.vs_transient = s.vs_transient /\
   r.vs_logs = s.vs_logs /\ r.vs_outcomes = s.vs_outcomes /\
   r.vs_requests = s.vs_requests /\ r.vs_pending_deletions = s.vs_pending_deletions /\
   r.vs_tx_ctx = s.vs_tx_ctx /\ r.vs_block_ctx = s.vs_block_ctx /\
   r.vs_fmp = s.vs_fmp /\ r.vs_gas_readings = s.vs_gas_readings` by
    (qpat_assum `r = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => pure_once_rewrite_tac [th]) >> simp[]) >>
  simp[selected_member_frame_def, abi_decode_footprint_frame_def]
QED

Theorem selected_member_run[local]:
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty)) ao vo st = (ops,mid) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) mid = ((),en) /\
  fn_has_code st mid fn /\ fn_has_code mid en fn /\ fn_inst_ids_distinct fn /\
  st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= en.cs_next_var /\
  en.cs_next_var <= limit.cs_next_var /\
  st.cs_next_id <= mid.cs_next_id /\ mid.cs_next_id <= en.cs_next_id /\
  unit_alloca_budget ctx < dimword (:256) /\
  (en.cs_current_insts = [] ==> !bb.
    lookup_block en.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf ty tv /\ selected_decoder_accepts ce env sf ty tv /\
  cd_decode F s.vs_call_ctx.cc_calldata tv
    (cd_member_ptr F s.vs_call_ctx.cc_calldata tv (w2n p) ao) = SOME x /\
  eval_operand (Var root) s = SOME (n2w d) /\ eval_operand src s = SOME p /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
  ptr_covers G tn root s extent /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  vo + type_memory_size tv <= extent /\ d + extent < dimword (:256) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\ selected_member_replays st en fn s /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ en.cs_next_id <= oid) /\
  base_addr <= d /\ d + extent <= base_addr + cap /\
  fresh_vars_wrt limit s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?v scratch J z.
    ~v.vs_halted /\ v.vs_current_bb = en.cs_current_bb /\
    v.vs_inst_idx = LENGTH en.cs_current_insts /\ value_has_type tv x /\ val_wf tv x /\
    (!mem. mem_agree_outside z.t_mem v.vs_memory mem ==> val_in_memory tv x (d+vo) mem) /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\ allocas_from lo v /\
    fresh_vars_wrt limit v /\ selected_member_replays st en fn v /\
    selected_member_frame st en (s,G,tn) (v,J,z) /\
    abi_decode_footprint_frame ((d+vo,type_memory_size tv)::scratch) s v /\
    (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < en.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK v,J,z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `mid.cs_next_var <= limit.cs_next_var` by decide_tac >>
  drule_all selected_member_setup_accepts >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `r.vs_allocas = s.vs_allocas /\ r.vs_alloca_next = s.vs_alloca_next /\ ~r.vs_halted` by
    (qpat_assum `r = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => pure_once_rewrite_tac [th]) >> simp[]) >>
  `alloca_inv r /\ alloca_frontier_inv ctx fn site r /\ allocas_from lo r` by
    (drule selected_setup_frontier >> simp[]) >>
  `selected_member_frame st mid (s,G,tn) (r,H,u)` by
    (drule_all selected_setup_frame >> simp[]) >>
  `selected_member_replays mid en fn s` by
    metis_tac[selected_member_replays_narrow, LESS_EQ_REFL] >>
  `selected_member_replays mid en fn r` by
    (rewrite_tac[selected_member_replays_def] >> asm_rewrite_tac[] >>
     qpat_assum `selected_member_replays mid en fn s`
       (ACCEPT_TAC o REWRITE_RULE[selected_member_replays_def])) >>
  SUBGOAL_THEN ``oid < mid.cs_next_id \/ en.cs_next_id <= oid`` assume_tac
  >- decide_tac >>
  `base_addr <= d+vo /\ d+vo+type_memory_size tv <= base_addr+cap /\
   d+vo+type_memory_size tv < dimword (:256)` by decide_tac >>
  `!fp. abi_decode_footprint_frame fp s r` by
    (drule_all selected_setup_frame >> simp[]) >>
  qpat_x_assum `r = s with <|vs_vars := _; vs_inst_idx := _|>` kall_tac >>
  `eval_operand (Var q) r = SOME (n2w (d+vo)) /\ abi_decoder_operand_live mid.cs_next_var (Var q)` by
    metis_tac[] >>
  `lo <= r.vs_alloca_next /\ FLOOKUP r.vs_allocas oid = SOME (base_addr,cap)` by simp[] >>
  `compile_abi_decode_to_buf (Var q) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) mid = ((),en)` by metis_tac[] >>
  qpat_assum `selected_member_replays mid en fn r`
    (assume_tac o REWRITE_RULE[selected_member_replays_def]) >>
  qpat_x_assum `selected_decoder_accepts ce env sf ty tv`
    (drule_all o REWRITE_RULE[selected_decoder_accepts_def]) >>
  disch_then (qspec_then `PG`
    (qx_choose_then `v` (qx_choose_then `scratch`
      (qx_choose_then `J` (qx_choose_then `z` strip_assume_tac))))) >>
  `selected_member_replays mid en fn v` by
    (rewrite_tac[selected_member_replays_def] >> first_assum ACCEPT_TAC) >>
  `selected_member_frame mid en (r,H,u) (v,J,z)` by
    (rewrite_tac[selected_member_frame_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `selected_member_replays st mid fn r` by
    (`selected_member_replays st mid fn s` by
       (qpat_assum `selected_member_replays st en fn s` mp_tac >>
        qpat_assum `mid.cs_next_id <= en.cs_next_id` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        metis_tac[selected_member_replays_narrow, LESS_EQ_REFL]) >>
     rewrite_tac[selected_member_replays_def] >> asm_rewrite_tac[] >>
     qpat_assum `selected_member_replays st mid fn s`
       (ACCEPT_TAC o REWRITE_RULE[selected_member_replays_def])) >>
  `selected_member_replays st mid fn v` by
    (qpat_assum `selected_member_frame mid en (r,H,u) (v,J,z)` mp_tac >>
     qpat_assum `selected_member_replays st mid fn r` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[selected_member_replays_outside, LESS_EQ_REFL]) >>
  qexistsl [`v`,`scratch`,`J`,`z`] >>
  ntac 10 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (irule selected_member_replays_join >> metis_tac[]) >>
  conj_tac >- (drule_all selected_member_frame_trans >> first_assum ACCEPT_TAC ORELSE
    metis_tac[selected_member_frame_trans]) >>
  conj_tac >-
    (qpat_assum `abi_decode_footprint_frame _ r v` mp_tac >>
     qpat_assum `!fp. abi_decode_footprint_frame fp s r` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[abi_decode_footprint_frame_trans]) >>
  conj_tac >-
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!q k. MEM (q,k) scratch ==> _` drule >> strip_tac >>
     qexists_tac `id` >> rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE decide_tac)) >>
  rpt gen_tac >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] (OK r,H,u)` mp_tac >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (r,H,u) [] (OK v,J,z)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[gas_origin_ptr_path_trans]
QED

(* The old root pointer and the immutable input operand survive each
   slice of the member program. *)
Theorem selected_member_root_frame[local]:
  selected_member_frame st en (s,G,tn) (t,H,u) /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
  abi_decoder_operand_live st.cs_next_var src /\
  ptr_covers G tn root s extent /\ op_taint tn src = {} /\ op_prov G src = NONE ==>
  t.vs_call_ctx = s.vs_call_ctx /\
  eval_operand (Var root) t = eval_operand (Var root) s /\
  eval_operand src t = eval_operand src s /\
  ptr_covers H u root t extent /\ op_taint u src = {} /\ op_prov H src = NONE
Proof
  simp[selected_member_frame_def] >> strip_tac >>
  `eval_operand (Var root) t = eval_operand (Var root) s /\
   eval_operand src t = eval_operand src s` by metis_tac[] >>
  `not_fresh_at st root /\ (!name. src = Var name ==> not_fresh_at st name)` by
    (Cases_on `src` >>
     gvs[abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def]) >>
  `ptr_covers H u root t extent` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     goal_assum (drule_at Any) >> fs[eval_operand_def,op_taint_def]) >>
  Cases_on `src` >> gvs[op_taint_def,op_prov_def] >> metis_tac[]
QED

Theorem selected_member_window_survives[local]:
  selected_member_frame st en (s,G,tn) (t,H,u) /\
  abi_decode_footprint_frame ((d,sz)::scratch) s t /\ alloca_inv t /\
  (oid < st.cs_next_id \/ en.cs_next_id <= oid) /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < en.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
  base_addr <= b /\ b + type_memory_size tv <= base_addr + cap /\
  b + type_memory_size tv <= d /\ val_wf tv x /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv x b m) ==>
  !m. mem_agree_outside u.t_mem t.vs_memory m ==> val_in_memory tv x b m
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `selected_member_frame _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[selected_member_frame_def]) >>
  `mem_bytes_at b (type_memory_size tv) t.vs_memory =
   mem_bytes_at b (type_memory_size tv) s.vs_memory` by
    (irule (cj 2 calldataChildFrameTheory.calldata_child_preserves_allocated_region) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     qexistsl_tac [`base_addr`,`cap`,`d`,`oid`,`scratch`,`sz`] >>
     simp[]) >>
  rpt gen_tac >> disch_tac >>
  irule bodyPtrBytestringBuiltinsWindowGhostTheory.robust_val_in_memory_window_transport >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`tn.t_mem`,`u.t_mem`,`type_memory_size tv`,`s.vs_memory`,`t.vs_memory`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (rpt strip_tac >> fs[SUBSET_DEF]) >>
  simp[exprSimPropsTheory.val_footprint_le]
QED

(* Result shared by a singleton and a suffix of the installed member list. *)
Definition selected_member_segment_def:
  selected_member_segment ctx fn site lo PG limit st en b n
    (s,G,tn) (t,H,u) scratch <=>
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lo t /\
    fresh_vars_wrt limit t /\ selected_member_replays st en fn t /\
    selected_member_frame st en (s,G,tn) (t,H,u) /\
    abi_decode_footprint_frame ((b,n)::scratch) s t /\
    (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < en.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,H,u))
End

Theorem selected_member_segment_append[local]:
  selected_member_segment ctx fn site lo PG limit st en b n (s,G,tn) (t,H,u) sc /\
  selected_member_segment ctx fn site lo PG limit en fin (b+n) m (t,H,u) (v,J,z) sd /\
  st.cs_next_id <= en.cs_next_id /\ en.cs_next_id <= fin.cs_next_id /\
  st.cs_next_var <= en.cs_next_var ==>
  selected_member_segment ctx fn site lo PG limit st fin b (n+m) (s,G,tn) (v,J,z) (sc++sd)
Proof
  rewrite_tac[selected_member_segment_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  ntac 7 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (`selected_member_replays st en fn v` by
       (qpat_assum `selected_member_frame en fin (t,H,u) (v,J,z)` mp_tac >>
        qpat_assum `selected_member_replays st en fn t` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        metis_tac[selected_member_replays_outside,LESS_EQ_REFL]) >>
     irule selected_member_replays_join >> metis_tac[]) >>
  conj_tac >- (drule_all selected_member_frame_trans >> disch_then ACCEPT_TAC) >>
  conj_tac >-
    (irule abi_decode_footprint_frame_trans >> qexists_tac `t` >> conj_tac
     >- (irule abi_decode_footprint_frame_weaken >> goal_assum (drule_at Any) >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp[MEM_APPEND] >> rpt gen_tac >> strip_tac
         >- (qexistsl [`b`,`n+m`] >> simp[]) >>
         qexistsl [`d`,`sz`] >> simp[]) >>
     irule abi_decode_footprint_frame_weaken >> goal_assum (drule_at Any) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[MEM_APPEND] >> rpt gen_tac >> strip_tac
     >- (qexistsl [`b`,`m+n`] >> simp[]) >>
     qexistsl [`d`,`sz`] >> simp[]) >>
  conj_tac >-
    (rpt gen_tac >> simp[MEM_APPEND] >> strip_tac
     >- (qpat_assum `!q k. MEM (q,k) sc ==> _` drule >> strip_tac >>
         qexists_tac `id` >> conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- decide_tac >>
         qpat_assum `selected_member_frame en fin (t,H,u) (v,J,z)`
           (mp_tac o REWRITE_RULE[selected_member_frame_def]) >>
         strip_tac >> metis_tac[]) >>
     qpat_assum `!q k. MEM (q,k) sd ==> _` drule >> strip_tac >>
     qexists_tac `id` >> simp[] >> decide_tac) >>
  rpt gen_tac >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] (OK t,H,u)` mp_tac >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (t,H,u) [] (OK v,J,z)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[gas_origin_ptr_path_trans]
QED

(* Fold over the compiler's suffix at the source ABI and memory cursors. *)
Theorem selected_member_list_run[local]:
  !tys tvs xs ao vo st last limit ctx fn site lo PG root src s G tn p d extent oid base_addr cap.
    LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
    LIST_REL (selected_decoder_accepts ce env sf) tys tvs /\
    compile_abi_decode_complex_elems (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
       (abi_decoder_member_infos sf ce tys) ao vo st = ((),last) /\
    fn_has_code st last fn /\ fn_inst_ids_distinct fn /\ last.cs_next_var <= limit.cs_next_var /\
    unit_alloca_budget ctx < dimword (:256) /\
    (last.cs_current_insts = [] ==> !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    cd_decode_list F s.vs_call_ctx.cc_calldata tvs (w2n p) ao = SOME xs /\
    eval_operand (Var root) s = SOME (n2w d) /\ eval_operand src s = SOME p /\
    abi_decoder_operand_live st.cs_next_var src /\
    abi_decoder_operand_live st.cs_next_var (Var root) /\
    ptr_covers G tn root s extent /\ op_taint tn src = {} /\ op_prov G src = NONE /\
    vo + type_memory_size_list tvs <= extent /\ d + extent < dimword (:256) /\
    alloca_inv s /\ alloca_frontier_inv ctx fn site s /\ selected_member_replays st last fn s /\
    FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
    (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
    base_addr <= d /\ d + extent <= base_addr + cap /\
    fresh_vars_wrt limit s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?v scratch J z.
      selected_member_segment ctx fn site lo PG limit st last (d+vo) (type_memory_size_list tvs)
        (s,G,tn) (v,J,z) scratch /\
      LIST_REL value_has_type tvs xs /\
      (!mem. mem_agree_outside z.t_mem v.vs_memory mem ==> tuple_in_memory xs tvs (d+vo) mem)
Proof
  Induct
  >- (simp[abiDecoderMemberInfosTheory.abi_decoder_member_infos_def,
       Once compile_abi_decode_to_buf_def,comp_return_def] >> rpt gen_tac >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      gvs[Once cd_decode_def] >>
      qexistsl [`s`,`[]`,`G`,`tn`] >>
      simp[selected_member_segment_def,selected_member_frame_refl,
           abi_decode_footprint_frame_refl,val_in_memory_def] >>
      metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_rules]) >>
  rpt gen_tac >>
  Cases_on `tvs` >- simp[] >>
  rename1 `LIST_REL _ (ty::tys) (tv::tvs)` >>
  simp[Once cd_decode_def,CaseEq "option",
       abiDecoderMemberInfosTheory.abi_decoder_member_infos_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?v. cd_decode F _ tv _ = SOME v /\ _`
    (qx_choose_then `y` strip_assume_tac) >>
  rename1 `cd_decode_list F s.vs_call_ctx.cc_calldata tvs (w2n p) (ao + tv_abi_size tv) = SOME ys` >>
  rename1 `cd_decode F s.vs_call_ctx.cc_calldata tv _ = SOME y` >>
  drule_all selected_member_cons_trace >> strip_tac >>
  `abi_embedded_static_size ce.ce_struct_fields ty = tv_abi_size tv /\
   type_memory_bytes ce ty = type_memory_size tv` by
    (drule abi_decoder_coherent_header >> simp[abi_decoder_header_def] >>
     metis_tac[calldataSourceSizeTheory.calldata_coherent_embedded_size]) >>
  `vo + type_memory_size tv <= extent /\
   vo + type_memory_size tv + type_memory_size_list tvs <= extent` by
    (qpat_assum `vo + type_memory_size_list (tv::tvs) <= extent`
       (assume_tac o REWRITE_RULE[type_memory_size_def]) >> decide_tac) >>
  `en.cs_next_var <= limit.cs_next_var` by decide_tac >>
  SUBGOAL_THEN ``oid < st.cs_next_id \/ en.cs_next_id <= oid`` assume_tac
  >- decide_tac >>
  `selected_member_replays st en fn s` by
    (irule selected_member_replays_narrow >> metis_tac[LESS_EQ_REFL]) >>
  `en.cs_current_insts = [] ==> !bb. lookup_block en.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[selected_member_exit_phi] >>
  drule_all selected_member_run >>
  disch_then (qspec_then `PG` (qx_choose_then `t` (qx_choose_then `sc`
    (qx_choose_then `H` (qx_choose_then `u` strip_assume_tac))))) >>
  drule_all selected_member_root_frame >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `st.cs_next_id <= en.cs_next_id` by decide_tac >>
  `selected_member_replays en last fn s` by
    (irule selected_member_replays_narrow >> metis_tac[LESS_EQ_REFL]) >>
  `selected_member_replays en last fn t` by
    (qpat_assum `selected_member_frame st en (s,G,tn) (t,H,u)` mp_tac >>
     qpat_assum `selected_member_replays en last fn s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[selected_member_replays_outside,LESS_EQ_REFL]) >>
  `FLOOKUP t.vs_allocas oid = SOME (base_addr,cap) /\ lo <= t.vs_alloca_next` by
    (qpat_assum `selected_member_frame st en (s,G,tn) (t,H,u)`
      (mp_tac o REWRITE_RULE[selected_member_frame_def]) >>
     strip_tac >> conj_tac >- metis_tac[] >> decide_tac) >>
  `abi_decoder_operand_live en.cs_next_var src /\
   abi_decoder_operand_live en.cs_next_var (Var root)` by
    (`st.cs_next_var <= en.cs_next_var` by decide_tac >>
     metis_tac[abi_decoder_operand_live_mono]) >>
  SUBGOAL_THEN ``oid < en.cs_next_id \/ last.cs_next_id <= oid`` assume_tac
  >- decide_tac >>
  `compile_abi_decode_complex_elems (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
      (abi_decoder_member_infos sf ce tys) (ao + tv_abi_size tv) (vo + type_memory_size tv) en = ((),last)` by
    (simp[abiDecoderMemberInfosTheory.abi_decoder_member_infos_def] >> metis_tac[]) >>
  `cd_decode_list F t.vs_call_ctx.cc_calldata tvs (w2n p) (ao + tv_abi_size tv) = SOME ys /\
   eval_operand (Var root) t = SOME (n2w d) /\ eval_operand src t = SOME p` by simp[] >>
  last_x_assum (qspecl_then [`tvs`,`ys`,`ao + tv_abi_size tv`,`vo + type_memory_size tv`,
    `en`,`last`,`limit`,`ctx`,`fn`,`site`,`lo`,`PG`,`root`,`src`,`t`,`H`,`u`,`p`,`d`,`extent`,
    `oid`,`base_addr`,`cap`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `v` (qx_choose_then `sd`
    (qx_choose_then `J` (qx_choose_then `z` strip_assume_tac)))) >>
  `(d + vo) + type_memory_size tv = d + (vo + type_memory_size tv)` by decide_tac >>
  `selected_member_segment ctx fn site lo PG limit st en (d+vo) (type_memory_size tv)
     (s,G,tn) (t,H,u) sc` by
    (rewrite_tac[selected_member_segment_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `selected_member_segment ctx fn site lo PG limit en last ((d+vo) + type_memory_size tv)
     (type_memory_size_list tvs) (t,H,u) (v,J,z) sd` by simp[] >>
  `st.cs_next_var <= en.cs_next_var` by decide_tac >>
  qpat_assum `selected_member_segment _ _ _ _ _ _ st en _ _ _ _ sc`
    (mp_then (Pos hd) mp_tac selected_member_segment_append) >>
  disch_then (drule_all_then assume_tac) >>
  `!mem. mem_agree_outside z.t_mem v.vs_memory mem ==> val_in_memory tv y (d+vo) mem` by
    (qpat_assum `selected_member_segment _ _ _ _ _ _ en last _ _ _ _ sd`
        (map_every assume_tac o CONJUNCTS o REWRITE_RULE[selected_member_segment_def]) >>
     `base_addr <= d+vo /\ d+vo+type_memory_size tv <= base_addr+cap` by decide_tac >>
     gen_tac >> disch_tac >>
     qpat_assum `selected_member_frame en last (t,H,u) (v,J,z)`
       (mp_then (Pos hd) irule selected_member_window_survives) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qexistsl [`base_addr`,`cap`,`oid`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     goal_assum (drule_at (Pat `abi_decode_footprint_frame _ _ _`)) >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE decide_tac)) >>
  qexistsl [`v`,`sc++sd`,`J`,`z`] >>
  conj_tac >- (rewrite_tac[type_memory_size_def] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `y::ys = xs` (fn th => rewrite_tac[GSYM th]) >>
  simp[val_in_memory_def] >> metis_tac[]
QED
