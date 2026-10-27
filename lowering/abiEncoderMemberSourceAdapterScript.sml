(* Early source-contract interpretation of the common member engine. *)
Theory abiEncoderMemberSourceAdapter
Ancestors
  abiEncoderMemberSpine abiEncoderMemberSourceContract abiEncoderMemberSourceInterpret
  abiEncoderChildSourcePhase abiEncoderAddressReach
  abiEncoderMemberPhaseRaw abiDecoderDynamicLoopSetup abiDecoderArrayInitExec
  abiEncoderChildFrames abiEncoderCorrect abiEncoderChildInputs abiDecoderEffect
  abiDecoderReentry abiDecoderContract abiDecoderLoop fragExec compileEnv
  abiEncoderChildContext abiEncoderChildCompose abiEncoderChildPrefix abiEncoderChildSuffixReach abiEncoderChildSuffix abiEncoderChildEffect
  abiEncoderExtendSim abiEncoderChildCode abiDecoderAllocation abiDecoderProtectedScratch finite_map pred_set
  venomInstProps venomExecSemantics exprLoweringProps
  valueEncoding venomState words list arithmetic

Theorem abi_encoder_static_child_spine_reach:
  abi_encoder_correct ei /\ compile_abi_encode_child dst src ei F offset dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  offset+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. mem_bytes_at (d+offset) (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_footprint_frame [(d+offset,LENGTH (enc at av));(b,cap)] initial t /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_member_source_static_input >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_encoder_member_source_child_run >> strip_tac >>
  qexists_tac `t` >> irule abi_encoder_member_source_static_output >>
  goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
  goal_assum (drule_at Any) >> asm_rewrite_tac []
QED

(* This layer must remain available before all member execution owners. *)
val _ =
  if List.exists
       (fn name => List.exists (fn parent => parent = name) (Theory.ancestry "-"))
       ["abiEncoderStatic", "abiEncoderDynamic", "abiEncoderMemberSourcePhase", "abiEncoderMembersDefs",
        "abiScratchStatic", "abiScratchDynamicChild", "abiScratchMemberStep", "abiScratchComplex",
        "abiEncoderMemberSpineCompat", "abiEncoderMemberPhaseExec", "abiEncoderMember",
        "abiScratchMembers", "abiEncoderMembersCorrect", "abiEncoderComplexStatic"]
  then raise Fail "source adapter imports a member execution owner"
  else ();

val _ =
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag abi_encoder_static_child_spine_reach) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print "ENCODER_SOURCE_ADAPTER_AUDIT_OK static_child_spine_reach\n"
    else raise Fail "source adapter admission dependency: static_child_spine_reach"
  end;

Theorem abi_encoder_source_suffix_raw_post:
  abi_encode_child_suffix head dp offset len st = (out,final) /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand dp initial = SOME (n2w slot) /\
  eval_operand offset initial = SOME (n2w off) /\ eval_operand len initial = SOME (n2w n) /\
  abi_decoder_operand_live st.cs_next_var dp /\ abi_decoder_operand_live st.cs_next_var len /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial actual ==>
  abi_encoder_child_suffix_post out st limit_st h slot off n initial actual
Proof
  strip_tac >> drule_all abi_encoder_member_cursor_transport >>
  simp[abi_encoder_child_suffix_post_def]
QED

Theorem abi_encoder_source_suffix_raw_sim:
  abi_encode_child_suffix head dp offset len st = (out,final) /\
  fn_has_code st final func /\ abi_encoder_member_phase_raw st final initial actual /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule abi_encode_child_suffix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st final)` by fs[EVERY_CONJ] >>
  drule_all abi_encoder_member_phase_extend_sim >>
  metis_tac[abi_encoder_extend_sim_sim]
QED

Theorem abi_encoder_source_suffix_raw_control:
  abi_encode_child_suffix head dp offset len st = (out,final) /\
  abi_encoder_member_phase_raw st final initial actual /\
  initial.vs_current_bb = st.cs_current_bb ==>
  actual.vs_current_bb = final.cs_current_bb /\
  actual.vs_inst_idx = LENGTH final.cs_current_insts
Proof
  strip_tac >> drule abi_encode_child_suffix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st final)` by fs[EVERY_CONJ] >>
  gvs[abi_encoder_member_phase_raw_def] >>
  rename1 `run_inst_seq _ initial = OK u` >>
  `u.vs_current_bb = initial.vs_current_bb` suffices_by simp[] >>
  irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_current_bb` run_inst_seq_preserves_field)) >>
  qexists_tac `emitted_insts st final` >> asm_rewrite_tac [] >>
  rpt strip_tac >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
  drule_all step_preserves_control_flow >> simp[]
QED

(* Universal final transport, not another suffix execution proof. *)
Theorem abi_encoder_source_dynamic_finish_transport:
  abi_encode_child_suffix head dyn_ptr offset child_len st = (out,st') /\ fn_has_code st st' func /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  eval_operand offset initial = SOME (n2w off) /\ eval_operand child_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ abi_decoder_operand_live st.cs_next_var child_len /\
  mem_bytes_at (d+off) len initial.vs_memory = bytes /\
  d <= h /\ h+32 <= d+off /\ off+len <= output_size /\
  d+output_size < dimword (:256) /\ (d+output_size <= b \/ b+cap <= d) /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_member_phase_raw st st' initial actual ==>
  mem_bytes_at (d+off) len actual.vs_memory = bytes /\
  mem_word_at h actual.vs_memory = n2w off /\ mem_word_at slot actual.vs_memory = n2w (off+len) /\
  eval_operand out actual = SOME (n2w len) /\
  abi_decode_footprint_frame [(h,32);(slot,32)] initial actual /\
  FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
  abi_decoder_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial actual /\
  actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
  ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `b+cap < dimword (:256)` by
    (qpat_assum `abi_decoder_budget _ _ _ _ initial`
       (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >> simp[]) >>
  `h < dimword (:256) /\ slot < dimword (:256) /\ h+32 <= d+output_size /\
   ((d+off)+len <= h \/ h+32 <= d+off) /\
   ((d+off)+len <= slot \/ slot+32 <= d+off) /\
   (h+32 <= slot \/ slot+32 <= h)` by decide_tac >>
  drule_all abi_encoder_source_suffix_raw_post >> disch_tac >>
  mp_tac (Q.INST [`q` |-> `d+off`, `offset` |-> `off:num`] abi_encoder_child_suffix_output) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  `abi_decoder_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial actual` by
    (mp_tac (Q.INST [`sz` |-> `output_size:num`, `off` |-> `off:num`]
       abi_encoder_child_suffix_effect) >>
     impl_tac >- asm_simp_tac bool_ss [] >> simp[]) >>
  drule_all abi_encoder_source_suffix_raw_control >> strip_tac >>
  drule_all abi_encoder_source_suffix_raw_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  fs[abi_encoder_child_suffix_post_def]
QED

val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print ("ENCODER_SOURCE_ADAPTER_AUDIT_OK " ^ name ^ "\n")
    else raise Fail ("source adapter admission dependency: " ^ name)
  end)
  [("suffix_raw_post", abi_encoder_source_suffix_raw_post),
   ("suffix_raw_sim", abi_encoder_source_suffix_raw_sim),
   ("suffix_raw_control", abi_encoder_source_suffix_raw_control),
   ("dynamic_finish_transport", abi_encoder_source_dynamic_finish_transport)];

Theorem abi_encoder_source_dynamic_prepare_transport:
  abi_encode_child_prefix dst head_offset dyn_ptr st = (ops,prepared) /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ slot < dimword (:256) /\
  off+LENGTH (enc at av) <= output_size /\ abi_decoder_budget first last b cap initial /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_member_phase_raw st prepared initial ready ==>
  abi_encoder_pre ei at av prepared src (SND (SND ops)) sb source_cap (d+off) b cap ready /\
  eval_operand (FST ops) ready = SOME (n2w (d+head_offset)) /\
  eval_operand (FST (SND ops)) ready = SOME (n2w off) /\
  abi_decoder_operand_live prepared.cs_next_var (FST ops) /\
  abi_decoder_operand_live prepared.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live prepared.cs_next_var (SND (SND ops)) /\
  fresh_vars_wrt limit_st ready /\ abi_decoder_budget first last b cap ready /\
  abi_decoder_address_frame st.cs_next_var initial ready /\
  ready.vs_current_bb = prepared.cs_current_bb /\ ready.vs_inst_idx = LENGTH prepared.cs_current_insts /\
  ~ready.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand dst initial = SOME (n2w d) /\ abi_decoder_operand_live st.cs_next_var dst` by
    fs[abi_encoder_buffer_pre_def] >>
  drule abi_encode_child_prefix_shape >> strip_tac >>
  drule abi_encode_child_prefix_live >> strip_tac >>
  drule_all abi_encoder_member_prefix_transport >> strip_tac >>
  drule_all abi_encoder_member_prefix_control >> strip_tac >>
  `st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  `abi_encoder_pre ei at av prepared src (SND (SND ops)) sb source_cap (d+off) b cap ready` by
    (mp_tac (Q.INST [`child_st` |-> `prepared`, `child_dst` |-> `SND (SND (ops:operand # operand # operand))`,
       `actual` |-> `ready:venom_state`, `offset` |-> `off:num`] abi_encoder_child_pre_address) >>
     asm_simp_tac bool_ss []) >>
  `abi_decoder_budget first last b cap ready` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `ready:venom_state`]
      abi_decoder_budget_transport) >> fs[abi_decoder_address_frame_def]) >>
  asm_simp_tac bool_ss []
QED

(* Only the core contract is executed here; saved operands are pure effect transport. *)
Theorem abi_encoder_source_dynamic_core_run:
  abi_encoder_correct ei /\ compile_abi_encode_to_buf dst src ei start = (out,end_st) /\
  fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_pre ei at av start src dst sb source_cap d b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_operand_live start.cs_next_var head /\ abi_decoder_operand_live start.cs_next_var offset /\
  abi_decoder_operand_live start.cs_next_var dyn_ptr /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand offset initial = SOME (n2w off) /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\
  first <= site /\ site < last /\ site < start.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?t. mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_decoder_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap initial t /\
    eval_operand head t = SOME (n2w h) /\ eval_operand offset t = SOME (n2w off) /\
    eval_operand dyn_ptr t = SOME (n2w slot) /\ FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    mload slot t = mload slot initial /\ fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_encoder_spine_core_code func (ei,dst,src,start,end_st,out)` by
    fs[abi_encoder_spine_core_code_def] >>
  `abi_encoder_member_core_pre (at,av,sb,source_cap,d) (first,last,b,cap,limit_st)
    (ei,dst,src,start,end_st,out) initial` by fs[abi_encoder_member_core_pre_def] >>
  drule_all abi_encoder_member_source_core_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  drule_all abi_encoder_member_source_core_saved >> strip_tac >>
  qexists_tac `actual` >> fs[abi_encoder_member_core_post_def] >> metis_tac[]
QED

Theorem abi_encoder_dynamic_child_spine_reach:
  abi_encoder_correct ei /\ compile_abi_encode_child dst src ei T head_offset dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\
  head_offset+32 <= off /\ off+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < st.cs_next_id /\ lo <= site /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. mem_bytes_at (d+off) (LENGTH (enc at av)) t.vs_memory = enc at av /\
    mem_word_at (d+head_offset) t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off+LENGTH (enc at av)) /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_footprint_frame [(d+head_offset,32);(d+off,LENGTH (enc at av));(b,cap)] initial t /\
    abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_dynamic_child_context >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\ child_end.cs_next_var <= limit_st.cs_next_var /\
    first <= prepared.cs_next_id /\ child_end.cs_next_id <= last /\ site < last /\
    site < prepared.cs_next_id /\ st.cs_next_var <= prepared.cs_next_var /\
    st.cs_next_var <= child_end.cs_next_var` by decide_tac >>
  `eval_operand dst initial = SOME (n2w d) /\ abi_decoder_operand_live st.cs_next_var dst /\
    d+output_size < dimword (:256) /\ (d+output_size <= b \/ b+cap <= d)` by
    (qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
     simp_tac bool_ss [] >> metis_tac[]) >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `b+cap < dimword (:256)` by
    (qpat_assum `abi_decoder_budget _ _ _ _ initial`
       (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >> simp[]) >>
  `slot < dimword (:256) /\ d+head_offset < dimword (:256)` by decide_tac >>
  `abi_decoder_operand_live prepared.cs_next_var dyn_ptr /\
    abi_decoder_operand_live child_end.cs_next_var dyn_ptr` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `abi_encoder_spine_core_code func (ei,SND (SND ops),src,prepared,child_end,child_len)` by
    (simp_tac bool_ss [abi_encoder_spine_core_code_def] >> metis_tac[]) >>
  qabbrev_tac `Pre = \(e,dd,ss,p,en,op:operand) s.
    abi_encoder_correct e /\ abi_encoder_pre e at av p ss dd sb source_cap (d+off) b cap s /\
    abi_decoder_budget first last b cap s /\ first <= p.cs_next_id /\ en.cs_next_id <= last /\
    en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
    abi_decoder_operand_live p.cs_next_var (FST ops) /\
    abi_decoder_operand_live p.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live p.cs_next_var dyn_ptr /\
    eval_operand (FST ops) s = SOME (n2w (d+head_offset)) /\
    eval_operand (FST (SND ops)) s = SOME (n2w off) /\
    eval_operand dyn_ptr s = SOME (n2w slot) /\ site < p.cs_next_id /\
    FLOOKUP s.vs_allocas site = SOME (slot,32) /\
    ~s.vs_halted /\ s.vs_current_bb = p.cs_current_bb /\ s.vs_inst_idx = LENGTH p.cs_current_insts` >>
  qabbrev_tac `Post = \(e:abi_enc_info,dd:operand,ss:operand,p,en,op) s t.
    mem_bytes_at (d+off) (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand op t = SOME (n2w (LENGTH (enc at av))) /\
    abi_decoder_effect first last p.cs_next_id en.cs_next_id p.cs_next_var
      limit_st (d+off) (LENGTH (enc at av)) b cap s t /\
    eval_operand (FST ops) t = SOME (n2w (d+head_offset)) /\
    eval_operand (FST (SND ops)) t = SOME (n2w off) /\
    eval_operand dyn_ptr t = SOME (n2w slot) /\ FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    mload slot t = mload slot s /\ fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func s t` >>
  `!c r. abi_encoder_spine_core_code func c /\ Pre c r ==>
    ?u. Post c r u /\ Post c r u` by
    (rpt gen_tac >> PairCases_on `c` >>
     simp_tac (srw_ss()) [Abbr `Pre`, Abbr `Post`, abi_encoder_spine_core_code_def] >>
     rpt strip_tac >> irule abi_encoder_source_dynamic_core_run >>
     goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac []) >>
  `!r. abi_encoder_member_phase_raw st prepared initial r ==>
    Pre (ei,SND (SND ops),src,prepared,child_end,child_len) r` by
    (rpt strip_tac >> drule_all abi_encoder_source_dynamic_prepare_transport >> strip_tac >>
     fs[Abbr `Pre`, abi_decoder_address_frame_def]) >>
  `!r u. Post (ei,SND (SND ops),src,prepared,child_end,child_len) r u ==>
    abi_encoder_spine_cursor_input (FST ops,dyn_ptr,FST (SND ops),child_len,child_end,end_st,limit_st) u` by
    (simp_tac (srw_ss()) [Abbr `Post`, abi_encoder_spine_cursor_input_def] >>
     rpt strip_tac >> qexistsl_tac [`d+head_offset`, `slot`, `off`, `LENGTH (enc at av)`] >>
     asm_rewrite_tac []) >>
  drule_all abi_encoder_spine_dynamic_run >> strip_tac >>
  qpat_x_assum `Post _ _ _` mp_tac >>
  simp_tac (srw_ss()) [Abbr `Post`] >> strip_tac >>
  rename1 `abi_decode_sim ctx func r u` >>
  qpat_x_assum `abi_encoder_spine_child _ _ _ _` kall_tac >>
  qpat_x_assum `!c rr. _` kall_tac >>
  qpat_x_assum `!rr. abi_encoder_member_phase_raw _ _ _ _ ==> _` kall_tac >>
  qpat_x_assum `!rr uu. _` kall_tac >>
  qpat_x_assum `Abbrev (Pre = _)` kall_tac >>
  drule_all abi_encoder_source_dynamic_prepare_transport >> strip_tac >>
  `d <= d+head_offset /\ d+head_offset+32 <= d+off /\ site < end_st.cs_next_id` by decide_tac >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o cj 10 o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  drule_all (Q.INST [`lo` |-> `lo:num`, `hi` |-> `end_st.cs_next_id`]
    abi_encoder_source_dynamic_finish_transport) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule abi_encode_child_prefix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st prepared)` by fs[EVERY_CONJ] >>
  drule_all abi_encoder_member_phase_extend_sim >>
  disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (assume_tac o MATCH_MP abi_encoder_extend_sim_sim) >>
  `abi_decode_footprint_frame [(d+off,LENGTH (enc at av));(b,cap)] r u` by
    (qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ r u`
       (mp_tac o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
     simp_tac bool_ss [] >> metis_tac[]) >>
  drule_all abi_encoder_dynamic_child_frame >> disch_tac >>
  `lo <= prepared.cs_next_id /\ child_end.cs_next_id <= end_st.cs_next_id /\
    d <= d+off /\ (d+off)+LENGTH (enc at av) <= d+output_size` by decide_tac >>
  drule_all abi_encoder_child_compose >> strip_tac >>
  qexists_tac `t` >> asm_simp_tac bool_ss []
QED

val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print ("ENCODER_SOURCE_ADAPTER_AUDIT_OK " ^ name ^ "\n")
    else raise Fail ("source adapter admission dependency: " ^ name)
  end)
  [("dynamic_prepare_transport", abi_encoder_source_dynamic_prepare_transport),
   ("dynamic_core_run", abi_encoder_source_dynamic_core_run),
   ("dynamic_child_spine_reach", abi_encoder_dynamic_child_spine_reach)];
