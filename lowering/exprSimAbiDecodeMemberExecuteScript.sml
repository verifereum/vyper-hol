(* Member setup reaches a recursive child without changing allocation sites. *)
Theory exprSimAbiDecodeMemberExecute
Ancestors
  exprSimAbiDecodeMemberOutcome exprSimAbiDecodeSiteProvenance
  abiDecoderMemberSetup abiDecoderDynamicLoopSetup abiDecoderFiniteControl
  abiDecoderSequenceReach abiDecoderContract abiEncoder compileEnv emitHelper
  emitHelperProps exprLoweringProps venomState venomInst instIdxIndep
  abiDecoderSiteEffect abiDecoderBytestringOutcome actualDecoderSites
  abiValidMembers abiDecodeRanges vyperABI contractABI rich_list fragExec
  exprSimAbiDecodeChildBounds abiDecoderReentry abiValidAggregateHeads
  abiCanonicalHeadSize abiValidMember abiDecoderAppend abiDecoderCounters
  abiDecoderVarSequence abiDecoderVarExtend execEquivParamProps stateEquiv venomExecSemantics
  finite_map pred_set words list arithmetic

Theorem abi_decode_member_setup_reach:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,middle) /\
  eval_operand src s = SOME(n2w p) /\ eval_operand dst s = SOME(n2w d) /\
  (dyn ==> eval_operand base_op s = SOME(n2w B) /\
    abi_decode_load MLOAD (n2w(B+(p+ao)):bytes32) s = n2w delta /\
    p+delta < dimword(:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  decode_site_resources ctx func s /\
  fn_has_code st middle fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. Dreach ctx fn s t /\
    t.vs_current_bb = middle.cs_current_bb /\
    t.vs_inst_idx = LENGTH middle.cs_current_insts /\
    eval_operand (FST ops) t = SOME(n2w(p+if dyn then delta else ao)) /\
    eval_operand (SND ops) t = SOME(n2w(d+vo)) /\
    abi_decoder_operand_live middle.cs_next_var (FST ops) /\
    abi_decoder_operand_live middle.cs_next_var (SND ops) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    abi_decode_alloc_progress sites s t /\
    decode_site_effect ctx func st.cs_next_var writes s t /\ ~t.vs_halted
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_reentry >> strip_tac >>
  drule abi_decode_member_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st middle)` by fs[EVERY_MEM] >>
  `EVERY (\i. abi_bytes_opcode i.inst_opcode) (emitted_insts st middle)`
    by fs[EVERY_MEM] >>
  drule_all abi_bytes_sequence_static >> strip_tac >>
  `decode_site_resources ctx func t` by
    (irule decode_site_resources_fields >>
     qexists_tac `s` >> fs[abi_decoder_address_frame_def,
       venom_state_component_equality]) >>
  `decode_site_effect ctx func st.cs_next_var writes s t` by
    (simp[decode_site_effect_def, decode_memory_frame_def,
       abi_decoder_address_frame_def] >>
     fs[abi_decoder_address_frame_def, decode_static_frame_def,
        venom_state_component_equality]) >>
  qpat_x_assum `t = s with <|vs_vars := _; vs_memory := _|>` kall_tac >>
  drule_all abi_decoder_run_sequence_prefix >> strip_tac >>
  qexists_tac `t'` >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx,
      abi_decode_alloc_progress_def] >>
  conj_tac >- (irule Dreach_straight_prefix >> simp[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem abi_decode_member_setup_wrap_abort:
  abi_decode_member_setup dst src MLOAD base_op hi T ao vo st = (ops,middle) /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand src s = SOME(n2w p) /\ eval_operand base_op s = SOME(n2w B) /\
  eval_operand hi s = SOME(n2w H) /\ p+ao+32 <= H /\ B+H < dimword(:256) /\
  delta = w2n(abi_decode_load MLOAD (n2w(B+p+ao):bytes32) s) /\
  dimword(:256) <= p+delta /\ fresh_vars_wrt st s /\
  fn_has_code st middle fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. Dabort ctx fn s Revert_abort u
Proof
  strip_tac >> drule_all abi_decode_member_setup_revert >> strip_tac >>
  drule abi_decode_member_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st middle)` by fs[EVERY_MEM] >>
  drule_all abi_decoder_run_sequence_abort >> strip_tac >>
  qpat_x_assum `!ctx. _` (qspec_then `ctx` strip_assume_tac) >>
  simp[Dabort_def] >> qexistsl_tac [`t with vs_inst_idx := n`, `0`] >> simp[]
QED

(* A recursive decoder keeps the ambient payload fixed.  Only its view changes:
   an inline child gets exactly its static width, not the whole suffix. *)
Definition abi_decode_source_view_def:
  abi_decode_source_view at bs pos =
    if is_dynamic at then DROP pos bs
    else TAKE (static_length at) (DROP pos bs)
End

Theorem abi_decode_member_static_view:
  ~is_dynamic at ==>
  abi_decode_member_bytes at (DROP pos bs) (DROP ao (DROP pos bs)) =
    abi_decode_source_view at bs (pos+ao)
Proof
  simp[abi_decode_member_bytes_def, abi_decode_source_view_def,
       DROP_DROP_T, ADD_COMM]
QED

Theorem abi_decode_member_dynamic_view:
  is_dynamic at /\ delta = abi_head_word (DROP ao (DROP pos bs)) ==>
  abi_decode_member_bytes at (DROP pos bs) (DROP ao (DROP pos bs)) =
    abi_decode_source_view at bs (pos+delta)
Proof
  simp[abi_decode_member_bytes_def, abi_decode_source_view_def,
       DROP_DROP_T, ADD_COMM]
QED

Theorem abi_decode_member_contextual_view:
  (is_dynamic at ==> delta = abi_head_word (DROP ao (DROP pos bs))) ==>
  abi_decode_member_bytes at (DROP pos bs) (DROP ao (DROP pos bs)) =
    abi_decode_source_view at bs (pos + if is_dynamic at then delta else ao)
Proof
  Cases_on `is_dynamic at` >>
  simp[abi_decode_member_bytes_def, abi_decode_source_view_def,
       DROP_DROP_T, ADD_COMM]
QED

Theorem abi_decode_dynamic_empty_reject:
  is_dynamic at /\ (!elem. at <> Array (SOME 0) elem) ==>
  ~vyper_decode_valid_enc at ([]:byte list)
Proof
  rpt strip_tac >> drule_all abi_valid_dynamic_head_min >> simp[]
QED

Theorem abi_decode_member_wrap_source_reject:
  is_dynamic at /\ (!elem. at <> Array (SOME 0) elem) /\
  delta = abi_head_word (DROP ao (DROP pos bs)) /\
  LENGTH bs <= H /\ H < dimword(:256) /\
  dimword(:256) <= pos+delta ==>
  ~vyper_decode_valid_enc at
    (abi_decode_member_bytes at (DROP pos bs) (DROP ao (DROP pos bs)))
Proof
  strip_tac >>
  `LENGTH bs <= pos+delta` by decide_tac >>
  `DROP delta (DROP pos bs) = []` by
    (pure_rewrite_tac[DROP_EQ_NIL, LENGTH_DROP] >> decide_tac) >>
  `~vyper_decode_valid_enc at ([]:byte list)` by
    (irule abi_decode_dynamic_empty_reject >> simp[]) >>
  qpat_x_assum `delta = _` (fn th => rewrite_tac[abi_decode_member_bytes_def, GSYM th]) >>
  pure_asm_rewrite_tac[] >> simp[]
QED

Definition abi_decode_entry_def:
  abi_decode_entry st s <=>
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts
End

Definition abi_decode_code_context_def:
  abi_decode_code_context func fn st last <=>
    fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
    (!i. MEM i (fn_insts fn) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
      MEM i (fn_insts func)) /\
    (st.cs_blocks = last.cs_blocks \/ last.cs_current_insts <> [] \/
     !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
       phi_prefix_length bb.bb_instructions = 0)
End

Definition abi_decode_source_accepts_def:
  abi_decode_source_accepts env ty view v <=>
    vyper_decode_valid_enc (vyper_to_abi_type env ty) view /\
    abi_to_vyper env ty (dec (vyper_to_abi_type env ty) view) = SOME v
End

Definition abi_decode_context_pre_def:
  abi_decode_context_pre ctx func ce env ty tv limit_st next writes sites
    st dst src base_op hi B bs pos d s <=>
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    assignable_type env ty /\ abi_decode_bytes_widths env ty /\
    next <= st.cs_next_var /\ st.cs_next_var <= limit_st.cs_next_var /\
    EVERY (abi_decoder_operand_live st.cs_next_var) [dst;src;base_op;hi] /\
    base_op <> Lit 0w /\ hi <> Lit 0w /\
    eval_operand src s = SOME(n2w pos) /\ eval_operand dst s = SOME(n2w d) /\
    eval_operand base_op s = SOME(n2w B) /\
    eval_operand hi s = SOME(n2w(LENGTH bs)) /\
    pos < dimword(:256) /\ B+LENGTH bs < dimword(:256) /\
    d+type_memory_bytes ce ty < dimword(:256) /\
    (!clamp. type_to_abi_dec_info ce.ce_struct_fields ce ty = DecPrimWord clamp ==>
      pos+32 <= LENGTH bs) /\
    bs = mem_bytes_at B (LENGTH bs) s.vs_memory /\
    B+LENGTH bs <= s.vs_alloca_next /\
    abi_footprint_disjoint B (LENGTH bs) [(d,type_memory_bytes ce ty)] /\
    (!id b sz. id IN sites /\ FLOOKUP s.vs_allocas id = SOME(b,sz) ==>
      abi_footprint_disjoint B (LENGTH bs) [(b,sz)]) /\
    abi_decode_site_writes sites d (type_memory_bytes ce ty) s SUBSET writes /\
    (!a. B <= a /\ a < B+LENGTH bs ==> a NOTIN writes) /\
    decode_site_resources ctx func s /\ fn_inst_ids_distinct func /\
    fresh_vars_wrt limit_st s /\ abi_decode_entry st s
End

Definition abi_decode_context_result_def:
  abi_decode_context_result ctx func fn tv limit_st next writes sites last
    view env ty d s <=>
    (?t v. Dreach ctx fn s t /\ abi_decode_source_accepts env ty view v /\
      val_in_memory tv v d t.vs_memory /\ fresh_vars_wrt limit_st t /\
      decode_site_effect ctx func next writes s t /\
      abi_decode_alloc_progress sites s t /\ abi_decode_entry last t) \/
    (?u. Dabort ctx fn s Revert_abort u /\
      ~(?v. abi_decode_source_accepts env ty view v))
End

Definition abi_decode_child_contract_def:
  abi_decode_child_contract ce env ty tv <=>
    !ctx func fn limit_st next writes sites st last dst src base_op hi B bs pos d s.
    compile_abi_decode_to_buf dst src MLOAD base_op hi
      (type_to_abi_dec_info ce.ce_struct_fields ce ty) st = ((),last) /\
    abi_decode_code_context func fn st last /\
    last.cs_next_var <= limit_st.cs_next_var /\
    abi_decode_sites st.cs_next_id last.cs_next_id SUBSET sites /\
    abi_decode_context_pre ctx func ce env ty tv limit_st next writes sites
      st dst src base_op hi B bs pos d s ==>
    abi_decode_context_result ctx func fn tv limit_st next writes
      (abi_decode_sites st.cs_next_id last.cs_next_id) last
      (abi_decode_source_view (vyper_to_abi_type env ty) bs pos) env ty d s
End

Theorem abi_decode_entry_not_halted:
  abi_decode_entry st s ==> ~s.vs_halted
Proof
  simp[abi_decode_entry_def]
QED

Theorem abi_decode_source_accepts_unique:
  abi_decode_source_accepts env ty view v /\
  abi_decode_source_accepts env ty view w ==> v = w
Proof
  strip_tac >> gvs[abi_decode_source_accepts_def]
QED

Theorem abi_decode_context_reject:
  Dabort ctx fn s Revert_abort u /\
  ~vyper_decode_valid_enc (vyper_to_abi_type env ty) view ==>
  abi_decode_context_result ctx func fn tv limit_st next writes sites last
    view env ty d s
Proof
  simp[abi_decode_context_result_def, abi_decode_source_accepts_def] >>
  metis_tac[]
QED

Theorem abi_decode_context_result_prefix:
  Dreach ctx fn s t /\ decode_site_effect ctx func next writes s t /\
  abi_decode_alloc_progress sites s t /\ child_sites SUBSET sites /\
  abi_decode_context_result ctx func fn tv limit_st next writes child_sites last
    view env ty d t ==>
  abi_decode_context_result ctx func fn tv limit_st next writes sites last
    view env ty d s
Proof
  simp_tac bool_ss [abi_decode_context_result_def] >> strip_tac
  >- (disj1_tac >> qexistsl_tac [`t'`, `v`] >>
      `abi_decode_alloc_progress sites t t'` by
        (irule abi_decode_alloc_progress_widen >> metis_tac[]) >>
      conj_tac >- (irule Dreach_trans >> qexists_tac `t` >> simp[]) >>
      simp[] >> conj_tac
      >- metis_tac[decode_site_effect_trans, UNION_IDEMPOT] >>
      irule abi_decode_alloc_progress_trans >> qexists_tac `t` >> simp[]) >>
  disj2_tac >> metis_tac[Dreach_abort]
QED

Theorem abi_decode_code_context_after_setup:
  abi_decode_code_context func fn st last /\ cs_extends st middle /\
  cs_extends middle last /\ st.cs_blocks = middle.cs_blocks ==>
  abi_decode_code_context func fn middle last
Proof
  simp_tac bool_ss [abi_decode_code_context_def] >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >> gvs[]
QED

Definition abi_decode_member_pre_def:
  abi_decode_member_pre ctx func ce env ty tv limit_st next writes sites
    st dst src base_op hi B bs p d ao vo delta s <=>
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    assignable_type env ty /\ abi_decode_bytes_widths env ty /\
    next <= st.cs_next_var /\ st.cs_next_var <= limit_st.cs_next_var /\
    EVERY (abi_decoder_operand_live st.cs_next_var) [dst;src;base_op;hi] /\
    base_op <> Lit 0w /\ hi <> Lit 0w /\
    eval_operand src s = SOME(n2w p) /\ eval_operand dst s = SOME(n2w d) /\
    eval_operand base_op s = SOME(n2w B) /\
    eval_operand hi s = SOME(n2w(LENGTH bs)) /\
    p < dimword(:256) /\ B+LENGTH bs < dimword(:256) /\
    d+vo+type_memory_bytes ce ty < dimword(:256) /\
    (!clamp. type_to_abi_dec_info ce.ce_struct_fields ce ty = DecPrimWord clamp ==>
      p+ao+32 <= LENGTH bs) /\
    bs = mem_bytes_at B (LENGTH bs) s.vs_memory /\
    B+LENGTH bs <= s.vs_alloca_next /\
    abi_footprint_disjoint B (LENGTH bs) [(d+vo,type_memory_bytes ce ty)] /\
    (!id b sz. id IN sites /\ FLOOKUP s.vs_allocas id = SOME(b,sz) ==>
      abi_footprint_disjoint B (LENGTH bs) [(b,sz)]) /\
    abi_decode_site_writes sites (d+vo) (type_memory_bytes ce ty) s SUBSET writes /\
    (!a. B <= a /\ a < B+LENGTH bs ==> a NOTIN writes) /\
    decode_site_resources ctx func s /\ fn_inst_ids_distinct func /\
    fresh_vars_wrt limit_st s /\ abi_decode_entry st s /\
    (is_dynamic (vyper_to_abi_type env ty) ==> p+ao+32 <= LENGTH bs) /\
    (~is_dynamic (vyper_to_abi_type env ty) ==> p+ao < dimword(:256)) /\
    delta = abi_head_word (DROP ao (DROP p bs)) /\
    (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem)
End

Theorem abi_decode_member_child_pre:
  abi_decode_member_pre ctx func ce env ty tv limit_st next writes sites
    st dst src base_op hi B bs p d ao vo delta s /\
  abi_decode_member_setup dst src MLOAD base_op hi
    (is_dynamic (vyper_to_abi_type env ty)) ao vo st = (ops,middle) /\
  middle.cs_next_var <= limit_st.cs_next_var /\
  p+(if is_dynamic (vyper_to_abi_type env ty) then delta else ao) < dimword(:256) /\
  eval_operand (FST ops) t =
    SOME(n2w(p+if is_dynamic (vyper_to_abi_type env ty) then delta else ao)) /\
  eval_operand (SND ops) t = SOME(n2w(d+vo)) /\
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  abi_decoder_operand_live middle.cs_next_var (SND ops) /\
  fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
  decode_site_effect ctx func st.cs_next_var writes s t /\
  abi_decode_entry middle t ==>
  abi_decode_context_pre ctx func ce env ty tv limit_st next writes sites
    middle (SND ops) (FST ops) base_op hi B bs
    (p+if is_dynamic (vyper_to_abi_type env ty) then delta else ao) (d+vo) t
Proof
  simp_tac bool_ss [abi_decode_member_pre_def] >> strip_tac >>
  drule abi_decode_member_setup_shape >> strip_tac >>
  `st.cs_next_var <= middle.cs_next_var` by
    (drule abi_decode_member_setup_counters >> simp[]) >>
  `abi_decoder_operand_live middle.cs_next_var base_op /\
   abi_decoder_operand_live middle.cs_next_var hi` by
    (fs[] >> conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `decode_site_resources ctx func t` by
    (drule decode_site_effect_resources >> simp[]) >>
  simp_tac bool_ss [abi_decode_context_pre_def] >>
  fs[abi_decoder_address_frame_def, abi_decode_site_writes_def] >>
  conj_tac >- metis_tac[] >>
  reverse conj_tac >- metis_tac[] >>
  gen_tac >> strip_tac >> drule_all abi_decode_scalar_member_head >>
  strip_tac >> fs[]
QED

Theorem abi_decode_member_offset_load:
  bs = mem_bytes_at B (LENGTH bs) s.vs_memory /\
  p+ao+32 <= LENGTH bs /\ B+LENGTH bs < dimword(:256) ==>
  abi_decode_load MLOAD (n2w(B+p+ao):bytes32) s =
    n2w(abi_head_word (DROP ao (DROP p bs)))
Proof
  strip_tac >>
  `B+(p+ao) < dimword(:256)` by decide_tac >>
  `mem_bytes_at B (LENGTH bs) (abi_decode_source MLOAD s) = bs` by
    simp[abi_decode_source_def] >>
  `mem_bytes_at (B+(p+ao)) 32 (abi_decode_source MLOAD s) =
    TAKE 32 (DROP (p+ao) bs)` by
    (irule abi_decode_source_window >> simp[]) >>
  asm_simp_tac bool_ss [GSYM ADD_ASSOC, abi_decode_load_bytes] >>
  simp_tac (srw_ss()) [abi_head_word_bytes, DROP_DROP_T, ADD_COMM]
QED


(* The rejecting instruction in a member prefix is ASSERT; successful
   instructions already have a general variable-extension interface. *)
Theorem abi_decode_assert_extend_abort[local]:
  abi_decoder_vars_extend extras s t /\ inst.inst_opcode = ASSERT /\
  step_inst_base inst s = Abort Revert_abort u ==>
  ?v. step_inst_base inst t = Abort Revert_abort v
Proof
  strip_tac >>
  `abi_decoder_inputs_defined inst s` by
    (gvs[abi_decoder_inputs_defined_def, step_inst_base_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[eval_operand_def]) >>
  drule abi_decoder_vars_extend_inputs >> disch_then drule >> strip_tac >>
  mp_tac (Q.SPECL [`abi_decoder_vars_extend extras`,
    `\s t. vsr_term_frame s = vsr_term_frame t`, `0`, `ARB`, `inst`, `s`, `t`]
    step_inst_preserves_R) >>
  (impl_tac >- simp[abi_decoder_vars_extend_valid]) >>
  asm_simp_tac (srw_ss()) [step_inst_non_invoke] >>
  Cases_on `step_inst_base inst t` >> simp[lift_result_def] >> metis_tac[]
QED

Theorem abi_decode_member_abort_opcode[local]:
  MEM inst.inst_opcode [ADD; LT; ISZERO; MLOAD; ASSERT] /\
  step_inst_base inst s = Abort a u ==> inst.inst_opcode = ASSERT /\ a = Revert_abort
Proof
  strip_tac >> fs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_def] >>
  simp_tac (srw_ss()) [exec_pure1_def, exec_pure2_def, exec_read1_def,
      AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem abi_decode_member_sequence_extend_abort[local]:
  !insts extras s t u.
  EVERY (\i. MEM i.inst_opcode [ADD; LT; ISZERO; MLOAD; ASSERT]) insts /\
  abi_decoder_vars_extend extras s t /\
  run_inst_seq insts s = Abort Revert_abort u ==>
  ?v. run_inst_seq insts t = Abort Revert_abort v
Proof
  Induct >- simp[run_inst_seq_def] >>
  qx_gen_tac `inst` >> rpt gen_tac >>
  simp_tac bool_ss [EVERY_DEF, run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base inst s` >> gvs[]
  >>~- ([`step_inst_base inst s = OK v`],
      `abi_decoder_reentry_opcode inst.inst_opcode` by
        fs[abi_decoder_reentry_opcode_def] >>
      drule_all abi_decoder_step_vars_extend >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      qexists_tac `v''` >> simp[run_inst_seq_def]) >>
  `MEM inst.inst_opcode [ADD; LT; ISZERO; MLOAD; ASSERT]` by simp[] >>
  drule_all abi_decode_member_abort_opcode >> strip_tac >>
  drule_all abi_decode_assert_extend_abort >> strip_tac >>
  qexists_tac `v` >> simp[run_inst_seq_def]
QED

Theorem abi_decode_member_setup_reentry_opcodes[local]:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,middle) ==>
  EVERY (\i. MEM i.inst_opcode [ADD; LT; ISZERO; MLOAD; ASSERT])
    (emitted_insts st middle)
Proof
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  simp[abi_decode_member_setup_def, compile_getelemptr_abi_def, compile_abi_dec_addr_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_decode_member_setup_revert_reentry:
  abi_decode_member_setup dst src MLOAD base_op hi T ao vo st = (ops,middle) /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand src s = SOME(n2w p) /\ eval_operand base_op s = SOME(n2w B) /\
  eval_operand hi s = SOME(n2w H) /\ p+ao+32 <= H /\ B+H < dimword(:256) /\
  delta = w2n(abi_decode_load MLOAD (n2w(B+p+ao):bytes32) s) /\
  dimword(:256) <= p+delta /\
  EVERY (abi_decoder_operand_live st.cs_next_var) [src;dst;base_op;hi] /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st middle) s = Abort Revert_abort t
Proof
  strip_tac >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s)` by
    irule abi_decoder_prune_fresh >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w p) /\
   eval_operand base_op (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w B) /\
   eval_operand hi (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w H)` by
    (fs[] >> asm_simp_tac bool_ss [abi_decoder_prune_eval]) >>
  `delta = w2n(abi_decode_load MLOAD (n2w(B+p+ao):bytes32)
    (abi_decoder_prune_vars st.cs_next_var s))` by
    fs[abi_decode_load_def, abi_decode_source_def, abi_decoder_prune_vars_def, mload_def] >>
  drule_all abi_decode_member_setup_revert >> strip_tac >>
  `abi_decoder_vars_extend s.vs_vars (abi_decoder_prune_vars st.cs_next_var s) s` by
    irule abi_decoder_prune_extension >>
  drule abi_decode_member_setup_reentry_opcodes >> strip_tac >>
  drule_all abi_decode_member_sequence_extend_abort >> simp[]
QED

Theorem abi_decode_member_setup_wrap_abort_reentry:
  abi_decode_member_setup dst src MLOAD base_op hi T ao vo st = (ops,middle) /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand src s = SOME(n2w p) /\ eval_operand base_op s = SOME(n2w B) /\
  eval_operand hi s = SOME(n2w H) /\ p+ao+32 <= H /\ B+H < dimword(:256) /\
  delta = w2n(abi_decode_load MLOAD (n2w(B+p+ao):bytes32) s) /\
  dimword(:256) <= p+delta /\
  EVERY (abi_decoder_operand_live st.cs_next_var) [src;dst;base_op;hi] /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st middle fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. Dabort ctx fn s Revert_abort u
Proof
  strip_tac >> drule_all abi_decode_member_setup_revert_reentry >> strip_tac >>
  drule abi_decode_member_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st middle)` by fs[EVERY_MEM] >>
  drule_all abi_decoder_run_sequence_abort >> strip_tac >>
  qpat_x_assum `!ctx. _` (qspec_then `ctx` strip_assume_tac) >>
  simp[Dabort_def] >> qexistsl_tac [`t with vs_inst_idx := n`, `0`] >> simp[]
QED

Theorem abi_decode_member_conditional_outcome:
  abi_decode_child_contract ce env ty tv /\
  abi_decode_member_setup dst src MLOAD base_op hi
    (is_dynamic (vyper_to_abi_type env ty)) ao vo st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) MLOAD base_op hi
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) middle = ((),last) /\
  abi_decode_code_context func fn st last /\
  last.cs_next_var <= limit_st.cs_next_var /\
  abi_decode_sites st.cs_next_id last.cs_next_id SUBSET sites /\
  abi_decode_member_pre ctx func ce env ty tv limit_st next writes sites
    st dst src base_op hi B bs p d ao vo delta s ==>
  abi_decode_context_result ctx func fn tv limit_st next writes
    (abi_decode_sites st.cs_next_id last.cs_next_id) last
    (abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP p bs)
      (DROP ao (DROP p bs))) env ty (d+vo) s
Proof
  strip_tac >>
  drule abi_decode_member_setup_shape >> strip_tac >>
  `cs_extends st middle` by
    (irule cs_extends_same_block >> fs[inst_extends_def]) >>
  `cs_extends middle last` by (irule cs_extends_abi_decode >> metis_tac[]) >>
  `fn_has_code st middle fn /\ fn_has_code middle last fn` by
    (irule fn_has_code_split >> fs[abi_decode_code_context_def]) >>
  `middle.cs_next_var <= limit_st.cs_next_var` by
    (drule abi_decoder_variable_counter >> decide_tac) >>
  `abi_decode_code_context func fn middle last` by
    (irule abi_decode_code_context_after_setup >> metis_tac[]) >>
  `abi_decode_sites middle.cs_next_id last.cs_next_id SUBSET
     abi_decode_sites st.cs_next_id last.cs_next_id` by
    (`st.cs_next_id < middle.cs_next_id` by
       (drule abiDecoderMemberCodeTheory.abi_decode_member_setup_shape >>
        simp[abi_decode_source_opcode_def]) >>
     simp[abi_decode_sites_def, SUBSET_DEF] >> decide_tac) >>
  `is_dynamic (vyper_to_abi_type env ty) ==>
    abi_decode_load MLOAD (n2w(B+(p+ao)):bytes32) s = n2w delta` by
    (strip_tac >> qhdtm_assum `abi_decode_member_pre`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_member_pre_def]) >>
     pure_rewrite_tac[ADD_ASSOC] >> qpat_x_assum `delta = _` SUBST1_TAC >>
     irule abi_decode_member_offset_load >> metis_tac[]) >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty) /\ dimword(:256) <= p+delta`
  >- (qhdtm_assum `abi_decode_member_pre`
        (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_member_pre_def]) >>
      `delta = w2n(abi_decode_load MLOAD (n2w(B+p+ao):bytes32) s)` by
        (fs[GSYM ADD_ASSOC] >>
         simp[abi_head_word_def, dec_number_def, dest_NumV_def, w2n_lt]) >>
      `?u. Dabort ctx fn s Revert_abort u` by
        (fs[abi_decode_entry_def] >>
         drule abi_decode_member_setup_wrap_abort_reentry >>
         disch_then irule >>
         simp[EVERY_DEF] >> conj_tac
         >- (qexistsl_tac [`B`, `LENGTH bs`, `p`] >>
             simp[AC ADD_ASSOC ADD_COMM]) >>
         qexists_tac `limit_st` >> simp[]) >>
      `~vyper_decode_valid_enc (vyper_to_abi_type env ty)
        (abi_decode_member_bytes (vyper_to_abi_type env ty)
          (DROP p bs) (DROP ao (DROP p bs)))` by
        (irule abi_decode_member_wrap_source_reject >>
         simp[] >> qexists_tac `LENGTH bs` >> simp[] >> decide_tac) >>
      simp[abi_decode_context_result_def, abi_decode_source_accepts_def] >>
      metis_tac[]) >>
  qhdtm_assum `abi_decode_member_pre`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_member_pre_def]) >>
  `p+(if is_dynamic (vyper_to_abi_type env ty) then delta else ao) < dimword(:256)` by
    (Cases_on `is_dynamic (vyper_to_abi_type env ty)` >> fs[] >> decide_tac) >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst /\
   abi_decoder_operand_live st.cs_next_var base_op` by fs[] >>
  `is_dynamic (vyper_to_abi_type env ty) ==>
     eval_operand base_op s = SOME(n2w B) /\
     abi_decode_load MLOAD (n2w(B+(p+ao)):bytes32) s = n2w delta /\
     p+delta < dimword(:256)` by (strip_tac >> fs[] >> decide_tac) >>
  qhdtm_assum `abi_decode_entry` (strip_assume_tac o REWRITE_RULE [abi_decode_entry_def]) >>
  drule_all abi_decode_member_setup_reach >>
  disch_then (qspecl_then [`writes`, `abi_decode_sites st.cs_next_id last.cs_next_id`]
    strip_assume_tac) >>
  `abi_decode_entry middle t` by simp[abi_decode_entry_def] >>
  drule_all abi_decode_member_child_pre >> strip_tac >>
  `abi_decode_sites middle.cs_next_id last.cs_next_id SUBSET sites` by
    metis_tac[SUBSET_TRANS] >>
  qhdtm_x_assum `abi_decode_child_contract`
    (assume_tac o PURE_REWRITE_RULE [abi_decode_child_contract_def]) >>
  first_x_assum drule_all >> strip_tac >>
  `decode_site_effect ctx func next writes s t` by
    (irule decode_site_effect_threshold >> metis_tac[]) >>
  `abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP p bs)
      (DROP ao (DROP p bs)) =
    abi_decode_source_view (vyper_to_abi_type env ty) bs
      (p+if is_dynamic (vyper_to_abi_type env ty) then delta else ao)` by
    (irule abi_decode_member_contextual_view >> simp[]) >>
  qpat_x_assum `abi_decode_member_bytes _ _ _ = _` SUBST1_TAC >>
  drule_all abi_decode_context_result_prefix >> simp[]
QED
