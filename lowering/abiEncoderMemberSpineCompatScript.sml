(* Contract interpretations of the concrete member certificates. *)
Theory abiEncoderMemberSpineCompat
Ancestors
  abiEncoderMemberSpine abiEncoderMemberSourcePhase abiEncoderCorrect
  abiScratchEncoderContract abiEncoderSharedContract abiDecoderAllocation
  abiDecoderFrame abiDecoderContract fragExec compileEnv venomState words list
  abiEncoderChildInputs abiEncoderMemberPhaseRaw abiEncoderAddressReach
  abiEncoderMemberPhaseExec abiEncoderOpenInputFrame abiEncoderArrayFrame
  abiDecoderFootprint abiDecoderReentry emitHelperProps
  abiDecoderArrayInitExec abiDecoderDynamicLoopSetup
  abiEncoderMemberPhaseEffect abiScratchAfterAddress abiEncoderRegisteredEffect
  abiEncoderExtendSim pred_set venomInst abiEncoderChildCode abiEncoderChildPrefix
  abiScratchEffect abiScratchFootprint abiEncoderDynamic abiDecoderEffect
  abiEncoderResultLive abiEncoderCounters
  abiEncoderChildSuffix valueEncoding abiEncoderChildSuffixReach abiScratchChild

Definition abi_encoder_spine_source_pre_def:
  abi_encoder_spine_source_pre (at,av,sb,source_cap,d)
    (first,last,b,cap,limit_st) (ei,dst,src,st,en,out) s <=>
    abi_encoder_correct ei /\
    abi_encoder_pre ei at av st src dst sb source_cap d b cap s /\
    abi_decoder_budget first last b cap s /\
    first <= st.cs_next_id /\ en.cs_next_id <= last /\
    en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts
End

Definition abi_encoder_spine_source_post_def:
  abi_encoder_spine_source_post (ctx,func) (at,av,sb,source_cap,d)
    (first,last,b,cap,limit_st) (ei,dst,src,st,en,out) s t <=>
    mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_decoder_effect first last st.cs_next_id en.cs_next_id st.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap s t /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func s t
End

Theorem abi_encoder_spine_source_core_run:
  abi_encoder_spine_core_code func c /\
  abi_encoder_spine_source_pre value resources c s ==>
  ?t. abi_encoder_spine_source_post (ctx,func) value resources c s t
Proof
  PairCases_on `c` >> PairCases_on `value` >> PairCases_on `resources` >>
  simp_tac bool_ss [abi_encoder_spine_core_code_def,
    abi_encoder_spine_source_pre_def, abi_encoder_spine_source_post_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_correct_run >> simp[]
QED

Theorem abi_encoder_spine_static_source_pre:
  emit_op ADD [dst;Lit (n2w ho)] st = (head,p) /\
  abi_encoder_correct ei /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  ho+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\
  first <= p.cs_next_id /\ en.cs_next_id <= last /\
  p.cs_next_var <= limit_st.cs_next_var /\ en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  abi_encoder_member_phase_raw st p initial ready ==>
  abi_encoder_spine_source_pre (at,av,sb,source_cap,d+ho)
    (first,last,b,cap,limit_st) (ei,head,src,p,en,out) ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_member_static_place_raw_transport >> strip_tac >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_encoder_buffer_pre_def] >>
  `eval_operand (Lit (n2w ho)) initial = SOME (n2w ho)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_transport)) >>
  strip_tac >> drule abi_encoder_emit_address_shape >> strip_tac >>
  `abi_decoder_budget first last b cap ready` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `ready:venom_state`]
       abi_decoder_budget_transport) >>
     fs[abi_decoder_address_frame_def]) >>
  simp[abi_encoder_spine_source_pre_def]
QED

Theorem abi_encoder_spine_static_source:
  emit_op ADD [dst;Lit (n2w ho)] st = (head,p) /\
  abi_encoder_spine_core_code func (ei,head,src,p,en,out) /\
  abi_encoder_correct ei /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  ho+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\
  first <= p.cs_next_id /\ en.cs_next_id <= last /\
  p.cs_next_var <= limit_st.cs_next_var /\ en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb ==>
  ?ready actual.
    abi_encoder_spine_child
      (abi_encoder_spine_source_post (ctx,func) (at,av,sb,source_cap,d+ho)
        (first,last,b,cap,limit_st))
      (ei,F,dst,src,ho,dp,st,en,out) initial actual /\
    abi_encoder_member_phase_raw st p initial ready /\
    abi_encoder_spine_source_post (ctx,func) (at,av,sb,source_cap,d+ho)
      (first,last,b,cap,limit_st) (ei,head,src,p,en,out) ready actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  irule abi_encoder_spine_static_run >>
  conj_tac >- fs[abi_encoder_buffer_pre_def] >>
  conj_tac >- asm_rewrite_tac [] >>
  conj_tac
  >- (qexistsl_tac [`abi_encoder_spine_source_pre (at,av,sb,source_cap,d+ho)
          (first,last,b,cap,limit_st)`, `func`] >>
      asm_rewrite_tac [] >> conj_tac
      >- (rpt strip_tac >> drule_all abi_encoder_spine_source_core_run >> simp[]) >>
      rpt strip_tac >> irule abi_encoder_spine_static_source_pre >>
      asm_rewrite_tac [] >> qexistsl_tac [`dst`, `initial`, `output_size`, `st`] >> asm_rewrite_tac []) >>
  qexists_tac `limit_st` >> asm_rewrite_tac []
QED

val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print ("ENCODER_SPINE_COMPAT_AUDIT_OK " ^ name ^ "\n")
    else raise Fail ("encoder spine compatibility admission dependency: " ^ name)
  end)
  [("source_core_run", abi_encoder_spine_source_core_run),
   ("static_source_pre", abi_encoder_spine_static_source_pre),
   ("static_source", abi_encoder_spine_static_source)];

Definition abi_encoder_spine_scratch_pre_def:
  abi_encoder_spine_scratch_pre (at,av,sb,source_cap,d)
    (first,last,b,cap,limit_st) (ei,dst,src,st,en,out) s <=>
    abi_scratch_encoder ei /\
    abi_scratch_input ei at av st src dst sb source_cap d (LENGTH (enc at av))
      first last b cap s /\
    abi_decoder_budget first last b cap s /\
    first <= st.cs_next_id /\ en.cs_next_id <= last /\
    en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts
End

Definition abi_encoder_spine_scratch_post_def:
  abi_encoder_spine_scratch_post (ctx,func) (at,av,sb,source_cap,d)
    (first,last,b,cap,limit_st) (ei,dst,src,st,en,out) s t <=>
    mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_scratch_effect first last st.cs_next_id en.cs_next_id st.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap s t /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func s t
End

Theorem abi_encoder_spine_scratch_core_run:
  abi_encoder_spine_core_code func c /\
  abi_encoder_spine_scratch_pre value resources c s ==>
  ?t. abi_encoder_spine_scratch_post (ctx,func) value resources c s t
Proof
  PairCases_on `c` >> PairCases_on `value` >> PairCases_on `resources` >>
  simp_tac bool_ss [abi_encoder_spine_core_code_def,
    abi_encoder_spine_scratch_pre_def, abi_encoder_spine_scratch_post_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_scratch_encoder _`
    (mp_tac o PURE_REWRITE_RULE [abi_scratch_encoder_def]) >>
  metis_tac[]
QED

Theorem abi_encoder_spine_static_scratch_pre:
  emit_op ADD [dst;Lit (n2w ho)] st = (head,p) /\
  abi_scratch_encoder ei /\
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  ho+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\
  first <= p.cs_next_id /\ en.cs_next_id <= last /\
  p.cs_next_var <= limit_st.cs_next_var /\ en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  abi_encoder_member_phase_raw st p initial ready ==>
  abi_encoder_spine_scratch_pre (at,av,sb,source_cap,d+ho)
    (first,last,b,cap,limit_st) (ei,head,src,p,en,out) ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_member_static_place_raw_transport >> strip_tac >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_scratch_input_def] >>
  `eval_operand (Lit (n2w ho)) initial = SOME (n2w ho)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_transport)) >>
  strip_tac >> drule abi_encoder_emit_address_shape >> strip_tac >>
  `abi_decoder_budget first last b cap ready` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `ready:venom_state`]
       abi_decoder_budget_transport) >> fs[abi_decoder_address_frame_def]) >>
  simp[abi_encoder_spine_scratch_pre_def]
QED

Theorem abi_encoder_spine_static_scratch:
  emit_op ADD [dst;Lit (n2w ho)] st = (head,p) /\
  abi_encoder_spine_core_code func (ei,head,src,p,en,out) /\
  abi_scratch_encoder ei /\
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  ho+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\
  first <= p.cs_next_id /\ en.cs_next_id <= last /\
  p.cs_next_var <= limit_st.cs_next_var /\ en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb ==>
  ?ready actual.
    abi_encoder_spine_child
      (abi_encoder_spine_scratch_post (ctx,func) (at,av,sb,source_cap,d+ho)
        (first,last,b,cap,limit_st))
      (ei,F,dst,src,ho,dp,st,en,out) initial actual /\
    abi_encoder_member_phase_raw st p initial ready /\
    abi_encoder_spine_scratch_post (ctx,func) (at,av,sb,source_cap,d+ho)
      (first,last,b,cap,limit_st) (ei,head,src,p,en,out) ready actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  irule abi_encoder_spine_static_run >>
  conj_tac >- fs[abi_scratch_input_def] >>
  conj_tac >- asm_rewrite_tac [] >>
  conj_tac
  >- (qexistsl_tac [`abi_encoder_spine_scratch_pre (at,av,sb,source_cap,d+ho)
          (first,last,b,cap,limit_st)`, `func`] >>
      asm_rewrite_tac [] >> conj_tac
      >- (rpt strip_tac >> drule_all abi_encoder_spine_scratch_core_run >> simp[]) >>
      rpt strip_tac >> irule abi_encoder_spine_static_scratch_pre >>
      asm_rewrite_tac [] >>
      qexistsl_tac [`dst`, `initial`, `output_size`, `st`] >> asm_rewrite_tac []) >>
  qexists_tac `limit_st` >> asm_rewrite_tac []
QED

val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print ("ENCODER_SPINE_COMPAT_AUDIT_OK " ^ name ^ "\n")
    else raise Fail ("encoder spine compatibility admission dependency: " ^ name)
  end)
  [("scratch_core_run", abi_encoder_spine_scratch_core_run),
   ("static_scratch_pre", abi_encoder_spine_static_scratch_pre),
   ("static_scratch", abi_encoder_spine_static_scratch)];

(* The rich runner consumes open input and the shared child contract directly.
   In particular it is not obtained by strengthening either weak runner. *)
Definition abi_encoder_spine_shared_pre_def:
  abi_encoder_spine_shared_pre (at,av,sb,source_cap,d)
    (first,last,b,cap,limit_st) (ei,dst,src,st,en,out) s <=>
    abi_encoder_shared ei /\
    abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap)
      (d,LENGTH (enc at av)) (first,last,b,cap) s /\
    abi_decoder_budget first last b cap s /\
    first <= st.cs_next_id /\ en.cs_next_id <= last /\
    en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts
End

Definition abi_encoder_spine_shared_post_def:
  abi_encoder_spine_shared_post (ctx,func) (at,av,sb,source_cap,d)
    (first,last,b,cap,limit_st) (ei,dst,src,st,en,out) s t <=>
    abi_encoder_shared_endpoint (ctx,func) (st,en,out,limit_st)
      (first,last,b,cap) (at,av,d) s t
End

Theorem abi_encoder_spine_shared_core_run:
  abi_encoder_spine_core_code func c /\
  abi_encoder_spine_shared_pre value resources c s ==>
  ?t. abi_encoder_spine_shared_post (ctx,func) value resources c s t
Proof
  PairCases_on `c` >> PairCases_on `value` >> PairCases_on `resources` >>
  simp_tac bool_ss [abi_encoder_spine_core_code_def,
    abi_encoder_spine_shared_pre_def, abi_encoder_spine_shared_post_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_shared_run >> simp[]
QED

Theorem abi_encoder_spine_shared_input_address:
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap)
    (d,output_size) (first,last,b,cap) initial /\
  abi_decoder_address_frame st.cs_next_var initial actual /\
  st.cs_next_var <= prepared.cs_next_var /\
  abi_decoder_operand_live prepared.cs_next_var child_dst /\
  eval_operand child_dst actual = SOME (n2w (d+off)) /\
  off+LENGTH (enc at av) <= output_size ==>
  abi_encoder_shared_input (ei,at,av) (prepared,src,child_dst) (sb,source_cap)
    (d+off,LENGTH (enc at av)) (first,last,b,cap) actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_encoder_shared_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  `actual.vs_memory = initial.vs_memory /\
   actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next` by
    fs[abi_decoder_address_frame_def] >>
  `eval_operand src actual = SOME (n2w sb)` by fs[abi_decoder_address_frame_def] >>
  `abi_decoder_operand_live prepared.cs_next_var src` by
    (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual =
   abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial` by
    simp[abi_decoder_child_scratch_def] >>
  `abi_footprint_disjoint (d+off) (LENGTH (enc at av))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    (irule abi_footprint_disjoint_subwindow >> goal_assum (drule_at Any) >> decide_tac) >>
  simp_tac bool_ss [abi_encoder_shared_input_def] >>
  asm_rewrite_tac [] >>
  full_simp_tac bool_ss [abi_encoder_zero_aware_separation] >> decide_tac
QED

Theorem abi_encoder_spine_static_shared_pre:
  emit_op ADD [dst;Lit (n2w ho)] st = (head,p) /\
  abi_encoder_shared ei /\
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap)
    (d,output_size) (first,last,b,cap) initial /\
  ho+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\
  first <= p.cs_next_id /\ en.cs_next_id <= last /\
  p.cs_next_var <= limit_st.cs_next_var /\ en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  abi_encoder_member_phase_raw st p initial ready ==>
  abi_encoder_spine_shared_pre (at,av,sb,source_cap,d+ho)
    (first,last,b,cap,limit_st) (ei,head,src,p,en,out) ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_encoder_shared_input_def] >>
  `eval_operand (Lit (n2w ho)) initial = SOME (n2w ho)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_transport)) >>
  strip_tac >> drule abi_encoder_emit_address_shape >> strip_tac >>
  drule abi_decoder_operand_live_emit >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `st.cs_next_var <= p.cs_next_var` by decide_tac >>
  `eval_operand head ready = SOME (n2w (d+ho))` by fs[word_add_n2w] >>
  drule_all abi_encoder_spine_shared_input_address >> disch_tac >>
  `abi_decoder_budget first last b cap ready` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `ready:venom_state`]
       abi_decoder_budget_transport) >> fs[abi_decoder_address_frame_def]) >>
  simp[abi_encoder_spine_shared_pre_def]
QED

val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print ("ENCODER_SPINE_COMPAT_AUDIT_OK " ^ name ^ "\n")
    else raise Fail ("encoder spine compatibility admission dependency: " ^ name)
  end)
  [("shared_core_run", abi_encoder_spine_shared_core_run),
   ("shared_input_address", abi_encoder_spine_shared_input_address),
   ("static_shared_pre", abi_encoder_spine_static_shared_pre)];

(* Reattach the real ADD endpoint, retaining the exact child output window. *)
Theorem abi_encoder_spine_static_shared_transport:
  emit_op ADD [dst;Lit (n2w ho)] st = (head,p) /\
  fn_has_code st p func /\
  eval_operand dst initial = SOME (n2w d) /\
  p.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_member_phase_raw st p initial ready /\
  abi_encoder_shared_endpoint (ctx,func) (p,en,out,limit_st)
    (first,last,b,cap) (at,av,d+ho) ready actual ==>
  abi_encoder_shared_endpoint (ctx,func) (st,en,out,limit_st)
    (first,last,b,cap) (at,av,d+ho) initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand (Lit (n2w ho)) initial = SOME (n2w ho)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_transport)) >>
  strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st p)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all abi_encoder_member_phase_extend_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `abi_encoder_registered_effect (abi_decoder_ids st.cs_next_id en.cs_next_id)
    [(d+ho,LENGTH (enc at av))] initial ready /\
   (alloca_inv initial ==> alloca_inv ready)` by
    (drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_registered)) >>
     simp[]) >>
  qpat_x_assum `abi_encoder_shared_endpoint _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_endpoint_def]) >>
  `abi_scratch_effect first last st.cs_next_id en.cs_next_id st.cs_next_var
    limit_st (d+ho) (LENGTH (enc at av)) b cap initial actual` by
    (irule abi_scratch_effect_after_address >>
     qexistsl_tac [`d+ho`, `en.cs_next_id`, `p.cs_next_id`, `p.cs_next_var`,
       `LENGTH (enc at av)`, `ready`] >> simp[]) >>
  `abi_encoder_registered_effect (abi_decoder_ids st.cs_next_id en.cs_next_id)
    [(d+ho,LENGTH (enc at av))] ready actual` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`abi_decoder_ids p.cs_next_id en.cs_next_id`,
       `[(d+ho,LENGTH (enc at av))]`] >>
     simp[abi_decoder_ids_def, SUBSET_DEF]) >>
  simp_tac bool_ss [abi_encoder_shared_endpoint_def] >>
  asm_rewrite_tac [] >> rpt conj_tac
  >- (irule abi_encoder_registered_effect_trans >> qexists_tac `ready` >> simp[])
  >- metis_tac[] >>
  irule abi_encoder_extend_sim_trans >> qexists_tac `ready` >> simp[]
QED

Theorem abi_encoder_spine_static_shared:
  emit_op ADD [dst;Lit (n2w ho)] st = (head,p) /\
  fn_has_code st p func /\
  abi_encoder_spine_core_code func (ei,head,src,p,en,out) /\
  abi_encoder_shared ei /\
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap)
    (d,output_size) (first,last,b,cap) initial /\
  ho+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\
  first <= p.cs_next_id /\ en.cs_next_id <= last /\
  p.cs_next_var <= limit_st.cs_next_var /\ en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready actual.
    abi_encoder_spine_child
      (abi_encoder_spine_shared_post (ctx,func) (at,av,sb,source_cap,d+ho)
        (first,last,b,cap,limit_st))
      (ei,F,dst,src,ho,dp,st,en,out) initial actual /\
    abi_encoder_member_phase_raw st p initial ready /\
    abi_encoder_spine_shared_post (ctx,func) (at,av,sb,source_cap,d+ho)
      (first,last,b,cap,limit_st) (ei,head,src,p,en,out) ready actual /\
    abi_encoder_shared_endpoint (ctx,func) (st,en,out,limit_st)
      (first,last,b,cap) (at,av,d+ho) initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `?ready actual.
    abi_encoder_spine_child
      (abi_encoder_spine_shared_post (ctx,func) (at,av,sb,source_cap,d+ho)
        (first,last,b,cap,limit_st))
      (ei,F,dst,src,ho,dp,st,en,out) initial actual /\
    abi_encoder_member_phase_raw st p initial ready /\
    abi_encoder_spine_shared_post (ctx,func) (at,av,sb,source_cap,d+ho)
      (first,last,b,cap,limit_st) (ei,head,src,p,en,out) ready actual` by
    (irule abi_encoder_spine_static_run >>
     conj_tac >- fs[abi_encoder_shared_input_def] >>
     conj_tac >- asm_rewrite_tac [] >>
     conj_tac
     >- (qexistsl_tac [`abi_encoder_spine_shared_pre (at,av,sb,source_cap,d+ho)
             (first,last,b,cap,limit_st)`, `func`] >>
         asm_rewrite_tac [] >> conj_tac
         >- (rpt strip_tac >> drule_all abi_encoder_spine_shared_core_run >> simp[]) >>
         rpt strip_tac >> irule abi_encoder_spine_static_shared_pre >>
         asm_rewrite_tac [] >>
         qexistsl_tac [`dst`, `initial`, `output_size`, `st`] >> asm_rewrite_tac []) >>
     qexists_tac `limit_st` >> asm_rewrite_tac []) >>
  qexistsl_tac [`ready`, `actual`] >> asm_rewrite_tac [] >>
  irule abi_encoder_spine_static_shared_transport >>
  asm_rewrite_tac [] >> qexistsl_tac [`dst`, `head`, `p`, `ready`] >>
  fs[abi_encoder_shared_input_def, abi_encoder_spine_shared_post_def]
QED

val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print ("ENCODER_SPINE_COMPAT_AUDIT_OK " ^ name ^ "\n")
    else raise Fail ("encoder spine compatibility admission dependency: " ^ name)
  end)
  [("static_shared_transport", abi_encoder_spine_static_shared_transport),
   ("static_shared", abi_encoder_spine_static_shared)];

Theorem abi_encoder_spine_dynamic_shared_pre:
  abi_encode_child_prefix dst ho dp st = (ops,p) /\
  abi_encoder_shared ei /\
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap)
    (d,output_size) (first,last,b,cap) initial /\
  eval_operand dp initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dp /\
  off+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\
  first <= p.cs_next_id /\ ce.cs_next_id <= last /\
  p.cs_next_var <= limit_st.cs_next_var /\ ce.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  abi_encoder_member_phase_raw st p initial ready ==>
  abi_encoder_spine_shared_pre (at,av,sb,source_cap,d+off)
    (first,last,b,cap,limit_st) (ei,SND (SND ops),src,p,ce,len) ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand dst initial = SOME (n2w d) /\
   abi_decoder_operand_live st.cs_next_var dst` by fs[abi_encoder_shared_input_def] >>
  drule_all abi_encoder_member_prefix_transport >> strip_tac >>
  drule_all abi_encoder_member_prefix_control >> strip_tac >>
  drule abi_encode_child_prefix_shape >> strip_tac >>
  drule abi_encode_child_prefix_live >> strip_tac >>
  `st.cs_next_var <= p.cs_next_var` by decide_tac >>
  drule_all abi_encoder_spine_shared_input_address >> disch_tac >>
  `abi_decoder_budget first last b cap ready` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `ready:venom_state`]
       abi_decoder_budget_transport) >> fs[abi_decoder_address_frame_def]) >>
  simp[abi_encoder_spine_shared_pre_def]
QED

Theorem abi_encoder_spine_dynamic_shared_cursor:
  abi_encode_child_prefix dst ho dp st = (ops,p) /\
  abi_encoder_spine_core_code func (ei,SND (SND ops),src,p,ce,len) /\
  eval_operand dst initial = SOME (n2w d) /\ eval_operand dp initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\ d+ho < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dp /\
  p.cs_next_var <= limit_st.cs_next_var /\ en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st p initial ready /\
  abi_encoder_shared_endpoint (ctx,func) (p,ce,len,limit_st)
    (first,last,b,cap) (at,av,d+off) ready encoded ==>
  abi_encoder_spine_cursor_input (FST ops,dp,FST (SND ops),len,ce,en,limit_st) encoded
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_member_prefix_transport >> strip_tac >>
  drule abi_encode_child_prefix_live >> strip_tac >>
  drule abi_encode_child_prefix_shape >> strip_tac >>
  `abi_decoder_operand_live p.cs_next_var dp` by
    (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand dp ready = SOME (n2w slot)` by fs[abi_decoder_address_frame_def] >>
  drule abi_encoder_shared_endpoint_scratch >> disch_tac >>
  `eval_operand (FST ops) encoded = SOME (n2w (d+ho))` by
    (metis_tac[abi_scratch_effect_operand]) >>
  `eval_operand (FST (SND ops)) encoded = SOME (n2w off)` by
    (metis_tac[abi_scratch_effect_operand]) >>
  `eval_operand dp encoded = SOME (n2w slot)` by
    (drule_all (Q.INST [`op` |-> `dp`] abi_scratch_effect_operand) >> simp[]) >>
  `p.cs_next_var <= ce.cs_next_var` by
    (fs[abi_encoder_spine_core_code_def] >> drule abi_encoder_counters >> simp[]) >>
  `abi_decoder_operand_live ce.cs_next_var dp` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `p.cs_next_var` >> simp[]) >>
  `abi_decoder_operand_live ce.cs_next_var len` by
    (fs[abi_encoder_spine_core_code_def] >> drule abi_encode_result_live >> simp[]) >>
  simp_tac bool_ss [abi_encoder_spine_cursor_input_def] >>
  qexistsl_tac [`d+ho`, `slot`, `off`, `LENGTH (enc at av)`] >>
  fs[abi_encoder_shared_endpoint_def, abi_scratch_effect_def]
QED

val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print ("ENCODER_SPINE_COMPAT_AUDIT_OK " ^ name ^ "\n")
    else raise Fail ("encoder spine compatibility admission dependency: " ^ name)
  end)
  [("dynamic_shared_pre", abi_encoder_spine_dynamic_shared_pre),
   ("dynamic_shared_cursor", abi_encoder_spine_dynamic_shared_cursor)];

Definition abi_encoder_spine_dynamic_shared_post_def:
  abi_encoder_spine_dynamic_shared_post ambient value resources (st,p,initial) c ready encoded <=>
    abi_encoder_spine_shared_post ambient value resources c ready encoded /\
    abi_encoder_member_phase_raw st p initial ready
End

(* The shared dynamic core is run by the existing prefix/core/suffix engine.
   Its endpoint at encoded remains available for suffix effect composition. *)
Theorem abi_encoder_spine_dynamic_shared_run:
  abi_encode_child_prefix dst ho dp st = (ops,p) /\
  abi_encoder_spine_core_code func (ei,SND (SND ops),src,p,ce,len) /\
  abi_encode_child_suffix (FST ops) dp (FST (SND ops)) len ce = (out,en) /\
  abi_encoder_shared ei /\
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap)
    (d,output_size) (first,last,b,cap) initial /\
  eval_operand dp initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\ d+ho < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dp /\
  off+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\
  first <= p.cs_next_id /\ ce.cs_next_id <= last /\
  p.cs_next_var <= limit_st.cs_next_var /\ ce.cs_next_var <= limit_st.cs_next_var /\
  en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb ==>
  ?ready encoded actual.
    abi_encoder_spine_child
      (abi_encoder_spine_shared_post (ctx,func) (at,av,sb,source_cap,d+off)
        (first,last,b,cap,limit_st))
      (ei,T,dst,src,ho,dp,st,en,out) initial actual /\
    abi_encoder_member_phase_raw st p initial ready /\
    abi_encoder_spine_dynamic_shared_post (ctx,func) (at,av,sb,source_cap,d+off)
      (first,last,b,cap,limit_st) (st,p,initial)
      (ei,SND (SND ops),src,p,ce,len) ready encoded /\
    abi_encoder_member_phase_raw ce en encoded actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  irule abi_encoder_spine_dynamic_run >>
  conj_tac >- (qexistsl_tac [`off`, `slot`] >> simp[]) >>
  conj_tac >- (qexists_tac `d` >> fs[abi_encoder_shared_input_def]) >>
  asm_rewrite_tac [] >>
  conj_tac >- fs[abi_encoder_shared_input_def] >>
  conj_tac
  >- (qexistsl_tac [`\c r. abi_encoder_spine_shared_pre (at,av,sb,source_cap,d+off)
          (first,last,b,cap,limit_st) c r /\ abi_encoder_member_phase_raw st p initial r`, `func`] >>
      asm_rewrite_tac [] >> conj_tac
      >- (rpt gen_tac >> simp_tac bool_ss [] >> strip_tac >>
          drule_all abi_encoder_spine_shared_core_run >>
          disch_then (qspec_then `ctx` strip_assume_tac) >>
          qexists_tac `t` >> simp[abi_encoder_spine_dynamic_shared_post_def]) >>
      rpt gen_tac >> disch_tac >> simp[] >>
      irule abi_encoder_spine_dynamic_shared_pre >>
      asm_rewrite_tac [] >> goal_assum (drule_at Any) >>
      qexistsl_tac [`dp`, `dst`, `ho`, `output_size`, `slot`] >> asm_rewrite_tac []) >>
  qexists_tac `limit_st` >> asm_rewrite_tac [] >>
  rpt gen_tac >> simp_tac bool_ss [abi_encoder_spine_dynamic_shared_post_def,
    abi_encoder_spine_shared_post_def] >> strip_tac >>
  irule abi_encoder_spine_dynamic_shared_cursor >>
  asm_rewrite_tac [] >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`dst`, `ei`, `ho`, `slot`, `src`] >>
  fs[abi_encoder_shared_input_def]
QED

val _ =
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag abi_encoder_spine_dynamic_shared_run) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print "ENCODER_SPINE_COMPAT_AUDIT_OK dynamic_shared_run\n"
    else raise Fail "encoder spine compatibility admission dependency: dynamic_shared_run"
  end;

(* Rich observations are transported to the actual suffix endpoint, not by
   asserting the unchanged child endpoint predicate there. *)
Theorem abi_encoder_spine_shared_suffix_observations:
  abi_encoder_shared_endpoint (ctx,func) (p,ce,len,limit_st)
    (first,last,b,cap) (at,av,q) ready encoded /\
  abi_encode_child_suffix head dp offset len ce = (out,en) /\
  eval_operand head encoded = SOME (n2w h) /\ eval_operand dp encoded = SOME (n2w slot) /\
  eval_operand offset encoded = SOME (n2w off) /\
  abi_decoder_operand_live ce.cs_next_var dp /\ abi_decoder_operand_live ce.cs_next_var len /\
  h < dimword (:256) /\ slot < dimword (:256) /\ en.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_member_phase_raw ce en encoded actual /\
  (LENGTH (enc at av) = 0 \/
    ((q+LENGTH (enc at av) <= h \/ h+32 <= q) /\
     (q+LENGTH (enc at av) <= slot \/ slot+32 <= q))) /\
  d <= h /\ h+32 <= d+extent /\ id IN ids /\
  FLOOKUP encoded.vs_allocas id = SOME (slot,32) ==>
  mem_bytes_at q (LENGTH (enc at av)) actual.vs_memory = enc at av /\
  eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
  abi_encoder_registered_effect ids [(d,extent)] encoded actual /\
  (alloca_inv ready ==> alloca_inv actual)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand len encoded = SOME (n2w (LENGTH (enc at av))) /\
   fresh_vars_wrt limit_st encoded /\
   (alloca_inv ready ==> alloca_inv encoded)` by
    fs[abi_encoder_shared_endpoint_def, abi_scratch_effect_def] >>
  drule_all abi_encoder_member_cursor_transport >> strip_tac >>
  drule_all abi_encoder_member_cursor_registered >> strip_tac >>
  asm_rewrite_tac [] >>
  Cases_on `LENGTH (enc at av) = 0`
  >- (gvs[LENGTH_NIL] >> simp[mem_bytes_at_def]) >>
  `mem_bytes_at q (LENGTH (enc at av)) actual.vs_memory =
   mem_bytes_at q (LENGTH (enc at av)) encoded.vs_memory` by
    (asm_rewrite_tac [] >> irule abi_encoder_child_suffix_preserves_tail >> gvs[]) >>
  metis_tac[abi_encoder_shared_endpoint_bytes]
QED

val _ =
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag abi_encoder_spine_shared_suffix_observations) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print "ENCODER_SPINE_COMPAT_AUDIT_OK shared_suffix_observations\n"
    else raise Fail "encoder spine compatibility admission dependency: shared_suffix_observations"
  end;

(* Reuse the precise scratch composition interface at the raw cursor endpoint. *)
Theorem abi_encoder_spine_cursor_post:
  abi_encode_child_suffix head dp offset len ce = (out,en) /\
  eval_operand head encoded = SOME (n2w h) /\ eval_operand dp encoded = SOME (n2w slot) /\
  eval_operand offset encoded = SOME (n2w off) /\ eval_operand len encoded = SOME (n2w n) /\
  abi_decoder_operand_live ce.cs_next_var dp /\ abi_decoder_operand_live ce.cs_next_var len /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st encoded /\
  abi_encoder_member_phase_raw ce en encoded actual ==>
  abi_encoder_child_suffix_post out ce limit_st h slot off n encoded actual
Proof
  strip_tac >> drule_all abi_encoder_member_cursor_transport >>
  simp[abi_encoder_child_suffix_post_def]
QED

Theorem abi_encoder_spine_dynamic_shared_scratch:
  abi_encoder_shared_endpoint (ctx,func) (p,ce,len,limit_st)
    (first,last,b,cap) (at,av,q) ready encoded /\
  abi_decoder_address_frame st.cs_next_var initial ready /\
  abi_encode_child_suffix head dp offset len ce = (out,en) /\
  eval_operand head encoded = SOME (n2w h) /\ eval_operand dp encoded = SOME (n2w slot) /\
  eval_operand offset encoded = SOME (n2w off) /\
  abi_decoder_operand_live ce.cs_next_var dp /\ abi_decoder_operand_live ce.cs_next_var len /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  en.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_member_phase_raw ce en encoded actual /\
  first <= st.cs_next_id /\ en.cs_next_id <= last /\
  st.cs_next_id <= p.cs_next_id /\ ce.cs_next_id <= en.cs_next_id /\
  st.cs_next_var <= p.cs_next_var /\ st.cs_next_var <= ce.cs_next_var /\
  site IN abi_decoder_ids st.cs_next_id en.cs_next_id /\
  FLOOKUP encoded.vs_allocas site = SOME (slot,32) /\
  d <= h /\ h+32 <= d+extent /\ d <= q /\ q+LENGTH (enc at av) <= d+extent ==>
  abi_scratch_effect first last st.cs_next_id en.cs_next_id st.cs_next_var
    limit_st d extent b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand len encoded = SOME (n2w (LENGTH (enc at av))) /\
   fresh_vars_wrt limit_st encoded` by
    fs[abi_encoder_shared_endpoint_def, abi_scratch_effect_def] >>
  drule_all abi_encoder_spine_cursor_post >> disch_tac >>
  drule abi_encoder_shared_endpoint_scratch >> disch_tac >>
  irule (cj 1 abi_scratch_child_effect) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `site` >> simp[]
QED

val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print ("ENCODER_SPINE_COMPAT_AUDIT_OK " ^ name ^ "\n")
    else raise Fail ("encoder spine compatibility admission dependency: " ^ name)
  end)
  [("cursor_post",abi_encoder_spine_cursor_post),
   ("dynamic_shared_scratch",abi_encoder_spine_dynamic_shared_scratch)];

Theorem abi_encoder_spine_prefix_extend_sim:
  abi_encode_child_prefix dst ho dp st = (ops,p) /\ fn_has_code st p func /\
  abi_encoder_member_phase_raw st p initial ready /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_extend_sim ctx func initial ready
Proof
  strip_tac >> drule abi_encode_child_prefix_shape >> strip_tac >>
  irule abi_encoder_member_phase_extend_sim >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  fs[EVERY_MEM]
QED

Theorem abi_encoder_spine_suffix_extend_sim:
  abi_encode_child_suffix head dp offset len ce = (out,en) /\ fn_has_code ce en func /\
  abi_encoder_member_phase_raw ce en encoded actual /\ ~encoded.vs_halted /\
  encoded.vs_current_bb = ce.cs_current_bb /\
  encoded.vs_inst_idx = LENGTH ce.cs_current_insts ==>
  abi_encoder_extend_sim ctx func encoded actual
Proof
  strip_tac >> drule abi_encode_child_suffix_shape >> strip_tac >>
  irule abi_encoder_member_phase_extend_sim >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  fs[EVERY_MEM]
QED

Theorem abi_encoder_spine_dynamic_shared_sim:
  abi_encode_child_prefix dst ho dp st = (ops,p) /\ fn_has_code st p func /\
  abi_encoder_member_phase_raw st p initial ready /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_shared_endpoint (ctx,func) (p,ce,len,limit_st)
    (first,last,b,cap) (at,av,q) ready encoded /\
  abi_encode_child_suffix head dp offset len ce = (out,en) /\ fn_has_code ce en func /\
  abi_encoder_member_phase_raw ce en encoded actual ==>
  abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_spine_prefix_extend_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `~encoded.vs_halted /\ encoded.vs_current_bb = ce.cs_current_bb /\
   encoded.vs_inst_idx = LENGTH ce.cs_current_insts /\
   abi_encoder_extend_sim ctx func ready encoded` by
    fs[abi_encoder_shared_endpoint_def] >>
  drule_all abi_encoder_spine_suffix_extend_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  irule abi_encoder_extend_sim_trans >> qexists_tac `ready` >> simp[] >>
  irule abi_encoder_extend_sim_trans >> qexists_tac `encoded` >> simp[]
QED

Theorem abi_encoder_spine_shared_registered_window:
  abi_encoder_shared_endpoint (ctx,func) (p,ce,len,limit_st)
    (first,last,b,cap) (at,av,q) ready encoded /\
  lo <= p.cs_next_id /\ ce.cs_next_id <= hi /\
  d <= q /\ q+LENGTH (enc at av) <= d+extent ==>
  abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,extent)] ready encoded
Proof
  strip_tac >>
  `abi_encoder_registered_effect (abi_decoder_ids p.cs_next_id ce.cs_next_id)
    [(q,LENGTH (enc at av))] ready encoded` by
    fs[abi_encoder_shared_endpoint_def] >>
  irule abi_encoder_registered_effect_enlarge >>
  goal_assum (drule_at Any) >>
  simp[SUBSET_DEF,abi_decoder_ids_def] >> conj_tac >> rpt strip_tac >> decide_tac
QED

val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print ("ENCODER_SPINE_COMPAT_AUDIT_OK " ^ name ^ "\n")
    else raise Fail ("encoder spine compatibility admission dependency: " ^ name)
  end)
  [("prefix_extend_sim",abi_encoder_spine_prefix_extend_sim),
   ("suffix_extend_sim",abi_encoder_spine_suffix_extend_sim),
   ("dynamic_shared_sim",abi_encoder_spine_dynamic_shared_sim),
   ("shared_registered_window",abi_encoder_spine_shared_registered_window)];

Theorem abi_encoder_spine_dynamic_shared_registered:
  abi_encode_child_prefix dst ho dp st = (ops,p) /\
  eval_operand dst initial = SOME (n2w d) /\ eval_operand dp initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dp /\
  p.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st p initial ready /\
  abi_encoder_shared_endpoint (ctx,func) (p,ce,len,limit_st)
    (first,last,b,cap) (at,av,q) ready encoded /\
  abi_encode_child_suffix head dp offset len ce = (out,en) /\
  eval_operand head encoded = SOME (n2w h) /\ eval_operand dp encoded = SOME (n2w slot) /\
  eval_operand offset encoded = SOME (n2w off) /\
  abi_decoder_operand_live ce.cs_next_var dp /\ abi_decoder_operand_live ce.cs_next_var len /\
  h < dimword (:256) /\ en.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_member_phase_raw ce en encoded actual /\
  st.cs_next_id <= p.cs_next_id /\ ce.cs_next_id <= en.cs_next_id /\
  d <= h /\ h+32 <= d+extent /\ d <= q /\ q+LENGTH (enc at av) <= d+extent /\
  site IN abi_decoder_ids st.cs_next_id en.cs_next_id /\
  FLOOKUP encoded.vs_allocas site = SOME (slot,32) ==>
  abi_encoder_registered_effect (abi_decoder_ids st.cs_next_id en.cs_next_id)
    [(d,extent)] initial actual /\ (alloca_inv initial ==> alloca_inv actual)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand len encoded = SOME (n2w (LENGTH (enc at av))) /\
   fresh_vars_wrt limit_st encoded /\ (alloca_inv ready ==> alloca_inv encoded)` by
    fs[abi_encoder_shared_endpoint_def, abi_scratch_effect_def] >>
  `abi_encoder_registered_effect (abi_decoder_ids st.cs_next_id en.cs_next_id)
    [(d,extent)] initial ready /\ (alloca_inv initial ==> alloca_inv ready)` by
    (drule_all abi_encoder_member_prefix_registered >> simp[]) >>
  `abi_encoder_registered_effect (abi_decoder_ids st.cs_next_id en.cs_next_id)
    [(d,extent)] ready encoded` by
    (drule_all abi_encoder_spine_shared_registered_window >> simp[]) >>
  `abi_encoder_registered_effect (abi_decoder_ids st.cs_next_id en.cs_next_id)
    [(d,extent)] encoded actual /\ (alloca_inv encoded ==> alloca_inv actual)` by
    (drule_all abi_encoder_member_cursor_registered >> simp[]) >>
  conj_tac >- (irule abi_encoder_registered_effect_trans >>
    qexists_tac `ready` >> simp[] >>
    irule abi_encoder_registered_effect_trans >> qexists_tac `encoded` >> simp[]) >>
  metis_tac[]
QED

val _ =
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag abi_encoder_spine_dynamic_shared_registered) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print "ENCODER_SPINE_COMPAT_AUDIT_OK dynamic_shared_registered\n"
    else raise Fail "encoder spine compatibility admission dependency: dynamic_shared_registered"
  end;

(* The enclosing ledger includes the parent cursor even when its allocation
   precedes the current member's instruction interval. *)
Theorem abi_encoder_spine_dynamic_shared_effects:
  abi_encode_child_prefix dst ho dp st = (ops,p) /\
  eval_operand dst initial = SOME (n2w d) /\ eval_operand dp initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dp /\
  p.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st p initial ready /\
  abi_decoder_address_frame next initial ready /\
  abi_encoder_shared_endpoint (ctx,func) (p,ce,len,limit_st)
    (first,last,b,cap) (at,av,q) ready encoded /\
  abi_encode_child_suffix head dp offset len ce = (out,en) /\
  eval_operand head encoded = SOME (n2w h) /\ eval_operand dp encoded = SOME (n2w slot) /\
  eval_operand offset encoded = SOME (n2w off) /\
  abi_decoder_operand_live ce.cs_next_var dp /\ abi_decoder_operand_live ce.cs_next_var len /\
  h < dimword (:256) /\ en.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_member_phase_raw ce en encoded actual /\
  first <= lo /\ hi <= last /\ lo <= p.cs_next_id /\ ce.cs_next_id <= hi /\
  next <= p.cs_next_var /\ next <= ce.cs_next_var /\
  site IN abi_decoder_ids lo hi /\ FLOOKUP encoded.vs_allocas site = SOME (slot,32) /\
  d <= h /\ h+32 <= d+extent /\ d <= q /\ q+LENGTH (enc at av) <= d+extent ==>
  abi_scratch_effect first last lo hi next limit_st d extent b cap initial actual /\
  abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,extent)] initial actual /\
  (alloca_inv initial ==> alloca_inv actual)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand len encoded = SOME (n2w (LENGTH (enc at av))) /\
   fresh_vars_wrt limit_st encoded /\ (alloca_inv ready ==> alloca_inv encoded)` by
    fs[abi_encoder_shared_endpoint_def, abi_scratch_effect_def] >>
  drule_all abi_encoder_spine_cursor_post >> disch_tac >>
  drule abi_encoder_shared_endpoint_scratch >> disch_tac >>
  conj_tac
  >- (irule (cj 1 abi_scratch_child_effect) >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
      qexists_tac `site` >> simp[]) >>
  `abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,extent)] initial ready /\
   (alloca_inv initial ==> alloca_inv ready)` by
    (drule_all abi_encoder_member_prefix_registered >> simp[]) >>
  `abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,extent)] ready encoded` by
    (drule_all abi_encoder_spine_shared_registered_window >> simp[]) >>
  `abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,extent)] encoded actual /\
   (alloca_inv encoded ==> alloca_inv actual)` by
    (drule_all abi_encoder_member_cursor_registered >> simp[]) >>
  conj_tac >- (irule abi_encoder_registered_effect_trans >>
    qexists_tac `ready` >> simp[] >>
    irule abi_encoder_registered_effect_trans >> qexists_tac `encoded` >> simp[]) >>
  metis_tac[]
QED

val _ =
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag abi_encoder_spine_dynamic_shared_effects) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print "ENCODER_SPINE_COMPAT_AUDIT_OK dynamic_shared_effects\n"
    else raise Fail "encoder spine compatibility admission dependency: dynamic_shared_effects"
  end;

(* Full rich interpretation of the concrete dynamic engine.  The enclosing
   ledger owns the already allocated parent cursor as well as this child. *)
Theorem abi_encoder_spine_dynamic_shared:
  abi_encode_child_prefix dst ho dp st = (ops,p) /\
  abi_encoder_spine_core_code func (ei,SND (SND ops),src,p,ce,len) /\
  abi_encode_child_suffix (FST ops) dp (FST (SND ops)) len ce = (out,en) /\
  fn_has_code st p func /\ fn_has_code ce en func /\
  abi_encoder_shared ei /\
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap)
    (d,extent) (first,last,b,cap) initial /\
  eval_operand dp initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dp /\
  off+LENGTH (enc at av) <= extent /\ ho+32 <= off /\
  abi_decoder_budget first last b cap initial /\
  first <= lo /\ hi <= last /\ lo <= p.cs_next_id /\ ce.cs_next_id <= hi /\
  site IN abi_decoder_ids lo hi /\ site < p.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  next <= st.cs_next_var /\
  p.cs_next_var <= limit_st.cs_next_var /\ ce.cs_next_var <= limit_st.cs_next_var /\
  en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready encoded actual.
    abi_encoder_spine_child
      (abi_encoder_spine_shared_post (ctx,func) (at,av,sb,source_cap,d+off)
        (first,last,b,cap,limit_st))
      (ei,T,dst,src,ho,dp,st,en,out) initial actual /\
    abi_encoder_member_phase_raw st p initial ready /\
    abi_encoder_spine_dynamic_shared_post (ctx,func) (at,av,sb,source_cap,d+off)
      (first,last,b,cap,limit_st) (st,p,initial)
      (ei,SND (SND ops),src,p,ce,len) ready encoded /\
    abi_encoder_member_phase_raw ce en encoded actual /\
    mem_bytes_at (d+off) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_scratch_effect first last lo hi next limit_st d extent b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,extent)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand dst initial = SOME (n2w d) /\
   abi_decoder_operand_live st.cs_next_var dst /\
   d+extent < dimword (:256)` by fs[abi_encoder_shared_input_def] >>
  `first <= p.cs_next_id /\ ce.cs_next_id <= last /\ d+ho < dimword (:256)` by decide_tac >>
  drule_all abi_encoder_spine_dynamic_shared_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`ready`, `encoded`, `actual`] >> asm_rewrite_tac [] >>
  `abi_encoder_shared_endpoint (ctx,func) (p,ce,len,limit_st)
    (first,last,b,cap) (at,av,d+off) ready encoded` by
    fs[abi_encoder_spine_dynamic_shared_post_def,abi_encoder_spine_shared_post_def] >>
  drule_all abi_encoder_member_prefix_transport >> strip_tac >>
  drule abi_encode_child_prefix_shape >> strip_tac >>
  drule abi_encoder_shared_endpoint_scratch >> disch_tac >>
  `abi_decoder_operand_live p.cs_next_var dp` by
    (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand dp ready = SOME (n2w slot)` by fs[abi_decoder_address_frame_def] >>
  `eval_operand (FST ops) encoded = SOME (n2w (d+ho)) /\
   eval_operand (FST (SND ops)) encoded = SOME (n2w off) /\
   eval_operand dp encoded = SOME (n2w slot)` by
    (drule abi_encode_child_prefix_live >> strip_tac >>
     metis_tac[abi_scratch_effect_operand]) >>
  `p.cs_next_var <= ce.cs_next_var` by
    (fs[abi_encoder_spine_core_code_def] >> drule abi_encoder_counters >> simp[]) >>
  `abi_decoder_operand_live ce.cs_next_var dp` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `p.cs_next_var` >> simp[]) >>
  `abi_decoder_operand_live ce.cs_next_var len` by
    (fs[abi_encoder_spine_core_code_def] >> drule abi_encode_result_live >> simp[]) >>
  `abi_decoder_address_frame next initial ready` by
    (fs[abi_decoder_address_frame_def] >> rpt strip_tac >>
     first_x_assum irule >> simp[] >>
     irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_decoder_budget first last b cap ready /\
   FLOOKUP ready.vs_allocas site = SOME (slot,32)` by
    (fs[abi_decoder_address_frame_def] >>
     mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `ready:venom_state`]
       abi_decoder_budget_transport) >> simp[]) >>
  drule_all abi_encoder_spine_dynamic_shared_pre >>
  simp_tac bool_ss [abi_encoder_spine_shared_pre_def] >> strip_tac >>
  `site IN abi_decoder_ids first last /\
   ~(site IN abi_decoder_ids p.cs_next_id ce.cs_next_id)` by
    (fs[abi_decoder_ids_def] >> decide_tac) >>
  `abi_footprint_disjoint (d+off) (LENGTH (enc at av))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap ready)` by
    fs[abi_encoder_shared_input_def] >>
  drule_all abi_scratch_effect_slot >> strip_tac >>
  `MEM (slot,32) (abi_decoder_child_scratch (abi_decoder_ids first last) b cap ready)` by
    (irule abi_scratch_registered_member >> simp[] >> qexists_tac `site` >> simp[]) >>
  `LENGTH (enc at av) = 0 \/
    ((d+off+LENGTH (enc at av) <= d+ho \/ d+ho+32 <= d+off) /\
     (d+off+LENGTH (enc at av) <= slot \/ slot+32 <= d+off))` by
    (fs[abi_footprint_disjoint_def] >>
     first_x_assum (qspecl_then [`slot`, `32`] mp_tac) >> simp[] >> decide_tac) >>
  `d <= d+ho /\ d+ho+32 <= d+extent /\
   d <= d+off /\ d+off+LENGTH (enc at av) <= d+extent /\
   next <= p.cs_next_var /\ next <= ce.cs_next_var` by decide_tac >>
  `mem_bytes_at (d+off) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
   eval_operand out actual = SOME (n2w (LENGTH (enc at av)))` by
    (conj_tac
     >- (irule (cj 1 abi_encoder_spine_shared_suffix_observations) >>
         goal_assum (drule_at (Pat `abi_encoder_shared_endpoint _ _ _ _ _ _`)) >>
         goal_assum (drule_at (Pat `abi_encode_child_suffix _ _ _ _ _ = _`)) >>
         goal_assum (drule_at (Pat `abi_encoder_member_phase_raw _ _ _ _`)) >>
         qexistsl_tac [`d`, `extent`, `d+ho`, `site`,
           `abi_decoder_ids lo hi`, `off`, `slot`] >> gvs[LENGTH_NIL] >> decide_tac) >>
     irule (cj 2 abi_encoder_spine_shared_suffix_observations) >>
     goal_assum (drule_at (Pat `abi_encoder_shared_endpoint _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `abi_encode_child_suffix _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `abi_encoder_member_phase_raw _ _ _ _`)) >>
     qexistsl_tac [`d`, `extent`, `d+ho`, `site`,
       `abi_decoder_ids lo hi`, `off`, `slot`] >> gvs[LENGTH_NIL] >> decide_tac) >>
  drule_all abi_encoder_spine_dynamic_shared_effects >> strip_tac >>
  drule_all abi_encoder_spine_dynamic_shared_sim >> simp[]
QED

val _ =
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag abi_encoder_spine_dynamic_shared) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print "ENCODER_SPINE_COMPAT_AUDIT_OK dynamic_shared\n"
    else raise Fail "encoder spine compatibility admission dependency: dynamic_shared"
  end;

Theorem abi_encoder_spine_dynamic_source_pre:
  abi_encode_child_prefix dst ho dp st = (ops,p) /\
  abi_encoder_correct ei /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d extent b cap initial /\
  eval_operand dp initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dp /\
  off+LENGTH (enc at av) <= extent /\
  abi_decoder_budget first last b cap initial /\
  first <= p.cs_next_id /\ ce.cs_next_id <= last /\
  p.cs_next_var <= limit_st.cs_next_var /\ ce.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  abi_encoder_member_phase_raw st p initial ready ==>
  abi_encoder_spine_source_pre (at,av,sb,source_cap,d+off)
    (first,last,b,cap,limit_st) (ei,SND (SND ops),src,p,ce,len) ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand dst initial = SOME (n2w d) /\
   abi_decoder_operand_live st.cs_next_var dst` by fs[abi_encoder_buffer_pre_def] >>
  drule_all abi_encoder_member_prefix_transport >> strip_tac >>
  drule_all abi_encoder_member_prefix_control >> strip_tac >>
  drule abi_encode_child_prefix_shape >> strip_tac >>
  drule abi_encode_child_prefix_live >> strip_tac >>
  `st.cs_next_var <= p.cs_next_var` by decide_tac >>
  drule_all abi_encoder_child_pre_address >> disch_tac >>
  `abi_decoder_budget first last b cap ready` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `ready:venom_state`]
       abi_decoder_budget_transport) >> fs[abi_decoder_address_frame_def]) >>
  simp[abi_encoder_spine_source_pre_def]
QED

Theorem abi_encoder_spine_dynamic_source_cursor:
  abi_encode_child_prefix dst ho dp st = (ops,p) /\
  abi_encoder_spine_core_code func (ei,SND (SND ops),src,p,ce,len) /\
  eval_operand dst initial = SOME (n2w d) /\ eval_operand dp initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\ d+ho < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dp /\
  p.cs_next_var <= limit_st.cs_next_var /\ en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st p initial ready /\
  abi_encoder_spine_source_post (ctx,func) (at,av,sb,source_cap,d+off)
    (first,last,b,cap,limit_st) (ei,SND (SND ops),src,p,ce,len) ready encoded ==>
  abi_encoder_spine_cursor_input (FST ops,dp,FST (SND ops),len,ce,en,limit_st) encoded
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_member_prefix_transport >> strip_tac >>
  drule abi_encode_child_prefix_live >> strip_tac >>
  drule abi_encode_child_prefix_shape >> strip_tac >>
  `abi_decoder_operand_live p.cs_next_var dp` by
    (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand dp ready = SOME (n2w slot)` by fs[abi_decoder_address_frame_def] >>
  `abi_decoder_effect first last p.cs_next_id ce.cs_next_id p.cs_next_var
    limit_st (d+off) (LENGTH (enc at av)) b cap ready encoded` by
    fs[abi_encoder_spine_source_post_def] >>
  `eval_operand (FST ops) encoded = SOME (n2w (d+ho)) /\
   eval_operand (FST (SND ops)) encoded = SOME (n2w off) /\
   eval_operand dp encoded = SOME (n2w slot)` by
    metis_tac[abi_encoder_effect_operand] >>
  `p.cs_next_var <= ce.cs_next_var` by
    (fs[abi_encoder_spine_core_code_def] >> drule abi_encoder_counters >> simp[]) >>
  `abi_decoder_operand_live ce.cs_next_var dp` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `p.cs_next_var` >> simp[]) >>
  `abi_decoder_operand_live ce.cs_next_var len` by
    (fs[abi_encoder_spine_core_code_def] >> drule abi_encode_result_live >> simp[]) >>
  simp_tac bool_ss [abi_encoder_spine_cursor_input_def] >>
  qexistsl_tac [`d+ho`, `slot`, `off`, `LENGTH (enc at av)`] >>
  fs[abi_encoder_spine_source_post_def, abi_decoder_effect_def]
QED

Definition abi_encoder_spine_dynamic_source_post_def:
  abi_encoder_spine_dynamic_source_post ambient value resources (st,p,initial) c ready encoded <=>
    abi_encoder_spine_source_post ambient value resources c ready encoded /\
    abi_encoder_member_phase_raw st p initial ready
End

Theorem abi_encoder_spine_dynamic_source:
  abi_encode_child_prefix dst ho dp st = (ops,p) /\
  abi_encoder_spine_core_code func (ei,SND (SND ops),src,p,ce,len) /\
  abi_encode_child_suffix (FST ops) dp (FST (SND ops)) len ce = (out,en) /\
  abi_encoder_correct ei /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d extent b cap initial /\
  eval_operand dp initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\ d+ho < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dp /\
  off+LENGTH (enc at av) <= extent /\
  abi_decoder_budget first last b cap initial /\
  first <= p.cs_next_id /\ ce.cs_next_id <= last /\
  p.cs_next_var <= limit_st.cs_next_var /\ ce.cs_next_var <= limit_st.cs_next_var /\
  en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb ==>
  ?ready encoded actual.
    abi_encoder_spine_child
      (abi_encoder_spine_source_post (ctx,func) (at,av,sb,source_cap,d+off)
        (first,last,b,cap,limit_st))
      (ei,T,dst,src,ho,dp,st,en,out) initial actual /\
    abi_encoder_member_phase_raw st p initial ready /\
    abi_encoder_spine_dynamic_source_post (ctx,func) (at,av,sb,source_cap,d+off)
      (first,last,b,cap,limit_st) (st,p,initial)
      (ei,SND (SND ops),src,p,ce,len) ready encoded /\
    abi_encoder_member_phase_raw ce en encoded actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  irule abi_encoder_spine_dynamic_run >>
  conj_tac >- (qexistsl_tac [`off`, `slot`] >> simp[]) >>
  conj_tac >- (qexists_tac `d` >> fs[abi_encoder_buffer_pre_def]) >>
  asm_rewrite_tac [] >>
  conj_tac >- fs[abi_encoder_buffer_pre_def] >>
  conj_tac
  >- (qexistsl_tac [`\c r. abi_encoder_spine_source_pre (at,av,sb,source_cap,d+off)
          (first,last,b,cap,limit_st) c r /\ abi_encoder_member_phase_raw st p initial r`, `func`] >>
      asm_rewrite_tac [] >> conj_tac
      >- (rpt gen_tac >> simp_tac bool_ss [] >> strip_tac >>
          drule_all abi_encoder_spine_source_core_run >>
          disch_then (qspec_then `ctx` strip_assume_tac) >>
          qexists_tac `t` >> simp[abi_encoder_spine_dynamic_source_post_def]) >>
      rpt gen_tac >> disch_tac >> simp[] >>
      irule abi_encoder_spine_dynamic_source_pre >>
      asm_rewrite_tac [] >> goal_assum (drule_at Any) >>
      qexistsl_tac [`dp`, `dst`, `extent`, `ho`, `slot`] >> asm_rewrite_tac []) >>
  qexists_tac `limit_st` >> asm_rewrite_tac [] >>
  rpt gen_tac >> simp_tac bool_ss [abi_encoder_spine_dynamic_source_post_def] >> strip_tac >>
  `eval_operand dst initial = SOME (n2w d) /\
   abi_decoder_operand_live st.cs_next_var dst` by fs[abi_encoder_buffer_pre_def] >>
  drule_all abi_encoder_spine_dynamic_source_cursor >> simp[]
QED

val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print ("ENCODER_SPINE_COMPAT_AUDIT_OK " ^ name ^ "\n")
    else raise Fail ("encoder spine compatibility admission dependency: " ^ name)
  end)
  [("dynamic_source_pre",abi_encoder_spine_dynamic_source_pre),
   ("dynamic_source_cursor",abi_encoder_spine_dynamic_source_cursor),
   ("dynamic_source",abi_encoder_spine_dynamic_source)];
