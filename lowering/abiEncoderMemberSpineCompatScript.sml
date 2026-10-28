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
  abiEncoderChildSuffix valueEncoding abiEncoderChildSuffixReach abiScratchChild abiScratchAddress

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

val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print ("ENCODER_SPINE_COMPAT_AUDIT_OK " ^ name ^ "\n")
    else raise Fail ("encoder spine compatibility admission dependency: " ^ name)
  end)
  [("static_shared_transport", abi_encoder_spine_static_shared_transport)];

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

val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print ("ENCODER_SPINE_COMPAT_AUDIT_OK " ^ name ^ "\n")
    else raise Fail ("encoder spine compatibility admission dependency: " ^ name)
  end)
  [("dynamic_shared_pre", abi_encoder_spine_dynamic_shared_pre)];

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

val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print ("ENCODER_SPINE_COMPAT_AUDIT_OK " ^ name ^ "\n")
    else raise Fail ("encoder spine compatibility admission dependency: " ^ name)
  end)
  [("cursor_post",abi_encoder_spine_cursor_post)];

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
