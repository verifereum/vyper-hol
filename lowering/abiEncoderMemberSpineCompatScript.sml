(* Contract interpretations of the concrete member certificates. *)
Theory abiEncoderMemberSpineCompat
Ancestors
  abiEncoderMemberSpine abiEncoderMemberSourcePhase abiEncoderCorrect
  abiScratchEncoderContract abiEncoderSharedContract abiDecoderAllocation
  abiDecoderFrame abiDecoderContract fragExec compileEnv venomState words list
  abiEncoderChildInputs abiEncoderMemberPhaseRaw abiEncoderAddressReach
  abiEncoderMemberPhaseExec
  abiDecoderArrayInitExec abiDecoderDynamicLoopSetup

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
