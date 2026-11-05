(* One recursive invocation needs a fixed-site capability, not a universal
   site encoder. The guard records the client's compiler admissibility. *)
Theory abiEncoderChildCapability
Ancestors
  abiSiteEncoderContract abiSiteAllocation abiScratchEncoderRun abiScratchEffect
  abiEncoderMemberSpine abiScratchEncoderContract
  abiDecoderContract abiDecoderLoop abiDecoderAllocation abiDecoderReentry
  compileEnv valueEncoding venomState finite_map pred_set words list arithmetic

Definition abi_encoder_child_pre_def:
  abi_encoder_child_pre (at,av,sb,source_cap,d) (A,b,cap,limit_st)
      (ei,dst,src,st,en,out) s <=>
    abi_site_encoder_input ei at av st src dst sb source_cap d (LENGTH (enc at av)) A b cap s /\
    abi_site_budget A b cap s /\
    en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts
End

Definition abi_encoder_child_post_def:
  abi_encoder_child_post (ctx,func) (at,av,sb,source_cap,d) (A,b,cap,limit_st)
      (ei,dst,src,st,en,out) s t <=>
    mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_site_encoder_effect A st.cs_next_id en.cs_next_id st.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap s t /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func s t
End

Definition abi_encoder_child_capability_def:
  abi_encoder_child_capability A guard ei <=>
    !dst src st en out func ctx b cap limit_st s at av sb source_cap d.
      abi_encoder_spine_core_code func (ei,dst,src,st,en,out) /\ guard st en /\
      abi_encoder_child_pre (at,av,sb,source_cap,d) (A,b,cap,limit_st)
        (ei,dst,src,st,en,out) s ==>
      ?t. abi_encoder_child_post (ctx,func) (at,av,sb,source_cap,d) (A,b,cap,limit_st)
        (ei,dst,src,st,en,out) s t
End

Theorem abi_encoder_child_capability_site:
  abi_site_encoder ei ==>
  abi_encoder_child_capability A
    (\st en. abi_decoder_emitted_sites st.cs_next_id en.cs_next_id st en SUBSET A) ei
Proof
  simp_tac bool_ss [abi_encoder_child_capability_def, abi_encoder_child_pre_def,
    abi_encoder_child_post_def, abi_encoder_spine_core_code_def] >>
  disch_tac >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> drule_all abi_site_encoder_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `actual` >> asm_rewrite_tac[]
QED

Theorem abi_encoder_child_capability_interval:
  abi_scratch_encoder ei ==>
  abi_encoder_child_capability (abi_decoder_ids first last)
    (\st en. first <= st.cs_next_id /\ en.cs_next_id <= last) ei
Proof
  simp_tac bool_ss [abi_encoder_child_capability_def, abi_encoder_child_pre_def,
    abi_encoder_child_post_def, abi_encoder_spine_core_code_def,
    abi_site_encoder_input_interval, abi_site_budget_interval] >>
  disch_tac >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> drule_all abi_scratch_encoder_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [abi_site_encoder_effect_interval]
QED

Theorem abi_encoder_child_core_run:
  abi_encoder_spine_core_code func (ei,dst,src,st,en,out) /\
  abi_encoder_child_capability A guard ei /\ guard st en /\
  abi_encoder_child_pre value (A,b,cap,limit_st) (ei,dst,src,st,en,out) s ==>
  ?t. abi_decode_sim ctx func s t /\
    abi_encoder_child_post (ctx,func) value (A,b,cap,limit_st) (ei,dst,src,st,en,out) s t
Proof
  PairCases_on `value` >> strip_tac >>
  qpat_x_assum `abi_encoder_child_capability _ _ _` mp_tac >>
  rewrite_tac[abi_encoder_child_capability_def] >>
  disch_then drule_all >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac[] >> fs[abi_encoder_child_post_def]
QED

Definition abi_encoder_child_ready_def:
  abi_encoder_child_ready value (A,b,cap,limit_st) guard (ei,dst,src,st,en,out) s <=>
    abi_encoder_child_capability A guard ei /\ guard st en /\
    abi_encoder_child_pre value (A,b,cap,limit_st) (ei,dst,src,st,en,out) s
End

Theorem abi_encoder_child_ready_run:
  abi_encoder_spine_core_code func c /\
  abi_encoder_child_ready value resources guard c s ==>
  ?t. abi_decode_sim ctx func s t /\
    abi_encoder_child_post (ctx,func) value resources c s t
Proof
  PairCases_on `c` >> PairCases_on `resources` >>
  simp_tac bool_ss [abi_encoder_child_ready_def] >>
  strip_tac >> drule_all abi_encoder_child_core_run >> simp[]
QED

Theorem abi_encoder_child_spine_run:
  abi_encoder_spine_child_input func limit_st
    (abi_encoder_child_ready value resources guard)
    (abi_encoder_child_post (ctx,func) value resources) c s ==>
  ?t. abi_encoder_spine_child (\c r u. abi_decode_sim ctx func r u) c s t /\
    abi_encoder_spine_child_output
      (abi_encoder_child_post (ctx,func) value resources) c s t
Proof
  strip_tac >> irule abi_encoder_spine_child_generate >>
  goal_assum (drule_at Any) >> rpt strip_tac >> BETA_TAC >>
  drule_all abi_encoder_child_ready_run >> simp[]
QED

Theorem abi_encoder_child_saved:
  abi_encoder_child_pre (at,av,sb,source_cap,d) (A,b,cap,limit_st)
    (ei,dst,src,st,en,out) initial /\
  abi_encoder_child_post (ctx,func) (at,av,sb,source_cap,d) (A,b,cap,limit_st)
    (ei,dst,src,st,en,out) initial actual /\
  site IN A /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
  (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w) /\
  FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
  mload slot actual = mload slot initial /\ fresh_vars_wrt limit_st actual /\
  abi_site_budget A b cap actual
Proof
  simp_tac bool_ss [abi_encoder_child_pre_def, abi_encoder_child_post_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `~(site IN abi_decoder_ids st.cs_next_id en.cs_next_id)` by
    simp[abi_decoder_ids_def] >>
  `abi_footprint_disjoint d (LENGTH (enc at av))
    (abi_decoder_child_scratch A b cap initial)` by
    fs[abi_site_encoder_input_def] >>
  drule_all abi_site_effect_slot >> strip_tac >>
  asm_simp_tac bool_ss [] >> fs[abi_site_encoder_effect_def] >> metis_tac[]
QED

Theorem abi_encoder_child_saved_cursor:
  abi_encoder_child_pre (at,av,sb,source_cap,d) (A,b,cap,limit_st)
    (ei,dst,src,st,en,out) initial /\
  abi_encoder_child_post (ctx,func) (at,av,sb,source_cap,d) (A,b,cap,limit_st)
    (ei,dst,src,st,en,out) initial actual /\
  site IN A /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  abi_decoder_operand_live st.cs_next_var head /\
  abi_decoder_operand_live st.cs_next_var offset /\
  abi_decoder_operand_live st.cs_next_var dp /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand offset initial = SOME (n2w off) /\
  eval_operand dp initial = SOME (n2w slot) ==>
  eval_operand head actual = SOME (n2w h) /\ eval_operand offset actual = SOME (n2w off) /\
  eval_operand dp actual = SOME (n2w slot) /\
  FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
  mload slot actual = mload slot initial /\ fresh_vars_wrt limit_st actual /\
  abi_site_budget A b cap actual
Proof
  strip_tac >> drule_all abi_encoder_child_saved >> strip_tac >> metis_tac[]
QED

val _ = List.app (fn (name, th) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn tag => tag = "DISK_THM") oracles then ()
    else raise Fail ("non-clean child capability: " ^ name)
  end) (DB.thms "abiEncoderChildCapability");
