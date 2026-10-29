(* Genuine physical child contract for the shared member certificate generator. *)
Theory abiScratchMemberContract
Ancestors
  abiEncoderMemberSpine abiScratchEncoderContract abiScratchEncoderRun abiScratchEffect
  abiDecoderContract abiDecoderLoop abiDecoderAllocation abiDecoderReentry
  abiEncoderCounters abiEncoderResultLive
  fragExec compileEnv valueEncoding venomState finite_map

Definition abi_scratch_member_core_pre_def:
  abi_scratch_member_core_pre (at,av,sb,source_cap,d) (first,last,b,cap,limit_st)
      (ei,dst,src,st,en,out) s <=>
    abi_scratch_encoder ei /\
    abi_scratch_input ei at av st src dst sb source_cap d (LENGTH (enc at av))
      first last b cap s /\
    abi_decoder_budget first last b cap s /\
    first <= st.cs_next_id /\ en.cs_next_id <= last /\
    en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts
End

Definition abi_scratch_member_core_post_def:
  abi_scratch_member_core_post (ctx,func) (at,av,sb,source_cap,d)
      (first,last,b,cap,limit_st) (ei,dst,src,st,en,out) s t <=>
    mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_scratch_effect first last st.cs_next_id en.cs_next_id st.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap s t /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func s t
End

Theorem abi_scratch_member_core_run:
  abi_encoder_spine_core_code func c /\ abi_scratch_member_core_pre value resources c s ==>
  ?t. abi_decode_sim ctx func s t /\
    abi_scratch_member_core_post (ctx,func) value resources c s t
Proof
  PairCases_on `c` >> PairCases_on `value` >> PairCases_on `resources` >>
  simp_tac bool_ss [abi_encoder_spine_core_code_def, abi_scratch_member_core_pre_def,
    abi_scratch_member_core_post_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_encoder_run >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `actual` >> asm_rewrite_tac []
QED

Theorem abi_scratch_member_child_run:
  abi_encoder_spine_child_input func limit_st
    (abi_scratch_member_core_pre value resources)
    (abi_scratch_member_core_post (ctx,func) value resources) c s ==>
  ?t. abi_encoder_spine_child (\c r u. abi_decode_sim ctx func r u) c s t /\
    abi_encoder_spine_child_output
      (abi_scratch_member_core_post (ctx,func) value resources) c s t
Proof
  strip_tac >> irule abi_encoder_spine_child_generate >>
  goal_assum (drule_at Any) >> rpt strip_tac >> BETA_TAC >>
  irule abi_scratch_member_core_run >> asm_rewrite_tac []
QED

Theorem abi_scratch_member_core_saved:
  abi_scratch_member_core_pre (at,av,sb,source_cap,d)
    (first,last,b,cap,limit_st) (ei,dst,src,start,en,out) initial /\
  abi_scratch_member_core_post (ctx,func) (at,av,sb,source_cap,d)
    (first,last,b,cap,limit_st) (ei,dst,src,start,en,out) initial actual /\
  first <= site /\ site < last /\ site < start.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
  (!op w. abi_decoder_operand_live start.cs_next_var op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w) /\
  FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
  mload slot actual = mload slot initial /\ fresh_vars_wrt limit_st actual /\
  abi_decoder_budget first last b cap actual
Proof
  simp_tac bool_ss [abi_scratch_member_core_pre_def, abi_scratch_member_core_post_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site IN abi_decoder_ids first last /\
    ~(site IN abi_decoder_ids start.cs_next_id en.cs_next_id)` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  `abi_footprint_disjoint d (LENGTH (enc at av))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    fs[abi_scratch_input_def] >>
  drule_all abi_scratch_effect_slot >> strip_tac >>
  asm_simp_tac bool_ss [] >> fs[abi_scratch_effect_def] >> metis_tac[]
QED

Definition abi_scratch_member_cursor_saved_def:
  abi_scratch_member_cursor_saved (head,offset,dp,h,off,slot,site)
      (first,last,b,cap,limit_st) (ei,dst,src,st,en,out) s <=>
    abi_decoder_operand_live st.cs_next_var head /\
    abi_decoder_operand_live st.cs_next_var offset /\
    abi_decoder_operand_live st.cs_next_var dp /\
    eval_operand head s = SOME (n2w h) /\ eval_operand offset s = SOME (n2w off) /\
    eval_operand dp s = SOME (n2w slot) /\
    first <= site /\ site < last /\ site < st.cs_next_id /\
    FLOOKUP s.vs_allocas site = SOME (slot,32)
End

Definition abi_scratch_member_dynamic_pre_def:
  abi_scratch_member_dynamic_pre value resources cursor c s <=>
    abi_scratch_member_core_pre value resources c s /\
    abi_scratch_member_cursor_saved cursor resources c s
End

(* Physical protection requires the entry budget and output disjointness.
   Retaining the genuine pre at its original state makes these ghost facts explicit. *)
Definition abi_scratch_member_dynamic_post_def:
  abi_scratch_member_dynamic_post (ctx,func) value resources cursor c s t <=>
    abi_scratch_member_core_post (ctx,func) value resources c s t /\
    abi_scratch_member_dynamic_pre value resources cursor c s /\
    abi_encoder_spine_core_code func c
End

Theorem abi_scratch_member_dynamic_run:
  abi_encoder_spine_core_code func c /\
  abi_scratch_member_dynamic_pre value resources cursor c s ==>
  ?t. abi_decode_sim ctx func s t /\
    abi_scratch_member_dynamic_post (ctx,func) value resources cursor c s t
Proof
  simp_tac bool_ss [abi_scratch_member_dynamic_pre_def, abi_scratch_member_dynamic_post_def] >>
  strip_tac >> drule_all abi_scratch_member_core_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac []
QED

Theorem abi_scratch_member_dynamic_saved:
  abi_scratch_member_dynamic_post (ctx,func) (at,av,sb:num,source_cap:num,d)
    (first,last,b,cap,limit_st) (head,offset,dp,h,off,slot,site)
    (ei:abi_enc_info,dst:operand,src:operand,st,en,out) initial actual ==>
  eval_operand head actual = SOME (n2w h) /\ eval_operand offset actual = SOME (n2w off) /\
  eval_operand dp actual = SOME (n2w slot) /\
  FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
  mload slot actual = mload slot initial /\ fresh_vars_wrt limit_st actual /\
  abi_decoder_budget first last b cap actual
Proof
  simp_tac bool_ss [abi_scratch_member_dynamic_post_def, abi_scratch_member_dynamic_pre_def,
    abi_scratch_member_cursor_saved_def] >>
  strip_tac >> drule_all abi_scratch_member_core_saved >> strip_tac >> metis_tac[]
QED

Theorem abi_scratch_member_dynamic_child_run:
  abi_encoder_spine_child_input func limit_st
    (abi_scratch_member_dynamic_pre value resources cursor)
    (abi_scratch_member_dynamic_post (ctx,func) value resources cursor) c s ==>
  ?t. abi_encoder_spine_child (\c r u. abi_decode_sim ctx func r u) c s t /\
    abi_encoder_spine_child_output
      (abi_scratch_member_dynamic_post (ctx,func) value resources cursor) c s t
Proof
  strip_tac >> irule abi_encoder_spine_child_generate >>
  goal_assum (drule_at Any) >> rpt strip_tac >> BETA_TAC >>
  irule abi_scratch_member_dynamic_run >> asm_rewrite_tac []
QED

Theorem abi_scratch_member_dynamic_cursor_input:
  abi_scratch_member_dynamic_post (ctx,func) (at,av,sb:num,source_cap:num,d)
    (first,last,b,cap,limit_st) (head,offset,dp,h,off,slot,site)
    (ei:abi_enc_info,dst:operand,src:operand,st,en,len) initial actual /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var ==>
  abi_encoder_spine_cursor_input (head,dp,offset,len,en,final,limit_st) actual
Proof
  strip_tac >> drule_all abi_scratch_member_dynamic_saved >> strip_tac >>
  qpat_assum `abi_scratch_member_dynamic_post _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o
      PURE_REWRITE_RULE [abi_scratch_member_dynamic_post_def]) >>
  qpat_assum `abi_encoder_spine_core_code _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o
      PURE_REWRITE_RULE [abi_encoder_spine_core_code_def]) >>
  drule abi_encoder_counters >> strip_tac >>
  drule abi_encode_result_live >> strip_tac >>
  `abi_decoder_operand_live en.cs_next_var dp` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >>
     fs[abi_scratch_member_dynamic_pre_def, abi_scratch_member_cursor_saved_def]) >>
  pure_rewrite_tac [abi_encoder_spine_cursor_input_def] >>
  qexistsl_tac [`h`,`slot`,`off`,`LENGTH (enc at av)`] >>
  fs[abi_scratch_member_core_post_def]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "scratch core contract has an admission, axiom or hypothesis"
  end) [abi_scratch_member_core_run, abi_scratch_member_child_run,
    abi_scratch_member_core_saved, abi_scratch_member_dynamic_run,
    abi_scratch_member_dynamic_saved, abi_scratch_member_dynamic_child_run,
    abi_scratch_member_dynamic_cursor_input];
