(* Rich child callbacks at the shared generator's actual core endpoint. *)
Theory abiEncoderSharedMemberContract
Ancestors
  abiEncoderMemberSpineCompat abiEncoderMemberSpine abiEncoderSharedContract
  abiEncoderExtendSim abiScratchMemberContract abiScratchEncoderContract abiScratchEffect abiDecoderAllocation
  abiDecoderContract abiDecoderReentry abiEncoderCounters abiEncoderResultLive
  fragExec compileEnv valueEncoding venomState finite_map

Theorem abi_encoder_shared_member_core_run:
  abi_encoder_spine_core_code func c /\
  abi_encoder_spine_shared_pre value resources c s ==>
  ?t. abi_encoder_extend_sim ctx func s t /\
    abi_encoder_spine_shared_post (ctx,func) value resources c s t
Proof
  strip_tac >> drule_all abi_encoder_spine_shared_core_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> qexists_tac `t` >>
  asm_rewrite_tac [] >>
  PairCases_on `c` >> PairCases_on `value` >> PairCases_on `resources` >>
  fs[abi_encoder_spine_shared_post_def] >>
  drule abi_encoder_shared_endpoint_extend_sim >> simp[]
QED

Definition abi_encoder_shared_member_dynamic_pre_def:
  abi_encoder_shared_member_dynamic_pre value resources cursor c s <=>
    abi_encoder_spine_shared_pre value resources c s /\
    abi_scratch_member_cursor_saved cursor resources c s
End

Definition abi_encoder_shared_member_dynamic_post_def:
  abi_encoder_shared_member_dynamic_post ambient value resources cursor c s t <=>
    abi_encoder_spine_shared_post ambient value resources c s t /\
    abi_encoder_shared_member_dynamic_pre value resources cursor c s /\
    abi_encoder_spine_core_code (SND ambient) c
End

Theorem abi_encoder_shared_member_dynamic_run:
  abi_encoder_spine_core_code func c /\
  abi_encoder_shared_member_dynamic_pre value resources cursor c s ==>
  ?t. abi_encoder_extend_sim ctx func s t /\
    abi_encoder_shared_member_dynamic_post (ctx,func) value resources cursor c s t
Proof
  simp_tac bool_ss [abi_encoder_shared_member_dynamic_pre_def,
    abi_encoder_shared_member_dynamic_post_def, pairTheory.SND] >> strip_tac >>
  drule_all abi_encoder_shared_member_core_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac []
QED

Theorem abi_encoder_shared_member_dynamic_saved:
  abi_encoder_shared_member_dynamic_post (ctx,func) (at,av,sb:num,source_cap:num,d)
    (first,last,b,cap,limit_st) (head,offset,dp,h,off,slot,site)
    (ei:abi_enc_info,dst:operand,src:operand,st,en,out) initial actual ==>
  eval_operand head actual = SOME (n2w h) /\ eval_operand offset actual = SOME (n2w off) /\
  eval_operand dp actual = SOME (n2w slot) /\
  FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
  mload slot actual = mload slot initial /\ fresh_vars_wrt limit_st actual /\
  abi_decoder_budget first last b cap actual
Proof
  simp_tac bool_ss [abi_encoder_shared_member_dynamic_post_def,
    abi_encoder_shared_member_dynamic_pre_def, abi_scratch_member_cursor_saved_def,
    abi_encoder_spine_shared_pre_def, abi_encoder_spine_shared_post_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_shared_endpoint_scratch >> disch_tac >>
  `site IN abi_decoder_ids first last /\
    ~(site IN abi_decoder_ids st.cs_next_id en.cs_next_id)` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  `abi_footprint_disjoint d (LENGTH (enc at av))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    fs[abi_encoder_shared_input_def] >>
  drule_all abi_scratch_effect_slot >> strip_tac >>
  fs[abi_scratch_effect_def] >> metis_tac[]
QED

Theorem abi_encoder_shared_member_dynamic_cursor_input:
  abi_encoder_shared_member_dynamic_post (ctx,func) (at,av,sb:num,source_cap:num,d)
    (first,last,b,cap,limit_st) (head,offset,dp,h,off,slot,site)
    (ei:abi_enc_info,dst:operand,src:operand,st,en,len) initial actual /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var ==>
  abi_encoder_spine_cursor_input (head,dp,offset,len,en,final,limit_st) actual
Proof
  strip_tac >> drule_all abi_encoder_shared_member_dynamic_saved >> strip_tac >>
  qpat_assum `abi_encoder_shared_member_dynamic_post _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o
      PURE_REWRITE_RULE [abi_encoder_shared_member_dynamic_post_def]) >>
  qpat_assum `abi_encoder_spine_core_code _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_spine_core_code_def]) >>
  drule abi_encoder_counters >> strip_tac >>
  drule abi_encode_result_live >> strip_tac >>
  `abi_decoder_operand_live en.cs_next_var dp` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >>
     fs[abi_encoder_shared_member_dynamic_pre_def, abi_scratch_member_cursor_saved_def]) >>
  simp_tac bool_ss [abi_encoder_spine_cursor_input_def] >>
  qexistsl_tac [`h`,`slot`,`off`,`LENGTH (enc at av)`] >>
  fs[abi_encoder_spine_shared_post_def, abi_encoder_shared_endpoint_def]
QED

Definition abi_encoder_shared_members_child_pre_def:
  abi_encoder_shared_members_child_pre resources (dyn,value,cursor) c s <=>
    if dyn then abi_encoder_shared_member_dynamic_pre value resources cursor c s
    else abi_encoder_spine_shared_pre value resources c s
End

Definition abi_encoder_shared_members_child_post_def:
  abi_encoder_shared_members_child_post ambient resources (dyn,value,cursor) c s t <=>
    if dyn then abi_encoder_shared_member_dynamic_post ambient value resources cursor c s t
    else abi_encoder_spine_shared_post ambient value resources c s t
End

Theorem abi_encoder_shared_members_child_dispatch:
  abi_encoder_shared_members_child_pre resources (T,value,cursor) =
    abi_encoder_shared_member_dynamic_pre value resources cursor /\
  abi_encoder_shared_members_child_pre resources (F,value,cursor) =
    abi_encoder_spine_shared_pre value resources /\
  abi_encoder_shared_members_child_post ambient resources (T,value,cursor) =
    abi_encoder_shared_member_dynamic_post ambient value resources cursor /\
  abi_encoder_shared_members_child_post ambient resources (F,value,cursor) =
    abi_encoder_spine_shared_post ambient value resources
Proof
  simp[FUN_EQ_THM, abi_encoder_shared_members_child_pre_def,
    abi_encoder_shared_members_child_post_def]
QED

Theorem abi_encoder_shared_members_child_run:
  !y c r. abi_encoder_spine_core_code func c /\
    abi_encoder_shared_members_child_pre resources y c r ==>
    ?u. abi_encoder_extend_sim ctx func r u /\
      abi_encoder_shared_members_child_post (ctx,func) resources y c r u
Proof
  rpt gen_tac >> PairCases_on `y` >> Cases_on `y0` >>
  simp_tac bool_ss [abi_encoder_shared_members_child_pre_def,
    abi_encoder_shared_members_child_post_def, pairTheory.UNCURRY_DEF] >>
  rpt strip_tac
  >- (irule abi_encoder_shared_member_dynamic_run >> asm_rewrite_tac []) >>
  irule abi_encoder_shared_member_core_run >> asm_rewrite_tac []
QED
