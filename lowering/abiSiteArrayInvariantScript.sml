(* Finite-site array proof interface; legacy numeric cursor order is retained. *)
Theory abiSiteArrayInvariant
Ancestors
  abiSiteEncoderContract abiSiteAllocation abiScratchEffect abiScratchArrayLoopInvariant
  abiEncoderArrayPrefix abiEncoderArrayBodyCode abiEncoderMembersDefs abiEncoderInput
  abiEncoderChildCapability abiDecoderAllocation abiDecoderReentry abiDecoderLoop
  abiDecoderContract compileEnv valueEncoding contractABI venomState pred_set words list arithmetic

Definition abi_site_array_loop_inv_def:
  abi_site_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot A first hi sb source_cap d output_size b cap count_op label j origin s <=>
    abi_site_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      owner_st src dst sb source_cap d output_size A b cap s /\
    abi_encoder_array_prefix ty avs j d s.vs_memory /\
    abi_encoder_cursor T ip site slot first site owner_st j s /\
    abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first site owner_st
      (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) s /\
    site IN A /\ (active ==> cursor_site IN A) /\
    (active ==> site < cursor_site) /\ abi_decoder_operand_live owner_st.cs_next_var count_op /\
    eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
    s.vs_current_bb = label /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    abi_site_encoder_effect A site hi owner_st.cs_next_var limit_st d output_size b cap origin s
End

(* owner_st is before last; this makes the explicit cursor memberships redundant
   at the legacy interval instance. hi <= last is needed by effect specialization. *)
Theorem abi_site_array_loop_inv_interval:
  owner_st.cs_next_id <= last /\ hi <= last ==>
  (abi_site_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot (abi_decoder_ids first last) first hi
    sb source_cap d output_size b cap count_op label j origin s <=>
   abi_scratch_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi
    sb source_cap d output_size b cap count_op label j origin s)
Proof
  strip_tac >> simp_tac bool_ss [abi_site_array_loop_inv_def, abi_scratch_array_loop_inv_def,
    abi_site_encoder_input_interval] >> eq_tac >> strip_tac >>
  `first <= site` by fs[abi_encoder_cursor_def] >>
  `abi_site_encoder_effect (abi_decoder_ids first last) site hi owner_st.cs_next_var
      limit_st d output_size b cap origin s <=>
   abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin s`
    by (irule abi_site_encoder_effect_interval >> asm_rewrite_tac[]) >>
  full_simp_tac bool_ss [] >>
  fs[abi_encoder_cursor_def, abi_decoder_ids_def] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem abi_site_array_loop_inv_facts:
  abi_site_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot A first hi sb source_cap d output_size b cap count_op label j origin s ==>
  has_type (Array NONE ty) (ListV avs) /\ j <= LENGTH avs /\ LENGTH avs < dimword (:256) /\
  first <= site /\ fresh_vars_wrt limit_st s /\ abi_site_budget A b cap s
Proof
  simp_tac bool_ss [abi_site_array_loop_inv_def, abi_site_encoder_input_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_input_typed >> disch_tac >>
  `j <= LENGTH avs` by fs[abi_encoder_array_prefix_def] >>
  drule_all abi_encoder_array_prefix_types >> strip_tac >>
  fs[abi_site_encoder_effect_def, abi_encoder_cursor_def]
QED

Theorem abi_site_array_loop_inv_advance:
  abi_site_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot A first hi sb source_cap d output_size b cap count_op label j origin initial /\
  abi_site_encoder_effect A site hi owner_st.cs_next_var limit_st d output_size b cap initial actual /\
  abi_site_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size A b cap actual /\
  abi_encoder_array_prefix ty avs k d actual.vs_memory /\
  abi_encoder_cursor T ip site slot first site owner_st k actual /\
  abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE k avs))) actual /\
  actual.vs_current_bb = next_label /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted ==>
  abi_site_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot A first hi sb source_cap d output_size b cap count_op next_label k origin actual
Proof
  simp_tac bool_ss [abi_site_array_loop_inv_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand count_op actual = SOME (n2w (LENGTH avs))` by
    (drule_all abi_site_effect_operand >> simp[]) >>
  `abi_site_encoder_effect A site hi owner_st.cs_next_var limit_st d output_size b cap origin actual` by
    (irule abi_site_effect_trans >> qexists_tac `initial` >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss []
QED

(* Probe the dynamic-array callback boundary: a guarded child preserves the
   parent's saved cursor as well as the address operands used by its suffix. *)
Theorem abi_site_array_child_run:
  abi_encoder_spine_core_code func (ei,dst,src,st,en,out) /\
  abi_encoder_child_ready (at,av,sb,source_cap,d) (A,b,cap,limit_st) guard
    (ei,dst,src,st,en,out) initial /\
  site IN A /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  abi_decoder_operand_live st.cs_next_var head /\
  abi_decoder_operand_live st.cs_next_var offset /\
  abi_decoder_operand_live st.cs_next_var dp /\
  eval_operand head initial = SOME (n2w h) /\
  eval_operand offset initial = SOME (n2w off) /\
  eval_operand dp initial = SOME (n2w slot) ==>
  ?actual. abi_decode_sim ctx func initial actual /\
    abi_encoder_child_post (ctx,func) (at,av,sb,source_cap,d) (A,b,cap,limit_st)
      (ei,dst,src,st,en,out) initial actual /\
    eval_operand head actual = SOME (n2w h) /\
    eval_operand offset actual = SOME (n2w off) /\
    eval_operand dp actual = SOME (n2w slot) /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
    mload slot actual = mload slot initial /\ fresh_vars_wrt limit_st actual /\
    abi_site_budget A b cap actual
Proof
  strip_tac >> drule_all abi_encoder_child_ready_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_encoder_child_pre (at,av,sb,source_cap,d) (A,b,cap,limit_st)
    (ei,dst,src,st,en,out) initial` by fs[abi_encoder_child_ready_def] >>
  drule_all abi_encoder_child_saved >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >> metis_tac[]
QED

val _ = List.app (fn (name,th) =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if not (null (Thm.hyp th)) orelse not (null axs) orelse
       List.exists (fn s => s <> "DISK_THM") ors
    then raise Fail ("Finite-site array interface dependency: " ^ name) else ()
  end) (DB.thms "abiSiteArrayInvariant");
