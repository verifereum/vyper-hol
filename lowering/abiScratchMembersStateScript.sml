(* Pure state invariant for actual recursive member-list execution.
   TOP-LEVEL: abi_scratch_members_inv, its layout projection and the invariant
   after a completed child. The remaining source uses physical root ownership. *)
Theory abiScratchMembersState
Ancestors
  abiScratchMembersPre abiScratchMembersSource abiScratchEncoderContract
  abiEncoderMembersDefs abiEncoderMembersLayout abiEncoderTuplePrefix
  abiEncoderInput abiCanonicalWindows abiDecodeRanges abiDecoderAllocation
  abiDecoderReentry compileEnv valueEncoding contractABI venomState words list arithmetic

Definition abi_scratch_members_inv_def:
  abi_scratch_members_inv infos tys avs pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap s <=>
    abi_scratch_members_pre infos tys avs st src dst sb so d output_size first last b cap s /\
    has_types pre pvs /\ hl = head_lengths (pre++tys) 0 /\
    ho = SUM (MAP abi_member_head_size pre) /\
    LENGTH (enc (Tuple (pre++tys)) (ListV (pvs++avs))) <= output_size /\
    abi_encoder_tuple_prefix hl pre pvs d s.vs_memory /\
    abi_encoder_cursor active dyn_ptr site slot first lo st
      (hl+LENGTH (FLAT (abi_tuple_tails pre pvs))) s /\
    (active \/ EVERY (\(_,_,_,dyn). ~dyn) infos) /\
    abi_decoder_budget first last b cap s /\ first <= lo /\ lo <= st.cs_next_id /\
    st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts
End

Theorem abi_scratch_members_inv_layout:
  abi_scratch_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial ==>
  has_type ty av /\ has_types tys avs /\ LENGTH pre = LENGTH pvs /\
  abi_sz = abi_member_head_size ty /\ dyn = is_dynamic ty /\
  ho = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  SUM (MAP2 abi_member_tail_size pre pvs) = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  ho+abi_sz <= hl /\ hl+SUM (MAP2 abi_member_tail_size pre pvs) <= output_size /\
  (~dyn ==> ho+LENGTH (enc ty av) <= hl) /\
  (dyn ==> ho+32 <= hl /\ hl+SUM (MAP2 abi_member_tail_size pre pvs)+LENGTH (enc ty av) <= output_size)
Proof
  strip_tac >> qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`] abi_scratch_members_pre_cons) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `LENGTH pre = LENGTH pvs` by (irule has_types_length >> asm_simp_tac bool_ss []) >>
  `has_types (pre++ty::tys) (pvs++av::avs)` by simp[has_types_append, has_type_def] >>
  mp_tac (Q.INST [`heads` |-> `ho:num`, `tails` |-> `SUM (MAP2 abi_member_tail_size pre pvs)`]
    abi_encoder_members_layout) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `ho = SUM _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qpat_assum `hl = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_scratch_members_after_child:
  abi_scratch_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual /\
  abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d actual.vs_memory /\
  abi_encoder_cursor active dyn_ptr site slot first lo end_st
    (hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))) actual /\
  st.cs_next_var <= end_st.cs_next_var /\ st.cs_next_id <= end_st.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  ~actual.vs_halted /\ actual.vs_current_bb = end_st.cs_current_bb /\
  actual.vs_inst_idx = LENGTH end_st.cs_current_insts ==>
  abi_scratch_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot first last lo
    end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  mp_tac (Q.INST [`infos` |-> `(ei,abi_sz,mem_sz,dyn)::infos`, `tys` |-> `ty::tys`,
    `avs` |-> `av::avs`, `hi` |-> `end_st.cs_next_id`, `sz` |-> `output_size:num`]
    abi_scratch_members_pre_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`infos` |-> `(ei,abi_sz,mem_sz,dyn)::infos`, `tys` |-> `ty::tys`,
    `avs` |-> `av::avs`, `prepared` |-> `end_st`, `s` |-> `actual:venom_state`, `sz` |-> `output_size:num`]
    abi_scratch_members_pre_mono) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`st` |-> `end_st`, `s` |-> `actual:venom_state`] abi_scratch_members_pre_cons) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac abi_encoder_members_prefix_advance >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `lo <= end_st.cs_next_id` by decide_tac >>
  PURE_REWRITE_TAC [abi_scratch_members_inv_def, GSYM APPEND_ASSOC, APPEND] >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `active \/ EVERY _ _` mp_tac >> simp_tac (srw_ss()) [] >>
  rpt strip_tac >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_MEMBERS_STATE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch member invariant not kernel closed: " ^ n)
  end) (DB.thms "abiScratchMembersState");
