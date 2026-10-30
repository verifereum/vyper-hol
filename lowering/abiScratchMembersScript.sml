Theory abiScratchMembers
Ancestors
  abiScratchEncoderContract abiScratchEffect abiScratchFootprint abiScratchSubset
  abiEncoderInputFrame abiEncoderInput abiEncoderMembersInput abiDecoderDynamicLoopSetup
  abiDecoderAllocation abiDecoderFootprint abiDecoderFrame abiDecoderReentry compileEnv
  valueEncoding venomState pred_set words list arithmetic abiEncoderArrayFrame contractABI
  abiEncoderMembersDefs abiEncoderMembersLayout abiEncoderTuple abiCanonicalWindows
  abiDecodeRanges abiEncoderBufferFrame abiDecoderContract abiScratchAddress
  abiEncoderMembersContract abiEncoder abiDecoderLoop abiEncoderAddressReach emitHelperProps

(* ===== Pre ===== *)

(* Remaining tuple members retain complete source data and physical scratch
   separation. Source offsets refer to the original, live source operand.
   TOP-LEVEL: abi_scratch_members_pre and its state transport lemmas. *)

Definition abi_scratch_members_pre_def:
  abi_scratch_members_pre infos tys avs st src dst sb so d output_size first last b cap s <=>
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs)
      (sb+so) (abi_encoder_member_span infos) s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    sb+so+abi_encoder_member_span infos < dimword (:256) /\
    d+output_size < dimword (:256) /\
    (sb+so+abi_encoder_member_span infos <= d \/ d+output_size <= sb+so) /\
    abi_footprint_disjoint (sb+so) (abi_encoder_member_span infos)
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) /\
    abi_footprint_disjoint d output_size
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)
End

Theorem abi_scratch_members_pre_mono:
  abi_scratch_members_pre infos tys avs st src dst sb so d sz first last b cap s /\
  st.cs_next_var <= prepared.cs_next_var ==>
  abi_scratch_members_pre infos tys avs prepared src dst sb so d sz first last b cap s
Proof
  simp_tac bool_ss [abi_scratch_members_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> asm_simp_tac bool_ss [] >>
  conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]
QED

Theorem abi_scratch_members_pre_address:
  abi_scratch_members_pre infos tys avs st src dst sb so d sz first last b cap initial /\
  abi_decoder_address_frame st.cs_next_var initial actual /\
  st.cs_next_var <= prepared.cs_next_var ==>
  abi_scratch_members_pre infos tys avs prepared src dst sb so d sz first last b cap actual
Proof
  simp_tac bool_ss [abi_scratch_members_pre_def, abi_decoder_address_frame_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand src actual = SOME (n2w sb) /\ eval_operand dst actual = SOME (n2w d)` by
    (conj_tac >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual =
    abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial` by
    simp[abi_decoder_child_scratch_def] >>
  asm_simp_tac bool_ss [] >>
  conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]
QED

Theorem abi_scratch_members_pre_effect:
  abi_scratch_members_pre infos tys avs st src dst sb so d sz first last b cap initial /\
  abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap initial actual /\
  first <= lo /\ hi <= last ==>
  abi_scratch_members_pre infos tys avs st src dst sb so d sz first last b cap actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_pre_def]) >>
  `abi_decoder_ids lo hi SUBSET abi_decoder_ids first last` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `abi_footprint_disjoint (sb+so) (abi_encoder_member_span infos)
    (abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial)` by
    (irule abi_scratch_disjoint_subset >> qexists_tac `abi_decoder_ids first last` >> simp[]) >>
  `abi_footprint_disjoint (sb+so) (abi_encoder_member_span infos)
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial)` by
    simp[abi_scratch_disjoint_cons] >>
  `eval_operand src actual = SOME (n2w sb) /\ eval_operand dst actual = SOME (n2w d)` by
    (imp_res_tac abi_scratch_effect_operand >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) (sb+so)
    (abi_encoder_member_span infos) actual.vs_memory` by
    (drule_all abi_encoder_input_frame >> simp[]) >>
  `abi_footprint_disjoint (sb+so) (abi_encoder_member_span infos)
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual) /\
   abi_footprint_disjoint d sz
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual)` by
    (conj_tac >> irule abi_scratch_disjoint_advance >> simp[] >> qexists_tac `initial` >> simp[]) >>
  asm_simp_tac bool_ss [abi_scratch_members_pre_def]
QED

(* ===== Source ===== *)

(* Select the next member and advance the remaining physical source window.
   TOP-LEVEL: abi_scratch_members_pre_cons and abi_scratch_members_child_buffer.
   No numeric exclusion of the entire scratch arena is required. *)

Theorem abi_scratch_members_pre_cons:
  abi_scratch_members_pre ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    st src dst sb so d output_size first last b cap s ==>
  has_type ty av /\ has_types tys avs /\
  abi_sz = abi_member_head_size ty /\ dyn = is_dynamic ty /\
  abi_encoder_input ei ty av (sb+so) mem_sz s.vs_memory /\
  abi_scratch_members_pre infos tys avs st src dst sb (so+mem_sz) d output_size first last b cap s
Proof
  strip_tac >> qpat_x_assum `abi_scratch_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_pre_def]) >>
  drule abi_encoder_members_input_cons >> strip_tac >>
  `has_types tys avs` by (imp_res_tac abi_encoder_input_typed >> fs[Once has_type_def]) >>
  `abi_encoder_member_span ((ei,abi_sz,mem_sz,dyn)::infos) = mem_sz+abi_encoder_member_span infos`
    by simp[abi_encoder_member_span_def] >>
  `abi_footprint_disjoint (sb+(so+mem_sz)) (abi_encoder_member_span infos)
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`sb+so`, `abi_encoder_member_span ((ei,abi_sz,mem_sz,dyn)::infos)`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_scratch_members_pre_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >> PURE_REWRITE_TAC [ADD_ASSOC] >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_scratch_members_child_buffer:
  abi_scratch_members_pre ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    st src dst sb so d output_size first last b cap s /\
  abi_decoder_operand_live st.cs_next_var elem_src /\
  eval_operand elem_src s = SOME (n2w (sb+so)) /\ LENGTH (enc ty av) <= output_size ==>
  abi_scratch_input ei ty av st elem_src dst (sb+so) mem_sz d output_size first last b cap s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_scratch_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_pre_def]) >>
  drule abi_encoder_members_input_cons >> strip_tac >>
  `abi_encoder_member_span ((ei,abi_sz,mem_sz,dyn)::infos) = mem_sz+abi_encoder_member_span infos`
    by simp[abi_encoder_member_span_def] >>
  `abi_footprint_disjoint (sb+so) mem_sz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`sb+so`, `abi_encoder_member_span ((ei,abi_sz,mem_sz,dyn)::infos)`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_scratch_input_def] >> decide_tac
QED

(* ===== State ===== *)

(* Pure state invariant for actual recursive member-list execution.
   TOP-LEVEL: abi_scratch_members_inv, its layout projection and the invariant
   after a completed child. The remaining source uses physical root ownership. *)

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

(* ===== Boundary ===== *)

(* Input and output boundaries for the full precise complex member execution.
   TOP-LEVEL: root_pre, initial_inv and final_output connect complete source
   buffers and canonical tuple bytes to the recursive member-list invariant. *)

Theorem abi_scratch_members_root_pre:
  abi_scratch_input (AbiComplex infos) at (ListV avs) st src dst sb source_cap d output_size
    first last b cap initial /\ abi_encoder_tuple_type at tys ==>
  abi_scratch_members_pre infos tys avs st src dst sb 0 d output_size first last b cap initial /\
  has_types tys avs /\ enc at (ListV avs) = enc (Tuple tys) (ListV avs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule_all abi_encoder_complex_input_tuple >> strip_tac >>
  qpat_assum `abi_encoder_input (AbiComplex infos) at _ _ _ _`
    (qx_choose_then `layout` (qx_choose_then `values` strip_assume_tac) o
      REWRITE_RULE [abi_encoder_complex_input_iff]) >>
  `layout = tys` by
    (irule abi_encoder_tuple_type_unique >> qexists_tac `at` >> asm_simp_tac bool_ss []) >>
  gvs[Excl "enc_def"] >> drule_all abi_encoder_tuple_input_types >> strip_tac >>
  `abi_footprint_disjoint sb (abi_encoder_member_span infos)
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    (irule abi_footprint_disjoint_subwindow >> qexistsl_tac [`sb`, `source_cap`] >> simp[]) >>
  qpat_assum `enc at (ListV _) = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  asm_simp_tac bool_ss [abi_scratch_members_pre_def, ADD_CLAUSES] >> decide_tac
QED

Theorem abi_scratch_members_initial_inv:
  abi_scratch_members_pre infos tys avs st src dst sb 0 d output_size first last b cap initial /\
  hl = head_lengths tys 0 /\ LENGTH (enc (Tuple tys) (ListV avs)) <= output_size /\
  abi_encoder_cursor active dyn_ptr site slot first lo st hl initial /\
  (active \/ EVERY (\(_,_,_,dyn). ~dyn) infos) /\
  abi_decoder_budget first last b cap initial /\ first <= lo /\ lo <= st.cs_next_id /\
  st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_scratch_members_inv infos tys avs [] [] active dyn_ptr site slot first last lo st limit_st
    src dst sb 0 0 d hl output_size b cap initial
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `hl = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  asm_simp_tac (srw_ss()) [abi_scratch_members_inv_def, has_type_def, abi_tuple_tails_def,
    Excl "enc_def"]
QED

Theorem abi_scratch_members_final_output:
  abi_scratch_members_inv [] [] [] tys avs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap actual ==>
  mem_bytes_at d (LENGTH (enc (Tuple tys) (ListV avs))) actual.vs_memory =
    enc (Tuple tys) (ListV avs) /\
  abi_encoder_cursor active dyn_ptr site slot first lo st
    (LENGTH (enc (Tuple tys) (ListV avs))) actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS o
    SIMP_RULE bool_ss [abi_scratch_members_inv_def, APPEND_NIL]) >>
  drule has_types_length >> strip_tac >>
  `LENGTH (enc (Tuple tys) (ListV avs)) = hl+LENGTH (FLAT (abi_tuple_tails tys avs))` by
    asm_simp_tac bool_ss [canonical_tuple_length, abi_tuple_tails_length, head_lengths_acc, ADD_CLAUSES] >>
  conj_tac
  >- (qpat_assum `hl = _`
        (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
      irule abi_encoder_tuple_prefix_complete >> asm_simp_tac bool_ss []) >>
  qpat_assum `LENGTH (enc (Tuple tys) (ListV avs)) = _`
    (fn th => PURE_REWRITE_TAC [th]) >> first_assum ACCEPT_TAC
QED

(* ===== Contract ===== *)

(* Recursive execution interface for actual complex member lists.
   TOP-LEVEL: abi_scratch_members_correct, its empty case and application rule.
   The contract requires child encoder induction hypotheses and pure resources. *)

Definition abi_scratch_members_correct_def:
  abi_scratch_members_correct infos <=>
    !tys avs pre pvs active dyn_ptr site slot first last lo st end_st limit_st src dst sb so ho d hl
      output_size b cap initial out func ctx.
    EVERY (\(ei,_,_,_). abi_scratch_encoder ei) infos /\
    compile_abi_encode_complex_elems dst src infos so ho dyn_ptr st = (out,end_st) /\
    fn_has_code st end_st func /\
    (st.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_members_inv infos tys avs pre pvs active dyn_ptr site slot first last lo st limit_st
      src dst sb so ho d hl output_size b cap initial /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
    ?t. abi_scratch_members_inv [] [] [] (pre++tys) (pvs++avs) active dyn_ptr site slot first last lo
        end_st limit_st src dst sb (so+abi_encoder_member_span infos)
        (ho+SUM (MAP (\(_,abi_sz,_,_). abi_sz) infos)) d hl output_size b cap t /\
      abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
        limit_st d output_size b cap initial t /\ abi_decode_sim ctx func initial t
End

Theorem abi_scratch_members_correct_empty:
  abi_scratch_members_correct []
Proof
  simp_tac bool_ss [abi_scratch_members_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  qpat_assum `abi_scratch_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_pre_def]) >>
  drule abi_encoder_members_empty_types >> strip_tac >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ [] _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_abi_encode_child_def, comp_return_def] >> strip_tac >>
  gvs[Excl "enc_def"] >>
  `abi_decoder_address_frame end_st.cs_next_var initial initial` by simp[abi_decoder_address_frame_def] >>
  `abi_scratch_effect first last lo end_st.cs_next_id end_st.cs_next_var
    limit_st d output_size b cap initial initial` by
    (drule_all abi_scratch_address_effect >> simp[]) >>
  qexists_tac `initial` >>
  asm_simp_tac (srw_ss()) [abi_encoder_member_span_def, abi_decode_sim_refl]
QED

Theorem abi_scratch_members_run:
  abi_scratch_members_correct infos /\ EVERY (\(ei,_,_,_). abi_scratch_encoder ei) infos /\
  compile_abi_encode_complex_elems dst src infos so ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_members_inv infos tys avs pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?t. abi_scratch_members_inv [] [] [] (pre++tys) (pvs++avs) active dyn_ptr site slot first last lo
      end_st limit_st src dst sb (so+abi_encoder_member_span infos)
      (ho+SUM (MAP (\(_,abi_sz,_,_). abi_sz) infos)) d hl output_size b cap t /\
    abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial t /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_scratch_members_correct _`
    (mp_tac o PURE_REWRITE_RULE [abi_scratch_members_correct_def]) >>
  disch_then (qspecl_then [`tys`, `avs`, `pre`, `pvs`, `active`, `dyn_ptr`, `site`, `slot`,
    `first`, `last`, `lo`, `st`, `end_st`, `limit_st`, `src`, `dst`, `sb`, `so`, `ho`, `d`, `hl`,
    `output_size`, `b`, `cap`, `initial`, `out`, `func`, `ctx`] mp_tac) >>
  asm_simp_tac bool_ss []
QED

(* ===== Prepare ===== *)

(* Enter a member by running the compiler's actual source-address ADD.
   TOP-LEVEL: abi_scratch_members_prepare retains the processed prefix and
   cursor, and establishes the child's complete physical buffer contract. *)

Theorem abi_scratch_members_prepare:
  emit_op ADD [src;Lit (n2w so)] st = (elem_src,prepared) /\ fn_has_code st prepared func /\
  abi_scratch_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  prepared.cs_next_var <= limit_st.cs_next_var ==>
  ?ready. abi_scratch_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
      pre pvs active dyn_ptr site slot first last lo prepared limit_st
      src dst sb so ho d hl output_size b cap ready /\
    abi_scratch_input ei ty av prepared elem_src dst (sb+so) mem_sz d output_size first last b cap ready /\
    abi_decoder_address_frame st.cs_next_var initial ready /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_members_inv_layout >> strip_tac >>
  `LENGTH (enc ty av) <= output_size` by (Cases_on `dyn` >> fs[] >> decide_tac) >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  `eval_operand src initial = SOME (n2w sb)` by fs[abi_scratch_members_pre_def] >>
  drule emitted_insts_emit_op >> strip_tac >> drule abi_decoder_operand_live_emit >> strip_tac >>
  `st.cs_next_var <= prepared.cs_next_var /\ st.cs_next_id <= prepared.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`opc` |-> `ADD`, `lhs` |-> `src`, `rhs` |-> `Lit (n2w so)`,
    `st'` |-> `prepared`, `out` |-> `elem_src`, `a` |-> `n2w sb:bytes32`, `b` |-> `n2w so:bytes32`]
    abi_encoder_binary_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  `eval_operand elem_src ready = SOME (n2w (sb+so))` by fs[word_add_n2w] >>
  mp_tac (Q.INST [`actual` |-> `ready:venom_state`, `infos` |-> `(ei,abi_sz,mem_sz,dyn)::infos`,
    `tys` |-> `ty::tys`, `avs` |-> `av::avs`, `sz` |-> `output_size:num`]
    abi_scratch_members_pre_address) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`actual` |-> `ready:venom_state`,
    `off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`] abi_encoder_cursor_address) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`st` |-> `prepared:compile_state`, `s` |-> `ready:venom_state`]
    abi_scratch_members_child_buffer) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `s` |-> `initial:venom_state`,
    `t` |-> `ready:venom_state`] abi_scratch_address) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_encoder_tuple_prefix hl pre pvs d ready.vs_memory` by
    (qpat_assum `abi_decoder_address_frame _ _ _` (fn th =>
       assume_tac (CONJUNCT1 (CONJUNCT2 (PURE_REWRITE_RULE [abi_decoder_address_frame_def] th)))) >>
     gvs[Excl "enc_def"]) >>
  qpat_assum `hl = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qpat_assum `ho = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qexists_tac `ready` >> asm_simp_tac bool_ss [abi_scratch_members_inv_def] >> decide_tac
QED
