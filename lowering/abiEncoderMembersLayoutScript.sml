(* Canonical bounds and offsets needed by one recursive member step. *)
Theory abiEncoderMembersLayout
Ancestors
  abiEncoderMembersContract abiEncoderMembersSource abiEncoderTuplePrefix abiCanonicalWindows
  abiDecodeRanges contractABI list arithmetic

Theorem abi_encoder_members_layout:
  has_types (pre++ty::tys) (pvs++av::avs) /\ LENGTH pre = LENGTH pvs /\
  hl = head_lengths (pre++ty::tys) 0 /\ heads = SUM (MAP abi_member_head_size pre) /\
  tails = SUM (MAP2 abi_member_tail_size pre pvs) /\
  LENGTH (enc (Tuple (pre++ty::tys)) (ListV (pvs++av::avs))) <= output_size ==>
  has_types pre pvs /\ has_type ty av /\ has_types tys avs /\
  heads = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  tails = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  heads+abi_member_head_size ty <= hl /\ hl+tails <= output_size /\
  (~is_dynamic ty ==> heads+LENGTH (enc ty av) <= hl) /\
  (is_dynamic ty ==> heads+32 <= hl /\ hl+tails+LENGTH (enc ty av) <= output_size)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `has_types pre pvs /\ has_type ty av /\ has_types tys avs`
    by fs[has_types_append, has_type_def] >>
  `heads+abi_member_head_size ty <= hl` by
    simp[head_lengths_acc, MAP_APPEND, SUM_APPEND] >>
  `LENGTH (enc (Tuple (pre++ty::tys)) (ListV (pvs++av::avs))) =
    hl+tails+abi_member_tail_size ty av+SUM (MAP2 abi_member_tail_size tys avs)` by
    asm_simp_tac bool_ss [canonical_tuple_length, head_lengths_acc, MAP_APPEND, MAP2_APPEND,
      SUM_APPEND, MAP, MAP2, SUM, ADD_CLAUSES, AC ADD_COMM ADD_ASSOC] >>
  `~is_dynamic ty ==> LENGTH (enc ty av) = static_length ty` by
    (strip_tac >> irule (cj 1 enc_has_static_length) >> simp[]) >>
  Cases_on `is_dynamic ty` >>
  full_simp_tac bool_ss [abi_member_head_size_def, abi_member_tail_size_def,
    abi_tuple_heads_length, abi_tuple_tails_length] >> decide_tac
QED

Theorem abi_encoder_members_prefix_advance:
  has_types pre pvs /\ has_type ty av ==>
  has_types (pre++[ty]) (pvs++[av]) /\
  SUM (MAP abi_member_head_size (pre++[ty])) =
    SUM (MAP abi_member_head_size pre)+abi_member_head_size ty /\
  LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av]))) =
    LENGTH (FLAT (abi_tuple_tails pre pvs))+(if is_dynamic ty then LENGTH (enc ty av) else 0)
Proof
  strip_tac >> drule has_types_length >> strip_tac >>
  simp[has_types_append, has_type_def, MAP_APPEND, SUM_APPEND,
    abi_tuple_tails_append, abi_tuple_tails_def, FLAT_APPEND] >>
  Cases_on `is_dynamic ty` >> simp[]
QED

Theorem abi_encoder_members_inv_layout:
  abi_encoder_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
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
  strip_tac >> qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`] abi_encoder_members_pre_cons) >>
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

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_MEMBERS_LAYOUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder members layout not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderMembersLayout");
