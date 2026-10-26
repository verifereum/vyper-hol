(* Input and output boundaries for the full precise complex member execution.
   TOP-LEVEL: root_pre, initial_inv and final_output connect complete source
   buffers and canonical tuple bytes to the recursive member-list invariant. *)
Theory abiScratchMembersBoundary
Ancestors
  abiScratchMembersState abiScratchMembersPre abiScratchEncoderContract
  abiEncoderMembersDefs abiEncoderMembersInput abiEncoderInput abiEncoderInputLayout
  abiEncoderBufferFrame abiEncoderArrayFrame abiEncoderTuplePrefix abiCanonicalWindows
  abiDecodeRanges abiDecoderAllocation abiDecoderFootprint abiDecoderFrame
  abiDecoderReentry abiDecoderContract compileEnv valueEncoding contractABI
  venomState words list arithmetic

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

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_MEMBERS_BOUNDARY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch complex boundaries not kernel closed: " ^ n)
  end) (DB.thms "abiScratchMembersBoundary");
