(* Pure input and output boundaries for execution of all complex encoder members. *)
Theory abiEncoderMembersBoundary
Ancestors
  abiEncoderMembersContract abiEncoderMembersDefs abiEncoderMembersInput abiEncoderCorrect
  abiEncoderInput abiEncoderBufferFrame abiEncoderTuple abiCanonicalWindows abiDecodeRanges
  abiDecoderAllocation abiDecoderContract compileEnv valueEncoding contractABI venomState list
  arithmetic

Theorem abi_encoder_members_root_pre:
  abi_encoder_pre (AbiComplex infos) at (ListV avs) st src dst sb source_cap d b cap initial /\
  abi_encoder_tuple_type at tys ==>
  abi_encoder_members_pre infos tys avs st src dst sb 0 d
    (LENGTH (enc at (ListV avs))) b cap initial /\
  has_types tys avs /\ enc at (ListV avs) = enc (Tuple tys) (ListV avs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_pre _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_pre_def]) >>
  drule_all abi_encoder_complex_input_tuple >> strip_tac >>
  qpat_assum `abi_encoder_input (AbiComplex infos) at _ _ _ _`
    (qx_choose_then `layout` (qx_choose_then `values` strip_assume_tac) o
      REWRITE_RULE [abi_encoder_complex_input_iff]) >>
  `layout = tys` by
    (irule abi_encoder_tuple_type_unique >> qexists_tac `at` >> asm_simp_tac bool_ss []) >>
  gvs[Excl "enc_def"] >> drule_all abi_encoder_tuple_input_types >> strip_tac >>
  qpat_assum `enc at (ListV _) = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  asm_simp_tac bool_ss [abi_encoder_members_pre_def, ADD_CLAUSES] >> decide_tac
QED

Theorem abi_encoder_members_initial_inv:
  abi_encoder_members_pre infos tys avs st src dst sb 0 d output_size b cap initial /\
  hl = head_lengths tys 0 /\ LENGTH (enc (Tuple tys) (ListV avs)) <= output_size /\
  abi_encoder_cursor active dyn_ptr site slot first lo st hl initial /\
  (active \/ EVERY (\(_,_,_,dyn). ~dyn) infos) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ lo <= st.cs_next_id /\
  st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_members_inv infos tys avs [] [] active dyn_ptr site slot first last lo st limit_st
    src dst sb 0 0 d hl output_size b cap initial
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `hl = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  asm_simp_tac (srw_ss()) [abi_encoder_members_inv_def, has_type_def, abi_tuple_tails_def,
    Excl "enc_def"]
QED

Theorem abi_encoder_members_final_output:
  abi_encoder_members_inv [] [] [] tys avs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap actual ==>
  mem_bytes_at d (LENGTH (enc (Tuple tys) (ListV avs))) actual.vs_memory =
    enc (Tuple tys) (ListV avs) /\
  abi_encoder_cursor active dyn_ptr site slot first lo st
    (LENGTH (enc (Tuple tys) (ListV avs))) actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS o
    SIMP_RULE bool_ss [abi_encoder_members_inv_def, APPEND_NIL]) >>
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
