Theory abiScratchComplex
Ancestors
  abiScratchMembers abiScratchOwnedPrefix abiScratchPrefix abiScratchEncoderContract
  abiEncoderComplexPrefix abiEncoderComplexLayout abiEncoderMembersDefs abiEncoderInput
  abiDecoderAllocation abiDecoderReentry abiDecoderContract abiDecoderLoop compileEnv
  valueEncoding contractABI venomState words list arithmetic abiScratchAddress
  abiEncoderLoadReach abiDecoderDynamicLoopSetup abiDecoderProtectedScratch abiDecoderIndexInit
  emitHelperProps pred_set abiScratchMembersCorrect abiScratchEffect abiEncoderComplexContext
  abiEncoderComplexStatic abiEncoderComplexCode abiEncoderMemberCode abiEncoderMembersInput

(* ===== Prepare ===== *)

(* Establish the complex member invariant using the real cursor initializer.
   TOP-LEVEL: abi_scratch_complex_prepare derives the registered head-length
   cursor while preserving complete source data and physical root separation. *)

Theorem abi_scratch_complex_prepare:
  abi_encode_complex_prefix infos st = (dyn_ptr,prepared) /\ fn_has_code st prepared func /\
  abi_scratch_members_pre infos tys avs st src dst sb 0 d output_size first last b cap initial /\
  LENGTH (enc (Tuple tys) (ListV avs)) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  prepared.cs_next_id <= last /\ prepared.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready slot.
    abi_scratch_members_inv infos tys avs [] [] T dyn_ptr st.cs_next_id slot first last
      st.cs_next_id prepared limit_st src dst sb 0 0 d (head_lengths tys 0) output_size b cap ready /\
    abi_scratch_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial ready /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_pre_def]) >>
  drule abi_encoder_complex_input_metadata >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `st.cs_next_id < prepared.cs_next_id /\ st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  drule_all abi_scratch_owned_prefix_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  mp_tac (Q.INST [`site` |-> `st.cs_next_id`, `stop` |-> `prepared.cs_next_id`,
    `next` |-> `st.cs_next_var`, `sz` |-> `output_size:num`, `actual` |-> `ready:venom_state`]
    abi_scratch_prefix_effect) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `prepared.cs_next_id`,
    `so` |-> `0:num`, `sz` |-> `output_size:num`, `actual` |-> `ready:venom_state`]
    abi_scratch_members_pre_effect) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  mp_tac (Q.INST [`prepared` |-> `prepared:compile_state`, `s` |-> `ready:venom_state`,
    `so` |-> `0:num`, `sz` |-> `output_size:num`] abi_scratch_members_pre_mono) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  drule_all abi_scratch_prefix_cursor >> strip_tac >>
  `fresh_vars_wrt limit_st ready /\ abi_decoder_budget first last b cap ready` by
    fs[abi_scratch_effect_def] >>
  mp_tac (Q.INST [`active` |-> `T`, `site` |-> `st.cs_next_id`, `lo` |-> `st.cs_next_id`,
    `st` |-> `prepared`, `initial` |-> `ready:venom_state`, `hl` |-> `head_lengths tys 0`]
    abi_scratch_members_initial_inv) >>
  impl_tac >- (gvs[Excl "enc_def"] >> decide_tac) >> disch_tac >>
  qexistsl_tac [`ready`, `slot`] >> full_simp_tac bool_ss []
QED

(* ===== Finish ===== *)

(* Load the completed complex encoder's cursor at its real instruction endpoint.
   TOP-LEVEL: abi_scratch_complex_finish preserves exact encoded bytes and
   introduces a precise address-only effect without whole-arena separation. *)

Theorem abi_scratch_complex_finish:
  abi_scratch_members_inv [] [] [] tys avs T dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap encoded /\
  emit_op MLOAD [dyn_ptr] st = (out,end_st) /\ fn_has_code st end_st func /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual.
    mem_bytes_at d (LENGTH (enc (Tuple tys) (ListV avs))) actual.vs_memory =
      enc (Tuple tys) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple tys) (ListV avs)))) /\
    abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap encoded actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func encoded actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_members_final_output >> strip_tac >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ encoded`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  qpat_x_assum `abi_encoder_cursor T _ _ _ _ _ _ (LENGTH _) _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `site IN abi_decoder_ids first last` by
    (simp_tac std_ss [abi_decoder_ids_def, GSPECIFICATION] >> decide_tac) >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  drule abi_decoder_budget_word_bound >> strip_tac >> `slot < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`src` |-> `dyn_ptr`, `p` |-> `n2w slot:bytes32`,
    `w` |-> `n2w (LENGTH (enc (Tuple tys) (ListV avs))):bytes32`, `st'` |-> `end_st`,
    `initial` |-> `encoded:venom_state`] abi_encoder_load_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [w2n_n2w] >> strip_tac >>
  rename1 `abi_decode_sim ctx func encoded actual` >>
  mp_tac (Q.INST [`initial` |-> `encoded:venom_state`, `actual` |-> `actual:venom_state`,
    `next` |-> `st.cs_next_var`, `hi` |-> `end_st.cs_next_id`, `sz` |-> `output_size:num`]
    abi_scratch_address_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* ===== Dynamic ===== *)

(* Dynamic complex constructors execute cursor setup, every member and final load.
   TOP-LEVEL: abi_scratch_encoder_complex_dynamic proves the precise encoder
   contract, including registered parent-cursor writes and allocation evolution. *)

Theorem abi_scratch_complex_compose:
  abi_scratch_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
    limit_st d sz b cap initial ready /\
  abi_scratch_effect first last st.cs_next_id middle.cs_next_id prepared.cs_next_var
    limit_st d sz b cap ready encoded /\
  abi_scratch_effect first last st.cs_next_id end_st.cs_next_id middle.cs_next_var
    limit_st d sz b cap encoded actual /\
  first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  prepared.cs_next_id <= end_st.cs_next_id /\ middle.cs_next_id <= end_st.cs_next_id /\
  st.cs_next_var <= prepared.cs_next_var /\ st.cs_next_var <= middle.cs_next_var /\
  abi_decode_sim ctx func initial ready /\ abi_decode_sim ctx func ready encoded /\
  abi_decode_sim ctx func encoded actual ==>
  abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d sz b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d sz b cap initial ready` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `prepared.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `sz`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d sz b cap ready encoded` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `middle.cs_next_id`, `st.cs_next_id`, `prepared.cs_next_var`, `sz`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d sz b cap encoded actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `st.cs_next_id`, `middle.cs_next_var`, `sz`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d sz b cap initial encoded` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >> qexists_tac `ready` >> simp[]) >>
  conj_tac
  >- (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >> qexists_tac `encoded` >> simp[]) >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `encoded` >> simp[]
QED

Theorem abi_scratch_encoder_complex_dynamic:
  EVERY (\(ei,_,_,_). abi_scratch_encoder ei) infos /\
  EXISTS (\(_,_,_,dyn). dyn) infos ==>
  abi_scratch_encoder (AbiComplex infos)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [abi_scratch_encoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  disch_then (qx_choose_then `tys` (qx_choose_then `avs`
    (MAP_EVERY assume_tac o CONJUNCTS)) o REWRITE_RULE [abi_encoder_complex_input_iff]) >>
  qpat_x_assum `av = ListV avs` SUBST_ALL_TAC >>
  drule_all abi_scratch_members_root_pre >> strip_tac >>
  qpat_assum `enc at (ListV avs) = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  drule_all abi_encoder_complex_dynamic_context >>
  disch_then (qx_choose_then `dyn_ptr` (qx_choose_then `prepared`
    (qx_choose_then `ignored` (qx_choose_then `middle` (MAP_EVERY assume_tac o CONJUNCTS))))) >>
  `prepared.cs_next_id <= last /\ middle.cs_next_id <= last /\
    prepared.cs_next_var <= limit_st.cs_next_var /\ middle.cs_next_var <= limit_st.cs_next_var /\
    start.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `output_size` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_scratch_complex_prepare) >>
  impl_tac >- asm_simp_tac (srw_ss()) [Excl "enc_def"] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  mp_tac (Q.INST [`active` |-> `T`, `site` |-> `start.cs_next_id`, `lo` |-> `start.cs_next_id`,
    `st` |-> `prepared`, `end_st` |-> `middle`, `out` |-> `ignored`, `initial` |-> `ready:venom_state`,
    `pre` |-> `[]:abi_type list`, `pvs` |-> `[]:abi_value list`, `so` |-> `0:num`, `ho` |-> `0:num`,
    `hl` |-> `head_lengths tys 0`, `output_size` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_scratch_members_run) >>
  impl_tac >- asm_simp_tac bool_ss [abi_scratch_members_correct_all] >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready encoded` >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ encoded`
    (assume_tac o SIMP_RULE bool_ss [APPEND, ADD_CLAUSES]) >>
  mp_tac (Q.INST [`st` |-> `middle`, `site` |-> `start.cs_next_id`, `lo` |-> `start.cs_next_id`,
    `so` |-> `abi_encoder_member_span infos`,
    `ho` |-> `SUM (MAP (\(_,asz,_,_). asz) (infos:(abi_enc_info # num # num # bool) list))`,
    `hl` |-> `head_lengths tys 0`, `output_size` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_scratch_complex_finish) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func encoded actual` >>
  mp_tac (Q.INST [`st` |-> `start`, `sz` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_scratch_complex_compose) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* ===== Static ===== *)

(* Static complex constructors execute every actual member and return its size.
   TOP-LEVEL: abi_scratch_encoder_complex_static establishes the precise
   recursive encoder contract from the child constructor hypotheses. *)

Theorem abi_scratch_encoder_complex_static:
  EVERY (\(ei,_,_,_). abi_scratch_encoder ei) infos /\
  ~EXISTS (\(_,_,_,dyn). dyn) infos ==>
  abi_scratch_encoder (AbiComplex infos)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [abi_scratch_encoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  disch_then (qx_choose_then `tys` (qx_choose_then `avs`
    (MAP_EVERY assume_tac o CONJUNCTS)) o REWRITE_RULE [abi_encoder_complex_input_iff]) >>
  qpat_x_assum `av = ListV avs` SUBST_ALL_TAC >>
  drule_all abi_scratch_members_root_pre >> strip_tac >>
  qpat_assum `enc at (ListV avs) = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qpat_assum `abi_scratch_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_scratch_members_pre_def]) >> strip_tac >>
  drule_all abi_encoder_complex_static_length >> disch_tac >>
  drule abi_encoder_complex_static_flags >> disch_tac >>
  drule_all abi_encoder_complex_static_trace >> strip_tac >>
  drule abi_encoder_members_bounds >> strip_tac >>
  `start.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`active` |-> `F`, `dyn_ptr` |-> `Lit 0w`, `site` |-> `0:num`,
    `slot` |-> `0:num`, `lo` |-> `start.cs_next_id`, `st` |-> `start`,
    `hl` |-> `head_lengths tys 0`, `output_size` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_scratch_members_initial_inv) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_encoder_cursor_def, Excl "enc_def"] >> disch_tac >>
  mp_tac (Q.INST [`active` |-> `F`, `dyn_ptr` |-> `Lit 0w`, `site` |-> `0:num`,
    `slot` |-> `0:num`, `lo` |-> `start.cs_next_id`, `st` |-> `start`, `out` |-> `ignored`,
    `pre` |-> `[]:abi_type list`, `pvs` |-> `[]:abi_value list`, `so` |-> `0:num`, `ho` |-> `0:num`,
    `hl` |-> `head_lengths tys 0`, `output_size` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_scratch_members_run) >>
  impl_tac >- asm_simp_tac bool_ss [abi_scratch_members_correct_all] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ actual`
    (assume_tac o SIMP_RULE bool_ss [APPEND, ADD_CLAUSES]) >>
  drule abi_scratch_members_final_output >> strip_tac >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ actual`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [eval_operand_def, Excl "enc_def"]
QED
