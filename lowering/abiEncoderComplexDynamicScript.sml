Theory abiEncoderComplexDynamic
Ancestors
  abiEncoderComplexCode abiEncoderComplexPrefix abiEncoderMemberCode abiEncoderAddressReach
  abiDecoderContract fragExec emitHelperProps compileEnv valueEncoding venomState words list
  arithmetic abiEncoderLoadReach abiEncoderMembersBoundary abiEncoderMembersContract
  abiEncoderMembersDefs abiDecoderEffect abiDecoderDynamicLoopSetup abiDecoderProtectedScratch
  abiDecoderIndexInit abiDecoderAllocation contractABI pred_set abiDecoderLoop
  abiEncoderMembersInput abiEncoderInput abiDecodeRanges rich_list abiEncoderMembersCorrect
  abiEncoderCorrect abiDecoderReentry

(* Split a real dynamic complex encoder into its three executable CFG phases. *)
Theorem abi_encoder_complex_dynamic_context:
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  ?dyn_ptr prepared ignored middle.
    abi_encode_complex_prefix infos st = (dyn_ptr,prepared) /\
    compile_abi_encode_complex_elems dst src infos 0 0 dyn_ptr prepared = (ignored,middle) /\
    emit_op MLOAD [dyn_ptr] middle = (out,end_st) /\
    fn_has_code st prepared func /\ fn_has_code prepared middle func /\ fn_has_code middle end_st func /\
    prepared.cs_next_id = st.cs_next_id+2 /\ prepared.cs_next_var = st.cs_next_var+1 /\
    prepared.cs_next_id <= middle.cs_next_id /\ middle.cs_next_id < end_st.cs_next_id /\
    prepared.cs_next_var <= middle.cs_next_var /\ middle.cs_next_var < end_st.cs_next_var /\
    (prepared.cs_blocks = middle.cs_blocks \/
      !bb. lookup_block middle.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_complex_dynamic_trace >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  drule abi_encoder_members_bounds >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `cs_extends st prepared` by
    (irule cs_extends_same_block >> fs[inst_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends prepared end_st` by
    (irule cs_extends_trans >> qexists_tac `middle` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`st`, `prepared`, `end_st`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.SPECL [`prepared`, `middle`, `end_st`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `middle.cs_next_id < end_st.cs_next_id /\ middle.cs_next_var < end_st.cs_next_var` by decide_tac >>
  qexistsl_tac [`dyn_ptr`, `prepared`, `ignored`, `middle`] >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `_ \/ _` mp_tac >> asm_simp_tac bool_ss []
QED

(* Load the completed parent's cursor without changing the encoded bytes. *)
Theorem abi_encoder_complex_finish:
  abi_encoder_members_inv [] [] [] tys avs T dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap encoded /\
  emit_op MLOAD [dyn_ptr] st = (out,end_st) /\ fn_has_code st end_st func /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual.
    mem_bytes_at d (LENGTH (enc (Tuple tys) (ListV avs))) actual.vs_memory =
      enc (Tuple tys) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple tys) (ListV avs)))) /\
    abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap encoded actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func encoded actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_members_final_output >> strip_tac >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ encoded`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
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
  mp_tac (Q.INST [`s` |-> `encoded:venom_state`, `t` |-> `actual:venom_state`,
    `next` |-> `st.cs_next_var`, `child_next` |-> `st.cs_next_var`, `hi` |-> `end_st.cs_next_id`,
    `sz` |-> `output_size:num`] abi_decoder_address_effect) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* Sequential recursive effects can grow their owned interval and local-variable frontier. *)
Theorem abi_decoder_effect_sequence:
  abi_decoder_effect first last lo mid next limit_st d sz b cap initial ready /\
  abi_decoder_effect first last lo hi later limit_st d sz b cap ready actual /\
  mid <= hi /\ next <= later ==>
  abi_decoder_effect first last lo hi next limit_st d sz b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_effect first last lo hi next limit_st d sz b cap initial ready` by
    (irule abi_decoder_effect_widen >> qexistsl_tac [`d`, `mid`, `lo`, `next`, `sz`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decoder_effect first last lo hi next limit_st d sz b cap ready actual` by
    (irule abi_decoder_effect_widen >> qexistsl_tac [`d`, `hi`, `lo`, `later`, `sz`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  irule abi_decoder_effect_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_complex_compose:
  abi_decoder_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
    limit_st d sz b cap initial ready /\
  abi_decoder_effect first last st.cs_next_id middle.cs_next_id prepared.cs_next_var
    limit_st d sz b cap ready encoded /\
  abi_decoder_effect first last st.cs_next_id end_st.cs_next_id middle.cs_next_var
    limit_st d sz b cap encoded actual /\
  prepared.cs_next_id <= middle.cs_next_id /\ middle.cs_next_id <= end_st.cs_next_id /\
  st.cs_next_var <= prepared.cs_next_var /\ prepared.cs_next_var <= middle.cs_next_var /\
  abi_decode_sim ctx func initial ready /\ abi_decode_sim ctx func ready encoded /\
  abi_decode_sim ctx func encoded actual ==>
  abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d sz b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_effect first last st.cs_next_id middle.cs_next_id st.cs_next_var
    limit_st d sz b cap initial encoded` by
    (mp_tac (Q.INST [`ready` |-> `ready:venom_state`, `actual` |-> `encoded:venom_state`,
      `lo` |-> `st.cs_next_id`, `hi` |-> `middle.cs_next_id`, `next` |-> `st.cs_next_var`,
      `later` |-> `prepared.cs_next_var`, `mid` |-> `prepared.cs_next_id`]
      abi_decoder_effect_sequence) >> asm_simp_tac bool_ss []) >>
  conj_tac
  >- (mp_tac (Q.INST [`ready` |-> `encoded:venom_state`, `lo` |-> `st.cs_next_id`,
        `hi` |-> `end_st.cs_next_id`, `next` |-> `st.cs_next_var`, `later` |-> `middle.cs_next_var`,
        `mid` |-> `middle.cs_next_id`] abi_decoder_effect_sequence) >>
      impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> asm_simp_tac bool_ss []) >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `encoded` >> asm_simp_tac bool_ss []
QED

(* Complex descriptor heads and dynamic flags agree with semantic tuple layout. *)
Theorem abi_encoder_members_metadata:
  LENGTH (infos:(abi_enc_info # num # num # bool) list) = LENGTH tys /\
  (!i ei asz msz dyn. i < LENGTH infos /\ EL i infos = (ei,asz,msz,dyn) ==>
    asz = abi_member_head_size (EL i tys) /\ dyn = is_dynamic (EL i tys)) ==>
  MAP (\(_,asz,_,_). asz) infos = MAP abi_member_head_size tys /\
  MAP (\(_,_,_,dyn). dyn) infos = MAP is_dynamic tys
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> conj_tac >>
  irule LIST_EQ >> asm_simp_tac (srw_ss()) [EL_MAP] >> qx_gen_tac `i` >> strip_tac >>
  Cases_on `EL i infos` >> rename1 `EL i infos = (child,rest)` >> PairCases_on `rest` >>
  qpat_x_assum `!i ei asz msz dyn. _`
    (qspecl_then [`i`, `child`, `rest0`, `rest1`, `rest2`] mp_tac) >>
  asm_simp_tac (srw_ss()) []
QED

Theorem abi_encoder_any_dynamic:
  !tys. EXISTS is_dynamic tys = any_dynamic tys
Proof
  Induct >> simp[is_dynamic_def]
QED

Theorem abi_encoder_complex_input_metadata:
  abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb capacity mem ==>
  SUM (MAP (\(_,asz,_,_). asz) infos) = head_lengths tys 0 /\
  (EXISTS (\(_,_,_,dyn). dyn) infos <=> any_dynamic tys) /\ has_types tys avs
Proof
  strip_tac >> qpat_x_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `layout` (qx_choose_then `values` strip_assume_tac) o
      REWRITE_RULE [abi_encoder_complex_input_iff]) >>
  gvs[abi_encoder_tuple_type_def, Once has_type_def] >>
  rename1 `has_types tys avs` >>
  mp_tac (Q.INST [`tys` |-> `tys:abi_type list`] abi_encoder_members_metadata) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  strip_tac >>
  qpat_assum `MAP (\(_,_,_,dyn). dyn) infos = _`
    (assume_tac o SIMP_RULE (srw_ss()) [EXISTS_MAP, ETA_AX] o AP_TERM ``EXISTS I:bool list -> bool``) >>
  asm_simp_tac (srw_ss()) [head_lengths_acc, ADD_CLAUSES, GSYM abi_encoder_any_dynamic] >>
  qpat_x_assum `EXISTS _ infos = _` mp_tac >> simp[EXISTS_MEM]
QED

Theorem abi_encoder_static_tuple_tails:
  !tys avs. ~any_dynamic tys ==> SUM (MAP2 abi_member_tail_size tys avs) = 0
Proof
  Induct >> Cases_on `avs` >> simp[is_dynamic_def, abi_member_tail_size_def]
QED

Theorem abi_encoder_complex_static_length:
  abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb capacity mem /\
  ~EXISTS (\(_,_,_,dyn). dyn) infos ==>
  LENGTH (enc (Tuple tys) (ListV avs)) = SUM (MAP (\(_,asz,_,_). asz) infos)
Proof
  strip_tac >> drule abi_encoder_complex_input_metadata >> strip_tac >>
  `~any_dynamic tys` by
    (qpat_assum `EXISTS _ infos = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  drule abi_encoder_static_tuple_tails >> disch_then (qspec_then `avs` assume_tac) >>
  asm_simp_tac bool_ss [canonical_tuple_length, head_lengths_acc, ADD_CLAUSES]
QED

(* Top-level static complex encoders execute all members and return the exact length. *)
Theorem abi_encoder_complex_static_flags:
  !infos. ~EXISTS (\(_,_,_,dyn). dyn) infos ==>
    EVERY (\(_,_,_,dyn). ~dyn) infos
Proof
  Induct >> simp[] >> qx_gen_tac `entry` >> PairCases_on `entry` >> simp[]
QED

Theorem abi_encoder_correct_complex_static:
  EVERY (\(ei,_,_,_). abi_encoder_correct ei) infos /\
  ~EXISTS (\(_,_,_,dyn). dyn) infos ==>
  abi_encoder_correct (AbiComplex infos)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [abi_encoder_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_pre _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_encoder_pre_def]) >>
  disch_then (qx_choose_then `tys` (qx_choose_then `avs`
    (MAP_EVERY assume_tac o CONJUNCTS)) o REWRITE_RULE [abi_encoder_complex_input_iff]) >>
  qpat_x_assum `av = ListV avs` SUBST_ALL_TAC >>
  drule_all abi_encoder_members_root_pre >> strip_tac >>
  qpat_assum `enc at (ListV avs) = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qpat_assum `abi_encoder_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_encoder_members_pre_def]) >> strip_tac >>
  drule_all abi_encoder_complex_static_length >> disch_tac >>
  drule abi_encoder_complex_static_flags >> disch_tac >>
  drule_all abi_encoder_complex_static_trace >> strip_tac >>
  drule abi_encoder_members_bounds >> strip_tac >>
  `start.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`active` |-> `F`, `dyn_ptr` |-> `Lit 0w`, `site` |-> `0:num`,
    `slot` |-> `0:num`, `lo` |-> `start.cs_next_id`, `st` |-> `start`,
    `hl` |-> `head_lengths tys 0`, `output_size` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_encoder_members_initial_inv) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_encoder_cursor_def, Excl "enc_def"] >> disch_tac >>
  mp_tac (Q.INST [`active` |-> `F`, `dyn_ptr` |-> `Lit 0w`, `site` |-> `0:num`,
    `slot` |-> `0:num`, `lo` |-> `start.cs_next_id`, `st` |-> `start`, `out` |-> `ignored`,
    `pre` |-> `[]:abi_type list`, `pvs` |-> `[]:abi_value list`, `so` |-> `0:num`, `ho` |-> `0:num`,
    `hl` |-> `head_lengths tys 0`, `output_size` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_encoder_members_run) >>
  impl_tac >- asm_simp_tac bool_ss [abi_encoder_members_correct_all] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ actual`
    (assume_tac o SIMP_RULE bool_ss [APPEND, ADD_CLAUSES]) >>
  drule abi_encoder_members_final_output >> strip_tac >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ actual`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [eval_operand_def, Excl "enc_def"]
QED

(* Establish the full member-loop invariant by executing the real cursor initializer. *)
Theorem abi_encoder_complex_prepare:
  abi_encode_complex_prefix infos st = (dyn_ptr,prepared) /\ fn_has_code st prepared func /\
  abi_encoder_members_pre infos tys avs st src dst sb 0 d output_size b cap initial /\
  LENGTH (enc (Tuple tys) (ListV avs)) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  prepared.cs_next_id <= last /\ prepared.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready slot.
    abi_encoder_members_inv infos tys avs [] [] T dyn_ptr st.cs_next_id slot first last
      st.cs_next_id prepared limit_st src dst sb 0 0 d (head_lengths tys 0) output_size b cap ready /\
    abi_decoder_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial ready /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_pre_def]) >>
  drule abi_encoder_complex_input_metadata >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `st.cs_next_id IN abi_decoder_ids first last` by
    (simp_tac std_ss [abi_decoder_ids_def, GSPECIFICATION] >> decide_tac) >>
  drule_all abi_encoder_complex_prefix_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  mp_tac (Q.INST [`site` |-> `st.cs_next_id`, `hi` |-> `prepared.cs_next_id`,
    `next` |-> `st.cs_next_var`, `outsz` |-> `output_size:num`, `actual` |-> `ready:venom_state`]
    abi_encoder_complex_prefix_effect) >>
  impl_tac >- (full_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `prepared.cs_next_id`,
    `so` |-> `0:num`, `actual` |-> `ready:venom_state`] abi_encoder_members_pre_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  drule_all abi_encoder_members_pre_mono >> strip_tac >>
  qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ ready`
    (qx_choose_then `slot` (MAP_EVERY assume_tac o CONJUNCTS) o
      PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  `abi_decoder_operand_live prepared.cs_next_var dyn_ptr` by
    (asm_simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> decide_tac) >>
  `abi_encoder_cursor T dyn_ptr st.cs_next_id slot first st.cs_next_id prepared
    (head_lengths tys 0) ready` by
    (full_simp_tac bool_ss [abi_encoder_cursor_def] >> decide_tac) >>
  mp_tac (Q.INST [`active` |-> `T`, `site` |-> `st.cs_next_id`, `lo` |-> `st.cs_next_id`,
    `st` |-> `prepared`, `initial` |-> `ready:venom_state`, `hl` |-> `head_lengths tys 0`]
    abi_encoder_members_initial_inv) >>
  impl_tac >- (full_simp_tac bool_ss [] >> decide_tac) >> disch_tac >>
  qexistsl_tac [`ready`, `slot`] >> full_simp_tac bool_ss []
QED

(* Top-level dynamic complex encoders compose cursor setup, every member and the final load. *)
Theorem abi_encoder_correct_complex_dynamic:
  EVERY (\(ei,_,_,_). abi_encoder_correct ei) infos /\
  EXISTS (\(_,_,_,dyn). dyn) infos ==>
  abi_encoder_correct (AbiComplex infos)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [abi_encoder_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_pre _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_encoder_pre_def]) >>
  disch_then (qx_choose_then `tys` (qx_choose_then `avs`
    (MAP_EVERY assume_tac o CONJUNCTS)) o REWRITE_RULE [abi_encoder_complex_input_iff]) >>
  qpat_x_assum `av = ListV avs` SUBST_ALL_TAC >>
  drule_all abi_encoder_members_root_pre >> strip_tac >>
  qpat_assum `enc at (ListV avs) = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  drule_all abi_encoder_complex_dynamic_context >>
  disch_then (qx_choose_then `dyn_ptr` (qx_choose_then `prepared`
    (qx_choose_then `ignored` (qx_choose_then `middle` (MAP_EVERY assume_tac o CONJUNCTS))))) >>
  `prepared.cs_next_id <= last /\ middle.cs_next_id <= last /\
    prepared.cs_next_var <= limit_st.cs_next_var /\ middle.cs_next_var <= limit_st.cs_next_var /\
    start.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `output_size` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_encoder_complex_prepare) >>
  impl_tac >- asm_simp_tac (srw_ss()) [Excl "enc_def"] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  mp_tac (Q.INST [`active` |-> `T`, `site` |-> `start.cs_next_id`, `lo` |-> `start.cs_next_id`,
    `st` |-> `prepared`, `end_st` |-> `middle`, `out` |-> `ignored`, `initial` |-> `ready:venom_state`,
    `pre` |-> `[]:abi_type list`, `pvs` |-> `[]:abi_value list`, `so` |-> `0:num`, `ho` |-> `0:num`,
    `hl` |-> `head_lengths tys 0`, `output_size` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_encoder_members_run) >>
  impl_tac >- asm_simp_tac bool_ss [abi_encoder_members_correct_all] >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready encoded` >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ encoded`
    (assume_tac o SIMP_RULE bool_ss [APPEND, ADD_CLAUSES]) >>
  mp_tac (Q.INST [`st` |-> `middle`, `site` |-> `start.cs_next_id`, `lo` |-> `start.cs_next_id`,
    `so` |-> `abi_encoder_member_span infos`,
    `ho` |-> `SUM (MAP (\(_,asz,_,_). asz) (infos:(abi_enc_info # num # num # bool) list))`,
    `hl` |-> `head_lengths tys 0`, `output_size` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_encoder_complex_finish) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func encoded actual` >>
  mp_tac (Q.INST [`st` |-> `start`, `sz` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_encoder_complex_compose) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
