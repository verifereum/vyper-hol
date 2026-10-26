(* Execute an actual heterogeneous member using recursive child correctness.
   TOP-LEVEL: abi_decoder_member_body.
   Helper: split the containing code at member setup. *)
Theory abiDecoderMemberBody
Ancestors
  abiDecoderMemberPrepare abiDecoderMemberCode abiDecoderMemberSetup abiDecoderMembers
  abiDecoderMemberInputs abiDecoderEmpty abiDecoderEmptyMember abiDecoderOffset
  abiDecoderCorrect abiDecoderArrayBody abiDecoderArrayInitExec abiDecoderEffect
  abiDecoderDynamicLoopSetup abiDecoderDynamic abiDecoderReentry abiDecoderMemberSlice
  abiDecoderCounters abiDecoderAppend abiDecoderCoherence abiDecoderTypedContract
  abiDecoderAllocation abiDecoderLoop abiDecoderContract abiDecodeRanges fragExec
  abiEncoder compileEnv valueEncoding vyperABI venomState venomExecSemantics
  emitHelperProps words list arithmetic

Theorem abi_decoder_member_body_code:
  abi_decode_member_setup dst src opc hi dyn ao vo st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc hi di middle = ((),end_st) /\
  abi_decode_source_opcode opc /\ fn_has_code st end_st func ==>
  fn_has_code st middle func /\ fn_has_code middle end_st func /\
  st.cs_next_id < middle.cs_next_id /\ middle.cs_next_var <= end_st.cs_next_var /\
  st.cs_next_var <= middle.cs_next_var
Proof
  strip_tac >> drule_all abi_decode_member_setup_shape >> strip_tac >>
  `cs_extends st middle` by (irule cs_extends_same_block >> simp[]) >>
  drule cs_extends_abi_decode >> strip_tac >>
  mp_tac (Q.SPECL [`st`, `middle`, `end_st`, `func`] fn_has_code_split) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_variable_counter >> strip_tac >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >> gvs[]
QED

Theorem abi_decoder_member_body_helper:
  abi_decode_member_setup dst src opc hi (abi_decoder_dynamic (type_to_abi_dec_info sf ce ty))
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  fn_has_code st end_st func /\
  (middle.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_correct ce env sf ty tv /\
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))))
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) (abi_decode_source opc initial) =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_ranges_def, Excl "enc_def"] >>
  drule_all abi_decoder_member_body_code >> strip_tac >>
  `first <= middle.cs_next_id /\ middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `abi_decoder_reservation middle.cs_next_id last b cap initial` by
    (drule_all abi_decoder_budget_child_reservation >> simp[]) >>
  mp_tac abi_decoder_member_prepare >> impl_tac >- asm_simp_tac bool_ss [] >>
  strip_tac >> rename1 `abi_decode_sim ctx func initial prepared` >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `abi_decoder_budget first last b cap prepared` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `prepared:venom_state`]
      abi_decoder_budget_transport) >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`dst` |-> `SND (ops:operand # operand)`,
    `src` |-> `FST (ops:operand # operand)`, `start` |-> `middle`,
    `initial` |-> `prepared:venom_state`,
    `sb` |-> `sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
      (preavs ++ av::avs) (LENGTH pretys)`,
    `d` |-> `d + SUM (MAP (type_memory_bytes ce) pretys)`] abi_decoder_correct_run) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory` >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
    (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty) b cap initial actual` by
    (mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
      `next` |-> `st.cs_next_var`, `child_lo` |-> `middle.cs_next_id`,
      `child_next` |-> `middle.cs_next_var`, `s` |-> `initial:venom_state`,
      `prepared` |-> `prepared:venom_state`, `t` |-> `actual:venom_state`,
      `d` |-> `d + SUM (MAP (type_memory_bytes ce) pretys)`,
      `sz` |-> `type_memory_bytes ce ty`] abi_decoder_address_then_effect) >>
     asm_simp_tac arith_ss []) >>
  `abi_decode_sim ctx func initial actual` by metis_tac[abi_decode_sim_trans] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_empty_canonical_member:
  abi_decode_member_setup dst src opc hi (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  fn_has_code st end_st func /\
  type_to_abi_dec_info sf ce ty = DecComplex T [] /\
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))))
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap initial /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_budget first last b cap initial /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac abi_decoder_members_child_facts >> impl_tac >- asm_simp_tac bool_ss [] >>
  strip_tac >> drule_all abi_decoder_empty_metadata_value >> strip_tac >>
  qpat_x_assum `has_types _ _` (assume_tac o SIMP_RULE bool_ss [MAP_APPEND, MAP]) >>
  `LENGTH (MAP (vyper_to_abi_type env) pretys) = LENGTH preavs` by simp[] >>
  drule_all abi_tuple_child_offset_ranges >> strip_tac >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [MAP_APPEND, MAP]) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  SUBGOAL_THEN ``hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)) <= hb /\
    hb < dimword (:256)`` assume_tac
  >- (Cases_on `hi = Lit 0w` >- simp[] >>
      qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >> strip_tac >>
      rename1 `eval_operand hi initial = SOME (n2w hb)` >>
      qexists_tac `hb` >> asm_simp_tac arith_ss [] >> decide_tac) >>
  qpat_x_assum `type_to_abi_dec_info _ _ _ = DecComplex T []`
    (fn th => RULE_ASSUM_TAC (SIMP_RULE bool_ss [th, dec_info_needs_offset_def])) >>
  mp_tac (Q.INST [`ao` |-> `SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))`,
    `vo` |-> `SUM (MAP (type_memory_bytes ce) pretys)`, `dynamic` |-> `T`]
    abi_decode_empty_member_reach) >> impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
    (d + SUM (MAP (type_memory_bytes ce) pretys)) 0 b cap initial actual` by
    (irule abi_decoder_address_effect >> asm_simp_tac bool_ss [] >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_member_body:
  abi_decode_member_setup dst src opc hi (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  fn_has_code st end_st func /\
  (middle.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_correct ce env sf ty tv /\
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))))
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) (abi_decode_source opc initial) =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- (mp_tac abi_decoder_empty_canonical_member >>
      impl_tac >- asm_simp_tac bool_ss [] >> simp[]) >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
    abi_decoder_dynamic (type_to_abi_dec_info sf ce ty)` by
    simp[abi_decoder_needs_offset_iff] >>
  qpat_x_assum `dec_info_needs_offset _ = _`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  mp_tac abi_decoder_member_body_helper >> impl_tac >- asm_simp_tac bool_ss [] >> simp[]
QED
