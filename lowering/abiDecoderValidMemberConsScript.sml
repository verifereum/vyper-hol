Theory abiDecoderValidMemberCons
Ancestors
  abiDecoderMemberFrames abiDecoderEffect abiDecodeRanges compileEnv venomState words list
  arithmetic abiDecoderValidContract abiValidMember abiValidMembers abiValidAggregateHeads
  abiDecoderMemberSetup abiDecoderReentry abiDecoderCoherence abiDecoderTypedContract
  abiDecoderContract abiEncoder fragExec valueEncoding vyperABI contractABI venomExecSemantics
  abiDecoderMemberBody abiDecoderEmptyMember abiDecoderOffset abiDecoderOffsetHead
  abiDecoderArraySetupCode abiDecoderDynamic abiDecoderDynamicLoopSetup abiDecoderArrayInitExec
  abiDecoderAllocation abiDecoderLoop abiDecoderValidMemberTail abiDecoderMembersCode
  abiDecoderValidMemberCursor abiDecoderValidMembersCorrect abiDecoderMemberInfos
  abiDecoderMembers

(* A completed actual-source member preserves the enclosing source and inputs. *)
Theorem abi_decoder_valid_member_after_head:
  abi_decoder_ranges opc hi_op src dst sb (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
    (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty) b cap initial after_head /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi_op /\ st.cs_next_var <= end_st.cs_next_var ==>
  abi_decoder_ranges opc hi_op src dst sb (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap after_head /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc after_head) = bs /\
  fresh_vars_wrt limit_st after_head /\ abi_decoder_budget first last b cap after_head /\
  abi_decoder_operand_live end_st.cs_next_var src /\ abi_decoder_operand_live end_st.cs_next_var dst /\
  abi_decoder_operand_live end_st.cs_next_var hi_op
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
    `next` |-> `st.cs_next_var`, `new_next` |-> `end_st.cs_next_var`,
    `cell` |-> `d + SUM (MAP (type_memory_bytes ce) pretys)`, `sz` |-> `type_memory_bytes ce ty`,
    `len` |-> `LENGTH (bs:word8 list)`,
    `outsz` |-> `SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))`,
    `before` |-> `initial:venom_state`, `after` |-> `after_head:venom_state`,
    `bytes` |-> `bs:word8 list`] abi_decoder_member_observations) >>
  impl_tac >- asm_simp_tac arith_ss [MAP_APPEND, SUM_APPEND, MAP, SUM] >>
  strip_tac >> asm_simp_tac bool_ss []
QED

(* The real member prefix establishes the actual-source recursive input API. *)
Theorem abi_decoder_valid_member_readable:
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) ==>
  abi_member_head_size at <= LENGTH
    (abi_decode_member_bytes at bs (DROP (SUM (MAP abi_member_head_size pre)) bs))
Proof
  strip_tac >> drule abi_valid_member_head >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  Cases_on `is_dynamic at`
  >- (qpat_x_assum `vyper_decode_valid_enc at _` mp_tac >>
      asm_simp_tac bool_ss [abi_decode_member_bytes_def] >> strip_tac >>
      `!elem. at <> Array (SOME 0) elem` by metis_tac[] >>
      drule_all abi_valid_dynamic_head_min >>
      asm_simp_tac bool_ss [abi_member_head_size_def, abi_decode_member_bytes_def]) >>
  `static_length at <= LENGTH (DROP (SUM (MAP abi_member_head_size pre)) bs)` by
    (qpat_x_assum `_ + abi_member_head_size at <= _` mp_tac >>
     asm_simp_tac bool_ss [abi_member_head_size_def] >> strip_tac >>
     simp[LENGTH_DROP] >> decide_tac) >>
  asm_simp_tac (srw_ss()) [abi_member_head_size_def, abi_decode_member_bytes_def, LENGTH_TAKE_EQ]
QED

Theorem abi_decoder_valid_member_entry:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src opc hi (abi_decoder_dynamic (type_to_abi_dec_info sf ce ty))
    ao vo st = (ops,ready) /\ fn_has_code st ready func /\
  abi_decoder_coherent ce env sf ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs) d outsz b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared. abi_decoder_valid_pre ce env sf ty tv childbs v ready
      (FST ops) (SND ops) opc hi (sb + off) (d + vo) b cap prepared /\
    fresh_vars_wrt limit_st prepared /\ abi_decoder_address_frame st.cs_next_var initial prepared /\
    prepared.vs_current_bb = ready.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\ ~prepared.vs_halted /\
    abi_decode_sim ctx func initial prepared
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] abi_valid_member_entry) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  drule_all abi_decoder_valid_member_readable >> strip_tac >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  `st.cs_next_var <= ready.cs_next_var` by simp[] >>
  `abi_decoder_operand_live ready.cs_next_var hi` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  qexists_tac `prepared` >>
  asm_simp_tac bool_ss [abi_decoder_valid_pre_def, abi_decoder_head_window]
QED

(* Actual member-prefix execution followed by source-valid recursive child
   execution. The sole child hypothesis is the structural correctness API. *)
Theorem abi_decoder_valid_member_body_helper:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src opc hi (abi_decoder_dynamic (type_to_abi_dec_info sf ce ty))
    ao vo st = (ops,ready) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc hi (type_to_abi_dec_info sf ce ty)
    ready = ((),end_st) /\ fn_has_code st end_st func /\
  (ready.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_valid_correct ce env sf ty tv /\ abi_decoder_coherent ce env sf ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs) d outsz b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory tv v (d + vo) actual.vs_memory /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st (d + vo) (type_memory_bytes ce ty) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_ranges_def] >>
  drule_all abi_decoder_member_body_code >> strip_tac >>
  `first <= ready.cs_next_id /\ st.cs_next_id <= ready.cs_next_id /\
   ready.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all (SIMP_RULE bool_ss [LET_THM] abi_decoder_valid_member_entry) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  `abi_decoder_budget first last b cap prepared` by
    (qpat_assum `abi_decoder_address_frame _ _ _`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
     mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `prepared:venom_state`]
       abi_decoder_budget_transport) >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`start` |-> `ready`, `end_st` |-> `end_st`,
    `initial` |-> `prepared:venom_state`, `dst` |-> `SND (ops:operand # operand)`,
    `src` |-> `FST (ops:operand # operand)`,
    `bs` |-> `abi_decode_member_bytes (vyper_to_abi_type env ty) bs
      (DROP (SUM (MAP abi_member_head_size pre)) bs)`,
    `sb` |-> `sb + abi_decode_member_offset (vyper_to_abi_type env ty) bs
      (SUM (MAP abi_member_head_size pre))`, `d` |-> `d + vo`]
    abi_decoder_valid_correct_run) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `val_in_memory tv v (d + vo) actual.vs_memory` >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + vo) (type_memory_bytes ce ty) b cap initial actual` by
    (mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
      `next` |-> `st.cs_next_var`, `child_lo` |-> `ready.cs_next_id`,
      `child_next` |-> `ready.cs_next_var`, `s` |-> `initial:venom_state`,
      `prepared` |-> `prepared:venom_state`, `t` |-> `actual:venom_state`,
      `d` |-> `d + vo`, `sz` |-> `type_memory_bytes ce ty`] abi_decoder_address_then_effect) >>
     asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_valid_member_body:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src opc hi (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
    ao vo st = (ops,ready) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc hi (type_to_abi_dec_info sf ce ty)
    ready = ((),end_st) /\ fn_has_code st end_st func /\
  (ready.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_valid_correct ce env sf ty tv /\ abi_decoder_coherent ce env sf ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs) d outsz b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory tv v (d + vo) actual.vs_memory /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st (d + vo) (type_memory_bytes ce ty) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- (mp_tac (SIMP_RULE bool_ss [LET_THM]
        (Q.INST [`middle` |-> `ready`] abi_decoder_valid_empty_member)) >>
      impl_tac >- asm_simp_tac bool_ss [] >>
      disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
      `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
        limit_st (d + vo) (type_memory_bytes ce ty) b cap initial actual` by
        (irule abi_decoder_address_effect >> asm_simp_tac bool_ss [] >>
         qexists_tac `st.cs_next_var` >> simp[]) >>
      qexists_tac `actual` >> asm_simp_tac bool_ss []) >>
  `(is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem)` by
    (strip_tac >> drule_all abi_decoder_nonempty_readable_head >> simp[]) >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
    abi_decoder_dynamic (type_to_abi_dec_info sf ce ty)` by
    simp[abi_decoder_needs_offset_iff] >>
  qpat_x_assum `dec_info_needs_offset _ = _`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  mp_tac (SIMP_RULE bool_ss [LET_THM] abi_decoder_valid_member_body_helper) >>
  impl_tac >- asm_simp_tac bool_ss [] >> simp[]
QED

(* Actual-source member-list execution from head and suffix correctness.
   TOP-LEVEL: abi_decoder_valid_members_correct_cons. *)
Theorem abi_decoder_valid_members_correct_cons:
  abi_decoder_valid_correct ce env sf ty tv /\ abi_decoder_valid_members_correct ce env sf tys tvs ==>
  abi_decoder_valid_members_correct ce env sf (ty::tys) (tv::tvs)
Proof
  strip_tac >> rewrite_tac [abi_decoder_valid_members_correct_def] >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.SPECL [`ty::tys`, `tv::tvs`,
    `abi_decode_members (MAP (vyper_to_abi_type env) (ty::tys)) bs
      (DROP (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))) bs)`,
    `vs`] abi_decoder_members_lengths) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  Cases_on `vs` >- fs[] >> rename1 `v::vs` >>
  drule abi_decoder_valid_member_cursor >> strip_tac >>
  (* Empty members use their inline head; no nonempty-head list premise is needed. *)
  `abi_decode_source_opcode opc` by fs[abi_decoder_ranges_def, Excl "enc_def"] >>
  drule_all abi_decoder_members_cons_code >>
  disch_then (qx_choose_then `ops` (qx_choose_then `middle` (qx_choose_then `end_st`
    (MAP_EVERY assume_tac o CONJUNCTS)))) >>
  `end_st.cs_next_id <= last /\ first <= end_st.cs_next_id /\
   end_st.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= end_st.cs_next_var`
    by decide_tac >>
  mp_tac (SIMP_RULE bool_ss [LET_THM]
    (Q.INST [`ready` |-> `middle`, `pre` |-> `MAP (vyper_to_abi_type env) pretys`,
      `ats` |-> `MAP (vyper_to_abi_type env) tys`,
      `vo` |-> `SUM (MAP (type_memory_bytes ce) pretys)`,
      `outsz` |-> `SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))`]
      abi_decoder_valid_member_body)) >>
  impl_tac >- (RULE_ASSUM_TAC (SIMP_RULE arith_ss [MAP_APPEND, MAP, SUM_APPEND, SUM]) >>
    asm_simp_tac arith_ss [MAP_APPEND, MAP, SUM_APPEND, SUM]) >>
  disch_then (qx_choose_then `after_head` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  mp_tac (Q.INST [`hi_op` |-> `hi:operand`] abi_decoder_valid_member_after_head) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`st` |-> `end_st`, `initial` |-> `after_head:venom_state`]
    abi_decoder_valid_member_tail_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `mid_id` |-> `end_st.cs_next_id`,
    `hi` |-> `final.cs_next_id`, `next` |-> `st.cs_next_var`, `tail_next` |-> `end_st.cs_next_var`,
    `cell` |-> `d + SUM (MAP (type_memory_bytes ce) pretys)`, `headsz` |-> `type_memory_bytes ce ty`,
    `tailsz` |-> `SUM (MAP (type_memory_bytes ce) tys)`, `s` |-> `initial:venom_state`,
    `middle` |-> `after_head:venom_state`, `t` |-> `actual:venom_state`]
    abi_decoder_member_effects_compose) >>
  impl_tac >- asm_simp_tac arith_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [MAP, SUM] >>
  irule abi_decode_sim_trans >> qexists_tac `after_head` >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_valid_members_correct_list:
  !tys tvs. LIST_REL (abi_decoder_valid_correct ce env sf) tys tvs ==>
    abi_decoder_valid_members_correct ce env sf tys tvs
Proof
  Induct_on `tys` >> rpt gen_tac >> Cases_on `tvs` >> simp[abi_decoder_valid_members_correct_nil] >>
  strip_tac >> irule abi_decoder_valid_members_correct_cons >> simp[]
QED
