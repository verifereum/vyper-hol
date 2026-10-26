(* Nonempty member-list execution from head and suffix correctness.
   TOP-LEVEL: abi_decoder_members_correct_cons. *)
Theory abiDecoderMemberCons
Ancestors
  abiDecoderMemberTail abiDecoderMemberPhases abiDecoderMemberBody abiDecoderMemberCode
  abiDecoderMembersCorrect abiDecoderMemberInfos abiDecoderMemberFrames abiDecoderMembers
  abiDecoderCorrect abiDecoderTypedContract abiDecoderEffect abiDecoderReentry
  abiDecoderLoop abiDecoderContract abiDecodeRanges abiDecoderDynamic
  compileEnv valueEncoding vyperABI venomState words list arithmetic

Theorem abi_decoder_members_correct_cons:
  abi_decoder_correct ce env sf ty tv /\ abi_decoder_members_correct ce env sf tys tvs ==>
  abi_decoder_members_correct ce env sf (ty::tys) (tv::tvs)
Proof
  strip_tac >> rewrite_tac [abi_decoder_members_correct_def] >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.SPECL [`ty::tys`, `tv::tvs`, `avs`, `vs`] abi_decoder_members_lengths) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  Cases_on `avs` >- fs[] >> Cases_on `vs` >- fs[] >>
  rename1 `abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs)` >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_ranges_def, Excl "enc_def"] >>
  mp_tac (Q.INST [`ao` |-> `SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))`,
    `vo` |-> `SUM (MAP (type_memory_bytes ce) pretys)`] abi_decoder_member_cons_trace) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_member_setup dst src opc hi _ _ _ st = (ops,middle)` >>
  rename1 `compile_abi_decode_to_buf _ _ opc hi _ middle = ((),end_st)` >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  drule_all abi_decoder_members_child_phi >> disch_then assume_tac >>
  mp_tac abi_decoder_members_tail_phi >> impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then assume_tac >>
  `end_st.cs_next_id <= last /\ first <= end_st.cs_next_id /\
   end_st.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= end_st.cs_next_var`
    by decide_tac >>
  mp_tac abi_decoder_member_body >> impl_tac >- asm_simp_tac bool_ss [] >>
  strip_tac >> rename1 `abi_decode_sim ctx func initial after_head` >>
  mp_tac (Q.INST [`hi_op` |-> `hi:operand`] abi_decoder_member_after_head) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`st` |-> `end_st`, `initial` |-> `after_head:venom_state`]
    abi_decoder_member_tail_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func after_head actual` >>
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

Theorem abi_decoder_members_correct_list:
  !tys tvs. LIST_REL (abi_decoder_correct ce env sf) tys tvs ==>
    abi_decoder_members_correct ce env sf tys tvs
Proof
  Induct_on `tys` >> rpt gen_tac >> Cases_on `tvs` >> simp[abi_decoder_members_correct_nil] >>
  strip_tac >> irule abi_decoder_members_correct_cons >> simp[]
QED
