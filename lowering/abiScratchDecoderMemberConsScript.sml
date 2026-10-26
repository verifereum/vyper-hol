(* Member-list execution with physical child effects and preserved siblings.
   TOP-LEVEL: abi_scratch_decoder_members_cons. *)
Theory abiScratchDecoderMemberCons
Ancestors
  abiScratchDecoderMemberTail abiDecoderMembersCode abiScratchDecoderMemberBody
  abiDecoderValidMemberCursor abiScratchDecoderMemberFrames abiValidMembers
  abiScratchDecoderMembersContract abiDecoderMemberInfos abiDecoderMemberFrames abiDecoderMembers
  abiScratchDecoderContract abiDecoderValidContract abiDecoderTypedContract abiDecoderEffect abiDecoderReentry
  abiDecoderLoop abiDecoderContract abiDecodeRanges abiDecoderDynamic
  compileEnv valueEncoding vyperABI venomState words list arithmetic

Theorem abi_scratch_decoder_members_cons:
  abi_scratch_decoder ce env sf ty tv /\ abi_scratch_decoder_members ce env sf tys tvs ==>
  abi_scratch_decoder_members ce env sf (ty::tys) (tv::tvs)
Proof
  strip_tac >> rewrite_tac [abi_scratch_decoder_members_def] >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.SPECL [`ty::tys`, `tv::tvs`,
    `abi_decode_members (MAP (vyper_to_abi_type env) (ty::tys)) bs
      (DROP (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))) bs)`,
    `vs`] abi_decoder_members_lengths) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  Cases_on `vs` >- fs[] >> rename1 `v::vs` >>
  drule abi_decoder_valid_member_cursor >> strip_tac >>
  (* Empty members use their inline head; no nonempty-head list premise is needed. *)
  `abi_decode_source_opcode opc` by fs[abi_scratch_decoder_ranges_def, Excl "enc_def"] >>
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
      abi_scratch_decoder_member_body)) >>
  impl_tac >- (RULE_ASSUM_TAC (SIMP_RULE arith_ss [MAP_APPEND, MAP, SUM_APPEND, SUM]) >>
    asm_simp_tac arith_ss [MAP_APPEND, MAP, SUM_APPEND, SUM]) >>
  disch_then (qx_choose_then `after_head` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  mp_tac (Q.INST [`hi_op` |-> `hi:operand`] abi_scratch_decoder_member_after_head) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`st` |-> `end_st`, `initial` |-> `after_head:venom_state`]
    abi_scratch_decoder_member_tail_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `mid_id` |-> `end_st.cs_next_id`,
    `hi` |-> `final.cs_next_id`, `next` |-> `st.cs_next_var`, `tail_next` |-> `end_st.cs_next_var`,
    `cell` |-> `d + SUM (MAP (type_memory_bytes ce) pretys)`, `headsz` |-> `type_memory_bytes ce ty`,
    `tailsz` |-> `SUM (MAP (type_memory_bytes ce) tys)`, `s` |-> `initial:venom_state`,
    `middle` |-> `after_head:venom_state`, `t` |-> `actual:venom_state`]
    abi_scratch_decoder_member_effects_compose) >>
  impl_tac >- asm_simp_tac arith_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [MAP, SUM] >>
  irule abi_decode_sim_trans >> qexists_tac `after_head` >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_members_list:
  !tys tvs. LIST_REL (abi_scratch_decoder ce env sf) tys tvs ==>
    abi_scratch_decoder_members ce env sf tys tvs
Proof
  Induct_on `tys` >> rpt gen_tac >> Cases_on `tvs` >> simp[abi_scratch_decoder_members_nil] >>
  strip_tac >> irule abi_scratch_decoder_members_cons >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_MEMBER_CONS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical nonempty members not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderMemberCons");

