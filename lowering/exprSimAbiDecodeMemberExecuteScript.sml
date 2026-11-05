(* Member setup reaches a recursive child without changing allocation sites. *)
Theory exprSimAbiDecodeMemberExecute
Ancestors
  exprSimAbiDecodeMemberOutcome exprSimAbiDecodeSiteProvenance
  abiDecoderMemberSetup abiDecoderDynamicLoopSetup abiDecoderFiniteControl
  abiDecoderSequenceReach abiDecoderContract abiEncoder compileEnv emitHelper
  emitHelperProps exprLoweringProps venomState venomInst instIdxIndep
  abiDecoderSiteEffect abiDecoderBytestringOutcome actualDecoderSites
  abiValidMembers abiDecodeRanges vyperABI contractABI rich_list
  finite_map pred_set words list arithmetic

Theorem abi_decode_member_setup_reach:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,middle) /\
  eval_operand src s = SOME(n2w p) /\ eval_operand dst s = SOME(n2w d) /\
  (dyn ==> eval_operand base_op s = SOME(n2w B) /\
    abi_decode_load MLOAD (n2w(B+(p+ao)):bytes32) s = n2w delta /\
    p+delta < dimword(:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  decode_site_resources ctx func s /\
  fn_has_code st middle fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. Dreach ctx fn s t /\
    t.vs_current_bb = middle.cs_current_bb /\
    t.vs_inst_idx = LENGTH middle.cs_current_insts /\
    eval_operand (FST ops) t = SOME(n2w(p+if dyn then delta else ao)) /\
    eval_operand (SND ops) t = SOME(n2w(d+vo)) /\
    abi_decoder_operand_live middle.cs_next_var (FST ops) /\
    abi_decoder_operand_live middle.cs_next_var (SND ops) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    abi_decode_alloc_progress sites s t /\
    decode_site_effect ctx func st.cs_next_var writes s t /\ ~t.vs_halted
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_reentry >> strip_tac >>
  drule abi_decode_member_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st middle)` by fs[EVERY_MEM] >>
  `EVERY (\i. abi_bytes_opcode i.inst_opcode) (emitted_insts st middle)`
    by fs[EVERY_MEM] >>
  drule_all abi_bytes_sequence_static >> strip_tac >>
  `decode_site_resources ctx func t` by
    (irule decode_site_resources_fields >>
     qexists_tac `s` >> fs[abi_decoder_address_frame_def,
       venom_state_component_equality]) >>
  `decode_site_effect ctx func st.cs_next_var writes s t` by
    (simp[decode_site_effect_def, decode_memory_frame_def,
       abi_decoder_address_frame_def] >>
     fs[abi_decoder_address_frame_def, decode_static_frame_def,
        venom_state_component_equality]) >>
  qpat_x_assum `t = s with <|vs_vars := _; vs_memory := _|>` kall_tac >>
  drule_all abi_decoder_run_sequence_prefix >> strip_tac >>
  qexists_tac `t'` >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx,
      abi_decode_alloc_progress_def] >>
  conj_tac >- (irule Dreach_straight_prefix >> simp[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem abi_decode_member_setup_wrap_abort:
  abi_decode_member_setup dst src MLOAD base_op hi T ao vo st = (ops,middle) /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand src s = SOME(n2w p) /\ eval_operand base_op s = SOME(n2w B) /\
  eval_operand hi s = SOME(n2w H) /\ p+ao+32 <= H /\ B+H < dimword(:256) /\
  delta = w2n(abi_decode_load MLOAD (n2w(B+p+ao):bytes32) s) /\
  dimword(:256) <= p+delta /\ fresh_vars_wrt st s /\
  fn_has_code st middle fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. Dabort ctx fn s Revert_abort u
Proof
  strip_tac >> drule_all abi_decode_member_setup_revert >> strip_tac >>
  drule abi_decode_member_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st middle)` by fs[EVERY_MEM] >>
  drule_all abi_decoder_run_sequence_abort >> strip_tac >>
  qpat_x_assum `!ctx. _` (qspec_then `ctx` strip_assume_tac) >>
  simp[Dabort_def] >> qexistsl_tac [`t with vs_inst_idx := n`, `0`] >> simp[]
QED

(* A recursive decoder keeps the ambient payload fixed.  Only its view changes:
   an inline child gets exactly its static width, not the whole suffix. *)
Definition abi_decode_source_view_def:
  abi_decode_source_view at bs pos =
    if is_dynamic at then DROP pos bs
    else TAKE (static_length at) (DROP pos bs)
End

Theorem abi_decode_member_static_view:
  ~is_dynamic at ==>
  abi_decode_member_bytes at (DROP pos bs) (DROP ao (DROP pos bs)) =
    abi_decode_source_view at bs (pos+ao)
Proof
  simp[abi_decode_member_bytes_def, abi_decode_source_view_def,
       DROP_DROP_T, ADD_COMM]
QED

Theorem abi_decode_member_dynamic_view:
  is_dynamic at /\ delta = abi_head_word (DROP ao (DROP pos bs)) ==>
  abi_decode_member_bytes at (DROP pos bs) (DROP ao (DROP pos bs)) =
    abi_decode_source_view at bs (pos+delta)
Proof
  simp[abi_decode_member_bytes_def, abi_decode_source_view_def,
       DROP_DROP_T, ADD_COMM]
QED

Theorem abi_decode_member_contextual_view:
  (is_dynamic at ==> delta = abi_head_word (DROP ao (DROP pos bs))) ==>
  abi_decode_member_bytes at (DROP pos bs) (DROP ao (DROP pos bs)) =
    abi_decode_source_view at bs (pos + if is_dynamic at then delta else ao)
Proof
  Cases_on `is_dynamic at` >>
  simp[abi_decode_member_bytes_def, abi_decode_source_view_def,
       DROP_DROP_T, ADD_COMM]
QED

Theorem abi_decode_empty_tuple_static[local]:
  !ats. vyper_decode_valid_enc_tuple ats ([]:byte list) [] ==>
    ~EXISTS is_dynamic ats
Proof
  Induct >- simp[] >> rpt strip_tac >>
  drule abi_valid_member_cons >> strip_tac >>
  Cases_on `is_dynamic h` >>
  gvs[abi_member_head_size_def, Excl "vyper_decode_valid_enc_def",
      Excl "dec_def"] >>
  fs[EVERY_MEM, EXISTS_MEM, combinTheory.o_DEF] >> metis_tac[]
QED

Theorem abi_decode_dynamic_empty_reject:
  is_dynamic at /\ (!elem. at <> Array (SOME 0) elem) ==>
  ~vyper_decode_valid_enc at ([]:byte list)
Proof
  Cases_on `at` >>
  simp[Once is_dynamic_def, Once vyper_decode_valid_enc_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
  >- (Cases_on `o'` >> gvs[is_dynamic_def, vyper_decode_valid_enc_def])
  >- gvs[Once vyper_decode_valid_enc_def]
  >- (Cases_on `o'`
      >- gvs[Once vyper_decode_valid_enc_def] >>
      gvs[] >> rename1 `Array (SOME n) a` >> Cases_on `n` >>
      gvs[vyper_decode_valid_enc_def]) >>
  disj2_tac >> strip_tac >> drule abi_decode_empty_tuple_static >>
  simp[GSYM any_dynamic_EXISTS]
QED

Theorem abi_decode_member_wrap_source_reject:
  is_dynamic at /\ (!elem. at <> Array (SOME 0) elem) /\
  delta = abi_head_word (DROP ao (DROP pos bs)) /\
  LENGTH bs <= H /\ H < dimword(:256) /\
  dimword(:256) <= pos+delta ==>
  ~vyper_decode_valid_enc at
    (abi_decode_member_bytes at (DROP pos bs) (DROP ao (DROP pos bs)))
Proof
  strip_tac >>
  `LENGTH bs <= pos+delta` by decide_tac >>
  `DROP delta (DROP pos bs) = []` by
    (pure_rewrite_tac[DROP_EQ_NIL, LENGTH_DROP] >> decide_tac) >>
  `~vyper_decode_valid_enc at ([]:byte list)` by
    (irule abi_decode_dynamic_empty_reject >> simp[]) >>
  qpat_x_assum `delta = _` (fn th => rewrite_tac[abi_decode_member_bytes_def, GSYM th]) >>
  pure_asm_rewrite_tac[] >> simp[]
QED
