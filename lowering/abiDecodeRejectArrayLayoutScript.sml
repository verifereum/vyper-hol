(* The rejecting array checks are a straight-line prefix even when the
   subsequent decoder body changes blocks. *)
Theory abiDecodeRejectArrayLayout
Ancestors
  abiDecoderArrayLoopInit abiDecoderBulk abiDecoderBytesBound
  abiDecoderContract abiDecoderIndexInit freshWrites context
  abiDecoderDynarrayBound abiDecoderDynarrayPrefix abiDecoderGuard abiDecoderGuards
  abiDecoderRange abiDecoderReentry abiDecoderVarSequence abiEncoder
  bodyPtrBopScalarSeq externalEntryShape loweringShapeRules loweringStateRelDefs exprSimAccounts
  emitHelperProps emitHelper exprLoweringProps fragExec compileEnv venomInst list rich_list words
  arithmetic

Theorem dynarray_guard_contained[local]:
  compile_abi_decode_to_buf dst pos MLOAD (Var source) hi
     (DecDynArray ei stride mem_sz elem_dyn cap) st = ((),en) /\
  fn_has_code st en func ==>
  ?addr sp.
    abi_decode_dynarray_position_prefix pos MLOAD (Var source) hi cap stride st =
      (addr,sp) /\ fn_has_code st sp func /\ cs_extends sp en
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  Cases_on `elem_dyn \/ dec_info_needs_clamp ei`
  >- (drule_all abi_decode_loop_array_trace >> strip_tac >>
      drule abi_decode_array_loop_init_trace >> strip_tac >>
      drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
      drule_all abi_decode_array_header_shape >> strip_tac >>
      drule abi_decode_index_init_shape >> strip_tac >>
      `cs_extends loop_st en` by
        metis_tac[cj 1 (cj 3 compile_abi_decode_labels), pairTheory.SND] >>
      gns[inst_extends_def] >>
      `cs_extends st guard_st /\ cs_extends guard_st header_st /\
       cs_extends header_st loop_st` by (rpt conj_tac >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
      `cs_extends guard_st en` by metis_tac[cs_extends_trans] >>
      metis_tac[fn_has_code_split]) >>
  fs[] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_bulk_phases, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule_all abi_decode_bulk_body_shape >> strip_tac >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  rename1 `abi_decode_bulk_body _ _ _ _ _ _ sp = ((),en)` >>
  `cs_extends sp en` by
    (irule cs_extends_same_block >> fs[inst_extends_def, IS_PREFIX_APPEND, APPEND_ASSOC] >>
     simp[GSYM APPEND_ASSOC, IS_PREFIX_APPEND]) >>
  `cs_extends st sp` by
    (irule cs_extends_same_block >> fs[inst_extends_def, IS_PREFIX_APPEND]) >>
  simp[] >> metis_tac[fn_has_code_split]
QED

Theorem bounded_array_head_layout[local]:
  abi_decode_bytes_head pos hi st = (head,sh) /\ hi <> Lit 0w ==>
  inst_extends st sh /\ st.cs_next_var <= sh.cs_next_var /\
  abi_decoder_operand_live sh.cs_next_var head /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st sh)
Proof
  strip_tac >> drule abi_decode_bytes_head_fragment_shape >> strip_tac >>
  gvs[abi_decode_bytes_head_def, compile_abi_decode_range_check_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
      emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, abi_decoder_reentry_opcode_def, mk_inst_def,
       abi_decoder_operand_live_def, abiDecoderReentryTheory.abi_decoder_older_vars_def]
QED

Theorem bounded_array_payload_layout[local]:
  abi_decode_dynarray_payload_guard head cnt stride hi sc = ((),sp) /\ hi <> Lit 0w ==>
  inst_extends sc sp /\ sp.cs_current_bb = sc.cs_current_bb /\
  sp.cs_blocks = sc.cs_blocks /\ sc.cs_next_var <= sp.cs_next_var /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sc sp) /\
  (?A. bop_scalar_seq {x | not_fresh_at sc x} {head;cnt;Lit (n2w stride);hi}
      (emitted_insts sc sp) A)
Proof
  strip_tac >> drule abi_decode_dynarray_payload_guard_shape >> strip_tac >>
  gvs[abi_decode_dynarray_payload_guard_def, compile_abi_decode_range_check_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
      emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, abi_decoder_reentry_opcode_def, mk_inst_def] >>
  ntac 8 (simp[Once bop_scalar_seq_def, mk_inst_def, not_fresh_at_def]) >>
  simp[bop_scalar_seq_def]
QED

Theorem malformed_dynarray_guard_layout:
  (!addr n sa cnt sc.
    abi_decode_count_guard MLOAD (Var addr) n sa = (cnt,sc) ==>
    ?sb. emit_op MLOAD [Var addr] sa = (cnt,sb) /\
         abi_decode_le_guard cnt (Lit (n2w n)) sb = ((),sc) /\
         cs_extends sa sb /\ cs_extends sb sc /\
         sc.cs_current_bb = sb.cs_current_bb /\ sb.cs_next_var <= sc.cs_next_var /\
         EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sb sc) /\
         (!R. (!x. x IN R ==> not_fresh_at sb x) ==>
           ?A. bop_scalar_seq R {cnt;Lit (n2w n)} (emitted_insts sb sc) A)) /\
  compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
    (DecDynArray ei stride mem_sz elem_dyn cap) st = ((),en) /\
  hi <> Lit 0w /\ fn_has_code st en func ==>
  ?head ar cnt sh sa sl sc sp C P.
    abi_decode_bytes_head pos hi st = (head,sh) /\
    emit_op ADD [Var source;pos] sh = (Var ar,sa) /\
    emit_op MLOAD [Var ar] sa = (cnt,sl) /\
    abi_decode_le_guard cnt (Lit (n2w cap)) sl = ((),sc) /\
    abi_decode_dynarray_payload_guard head cnt stride hi sc = ((),sp) /\
    fn_has_code st sh func /\ fn_has_code sh sa func /\ fn_has_code sa sl func /\
    fn_has_code sl sc func /\ fn_has_code sc sp func /\ cs_extends sp en /\
    sh.cs_current_bb = st.cs_current_bb /\ sa.cs_current_bb = sh.cs_current_bb /\
    sl.cs_current_bb = sa.cs_current_bb /\ sc.cs_current_bb = sl.cs_current_bb /\
    sp.cs_current_bb = sc.cs_current_bb /\
    st.cs_next_var <= sh.cs_next_var /\ sh.cs_next_var <= sl.cs_next_var /\
    sl.cs_next_var <= sc.cs_next_var /\ sc.cs_next_var <= sp.cs_next_var /\
    abi_decoder_operand_live sh.cs_next_var head /\
    abi_decoder_operand_live sl.cs_next_var cnt /\
    EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st sh) /\
    EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sl sc) /\
    EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sc sp) /\
    bop_scalar_seq {x | not_fresh_at sl x} {cnt;Lit (n2w cap)} (emitted_insts sl sc) C /\
    bop_scalar_seq {x | not_fresh_at sc x} {head;cnt;Lit (n2w stride);hi}
      (emitted_insts sc sp) P
Proof
  strip_tac >> drule_all dynarray_guard_contained >> strip_tac >>
  fs[abi_decode_dynarray_position_prefix_trace, compile_abi_dec_addr_def] >>
  drule (Q.SPEC `ADD` emit_op_facts) >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule_all bounded_array_head_layout >> strip_tac >>
  drule_all bounded_array_payload_layout >> strip_tac >>
  drule abi_decode_bytes_head_fragment_shape >> strip_tac >>
  `inst_extends addr_st sb` by metis_tac[inst_extends_emit_op] >>
  drule (Q.SPEC `MLOAD` emit_op_facts) >> strip_tac >> gvs[] >>
  `inst_extends head_st addr_st` by metis_tac[inst_extends_emit_op] >>
  `cs_extends st head_st /\ cs_extends head_st addr_st /\
   cs_extends count_st sp` by
    (rpt conj_tac >> irule cs_extends_same_block >> gns[inst_extends_def, IS_PREFIX_APPEND]) >>
  `cs_extends st addr_st` by (irule cs_extends_trans >> qexists `head_st` >> simp[]) >>
  `cs_extends st sb` by (irule cs_extends_trans >> qexists `addr_st` >> simp[]) >>
  `cs_extends st count_st` by (irule cs_extends_trans >> qexists `sb` >> simp[]) >>
  mp_tac (Q.SPECL [`st`,`count_st`,`sp`,`func`] fn_has_code_split) >> simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`st`,`sb`,`count_st`,`func`] fn_has_code_split) >> simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`st`,`addr_st`,`sb`,`func`] fn_has_code_split) >> simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`st`,`head_st`,`addr_st`,`func`] fn_has_code_split) >> simp[] >> strip_tac >>
  qpat_x_assum `!R. _ ==> ?A. _` (qspec_then `{x | not_fresh_at sb x}` mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`A'`,`A`] >> simp[] >>
  qpat_assum `emit_op MLOAD _ _ = _`
    (mp_tac o MATCH_MP abi_decoder_operand_live_emit) >> simp[]
QED
