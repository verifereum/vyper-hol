Theory exprSimAbiDecodeRowCode
Ancestors
  exprSimAbiDecodeTupleOutcome exprSimAbiDecodePhiBoundary
  exprSimAbiDecodeMemberExecute exprSimAbiDecodeSiteProvenance
  abiDecoderMemberSetup abiDecoderAppend
  abiEncoder compileEnv emitHelper emitHelperProps exprLoweringProps
  fragExec venomExecSemantics venomInst list rich_list arithmetic pred_set

Theorem abi_decode_member_setup_empty_phi:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,prepared) /\
  st.cs_current_insts = [] ==>
  prepared.cs_current_bb = st.cs_current_bb /\
  prepared.cs_current_insts <> [] /\
  phi_prefix_length prepared.cs_current_insts = 0
Proof
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  simp[abi_decode_member_setup_def, compile_getelemptr_abi_def,
    compile_abi_dec_addr_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[phi_prefix_length_def, mk_inst_def]
QED

Theorem abi_decode_code_context_suffix:
  abi_decode_code_context func fn st last /\ cs_extends st middle /\
  cs_extends middle last ==>
  abi_decode_code_context func fn middle last
Proof
  simp_tac bool_ss [abi_decode_code_context_def] >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >> simp[] >>
  fs[cs_extends_def] >> gvs[] >>
  metis_tac[LENGTH_APPEND, arithmeticTheory.ADD_EQ_0, LENGTH_NIL]
QED

Theorem abi_decode_complex_elems_entry_phi:
  compile_abi_decode_complex_elems dst src MLOAD base_op hi
    ((ei,asz,msz)::rest) ao vo st = ((),last) /\
  fn_has_code st last fn /\ st.cs_current_insts = [] ==>
  !bb. lookup_block st.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  drule (iffLR abi_decode_complex_elems_cons_split) >> strip_tac >>
  drule_all abi_decode_complex_elems_child_context >> strip_tac >>
  drule_all abi_decode_member_setup_empty_phi >> strip_tac >>
  metis_tac[abi_decode_continuation_exit_phi]
QED

Theorem abi_decode_complex_elems_phase_contexts:
  abi_decode_member_setup dst src MLOAD base_op hi
    (dec_info_needs_offset ei) ao vo st = (ops,prepared) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) MLOAD base_op hi ei
    prepared = ((),child_end) /\
  compile_abi_decode_complex_elems dst src MLOAD base_op hi
    rest (ao+asz) (vo+msz) child_end = ((),last) /\
  abi_decode_code_context func fn st last ==>
  abi_decode_code_context func fn st child_end /\
  abi_decode_code_context func fn child_end last /\
  cs_extends st child_end /\ cs_extends child_end last
Proof
  strip_tac >>
  `fn_has_code st last fn` by fs[abi_decode_code_context_def] >>
  drule_all abi_decode_complex_elems_child_context >> strip_tac >>
  `abi_decode_code_context func fn child_end last` by
    metis_tac[abi_decode_code_context_suffix] >>
  simp[] >>
  Cases_on `rest`
  >- (gvs[abi_decode_complex_elems_nil]) >>
  PairCases_on `h` >>
  Cases_on `child_end.cs_current_insts = []`
  >- (`!bb. lookup_block child_end.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0` by
        metis_tac[abi_decode_complex_elems_entry_phi] >>
      fs[abi_decode_code_context_def]) >>
  fs[abi_decode_code_context_def]
QED

Theorem abi_decode_member_setup_mono:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,prepared) ==>
  ci_mono st prepared
Proof
  strip_tac >>
  drule exprSimAbiDecodeMemberOutcomeTheory.abi_decode_member_mload_setup_shape >> strip_tac >>
  `cs_extends st prepared` by
    fs[cs_extends_def, inst_extends_def] >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  simp[abi_decode_member_setup_def, compile_getelemptr_abi_def,
    compile_abi_dec_addr_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[ci_mono_def]
QED

Theorem abi_decode_complex_elems_phase_mono:
  abi_decode_member_setup dst src MLOAD base_op hi
    (dec_info_needs_offset ei) ao vo st = (ops,prepared) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) MLOAD base_op hi ei
    prepared = ((),child_end) /\
  compile_abi_decode_complex_elems dst src MLOAD base_op hi
    rest (ao+asz) (vo+msz) child_end = ((),last) ==>
  ci_mono st prepared /\ ci_mono prepared child_end /\ ci_mono child_end last
Proof
  strip_tac >> conj_tac >- metis_tac[abi_decode_member_setup_mono] >>
  metis_tac[ci_mono_compile_abi_decode, pairTheory.SND]
QED

Theorem abi_decode_mapped_rows_code_split:
  compile_abi_decode_complex_elems dst src MLOAD base_op hi
    (MAP abi_tuple_row_code ((ei,ty,tv,asz,msz)::rows)) ao vo st = ((),last) /\
  abi_decode_code_context func fn st last ==>
  ?ops prepared child_end.
    abi_decode_member_setup dst src MLOAD base_op hi
      (dec_info_needs_offset ei) ao vo st = (ops,prepared) /\
    compile_abi_decode_to_buf (SND ops) (FST ops) MLOAD base_op hi ei
      prepared = ((),child_end) /\
    compile_abi_decode_complex_elems dst src MLOAD base_op hi
      (MAP abi_tuple_row_code rows) (ao+asz) (vo+msz) child_end = ((),last) /\
    abi_decode_code_context func fn st child_end /\
    abi_decode_code_context func fn child_end last /\
    ci_mono st prepared /\ ci_mono prepared child_end /\ ci_mono child_end last /\
    abi_decode_sites st.cs_next_id child_end.cs_next_id SUBSET
      abi_decode_sites st.cs_next_id last.cs_next_id /\
    abi_decode_sites child_end.cs_next_id last.cs_next_id SUBSET
      abi_decode_sites st.cs_next_id last.cs_next_id
Proof
  simp_tac bool_ss [MAP, abi_tuple_row_code_def] >> strip_tac >>
  drule (iffLR abi_decode_complex_elems_cons_split) >> strip_tac >>
  drule_all abi_decode_complex_elems_phase_contexts >> strip_tac >>
  drule_all abi_decode_complex_elems_phase_mono >> strip_tac >>
  qexistsl_tac [`ops`,`prepared`,`child_end`] >> simp[] >>
  fs[abi_decode_sites_def, SUBSET_DEF, ci_mono_def] >> rpt strip_tac >> decide_tac
QED
