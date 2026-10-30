(* Actual member compiler phases, counter bounds and endpoint PHI conditions. *)
Theory abiEncoderMemberCode
Ancestors
  abiEncoderPhi abiEncoderAppend abiEncoderCounters abiEncoderAddressReach abiEncoder
  abiDecoderMemberCons abiDecoderLoopCode abiDecoderContract fragExec compileEnv emitHelper
  emitHelperProps venomState venomExecSemantics venomInst list rich_list arithmetic pair

Theorem abi_encoder_members_bounds:
  compile_abi_encode_complex_elems dst src infos so ho dyn_ptr st = (out,final) ==>
  cs_extends st final /\ st.cs_next_var <= final.cs_next_var /\ st.cs_next_id <= final.cs_next_id
Proof
  metis_tac[cj 3 cs_appends_abi_encode_mutual, cs_appends_def,
    cj 3 abi_encoder_counters_mono_mutual, abi_encoder_counters_mono_def, SND]
QED

Theorem abi_encoder_child_bounds:
  compile_abi_encode_child dst src ei dyn ho dyn_ptr st = (out,final) ==>
  cs_extends st final /\ st.cs_next_var <= final.cs_next_var /\ st.cs_next_id <= final.cs_next_id
Proof
  metis_tac[cj 1 cs_appends_abi_encode_mutual, cs_appends_def,
    cj 1 abi_encoder_counters_mono_mutual, abi_encoder_counters_mono_def, SND]
QED

Theorem abi_encoder_member_cons_trace:
  compile_abi_encode_complex_elems dst src ((ei,abi_sz,mem_sz,dyn)::infos)
    so ho dyn_ptr st = (out,final) ==>
  ?elem_src prepared child_len child_end.
    emit_op ADD [src;Lit (n2w so)] st = (elem_src,prepared) /\
    compile_abi_encode_child dst elem_src ei dyn ho dyn_ptr prepared = (child_len,child_end) /\
    compile_abi_encode_complex_elems dst src infos (so+mem_sz) (ho+abi_sz) dyn_ptr child_end = (out,final)
Proof
  simp_tac bool_ss [Once compile_abi_encode_child_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op ADD _ st = (elem_src,prepared)` >>
  rename1 `compile_abi_encode_child dst elem_src ei dyn ho dyn_ptr prepared = (child_len,child_end)` >>
  qexistsl_tac [`elem_src`, `prepared`, `child_len`, `child_end`] >> simp[ADD_COMM]
QED

Theorem abi_encoder_member_cons_context:
  compile_abi_encode_complex_elems dst src ((ei,abi_sz,mem_sz,dyn)::infos)
    so ho dyn_ptr st = (out,final) /\ fn_has_code st final func ==>
  ?elem_src prepared child_len child_end.
    emit_op ADD [src;Lit (n2w so)] st = (elem_src,prepared) /\
    compile_abi_encode_child dst elem_src ei dyn ho dyn_ptr prepared = (child_len,child_end) /\
    compile_abi_encode_complex_elems dst src infos (so+mem_sz) (ho+abi_sz) dyn_ptr child_end = (out,final) /\
    fn_has_code st prepared func /\ fn_has_code prepared child_end func /\ fn_has_code child_end final func /\
    cs_extends st prepared /\ cs_extends prepared child_end /\ cs_extends child_end final /\
    prepared.cs_blocks = st.cs_blocks /\ prepared.cs_next_id = st.cs_next_id+1 /\
    prepared.cs_next_var = st.cs_next_var+1 /\
    prepared.cs_next_id <= child_end.cs_next_id /\ child_end.cs_next_id <= final.cs_next_id /\
    prepared.cs_next_var <= child_end.cs_next_var /\ child_end.cs_next_var <= final.cs_next_var
Proof
  strip_tac >> drule abi_encoder_member_cons_trace >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule abi_encoder_child_bounds >> strip_tac >> drule abi_encoder_members_bounds >> strip_tac >>
  `cs_extends prepared final` by
    (irule cs_extends_trans >> qexists_tac `child_end` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`st`, `prepared`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.SPECL [`prepared`, `child_end`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexistsl_tac [`elem_src`, `prepared`, `child_len`, `child_end`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_member_successor_phi:
  compile_abi_encode_child dst child_src ei dyn ho dyn_ptr prepared = (child_len,child_end) /\
  emit_op ADD [src;Lit (n2w so)] child_end = (elem_src,next_st) /\
  cs_extends next_st final /\ fn_has_code next_st final func ==>
  prepared.cs_blocks = child_end.cs_blocks \/
  !bb. lookup_block child_end.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_child_exit_phi >> strip_tac >>
  Cases_on `prepared.cs_blocks = child_end.cs_blocks` >- simp[] >>
  `phi_prefix_length child_end.cs_current_insts = 0` by metis_tac[] >>
  drule emitted_insts_emit_op >> strip_tac >> drule abi_encoder_emit_address_shape >> strip_tac >>
  drule_all abi_decoder_code_entry_prefix >> strip_tac >>
  asm_simp_tac bool_ss [] >> gen_tac >> strip_tac >>
  Cases_on `child_end.cs_current_insts` >> gvs[IS_PREFIX_APPEND, phi_prefix_length_def, mk_inst_def] >>
  rename1 `inst.inst_opcode = PHI` >> Cases_on `inst.inst_opcode = PHI` >> gvs[]
QED

Theorem abi_encoder_members_entry_code:
  compile_abi_encode_complex_elems dst src ((ei,abi_sz,mem_sz,dyn)::infos)
    so ho dyn_ptr st = (out,final) /\ fn_has_code st final func ==>
  ?elem_src prepared. emit_op ADD [src;Lit (n2w so)] st = (elem_src,prepared) /\
    cs_extends prepared final /\ fn_has_code prepared final func
Proof
  strip_tac >> drule_all abi_encoder_member_cons_context >> strip_tac >>
  `cs_extends prepared final` by
    (irule cs_extends_trans >> qexists_tac `child_end` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`st`, `prepared`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexistsl_tac [`elem_src`, `prepared`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_members_child_phi:
  compile_abi_encode_child dst child_src ei dyn ho dyn_ptr prepared = (child_len,child_end) /\
  compile_abi_encode_complex_elems dst src infos so next_ho dyn_ptr child_end = (out,final) /\
  prepared.cs_blocks = st.cs_blocks /\ fn_has_code child_end final func /\
  (st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  prepared.cs_blocks = child_end.cs_blocks \/
  !bb. lookup_block child_end.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  Cases_on `infos`
  >- (disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      qpat_x_assum `compile_abi_encode_complex_elems _ _ [] _ _ _ _ = _`
        (mp_tac o SIMP_RULE (srw_ss()) [Once compile_abi_encode_child_def, comp_return_def]) >>
      strip_tac >> gvs[] >> metis_tac[]) >>
  rename1 `compile_abi_encode_complex_elems dst src (info::rest) so next_ho dyn_ptr child_end = (out,final)` >>
  PairCases_on `info` >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_members_entry_code >> strip_tac >>
  drule_all abi_encoder_member_successor_phi >> simp[]
QED
