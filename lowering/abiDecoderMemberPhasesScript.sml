(* Recover actual setup, child and tail compiler phases and containing code.
   TOP-LEVEL: abi_decoder_member_cons_trace, abi_decoder_member_cons_code.
   Helper: arbitrary member-list compilation extends code and SSA counters. *)
Theory abiDecoderMemberPhases
Ancestors
  abiDecoderMemberInfos abiDecoderMemberSetup abiDecoderMemberCode abiDecoderCode
  abiDecoderAppend abiDecoderCounters abiDecoderContract abiDecoderDynamic abiDecoderMemberSyntax
  abiEncoder fragExec compileEnv emitHelper emitHelperProps
  venomState venomInst list arithmetic pair

Theorem abi_decoder_members_extends:
  compile_abi_decode_complex_elems dst src opc hi elems ao vo st = ((),final) ==>
  cs_extends st final /\ st.cs_next_var <= final.cs_next_var
Proof
  strip_tac >> conj_tac
  >- metis_tac[cj 2 cs_appends_abi_decode_mutual, cs_appends_def] >>
  metis_tac[cj 2 abi_decoder_vars_mono_mutual, abi_decoder_vars_mono_def, SND]
QED

Theorem abi_decoder_member_cons_trace:
  compile_abi_decode_complex_elems dst src opc hi (abi_decoder_member_infos sf ce (ty::tys))
    ao vo st = ((),final) ==>
  ?ops middle end_st.
    abi_decode_member_setup dst src opc hi (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
      ao vo st = (ops,middle) /\
    compile_abi_decode_to_buf (SND ops) (FST ops) opc hi
      (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
    compile_abi_decode_complex_elems dst src opc hi (abi_decoder_member_infos sf ce tys)
      (ao + abi_embedded_static_size ce.ce_struct_fields ty)
      (vo + type_memory_bytes ce ty) end_st = ((),final)
Proof
  simp_tac bool_ss [abi_decoder_member_infos_def, MAP] >>
  rewrite_tac [abi_decode_complex_member_phases] >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_decode_member_setup dst src opc hi _ ao vo st = (ops,middle)` >>
  rename1 `compile_abi_decode_to_buf _ _ opc hi _ middle = ((),end_st)` >>
  qexistsl_tac [`ops`, `middle`, `end_st`] >> simp[]
QED

Theorem abi_decoder_member_cons_code:
  abi_decode_member_setup dst src opc hi dyn ao vo st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc hi di middle = ((),end_st) /\
  compile_abi_decode_complex_elems dst src opc hi elems next_ao next_vo end_st = ((),final) /\
  abi_decode_source_opcode opc /\ fn_has_code st final func ==>
  cs_extends st middle /\ cs_extends middle end_st /\ cs_extends end_st final /\
  cs_extends st end_st /\ cs_extends middle final /\
  fn_has_code st end_st func /\ fn_has_code end_st final func /\
  fn_has_code middle final func /\
  st.cs_next_id < middle.cs_next_id /\ middle.cs_next_id <= end_st.cs_next_id /\
  end_st.cs_next_id <= final.cs_next_id /\
  st.cs_next_var <= middle.cs_next_var /\ middle.cs_next_var <= end_st.cs_next_var /\
  end_st.cs_next_var <= final.cs_next_var
Proof
  strip_tac >> drule_all abi_decode_member_setup_shape >> strip_tac >>
  `cs_extends st middle` by (irule cs_extends_same_block >> simp[]) >>
  drule cs_extends_abi_decode >> strip_tac >>
  drule abi_decoder_members_extends >> strip_tac >>
  `cs_extends st end_st` by
    (irule cs_extends_trans >> qexists_tac `middle` >> simp[]) >>
  `cs_extends middle final` by
    (irule cs_extends_trans >> qexists_tac `end_st` >> simp[]) >>
  mp_tac (Q.SPECL [`st`, `end_st`, `final`, `func`] fn_has_code_split) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.SPECL [`st`, `middle`, `final`, `func`] fn_has_code_split) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_decoder_to_buf_code >> strip_tac >>
  drule_all abi_decoder_complex_elems_code >> strip_tac >>
  drule abi_decoder_variable_counter >> strip_tac >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >>
  gvs[abi_decoder_code_def]
QED

Theorem abi_decoder_members_entry_code:
  compile_abi_decode_complex_elems dst src opc hi (abi_decoder_member_infos sf ce (ty::tys))
    ao vo st = ((),final) /\ abi_decode_source_opcode opc /\ fn_has_code st final func ==>
  ?ops middle.
    abi_decode_member_setup dst src opc hi (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
      ao vo st = (ops,middle) /\
    cs_extends middle final /\ fn_has_code middle final func
Proof
  strip_tac >> drule abi_decoder_member_cons_trace >> strip_tac >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  qexistsl_tac [`ops`, `middle`] >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_members_tail_phi:
  cs_extends st end_st /\ cs_extends end_st final /\
  (st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  end_st.cs_blocks = final.cs_blocks \/
  !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  metis_tac[abi_decoder_extension_blocks_middle]
QED

Theorem abi_decoder_members_child_phi:
  compile_abi_decode_to_buf childdst childsrc opc hi di middle = ((),end_st) /\
  compile_abi_decode_complex_elems dst src opc hi (abi_decoder_member_infos sf ce tys)
    ao vo end_st = ((),final) /\
  middle.cs_blocks = st.cs_blocks /\ abi_decode_source_opcode opc /\
  fn_has_code end_st final func /\
  (st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  middle.cs_blocks = end_st.cs_blocks \/
  !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  Cases_on `tys`
  >- (simp[abi_decoder_member_infos_def, Once compile_abi_decode_to_buf_def,
        comp_return_def] >> metis_tac[]) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_members_entry_code >> strip_tac >>
  drule_all abi_decoder_member_exit_phi >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_MEMBER_PHASES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI member phases not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderMemberPhases");
