Theory abiDecoderMemberCons
Ancestors
  abiDecoderMemberCode abiDecoderMemberSetup abiDecoderLoopCode abiDecoderPhi abiDecoderAppend
  abiDecoderContract fragExec compileEnv venomExecSemantics venomInst list rich_list arithmetic
  abiDecoderMemberInfos abiDecoderCode abiDecoderCounters abiDecoderDynamic abiEncoder
  emitHelper emitHelperProps venomState pair abiDecoderMemberTail abiDecoderMemberBody
  abiDecoderMembersCorrect abiDecoderMemberFrames abiDecoderMembers abiDecoderCorrect
  abiDecoderTypedContract abiDecoderEffect abiDecoderReentry abiDecoderLoop abiDecodeRanges
  valueEncoding vyperABI words

(* Derive a recursive member's endpoint PHI condition from its actual successor.
   TOP-LEVEL: abi_decoder_member_exit_phi.
   Helper: a completed-block equality propagates through compiler extensions. *)
Theorem abi_decoder_extension_blocks_middle:
  cs_extends start middle /\ cs_extends middle final /\
  start.cs_blocks = final.cs_blocks ==>
  middle.cs_blocks = final.cs_blocks
Proof
  simp_tac bool_ss [cs_extends_def] >> strip_tac >>
  rename1 `middle.cs_blocks = prefix ++ start.cs_blocks` >>
  rename1 `final.cs_blocks = suffix ++ middle.cs_blocks` >>
  `LENGTH prefix = 0 /\ LENGTH suffix = 0` by
    (qpat_assum `start.cs_blocks = final.cs_blocks` (mp_tac o AP_TERM ``LENGTH:basic_block list -> num``) >>
     qpat_assum `final.cs_blocks = suffix ++ middle.cs_blocks` (fn fin =>
       qpat_assum `middle.cs_blocks = prefix ++ start.cs_blocks` (fn mid =>
         pure_rewrite_tac [fin, mid, LENGTH_APPEND])) >> decide_tac) >>
  gvs[LENGTH_NIL]
QED

Theorem abi_decoder_member_exit_phi:
  compile_abi_decode_to_buf childdst childsrc opc hi di middle = ((),end_st) /\
  abi_decode_member_setup dst src opc hi dyn ao vo end_st = (ops,next_st) /\
  cs_extends next_st final /\ fn_has_code next_st final func /\
  abi_decode_source_opcode opc ==>
  middle.cs_blocks = end_st.cs_blocks \/
  !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> drule_all abi_decoder_to_buf_exit_phi >> strip_tac >>
  Cases_on `middle.cs_blocks = end_st.cs_blocks` >- simp[] >>
  `phi_prefix_length end_st.cs_current_insts = 0` by metis_tac[] >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  drule_all abi_decoder_code_entry_prefix >> strip_tac >>
  asm_simp_tac bool_ss [] >> gen_tac >> strip_tac >>
  Cases_on `end_st.cs_current_insts` >>
  gvs[IS_PREFIX_APPEND, phi_prefix_length_def, mk_inst_def] >>
  rename1 `inst.inst_opcode = PHI` >> Cases_on `inst.inst_opcode = PHI` >> gvs[]
QED

(* Recover actual setup, child and tail compiler phases and containing code.
   TOP-LEVEL: abi_decoder_member_cons_trace, abi_decoder_member_cons_code.
   Helper: arbitrary member-list compilation extends code and SSA counters. *)
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

(* Nonempty member-list execution from head and suffix correctness.
   TOP-LEVEL: abi_decoder_members_correct_cons. *)
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
