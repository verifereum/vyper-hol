(* TOP-LEVEL: execute a member whose empty child needs no payload offset.
   The parent supplies its inline head bound; no source bytes are loaded. *)
Theory abiDecoderEmptyMember
Ancestors
  abiDecoderEmpty abiDecoderEmptyReach abiDecoderComplexGuard abiDecoderMemberCode
  abiDecoderMemberSetup abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderContract
  abiDecoderTypedContract abiDecoderAppend abiValidMemberWindows abiValidMembers
  abiDecoderLoop abiEncoder exprLoweringProps compileEnv fragExec vyperABI contractABI
  venomState venomExecSemantics words list arithmetic

Theorem abi_decode_empty_member_code:
  abi_decode_member_setup dst src opc hi F ao vo st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc hi (DecComplex dynamic [])
    middle = ((),end_st) /\ abi_decode_source_opcode opc /\ fn_has_code st end_st func ==>
  fn_has_code st middle func /\ fn_has_code middle end_st func /\
  st.cs_next_var <= middle.cs_next_var /\ middle.cs_next_var <= end_st.cs_next_var /\
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  abi_decoder_operand_live middle.cs_next_var (SND ops)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  `cs_extends st middle` by (irule cs_extends_same_block >> simp[]) >>
  drule cs_extends_abi_decode >> strip_tac >>
  mp_tac (Q.SPECL [`st`, `middle`, `end_st`, `func`] fn_has_code_split) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decode_complex_head_guard (FST ops) hi 0 middle = ((),end_st)` by
    fs[abi_decode_empty_complex_phases] >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  asm_simp_tac arith_ss []
QED

Theorem abi_decode_empty_member_reach:
  abi_decode_member_setup dst src opc hi F ao vo st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc hi (DecComplex dynamic [])
    middle = ((),end_st) /\ fn_has_code st end_st func /\ abi_decode_source_opcode opc /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + ao <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_empty_member_code >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`st'` |-> `middle`, `dyn` |-> `F`, `payload_off` |-> `0:num`]
    abi_decode_member_setup_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  `abi_decoder_operand_live middle.cs_next_var hi` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `s` |-> `initial:venom_state`,
    `t` |-> `prepared:venom_state`, `edge` |-> `sb + ao`] abi_decoder_address_frame_guard) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then assume_tac >>
  mp_tac (Q.INST [`st` |-> `middle`, `st'` |-> `end_st`, `src` |-> `FST (ops:operand # operand)`,
    `dst` |-> `SND (ops:operand # operand)`, `sb` |-> `sb + ao`,
    `initial` |-> `prepared:venom_state`] abi_decode_empty_complex_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func prepared actual` >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >> conj_tac
  >- (irule abi_decoder_address_frame_trans >>
      qexistsl_tac [`middle.cs_next_var`, `prepared`] >> simp[]) >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> simp[]
QED

Theorem abi_decoder_valid_empty_member:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src opc hi (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
    ao vo st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc hi (type_to_abi_dec_info sf ce ty)
    middle = ((),end_st) /\ fn_has_code st end_st func /\
  abi_decoder_coherent ce env sf ty tv /\ type_to_abi_dec_info sf ce ty = DecComplex T [] /\
  valid_enc_tuple (pre ++ at::ats) bs bs /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs) d outsz b cap initial /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory tv v (d + vo) actual.vs_memory /\
    fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_empty_descriptor_value >> strip_tac >>
  drule abi_valid_member_head >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  SUBGOAL_THEN ``hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + SUM (MAP abi_member_head_size pre) <= hb /\ hb < dimword (:256)`` assume_tac
  >- (Cases_on `hi = Lit 0w` >- simp[] >>
      qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >> strip_tac >>
      rename1 `eval_operand hi initial = SOME (n2w hb)` >>
      qexists_tac `hb` >> asm_simp_tac arith_ss [] >> decide_tac) >>
  qpat_x_assum `type_to_abi_dec_info _ _ _ = DecComplex T []`
    (fn th => RULE_ASSUM_TAC (SIMP_RULE bool_ss [th, dec_info_needs_offset_def])) >>
  mp_tac (Q.INST [`ao` |-> `SUM (MAP abi_member_head_size pre)`, `dynamic` |-> `T`]
    abi_decode_empty_member_reach) >> impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_EMPTY_MEMBER_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI empty member execution fact not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderEmptyMember");
