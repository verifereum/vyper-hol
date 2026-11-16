(* Compiler-only recovery of the concrete dynamic-loop header phases. *)
Theory bodyFullAbiDecodeLoopHeaderBridge
Ancestors
  bodyFullAbiDecodeLoopLayout abiDecoderLoopEmit abiDecoderRecursiveLoopLayout
  abiDecoderLoopCode abiDecoderLoopSetup abiDecoderAppend abiDecoderPhi abiEncoder fragExec
  compileEnv emitHelper venomInst venomExecSemantics words list rich_list arithmetic abiDecoderExecution abiDecoderContract

Theorem abi_decode_prefix_trace[local]:
  abi_decode_loop_prefix ip src opc base_op start = (labels,loop_body) ==>
  ?l1 l2 l3 entry sa sb sc sd se sf sg idx addr count_op lt done nb1 nb2.
    fresh_label "dec_dyn_hdr" start = (FST labels,l1) /\
    fresh_label "dec_dyn_body" l1 = (FST (SND labels),l2) /\
    fresh_label "dec_dyn_exit" l2 = (SND (SND labels),l3) /\
    emit_inst JMP [Label (FST labels)] [] l3 = ((),entry) /\
    new_block (FST labels) entry = (nb1,sa) /\
    emit_op MLOAD [ip] sa = (idx,sb) /\
    compile_abi_dec_addr base_op src sb = (addr,sc) /\
    emit_op opc [addr] sc = (count_op,sd) /\
    emit_op LT [idx;count_op] sd = (lt,se) /\
    emit_op ISZERO [lt] se = (done,sf) /\
    emit_inst JNZ [done;Label (SND (SND labels));Label (FST (SND labels))] [] sf = ((),sg) /\
    new_block (FST (SND labels)) sg = (nb2,loop_body)
Proof
  simp_tac bool_ss [abi_decode_loop_prefix_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >>
  strip_tac >>
  Cases_on `fresh_label "dec_dyn_hdr" start` >>
  rename1 `fresh_label "dec_dyn_hdr" start = (hdr,l1)` >> gvs[] >>
  Cases_on `fresh_label "dec_dyn_body" l1` >>
  rename1 `fresh_label "dec_dyn_body" l1 = (bl,l2)` >> gvs[] >>
  Cases_on `fresh_label "dec_dyn_exit" l2` >>
  rename1 `fresh_label "dec_dyn_exit" l2 = (el,l3)` >> gvs[] >>
  Cases_on `emit_inst JMP [Label hdr] [] l3` >>
  rename1 `emit_inst JMP [Label hdr] [] l3 = (u,entry)` >>
  Cases_on `u` >> gvs[] >>
  Cases_on `new_block hdr entry` >>
  rename1 `new_block hdr entry = (nl,sa)` >> gvs[] >>
  Cases_on `emit_op MLOAD [ip] sa` >>
  rename1 `emit_op MLOAD [ip] sa = (idx,sb)` >> gvs[] >>
  Cases_on `compile_abi_dec_addr base_op src sb` >>
  rename1 `compile_abi_dec_addr base_op src sb = (addr,sc)` >> gvs[] >>
  Cases_on `emit_op opc [addr] sc` >>
  rename1 `emit_op opc [addr] sc = (co,sd)` >> gvs[] >>
  Cases_on `emit_op LT [idx;co] sd` >>
  rename1 `emit_op LT [idx;co] sd = (lt,se)` >> gvs[] >>
  Cases_on `emit_op ISZERO [lt] se` >>
  rename1 `emit_op ISZERO [lt] se = (done,sf)` >> gvs[] >>
  Cases_on `emit_inst JNZ [done;Label el;Label bl] [] sf` >>
  rename1 `emit_inst JNZ [done;Label el;Label bl] [] sf = (u,sg)` >>
  Cases_on `u` >> gvs[] >>
  Cases_on `new_block bl sg` >>
  rename1 `new_block bl sg = (nb,last)` >> gvs[] >>
  metis_tac[]
QED

Theorem abi_decode_prefix_header_phases[local]:
  abi_decode_loop_prefix (Var counter) src MLOAD (Var input) start = (labels,loop_body) /\
  fn_has_code start loop_body fn ==>
  ?sa sb sc sd se sf sg idx addr count_op lt done.
    emit_op MLOAD [Var counter] sa = (Var idx,sb) /\
    compile_abi_dec_addr (Var input) src sb = (addr,sc) /\
    emit_op MLOAD [addr] sc = (count_op,sd) /\
    emit_op LT [Var idx;count_op] sd = (lt,se) /\
    emit_op ISZERO [lt] se = (done,sf) /\
    emit_inst JNZ [done;Label (SND (SND labels));Label (FST (SND labels))] [] sf = ((),sg) /\
    fn_has_code sa sb fn /\ fn_has_code sb sd fn /\ fn_has_code sd sg fn /\
    sa.cs_current_bb = FST labels /\ sa.cs_current_insts = [] /\
    sa.cs_next_var = start.cs_next_var /\ start.cs_next_id <= sa.cs_next_id /\
    sg.cs_next_var = loop_body.cs_next_var /\ sg.cs_next_id = loop_body.cs_next_id /\
    lookup_block start.cs_current_bb fn.fn_blocks = SOME
      <|bb_label := start.cs_current_bb; bb_instructions := start.cs_current_insts ++
        [mk_inst start.cs_next_id JMP [Label (FST labels)] []]|>
Proof
  strip_tac >> drule abi_decode_prefix_trace >> strip_tac >>
  `?iv. idx = Var iv` by
    (qpat_x_assum `emit_op MLOAD _ sa = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def, emit_inst_def] >> metis_tac[]) >>
  gvs[] >>
  imp_res_tac cs_extends_fresh_label >>
  imp_res_tac cs_extends_new_block >>
  imp_res_tac (REWRITE_RULE [cs_appends_def] cs_appends_emit_helpers) >>
  `cs_extends sb sc` by metis_tac[cs_appends_abi_dec_addr, cs_appends_def] >>
  `cs_extends start sa` by metis_tac[cs_extends_trans] >>
  `cs_extends sb sd /\ cs_extends sd sg /\ cs_extends sb loop_body /\
   cs_extends sd loop_body` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sb fn /\ fn_has_code sb sd fn /\ fn_has_code sd sg fn` by
    metis_tac[fn_has_code_mid, cs_extends_trans] >>
  qexistsl_tac [`sa`,`sb`,`sc`,`sd`,`se`,`sf`,`sg`,`iv`,`addr`,`count_op`,`lt`,`done`] >>
  asm_rewrite_tac[] >>
  `fn_has_code entry sa fn` by metis_tac[fn_has_code_mid, cs_extends_trans] >>
  `lookup_block entry.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := entry.cs_current_bb; bb_instructions := entry.cs_current_insts|>` by
    metis_tac[fn_has_code_new_block] >>
  gvs[fresh_label_def, new_block_def, emit_inst_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_id_def, emit_def]
QED

Theorem abi_decode_loop_header_phases:
  compile_abi_decode_dyn_loop dst src MLOAD (Var input) hi ei asz msz
    (Var counter) cnt start = ((),final_st) /\ fn_has_code start final_st fn ==>
  ?labels loop_body sa sb sc sd se sf sg idx addr count_op lt done.
    abi_decode_loop_prefix (Var counter) src MLOAD (Var input) start = (labels,loop_body) /\
    emit_op MLOAD [Var counter] sa = (Var idx,sb) /\
    compile_abi_dec_addr (Var input) src sb = (addr,sc) /\
    emit_op MLOAD [addr] sc = (count_op,sd) /\
    emit_op LT [Var idx;count_op] sd = (lt,se) /\
    emit_op ISZERO [lt] se = (done,sf) /\
    emit_inst JNZ [done;Label (SND (SND labels));Label (FST (SND labels))] [] sf = ((),sg) /\
    fn_has_code sa sb fn /\ fn_has_code sb sd fn /\ fn_has_code sd sg fn /\
    sa.cs_current_bb = FST labels /\ sa.cs_current_insts = [] /\
    sa.cs_next_var = start.cs_next_var /\ start.cs_next_id <= sa.cs_next_id /\
    sg.cs_next_var = loop_body.cs_next_var /\ sg.cs_next_id = loop_body.cs_next_id /\
    loop_body.cs_current_bb = FST (SND labels) /\ loop_body.cs_current_insts = [] /\
    final_st.cs_current_bb = SND (SND labels) /\ final_st.cs_current_insts = [] /\
    lookup_block start.cs_current_bb fn.fn_blocks = SOME
      <|bb_label := start.cs_current_bb; bb_instructions := start.cs_current_insts ++
        [mk_inst start.cs_next_id JMP [Label (FST labels)] []]|> /\
    lookup_block (FST labels) fn.fn_blocks = SOME
      <|bb_label := FST labels; bb_instructions :=
        abi_decode_position_header_insts (start.cs_next_id+1) (Var counter) src MLOAD
          (Var input) start.cs_next_var (FST (SND labels)) (SND (SND labels))|> /\
    phi_prefix_length (abi_decode_position_header_insts (start.cs_next_id+1)
      (Var counter) src MLOAD (Var input) start.cs_next_var
      (FST (SND labels)) (SND (SND labels))) = 0
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dyn_loop_layout >> strip_tac >>
  rename1 `abi_decode_loop_prefix _ _ _ _ start = (labels,loop_body)` >>
  `cs_extends returned final_st` by metis_tac[abi_decoder_loop_suffix_extends] >>
  `cs_extends start loop_body` by metis_tac[abi_decoder_loop_prefix_extends] >>
  `cs_extends loop_body final_st` by metis_tac[cs_extends_trans] >>
  `fn_has_code start loop_body fn` by metis_tac[fn_has_code_split] >>
  drule_all abi_decode_prefix_header_phases >> strip_tac >>
  qexistsl_tac [`labels`,`loop_body`,`sa`,`sb`,`sc`,`sd`,`se`,`sf`,`sg`,`idx`,
    `addr`,`count_op`,`lt`,`done`] >>
  asm_rewrite_tac[] >>
  simp[abi_decode_position_header_insts_def, abi_decode_header_insts_def,
    phi_prefix_length_def, mk_inst_def]
QED
