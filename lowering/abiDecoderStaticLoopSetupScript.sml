(* Concrete source and destination setup for clamped static array elements. *)
Theory abiDecoderStaticLoopSetup
Ancestors
  abiDecoderLoopSetup abiDecoderIndexedAddress abiDecoderReentryAddress abiDecoderReentry
  abiDecoderGuards abiDecoderContract abiDecoderDynamic
  emitHelperProps exprLoweringProps compileEnv emitHelper venomState venomInst
  venomExecSemantics words arithmetic list rich_list

Theorem abi_decode_static_element_setup_phases:
  ~dec_info_needs_offset di ==>
  abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz =
    do idx_op <- emit_op MLOAD [ip];
       child_src <- abi_decode_indexed_address src idx_op abi_sz;
       child_dst <- abi_decode_indexed_address dst idx_op mem_sz;
       return (idx_op,child_src,child_dst)
    od
Proof
  strip_tac >>
  simp[FUN_EQ_THM, abi_decode_array_element_setup_def, abi_decode_indexed_address_def,
       comp_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_decode_static_element_setup_shape:
  abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz st = (ops,st') /\
  ~dec_info_needs_offset di ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_array_element_setup_def, abi_decode_indexed_address_def,
    comp_bind_def, comp_return_def, emit_op_def, fresh_var_def, fresh_id_def,
    emit_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[emitted_insts_def, IS_PREFIX_APPEND, mk_inst_def, is_terminator_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp_tac bool_ss [DROP_LENGTH_APPEND, APPEND] >> simp[is_terminator_def]
QED

Theorem abi_decode_static_element_setup_operands:
  abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz st = (ops,st') /\
  ~dec_info_needs_offset di ==>
  st'.cs_next_var = st.cs_next_var + 7 /\
  abi_decoder_operand_live st'.cs_next_var (FST ops) /\
  abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live st'.cs_next_var (SND (SND ops))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_static_element_setup_phases, comp_bind_def,
                       comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MLOAD [ip] st = (idx_op,c1)` >>
  rename1 `abi_decode_indexed_address src idx_op abi_sz c1 = (child_src,c2)` >>
  rename1 `abi_decode_indexed_address dst idx_op mem_sz c2 = (child_dst,end_st)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  imp_res_tac abi_decode_indexed_address_counters >>
  `c1.cs_next_var <= end_st.cs_next_var /\ c2.cs_next_var <= end_st.cs_next_var` by decide_tac >>
  conj_tac >- decide_tac >> metis_tac[abi_decoder_operand_live_mono]
QED

Theorem abi_decode_static_element_setup_reentry:
  abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz st = (ops,st') /\
  ~dec_info_needs_offset di /\ eval_operand ip s = SOME p /\
  mload (w2n p) s = n2w i /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand (FST ops) t = SOME (n2w i) /\
    eval_operand (FST (SND ops)) t = SOME (n2w (sb + 32 + i * abi_sz)) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d + 32 + i * mem_sz)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_static_element_setup_operands >> strip_tac >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_static_element_setup_phases, comp_bind_def,
                       comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op MLOAD [ip] st = (idx_op,c1)` >>
  rename1 `abi_decode_indexed_address src idx_op abi_sz c1 = (child_src,c2)` >>
  rename1 `abi_decode_indexed_address dst idx_op mem_sz c2 = (child_dst,end_st)` >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac abi_decoder_operand_live_emit >>
  imp_res_tac abi_decode_indexed_address_counters >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ c2.cs_next_var <= limit_st.cs_next_var`
    by decide_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_read_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand idx_op s1 = SOME (n2w i) /\
   eval_operand src s1 = SOME (n2w sb) /\ eval_operand dst s1 = SOME (n2w d)` by
    (fs[abi_decode_load_def] >> metis_tac[]) >>
  drule_all abi_decode_indexed_address_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `abi_decoder_operand_live c1.cs_next_var dst /\
   abi_decoder_operand_live c2.cs_next_var idx_op` by
    (conj_tac >- (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
     irule abi_decoder_operand_live_mono >> qexists_tac `c1.cs_next_var` >> simp[]) >>
  `eval_operand dst s2 = SOME (n2w d) /\ eval_operand idx_op s2 = SOME (n2w i)`
    by metis_tac[] >>
  mp_tac (Q.INST [`base_op` |-> `dst`, `idx` |-> `idx_op`, `stride` |-> `mem_sz`,
    `st` |-> `c2`, `st'` |-> `end_st`, `address_op` |-> `child_dst`, `s` |-> `s2`,
    `sb` |-> `d`] abi_decode_indexed_address_reentry) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 end_st) s2 = OK t` >>
  `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  `run_inst_seq (emitted_insts st end_st) s = OK t /\ inst_extends st end_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`, `c2`] >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op /\ abi_decoder_operand_live c2.cs_next_var op`
       by (conj_tac >> irule abi_decoder_operand_live_mono >>
           qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]) >>
  qexists_tac `t` >> gvs[update_var_def] >> metis_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_STATIC_LOOP_SETUP_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI static loop setup not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderStaticLoopSetup");
