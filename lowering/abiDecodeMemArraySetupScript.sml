(* Actual-state array head and guarded element preparation. *)
Theory abiDecodeMemArraySetup
Ancestors
  abiDecodeMemIndexedSetup abiDecodeMemElementReentry abiDecoderDynamicLoopSetup
  calldataDynOwned calldataDynStep entryDecoderHistoryFrame entrySinkExtraction
  fragGasSeqMem fragExecMem fragExec compileEnv emitHelper emitHelperProps
  exprLoweringProps venomExecSemantics venomState venomInst words list rich_list
  allocaFootprint abiDecoderReentry arithmetic abiDecoderIndexedAddress
  abiDecodeMemElementPointer calldataFiniteTransport abiDecoderContract
  fragGasMode fragGasPathMem

Theorem abi_decode_coordinates_address[local]:
  abi_decode_indexed_coordinates src idx stride st = ((data,head),st') ==>
  abi_decode_indexed_address src idx stride st = (head,st')
Proof
  simp[abi_decode_indexed_coordinates_def, abi_decode_indexed_address_def,
       comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem abi_decode_array_head_memory[local]:
  abi_decode_array_head_setup ip src asz st = ((idx,data,head),st') /\
  eval_operand ip s = SOME p /\ w2n p + 32 <= s.vs_alloca_next ==>
  st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts st st') /\
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp[abi_decode_array_head_setup_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MLOAD [ip] st = (idx,c1)` >>
  rename1 `abi_decode_indexed_coordinates src idx asz c1 = ((data,head),end_st)` >>
  drule abi_decode_coordinates_address >> strip_tac >>
  drule calldata_indexed_address_code_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  `isPREFIX st.cs_current_insts c1.cs_current_insts` by simp[IS_PREFIX_APPEND] >>
  `emitted_insts st end_st = emitted_insts st c1 ++ emitted_insts c1 end_st` by
    (irule emitted_insts_append >> simp[] >>
     metis_tac[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  suspend "checks"
QED
Resume abi_decode_array_head_memory[checks]:
  `c1.cs_current_bb = st.cs_current_bb` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def, emit_def,
          comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[]) >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts c1 end_st)` by
    (qpat_x_assum `abi_decode_indexed_address _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decode_indexed_address_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[] >> simp[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND, mk_inst_def]) >>
  `!u. run_inst_seq_mem_ok (emitted_insts c1 end_st) u` by
    (gen_tac >> irule run_inst_seq_mem_ok_of_prefix_safe >>
     fs[EVERY_MEM] >>
     drule (GEN_ALL calldata_indexed_address_prefix_safe) >>
     disch_then (qspec_then `u` mp_tac) >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts st c1) s` by
    metis_tac[emit_mload_mem_ok] >>
  `run_inst_seq_mem_ok (emitted_insts st end_st) s` by
    metis_tac[run_inst_seq_mem_ok_append] >>
  asm_simp_tac bool_ss [EVERY_APPEND, EVERY_DEF, mk_inst_def, is_terminator_def] >>
  simp[is_terminator_def] >> conj_tac >- metis_tac[IS_PREFIX_TRANS] >> fs[EVERY_MEM]
QED
Finalise abi_decode_array_head_memory

Theorem abi_decode_array_head_setup_path_mem[local]:
  abi_decode_array_head_setup ip src asz st = ((idx,data,head),st') /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  w2n p + 32 <= s.vs_alloca_next /\
  eval_operand src s = SOME (n2w sb) /\
  abi_decoder_operand_live st.cs_next_var src /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    eval_operand idx t = SOME (n2w j) /\
    eval_operand data t = SOME (n2w (sb+32)) /\
    eval_operand head t = SOME (n2w (sb+32+j*asz)) /\
    abi_decoder_operand_live st'.cs_next_var idx /\
    abi_decoder_operand_live st'.cs_next_var data /\
    abi_decoder_operand_live st'.cs_next_var head /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
    alloca_history func t
Proof
  strip_tac >> drule_all calldata_head_setup_repeat >> strip_tac >>
  drule_all abi_decode_array_head_memory >> strip_tac >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)`
    by simp[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st') /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st') /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')) = 0`
    by (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  drule_all run_inst_seq_gas_path_mem >> disch_then (qspec_then `ctx` assume_tac) >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts st st') = LENGTH st'.cs_current_insts`
    by gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  qexists_tac `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def] >> gvs[]
QED

Theorem abi_decode_array_head_extends[local]:
  abi_decode_array_head_setup ip src asz st = (ops,st') ==>
  cs_extends st st'
Proof
  simp[abi_decode_array_head_setup_def, abi_decode_indexed_coordinates_def,
    comp_bind_def, comp_return_def, comp_ignore_bind_def, emit_op_def,
    fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  simp[cs_extends_def, IS_PREFIX_APPEND, APPEND_ASSOC]
QED

Theorem abi_decode_array_source_setup_path_mem[local]:
  abi_decode_array_source_setup ip src MLOAD bop hi asz st = (ops,st') /\
  hi <> Lit 0w /\ eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  w2n p + 32 <= s.vs_alloca_next /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand bop s = SOME b /\ eval_operand hi s = SOME h /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var bop /\
  abi_decoder_operand_live st.cs_next_var hi /\
  w2n (b+n2w (sb+32+j*asz)) + 32 <= s.vs_alloca_next /\
  asz < dimword (:256) /\ fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  let off = abi_decode_load MLOAD (b+n2w (sb+32+j*asz)) s;
      data = (n2w (sb+32):bytes32) in
  (w2n data + w2n off + asz <= w2n h ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand (FST ops) t = SOME (n2w j) /\
      eval_operand (SND ops) t = SOME (data+off) /\
      w2n (data+off) = w2n data + w2n off /\
      w2n data <= w2n (data+off) /\ w2n (data+off)+asz <= w2n h /\
      abi_decoder_operand_live st'.cs_next_var (FST ops) /\
      abi_decoder_operand_live st'.cs_next_var (SND ops) /\
      (!op w. abi_decoder_operand_live st.cs_next_var op /\
        eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
      alloca_history func t) /\
  (~(w2n data + w2n off + asz <= w2n h) ==>
    ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule abi_decode_array_source_setup_split >> strip_tac >>
  PairCases_on `head_ops` >> gvs[] >>
  imp_res_tac abi_decode_array_head_extends >>
  imp_res_tac abi_decode_element_shape >>
  `cs_extends c1 st'` by fs[cs_extends_def, inst_extends_def] >>
  `fn_has_code st c1 func /\ fn_has_code c1 st' func` by
    metis_tac[fn_has_code_split] >>
  drule_all abi_decode_array_head_setup_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path_mem ctx func s 0 (OK s1)` >>
  imp_res_tac abi_decode_array_head_setup_counters >>
  `abi_decoder_operand_live c1.cs_next_var bop /\
   abi_decoder_operand_live c1.cs_next_var hi` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand bop s1 = SOME b /\ eval_operand hi s1 = SOME h /\
   alloca_inv s1` by metis_tac[calldata_alloca_inv_fields] >>
  `abi_decode_load MLOAD (b+n2w (sb+32+j*asz)) s1 =
   abi_decode_load MLOAD (b+n2w (sb+32+j*asz)) s` by
    simp[abi_decode_load_def, mload_def] >>
  `w2n (b+n2w (sb+32+j*asz)) + 32 <= s1.vs_alloca_next` by
    (asm_simp_tac bool_ss [] >>
     qpat_x_assum `w2n _ + 32 <= s.vs_alloca_next` mp_tac >>
     simp_tac bool_ss [ADD_ASSOC, ADD_COMM, MULT_COMM]) >>
  drule_all abi_decode_mload_element_reentry_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  conj_tac >- suspend "accept" >> suspend "reject"
QED
Resume abi_decode_array_source_setup_path_mem[accept]:
  strip_tac >> gvs[] >>
  imp_res_tac abi_decode_array_source_setup_counters >>
  `gas_path_mem ctx func s 0 (OK t)` by
    (qpat_x_assum `gas_path_mem ctx func s 0 (OK s1)` mp_tac >>
     qpat_x_assum `gas_path_mem ctx func s1 0 (OK t)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_path_mem_then, ADD_CLAUSES]) >>
  `eval_operand (FST ops) t = SOME (n2w j)` by metis_tac[] >>
  `!op w. abi_decoder_operand_live st.cs_next_var op /\
    eval_operand op s = SOME w ==> eval_operand op t = SOME w` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >>
        qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >>
  simp_tac bool_ss [ADD_ASSOC, ADD_COMM, MULT_COMM]
QED
Resume abi_decode_array_source_setup_path_mem[reject]:
  strip_tac >> gvs[] >>
  fs[gas_marked_path_def] >>
  qpat_x_assum `gas_path_mem ctx func s 0 (OK s1)` mp_tac >>
  qpat_x_assum `gas_path_mem ctx func s1 0 (Abort _ _)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_path_mem_then, ADD_CLAUSES]
QED
Finalise abi_decode_array_source_setup_path_mem

Theorem abi_decode_array_source_extends[local]:
  abi_decode_array_source_setup ip src MLOAD bop hi asz st = (ops,st') ==>
  cs_extends st st'
Proof
  strip_tac >> drule abi_decode_array_source_setup_split >> strip_tac >>
  imp_res_tac abi_decode_array_head_extends >>
  imp_res_tac abi_decode_element_shape >>
  `cs_extends c1 st'` by fs[cs_extends_def, inst_extends_def] >>
  metis_tac[cs_extends_trans]
QED

Theorem abi_decode_dynamic_element_setup_path_mem[local]:
  abi_decode_array_element_setup ip src dst MLOAD bop hi di asz msz st = (ops,st') /\
  dec_info_needs_offset di /\ hi <> Lit 0w /\ eval_operand ip s = SOME p /\
  mload (w2n p) s = n2w j /\ w2n p + 32 <= s.vs_alloca_next /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  eval_operand bop s = SOME b /\ eval_operand hi s = SOME h /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var bop /\
  abi_decoder_operand_live st.cs_next_var hi /\
  w2n (b+n2w (sb+32+j*asz)) + 32 <= s.vs_alloca_next /\
  asz < dimword (:256) /\ fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  let off = abi_decode_load MLOAD (b+n2w (sb+32+j*asz)) s;
      data = (n2w (sb+32):bytes32) in
  (w2n data + w2n off + asz <= w2n h ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand (FST ops) t = SOME (n2w j) /\
      eval_operand (FST (SND ops)) t = SOME (data+off) /\
      eval_operand (SND (SND ops)) t = SOME (n2w (d+32+j*msz)) /\
      w2n (data+off) = w2n data + w2n off /\
      w2n data <= w2n (data+off) /\ w2n (data+off)+asz <= w2n h /\
      abi_decoder_operand_live st'.cs_next_var (FST ops) /\
      abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
      abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
      (!op w. abi_decoder_operand_live st.cs_next_var op /\
        eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
      alloca_history func t) /\
  (~(w2n data + w2n off + asz <= w2n h) ==>
    ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_decode_dynamic_element_setup_split >> strip_tac >>
  imp_res_tac abi_decode_array_source_extends >>
  imp_res_tac calldata_indexed_address_code_shape >>
  `cs_extends c1 st'` by simp[cs_extends_def] >>
  `fn_has_code st c1 func /\ fn_has_code c1 st' func` by
    metis_tac[fn_has_code_split] >>
  drule_all abi_decode_array_source_setup_path_mem >>
  disch_then (qspec_then `ctx` mp_tac) >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  suspend "accept"
QED
Resume abi_decode_dynamic_element_setup_path_mem[accept]:
  strip_tac >> gvs[] >>
  rename1 `gas_path_mem ctx func s 0 (OK s1)` >>
  imp_res_tac abi_decode_array_source_setup_counters >>
  `alloca_inv s1` by metis_tac[calldata_alloca_inv_fields] >>
  `abi_decoder_operand_live c1.cs_next_var dst` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >>
     fs[cs_extends_def]) >>
  `eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  drule_all abi_decode_indexed_address_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path_mem ctx func s1 0 (OK t)` >>
  `gas_path_mem ctx func s 0 (OK t)` by
    (qpat_x_assum `gas_path_mem ctx func s 0 (OK s1)` mp_tac >>
     qpat_x_assum `gas_path_mem ctx func s1 0 (OK t)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_path_mem_then, ADD_CLAUSES]) >>
  `!op w. abi_decoder_operand_live st.cs_next_var op /\
    eval_operand op s = SOME w ==> eval_operand op t = SOME w` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >>
        fs[cs_extends_def]) >> metis_tac[]) >>
  imp_res_tac abi_decode_dynamic_element_setup_counters >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >>
  gvs[]
QED
Finalise abi_decode_dynamic_element_setup_path_mem

Theorem abi_decode_array_element_setup_path_mem:
  abi_decode_array_element_setup ip src dst MLOAD bop hi di asz msz st = (ops,st') /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  w2n p + 32 <= s.vs_alloca_next /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  (dec_info_needs_offset di ==>
    hi <> Lit 0w /\ eval_operand bop s = SOME b /\ eval_operand hi s = SOME h /\
    abi_decoder_operand_live st.cs_next_var bop /\
    abi_decoder_operand_live st.cs_next_var hi /\ asz < dimword (:256) /\
    w2n (b+n2w (sb+32+j*asz)) + 32 <= s.vs_alloca_next) /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  let off = abi_decode_load MLOAD (b+n2w (sb+32+j*asz)) s;
      data = (n2w (sb+32):bytes32);
      child = (if dec_info_needs_offset di then data+off else n2w (sb+32+j*asz));
      accept = (~dec_info_needs_offset di \/ w2n data + w2n off + asz <= w2n h) in
  (accept ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand (FST ops) t = SOME (n2w j) /\
      eval_operand (FST (SND ops)) t = SOME child /\
      eval_operand (SND (SND ops)) t = SOME (n2w (d+32+j*msz)) /\
      (dec_info_needs_offset di ==>
        w2n child = w2n data + w2n off /\
        w2n data <= w2n child /\ w2n child+asz <= w2n h) /\
      abi_decoder_operand_live st'.cs_next_var (FST ops) /\
      abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
      abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
      (!op w. abi_decoder_operand_live st.cs_next_var op /\
        eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
      alloca_history func t) /\
  (~accept ==> ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  strip_tac >> Cases_on `dec_info_needs_offset di`
  >- (qpat_x_assum `dec_info_needs_offset di ==> _` mp_tac >>
      asm_simp_tac bool_ss [] >> strip_tac >>
      drule_all abi_decode_dynamic_element_setup_path_mem >>
      disch_then (qspec_then `ctx` mp_tac) >> simp[LET_THM] >>
      POP_ASSUM_LIST (K all_tac) >> simp[CONJ_ASSOC]) >>
  gvs[] >> drule_all abi_decode_static_element_setup_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  simp[LET_THM] >> qexists_tac `t` >> simp[]
QED
