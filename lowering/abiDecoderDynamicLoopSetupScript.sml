(* Execute the dynamic array element's actual head, offset and output setup. *)
Theory abiDecoderDynamicLoopSetup
Ancestors
  abiDecoderLoopSetup abiDecoderIndexedAddress abiDecoderReentryAddress
  abiDecoderReentryPointer abiDecoderReentry abiDecoderGuards abiDecoderContract
  abiDecoderDynamic abiEncoder emitHelperProps exprLoweringProps
  compileEnv emitHelper venomExecSemantics venomState venomInst words arithmetic list rich_list

Definition abi_decoder_address_frame_def:
  abi_decoder_address_frame next s t <=>
    (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted
End

Theorem abi_decoder_address_frame_trans:
  abi_decoder_address_frame first s t /\ abi_decoder_address_frame next t u /\ first <= next ==>
  abi_decoder_address_frame first s u
Proof
  rw[abi_decoder_address_frame_def] >>
  `abi_decoder_operand_live next op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `first` >> simp[]) >>
  metis_tac[]
QED

Definition abi_decode_indexed_coordinates_def:
  abi_decode_indexed_coordinates base_op idx stride =
    do data_op <- emit_op ADD [base_op; Lit 32w];
       offset_op <- emit_op MUL [idx; Lit (n2w stride)];
       address_op <- emit_op ADD [data_op; offset_op];
       return (data_op,address_op)
    od
End

Theorem abi_decoder_address_frame_load:
  abi_decoder_address_frame next s t ==>
  abi_decode_load opc (p:bytes32) t = abi_decode_load opc p s
Proof
  rw[abi_decoder_address_frame_def] >>
  simp[abi_decode_load_def, abi_decode_source_def, mload_def]
QED

Theorem abi_decoder_address_frame_guard:
  abi_decoder_address_frame next s t /\ abi_decoder_operand_live next hi /\
  (hi = Lit 0w \/ ?hb. eval_operand hi s = SOME (n2w hb) /\ edge <= hb /\ hb < dimword (:256)) ==>
  hi = Lit 0w \/ ?hb. eval_operand hi t = SOME (n2w hb) /\ edge <= hb /\ hb < dimword (:256)
Proof
  rw[abi_decoder_address_frame_def] >> metis_tac[]
QED

Theorem abi_decode_indexed_coordinates_counters:
  abi_decode_indexed_coordinates base_op idx stride st = (ops,st') ==>
  st'.cs_next_var = st.cs_next_var + 3 /\
  abi_decoder_operand_live st'.cs_next_var (FST ops) /\
  abi_decoder_operand_live st'.cs_next_var (SND ops)
Proof
  simp[abi_decode_indexed_coordinates_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [base_op; Lit 32w] st = (data_op,c1)` >>
  rename1 `emit_op ADD [data_op;offset_op] c2 = (address_op,end_st)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  `c1.cs_next_var <= end_st.cs_next_var` by decide_tac >>
  conj_tac >- decide_tac >> metis_tac[abi_decoder_operand_live_mono]
QED

Theorem abi_decode_indexed_coordinates_reentry:
  abi_decode_indexed_coordinates base_op idx stride st = (ops,st') /\
  eval_operand base_op s = SOME (n2w sb) /\ eval_operand idx s = SOME (n2w i) /\
  abi_decoder_operand_live st.cs_next_var idx /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand (FST ops) t = SOME (n2w (sb + 32)) /\
    eval_operand (SND ops) t = SOME (n2w (sb + 32 + i * stride)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st'
Proof
  simp[abi_decode_indexed_coordinates_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [base_op; Lit 32w] st = (data_op,c1)` >>
  rename1 `emit_op MUL [idx; Lit (n2w stride)] c1 = (offset_op,c2)` >>
  rename1 `emit_op ADD [data_op;offset_op] c2 = (address_op,end_st)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ c2.cs_next_var <= limit_st.cs_next_var`
    by decide_tac >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] abi_decoder_binary_reentry)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand idx s1 = SOME (n2w i)` by metis_tac[] >>
  `eval_operand (Lit (n2w stride)) s1 = SOME (n2w stride)` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `MUL`] abi_decoder_binary_reentry)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand data_op s2 = SOME ((n2w sb : bytes32) + 32w)` by metis_tac[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] abi_decoder_binary_reentry)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 end_st) s2 = OK t` >>
  `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  `run_inst_seq (emitted_insts st end_st) s = OK t /\ inst_extends st end_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`, `c2`] >> simp[]) >>
  `abi_decoder_operand_live c2.cs_next_var data_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `c1.cs_next_var` >> simp[]) >>
  `eval_operand data_op t = SOME ((n2w sb : bytes32) + 32w)` by metis_tac[] >>
  `abi_decoder_address_frame st.cs_next_var s t` by
    (simp[abi_decoder_address_frame_def, update_var_def] >> rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op /\ abi_decoder_operand_live c2.cs_next_var op`
       by (conj_tac >> irule abi_decoder_operand_live_mono >>
           qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]) >>
  qexists_tac `t` >> gvs[word_add_n2w, word_mul_n2w]
QED

Definition abi_decode_array_head_setup_def:
  abi_decode_array_head_setup ip src abi_sz =
    do idx <- emit_op MLOAD [ip];
       coords <- abi_decode_indexed_coordinates src idx abi_sz;
       return (idx,coords)
    od
End

Theorem abi_decode_array_head_setup_counters:
  abi_decode_array_head_setup ip src abi_sz st = (ops,st') ==>
  st'.cs_next_var = st.cs_next_var + 4 /\
  abi_decoder_operand_live st'.cs_next_var (FST ops) /\
  abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live st'.cs_next_var (SND (SND ops))
Proof
  simp[abi_decode_array_head_setup_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MLOAD [ip] st = (idx,c1)` >>
  rename1 `abi_decode_indexed_coordinates src idx abi_sz c1 = (coords,end_st)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  imp_res_tac abi_decode_indexed_coordinates_counters >>
  `c1.cs_next_var <= end_st.cs_next_var` by decide_tac >>
  conj_tac >- decide_tac >> metis_tac[abi_decoder_operand_live_mono]
QED

Theorem abi_decode_array_head_setup_reentry:
  abi_decode_array_head_setup ip src abi_sz st = (ops,st') /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w i /\
  eval_operand src s = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand (FST ops) t = SOME (n2w i) /\
    eval_operand (FST (SND ops)) t = SOME (n2w (sb + 32)) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (sb + 32 + i * abi_sz)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st'
Proof
  simp[abi_decode_array_head_setup_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MLOAD [ip] st = (idx,c1)` >>
  rename1 `abi_decode_indexed_coordinates src idx abi_sz c1 = (coords,end_st)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  imp_res_tac abi_decode_indexed_coordinates_counters >>
  `c1.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_read_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand idx s1 = SOME (n2w i) /\ eval_operand src s1 = SOME (n2w sb)`
    by (fs[abi_decode_load_def] >> metis_tac[]) >>
  `abi_decoder_address_frame st.cs_next_var s s1`
    by simp[abi_decoder_address_frame_def, update_var_def] >>
  drule_all abi_decode_indexed_coordinates_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 end_st) s1 = OK t` >>
  `abi_decoder_operand_live c1.cs_next_var idx` by first_assum ACCEPT_TAC >>
  `eval_operand idx t = SOME (n2w i)` by (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts st end_st) s = OK t /\ inst_extends st end_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  `abi_decoder_address_frame st.cs_next_var s t` by
    (irule abi_decoder_address_frame_trans >> qexistsl_tac [`c1.cs_next_var`, `s1`] >> simp[]) >>
  qexists_tac `t` >> gvs[]
QED

Theorem abi_decoder_array_pointer_counters:
  compile_abi_decode_dyn_elem_ptr opc head data_op hi abi_sz st = (child_op,st') ==>
  st'.cs_next_var = st.cs_next_var + (if hi = Lit 0w then 2 else 7) /\
  abi_decoder_operand_live st'.cs_next_var child_op
Proof
  Cases_on `hi = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  imp_res_tac abi_decoder_operand_live_emit >> gvs[] >>
  FIRST [first_assum ACCEPT_TAC,
    irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var + 2` >>
    conj_tac >- decide_tac >> first_assum ACCEPT_TAC]
QED

Definition abi_decode_array_source_setup_def:
  abi_decode_array_source_setup ip src opc hi abi_sz =
    do head_ops <- abi_decode_array_head_setup ip src abi_sz;
       child_src <- compile_abi_decode_dyn_elem_ptr opc (SND (SND head_ops))
         (FST (SND head_ops)) hi abi_sz;
       return (FST head_ops,child_src)
    od
End

Theorem abi_decode_array_source_setup_counters:
  abi_decode_array_source_setup ip src opc hi abi_sz st = (ops,st') ==>
  st'.cs_next_var = st.cs_next_var + 4 + (if hi = Lit 0w then 2 else 7) /\
  abi_decoder_operand_live st'.cs_next_var (FST ops) /\
  abi_decoder_operand_live st'.cs_next_var (SND ops)
Proof
  simp[abi_decode_array_source_setup_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_decode_array_head_setup ip src abi_sz st = (head_ops,c1)` >>
  rename1 `compile_abi_decode_dyn_elem_ptr opc _ _ hi abi_sz c1 = (child_src,end_st)` >>
  imp_res_tac abi_decode_array_head_setup_counters >> imp_res_tac abi_decoder_array_pointer_counters >>
  `c1.cs_next_var <= end_st.cs_next_var` by (Cases_on `hi = Lit 0w` >> gvs[]) >>
  conj_tac >- (Cases_on `hi = Lit 0w` >> gvs[]) >>
  metis_tac[abi_decoder_operand_live_mono]
QED

Theorem abi_decode_array_source_setup_split:
  abi_decode_array_source_setup ip src opc hi abi_sz st = (ops,st') ==>
  ?head_ops c1.
    abi_decode_array_head_setup ip src abi_sz st = (head_ops,c1) /\
    compile_abi_decode_dyn_elem_ptr opc (SND (SND head_ops)) (FST (SND head_ops))
      hi abi_sz c1 = (SND ops,st') /\ FST ops = FST head_ops
Proof
  simp[abi_decode_array_source_setup_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_decode_array_head_setup ip src abi_sz st = (head_ops,c1)` >>
  qexistsl_tac [`head_ops`, `c1`] >> simp[]
QED

Theorem abi_decode_array_source_setup_reentry:
  abi_decode_array_source_setup ip src opc hi abi_sz st = (ops,st') /\
  abi_decode_source_opcode opc /\ eval_operand ip s = SOME p /\ mload (w2n p) s = n2w i /\
  eval_operand src s = SOME (n2w sb) /\
  abi_decode_load opc (n2w (sb + 32 + i * abi_sz) : bytes32) s = n2w child_off /\
  (hi = Lit 0w \/ ?hb. eval_operand hi s = SOME (n2w hb) /\
    sb + 32 + child_off + abi_sz <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand (FST ops) t = SOME (n2w i) /\
    eval_operand (SND ops) t = SOME (n2w (sb + 32 + child_off)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decode_array_source_setup_split >> strip_tac >>
  imp_res_tac abi_decode_array_head_setup_counters >> imp_res_tac abi_decoder_array_pointer_counters >>
  `c1.cs_next_var <= limit_st.cs_next_var` by (Cases_on `hi = Lit 0w` >> gvs[] >> decide_tac) >>
  `abi_decoder_operand_live c1.cs_next_var hi` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  drule_all abi_decode_array_head_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `abi_decode_load opc (n2w (sb + 32 + i * abi_sz) : bytes32) s1 = n2w child_off`
    by (drule_all abi_decoder_address_frame_load >> strip_tac >> gvs[]) >>
  SUBGOAL_THEN ``hi = Lit 0w \/ ?hb. eval_operand hi s1 = SOME (n2w hb) /\
     sb + 32 + child_off + abi_sz <= hb /\ hb < dimword (:256)`` assume_tac
  >- (irule abi_decoder_address_frame_guard >> qexistsl_tac [`st.cs_next_var`, `s`] >>
      asm_simp_tac bool_ss []) >>
  drule_all abi_decoder_array_pointer_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  `abi_decoder_address_frame c1.cs_next_var s1 t` by simp[abi_decoder_address_frame_def] >>
  `eval_operand (FST head_ops) t = SOME (n2w i)` by
    (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  `abi_decoder_address_frame st.cs_next_var s t` by
    (irule abi_decoder_address_frame_trans >> qexistsl_tac [`c1.cs_next_var`, `s1`] >> simp[]) >>
  qexists_tac `t` >> gvs[]
QED

Theorem abi_decode_dynamic_element_setup_phases:
  dec_info_needs_offset di ==>
  abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz =
    do src_ops <- abi_decode_array_source_setup ip src opc hi abi_sz;
       child_dst <- abi_decode_indexed_address dst (FST src_ops) mem_sz;
       return (FST src_ops,SND src_ops,child_dst)
    od
Proof
  strip_tac >> simp[FUN_EQ_THM, abi_decode_array_element_setup_def,
    abi_decode_array_source_setup_def, abi_decode_array_head_setup_def,
    abi_decode_indexed_coordinates_def,
    comp_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_decode_dynamic_element_setup_split:
  abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz st = (ops,st') /\
  dec_info_needs_offset di ==>
  ?src_ops c1.
    abi_decode_array_source_setup ip src opc hi abi_sz st = (src_ops,c1) /\
    abi_decode_indexed_address dst (FST src_ops) mem_sz c1 = (SND (SND ops),st') /\
    FST ops = FST src_ops /\ FST (SND ops) = SND src_ops
Proof
  strip_tac >> qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_dynamic_element_setup_phases, comp_bind_def,
    comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_decode_array_source_setup ip src opc hi abi_sz st = (src_ops,c1)` >>
  qexistsl_tac [`src_ops`, `c1`] >> simp[]
QED

Theorem abi_decode_dynamic_element_setup_counters:
  abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz st = (ops,st') /\
  dec_info_needs_offset di ==>
  st'.cs_next_var = st.cs_next_var + 7 + (if hi = Lit 0w then 2 else 7) /\
  abi_decoder_operand_live st'.cs_next_var (FST ops) /\
  abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live st'.cs_next_var (SND (SND ops))
Proof
  strip_tac >> drule_all abi_decode_dynamic_element_setup_split >> strip_tac >>
  imp_res_tac abi_decode_array_source_setup_counters >>
  imp_res_tac abi_decode_indexed_address_counters >>
  `c1.cs_next_var <= st'.cs_next_var` by decide_tac >>
  conj_tac >- (Cases_on `hi = Lit 0w` >> gvs[]) >>
  metis_tac[abi_decoder_operand_live_mono]
QED

Theorem abi_decode_dynamic_element_setup_reentry:
  abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz st = (ops,st') /\
  dec_info_needs_offset di /\ abi_decode_source_opcode opc /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w i /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decode_load opc (n2w (sb + 32 + i * abi_sz) : bytes32) s = n2w child_off /\
  (hi = Lit 0w \/ ?hb. eval_operand hi s = SOME (n2w hb) /\
    sb + 32 + child_off + abi_sz <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand (FST ops) t = SOME (n2w i) /\
    eval_operand (FST (SND ops)) t = SOME (n2w (sb + 32 + child_off)) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d + 32 + i * mem_sz)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_dynamic_element_setup_counters >> strip_tac >>
  drule_all abi_decode_dynamic_element_setup_split >> strip_tac >>
  imp_res_tac abi_decode_array_source_setup_counters >>
  imp_res_tac abi_decode_indexed_address_counters >>
  `c1.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `st.cs_next_var <= c1.cs_next_var` by (Cases_on `hi = Lit 0w` >> gvs[]) >>
  drule_all abi_decode_array_source_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand dst s1 = SOME (n2w d)` by (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
  drule_all abi_decode_indexed_address_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  `abi_decoder_address_frame c1.cs_next_var s1 t` by simp[abi_decoder_address_frame_def] >>
  `eval_operand (FST src_ops) t = SOME (n2w i) /\
   eval_operand (SND src_ops) t = SOME (n2w (sb + 32 + child_off))` by
    (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  `abi_decoder_address_frame st.cs_next_var s t` by
    (irule abi_decoder_address_frame_trans >> qexistsl_tac [`c1.cs_next_var`, `s1`] >> simp[]) >>
  qexists_tac `t` >> gvs[]
QED

Theorem abi_decode_dynamic_element_setup_shape:
  abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz st = (ops,st') /\
  dec_info_needs_offset di /\ abi_decode_source_opcode opc ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `hi = Lit 0w` >>
  asm_simp_tac bool_ss [abi_decode_array_element_setup_def, abi_decode_indexed_address_def,
    compile_abi_decode_dyn_elem_ptr_def, comp_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
    comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[emitted_insts_def, IS_PREFIX_APPEND, mk_inst_def, is_terminator_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp_tac bool_ss [DROP_LENGTH_APPEND, APPEND] >>
  gvs[abi_decode_source_opcode_def, is_terminator_def, mk_inst_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_DYNAMIC_LOOP_SETUP_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI dynamic loop setup not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderDynamicLoopSetup");
