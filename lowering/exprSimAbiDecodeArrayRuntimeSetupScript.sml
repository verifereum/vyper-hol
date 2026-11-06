(* The actual runtime-indexed element setup, not a static tuple member. *)
Theory exprSimAbiDecodeArrayRuntimeSetup
Ancestors
  exprSimAbiDecodeArrayInvariant abiDecoderDynamicLoopSetup
  abiDecoderLoopSetup abiDecoderIndexedAddress abiDecoderReentry abiDecoderSequenceReach
  abiDecoderFiniteControl abiDecoderBytestringOutcome abiDecoderRange
  abiDecoderArrayPtr abiDecoderArrayBound abiDecoderGuard abiDecoderGuards abiDecoderComplexGuard
  abiDecoderComplexHead exprSimAbiDecodeCompositePrefix
  abiEncoder compileEnv emitHelper emitHelperProps exprLoweringProps
  venomState venomInst words list arithmetic

Theorem abi_array_static_element_setup_phases:
  ~dec_info_needs_offset di ==>
  abi_decode_array_element_setup ip src dst opc base_op hi di abi_sz mem_sz =
    do head_ops <- abi_decode_array_head_setup ip src abi_sz;
       child_dst <- abi_decode_indexed_address dst (FST head_ops) mem_sz;
       return (FST head_ops,SND (SND head_ops),child_dst)
    od
Proof
  strip_tac >> simp[FUN_EQ_THM, abi_decode_array_element_setup_def,
    abi_decode_array_head_setup_def, abi_decode_indexed_coordinates_def,
    comp_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_array_static_element_setup_split:
  abi_decode_array_element_setup ip src dst opc base_op hi di abi_sz mem_sz st = (ops,last) /\
  ~dec_info_needs_offset di ==>
  ?head_ops middle.
    abi_decode_array_head_setup ip src abi_sz st = (head_ops,middle) /\
    abi_decode_indexed_address dst (FST head_ops) mem_sz middle =
      (SND (SND ops),last) /\
    FST ops = FST head_ops /\ FST (SND ops) = SND (SND head_ops)
Proof
  strip_tac >>
  qhdtm_x_assum `abi_decode_array_element_setup` mp_tac >>
  asm_simp_tac bool_ss [abi_array_static_element_setup_phases,
    comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  metis_tac[]
QED

Theorem abi_array_static_element_setup_counters:
  abi_decode_array_element_setup ip src dst opc base_op hi di abi_sz mem_sz st = (ops,last) /\
  ~dec_info_needs_offset di ==>
  last.cs_next_var = st.cs_next_var+7 /\
  abi_decoder_operand_live last.cs_next_var (FST ops) /\
  abi_decoder_operand_live last.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live last.cs_next_var (SND (SND ops))
Proof
  strip_tac >> drule_all abi_array_static_element_setup_split >> strip_tac >>
  drule abi_decode_array_head_setup_counters >> strip_tac >>
  drule abi_decode_indexed_address_counters >> strip_tac >>
  `middle.cs_next_var <= last.cs_next_var` by decide_tac >>
  conj_tac >- decide_tac >> metis_tac[abi_decoder_operand_live_mono]
QED

Theorem abi_array_static_element_setup_reentry:
  abi_decode_array_element_setup ip src dst opc base_op hi di abi_sz mem_sz st = (ops,last) /\
  ~dec_info_needs_offset di /\
  eval_operand ip s = SOME slotword /\ mload (w2n slotword) s = n2w j /\
  eval_operand src s = SOME(n2w p) /\ eval_operand dst s = SOME(n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st last) s = OK t /\
    eval_operand (FST ops) t = SOME(n2w j) /\
    eval_operand (FST (SND ops)) t = SOME(n2w(p+32+j*abi_sz)) /\
    eval_operand (SND (SND ops)) t = SOME(n2w(d+32+j*mem_sz)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st last
Proof
  strip_tac >> drule_all abi_array_static_element_setup_split >> strip_tac >>
  drule abi_decode_array_head_setup_counters >> strip_tac >>
  drule abi_decode_indexed_address_counters >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_decode_array_head_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st middle) s = OK s1` >>
  `eval_operand dst s1 = SOME(n2w d)` by
    (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
  drule_all abi_decode_indexed_address_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts middle last) s1 = OK t` >>
  `abi_decoder_address_frame middle.cs_next_var s1 t` by
    simp[abi_decoder_address_frame_def] >>
  `eval_operand (FST head_ops) t = SOME(n2w j) /\
   eval_operand (SND (SND head_ops)) t = SOME(n2w(p+32+j*abi_sz))` by
    (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts st last) s = OK t /\ inst_extends st last` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`middle`] >> simp[]) >>
  `abi_decoder_address_frame st.cs_next_var s t` by
    (irule abi_decoder_address_frame_trans >>
     qexistsl_tac [`middle.cs_next_var`,`s1`] >> simp[]) >>
  qexists_tac `t` >> gvs[]
QED

Theorem abi_array_pointer_guard_phases:
  hi <> Lit 0w ==>
  abi_decode_array_pointer_guard child_op src_data hi abi_sz =
    do abi_decode_ge_guard child_op src_data;
       abi_decode_complex_head_guard child_op hi abi_sz
    od
Proof
  strip_tac >> simp[FUN_EQ_THM, abi_decode_array_pointer_guard_def,
    abi_decode_complex_head_guard_def, comp_bind_def, comp_ignore_bind_def]
QED

Theorem abi_array_pointer_guard_revert:
  abi_decode_array_pointer_guard child_op src_data hi abi_sz st = ((),last) /\
  hi <> Lit 0w /\
  eval_operand child_op s = SOME(n2w child_base) /\
  eval_operand src_data s = SOME(n2w data_base) /\
  eval_operand hi s = SOME(n2w H) /\
  child_base < dimword(:256) /\ data_base < dimword(:256) /\
  abi_sz < dimword(:256) /\ H < dimword(:256) /\
  (child_base < data_base \/ H < child_base+abi_sz) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st last) s = Abort Revert_abort t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `abi_decode_array_pointer_guard` mp_tac >>
  asm_simp_tac bool_ss [abi_array_pointer_guard_phases, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gnvs[] >>
  rename1 `abi_decode_ge_guard child_op src_data st = (u,middle)` >>
  Cases_on `u` >> gnvs[] >>
  drule abi_decode_ge_guard_shape >> strip_tac >>
  drule abi_decode_complex_head_guard_prefix_shape >> strip_tac >>
  Cases_on `child_base < data_base`
  >- (`w2n(n2w child_base:bytes32) < w2n(n2w data_base:bytes32)` by
        simp[w2n_n2w] >>
      drule_all abi_decode_ge_guard_revert >> strip_tac >>
      `!u. run_inst_seq (emitted_insts st middle) s <> OK u` by simp[] >>
      drule_all run_inst_seq_emit_extend_err >> simp[]) >>
  `w2n(n2w data_base:bytes32) <= w2n(n2w child_base:bytes32)` by
    simp[w2n_n2w] >>
  drule_all abi_decode_ge_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st middle) s = OK s1` >>
  `eval_operand child_op s1 = SOME(n2w child_base) /\
   eval_operand hi s1 = SOME(n2w H)` by metis_tac[] >>
  `H < child_base+abi_sz` by decide_tac >>
  drule_all abi_decode_complex_head_guard_revert >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> simp[]
QED

Theorem abi_array_pointer_guard_extends:
  abi_decode_array_pointer_guard child_op src_data hi abi_sz st = ((),last) /\
  hi <> Lit 0w ==> inst_extends st last
Proof
  strip_tac >> qhdtm_x_assum `abi_decode_array_pointer_guard` mp_tac >>
  asm_simp_tac bool_ss [abi_array_pointer_guard_phases, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_ge_guard child_op src_data st = (u,middle)` >>
  Cases_on `u` >> gvs[] >>
  metis_tac[abi_decode_ge_guard_shape, abi_decode_complex_head_guard_prefix_shape,
    inst_extends_trans]
QED

Theorem abi_array_bounded_pointer_revert:
  compile_abi_decode_dyn_elem_ptr opc base_op elem_src src_data hi abi_sz st = (child_op,last) /\
  hi <> Lit 0w /\ abi_decode_source_opcode opc /\
  eval_operand elem_src s = SOME(n2w pos) /\
  eval_operand base_op s = SOME(n2w B) /\
  eval_operand src_data s = SOME(n2w data_base) /\
  abi_decode_load opc (n2w(B+pos):bytes32) s = n2w child_off /\
  eval_operand hi s = SOME(n2w H) /\
  data_base < dimword(:256) /\ abi_sz < dimword(:256) /\ H < dimword(:256) /\
  (w2n(n2w(data_base+child_off):bytes32) < data_base \/
   H < w2n(n2w(data_base+child_off):bytes32)+abi_sz) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st last) s = Abort Revert_abort t /\
    inst_extends st last
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `compile_abi_decode_dyn_elem_ptr` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bounded_array_pointer_phases,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  rename1 `compile_abi_decode_dyn_elem_ptr opc base_op elem_src src_data (Lit 0w)
    abi_sz st = (child_op,middle)` >>
  rename1 `abi_decode_array_pointer_guard child_op src_data hi abi_sz middle = (u,last)` >>
  Cases_on `u` >> gnvs[] >>
  drule_all abi_decode_array_pointer_sentinel >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st middle) s = OK s1` >>
  `eval_operand child_op s1 = SOME(n2w(w2n(n2w(data_base+child_off):bytes32))) /\
   eval_operand src_data s1 = SOME(n2w data_base) /\
   eval_operand hi s1 = SOME(n2w H)` by simp[] >>
  drule abi_array_pointer_guard_revert >>
  disch_then (qspecl_then [`s1`,`data_base`,
    `w2n(n2w(data_base+child_off):bytes32)`,`H`] mp_tac) >>
  (impl_tac >- simp[w2n_n2w, ADD_COMM]) >> strip_tac >>
  drule_all abi_array_pointer_guard_extends >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> strip_tac >>
  metis_tac[inst_extends_trans]
QED
