(* The actual runtime-indexed element setup, not a static tuple member. *)
Theory exprSimAbiDecodeArrayRuntimeSetup
Ancestors
  exprSimAbiDecodeArrayInvariant abiDecoderDynamicLoopSetup
  exprSimAbiDecodeAbortReentry abiDecoderVarExtend abiDecoderContract
  exprSimAbiDecodeArrayFetched abiDecoderWordOutcome instIdxIndep
  abiDecoderSiteEffect exprSimAbiDecodeSiteProvenance
  exprSimAbiDecodeOwnedContext exprSimAbiDecodeOwnedMember
  abiDecoderFrame abiDecoderLoopData venomMemDefs vyperABI vyperValue contractABI finite_map pred_set
  exprSimAbiDecodeArrayMembers exprSimAbiDecodeMemberExecute
  abiValidAggregateHeads abiValidMembers abiDecodeRanges
  abiDecoderLoopSetup abiDecoderIndexedAddress abiDecoderReentry abiDecoderSequenceReach
  abiDecoderFiniteControl abiDecoderBytestringOutcome abiDecoderRange
  abiDecoderArrayPtr abiDecoderArrayBound abiDecoderGuard abiDecoderGuards abiDecoderComplexGuard
  abiDecoderComplexHead exprSimAbiDecodeCompositePrefix
  abiEncoder compileEnv emitHelper emitHelperProps exprLoweringProps
  venomState venomInst words list rich_list arithmetic

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

Theorem abi_array_pointer_reentry_opcodes:
  compile_abi_decode_dyn_elem_ptr MLOAD base_op elem_src src_data hi abi_sz st = (child,last) ==>
  EVERY (\i. MEM i.inst_opcode [ADD; LT; GT; AND; ISZERO; MLOAD; ASSERT])
    (emitted_insts st last)
Proof
  Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_array_bounded_pointer_revert_reentry:
  compile_abi_decode_dyn_elem_ptr MLOAD base_op elem_src src_data hi abi_sz st = (child_op,last) /\
  hi <> Lit 0w /\
  eval_operand elem_src s = SOME(n2w pos) /\
  eval_operand base_op s = SOME(n2w B) /\
  eval_operand src_data s = SOME(n2w data_base) /\
  abi_decode_load MLOAD (n2w(B+pos):bytes32) s = n2w child_off /\
  eval_operand hi s = SOME(n2w H) /\
  data_base < dimword(:256) /\ abi_sz < dimword(:256) /\ H < dimword(:256) /\
  (w2n(n2w(data_base+child_off):bytes32) < data_base \/
   H < w2n(n2w(data_base+child_off):bytes32)+abi_sz) /\
  EVERY (abi_decoder_operand_live st.cs_next_var) [elem_src;base_op;src_data;hi] /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st last) s = Abort Revert_abort t /\
    inst_extends st last
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s)` by
    irule abi_decoder_prune_fresh >>
  `eval_operand elem_src (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w pos) /\
   eval_operand base_op (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w B) /\
   eval_operand src_data (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w data_base) /\
   eval_operand hi (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w H)` by
    (fs[] >> asm_simp_tac bool_ss [abi_decoder_prune_eval]) >>
  `abi_decode_load MLOAD (n2w(B+pos):bytes32)
    (abi_decoder_prune_vars st.cs_next_var s) = n2w child_off` by
    fs[abi_decode_load_def, abi_decode_source_def, abi_decoder_prune_vars_def, mload_def] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_array_bounded_pointer_revert >> strip_tac >>
  `abi_decoder_vars_extend s.vs_vars (abi_decoder_prune_vars st.cs_next_var s) s` by
    irule abi_decoder_prune_extension >>
  drule abi_array_pointer_reentry_opcodes >> strip_tac >>
  drule_all abi_decode_guard_sequence_vars_extend_abort >> simp[]
QED

Theorem abi_array_source_setup_revert_reentry:
  abi_decode_array_source_setup ip src MLOAD base_op hi abi_sz st = (ops,last) /\
  hi <> Lit 0w /\ eval_operand ip s = SOME slotword /\ mload (w2n slotword) s = n2w j /\
  eval_operand src s = SOME(n2w p) /\ eval_operand base_op s = SOME(n2w B) /\
  eval_operand hi s = SOME(n2w H) /\
  abi_decode_load MLOAD (n2w(B+(p+32+j*abi_sz)):bytes32) s = n2w child_off /\
  p+32 < dimword(:256) /\ abi_sz < dimword(:256) /\ H < dimword(:256) /\
  (w2n(n2w(p+32+child_off):bytes32) < p+32 \/
   H < w2n(n2w(p+32+child_off):bytes32)+abi_sz) /\
  EVERY (abi_decoder_operand_live st.cs_next_var) [src;base_op;hi] /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st last) s = Abort Revert_abort t /\
    inst_extends st last
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_decode_array_source_setup_split >> strip_tac >>
  drule abi_decode_array_head_setup_counters >> strip_tac >>
  drule abi_decoder_array_pointer_counters >> strip_tac >>
  `c1.cs_next_var <= limit_st.cs_next_var` by
    (Cases_on `base_op = Lit 0w` >> gvs[] >> decide_tac) >>
  `abi_decoder_operand_live c1.cs_next_var base_op /\
   abi_decoder_operand_live c1.cs_next_var hi` by
    (fs[] >> conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `abi_decoder_operand_live st.cs_next_var src` by fs[] >>
  drule_all abi_decode_array_head_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand base_op s1 = SOME(n2w B) /\ eval_operand hi s1 = SOME(n2w H)` by
    (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
  `abi_decode_load MLOAD (n2w(B+(p+32+j*abi_sz)):bytes32) s1 = n2w child_off` by
    (drule abi_decoder_address_frame_load >> strip_tac >> gvs[]) >>
  `EVERY (abi_decoder_operand_live c1.cs_next_var)
    [SND (SND head_ops);base_op;FST (SND head_ops);hi]` by simp[] >>
  drule_all abi_array_bounded_pointer_revert_reentry >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> strip_tac >>
  metis_tac[inst_extends_trans]
QED

Theorem abi_array_dynamic_element_setup_revert_reentry:
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di abi_sz mem_sz st = (ops,last) /\
  dec_info_needs_offset di /\ hi <> Lit 0w /\
  eval_operand ip s = SOME slotword /\ mload (w2n slotword) s = n2w j /\
  eval_operand src s = SOME(n2w p) /\ eval_operand base_op s = SOME(n2w B) /\
  eval_operand hi s = SOME(n2w H) /\
  abi_decode_load MLOAD (n2w(B+(p+32+j*abi_sz)):bytes32) s = n2w child_off /\
  p+32 < dimword(:256) /\ abi_sz < dimword(:256) /\ H < dimword(:256) /\
  (w2n(n2w(p+32+child_off):bytes32) < p+32 \/
   H < w2n(n2w(p+32+child_off):bytes32)+abi_sz) /\
  EVERY (abi_decoder_operand_live st.cs_next_var) [src;base_op;hi] /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st last) s = Abort Revert_abort t /\
    inst_extends st last
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decode_dynamic_element_setup_split >> strip_tac >>
  drule abi_decode_indexed_address_counters >> strip_tac >>
  `c1.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_array_source_setup_revert_reentry >> strip_tac >>
  `inst_extends c1 last` by
    (qhdtm_x_assum `abi_decode_indexed_address` mp_tac >>
     simp[abi_decode_indexed_address_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[] >>
     simp[inst_extends_def, same_blocks_def, emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND]) >>
  `!u. run_inst_seq (emitted_insts st c1) s <> OK u` by simp[] >>
  drule_all run_inst_seq_emit_extend_err >> strip_tac >>
  metis_tac[inst_extends_trans]
QED

Theorem abi_array_dynamic_pointer_source_reject:
  is_dynamic at /\ (!elem. at <> Array (SOME 0) elem) /\
  delta = abi_head_word (DROP (j * abi_member_head_size at) (DROP (p+32) bs)) /\
  LENGTH bs <= H /\ H < dimword(:256) /\
  (w2n(n2w(p+32+delta):bytes32) < p+32 \/
   H < w2n(n2w(p+32+delta):bytes32)+32) ==>
  ~vyper_decode_valid_enc at (abi_array_member_view at bs p j)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> strip_tac >>
  `32 <= LENGTH (abi_array_member_view at bs p j)` by
    metis_tac[abi_valid_dynamic_head_min] >>
  `abi_array_member_view at bs p j = DROP delta (DROP (p+32) bs)` by
    simp[abi_array_member_view_def, abi_decode_member_bytes_def] >>
  `p+32+delta+32 <= LENGTH bs` by
    (fs[LENGTH_DROP] >> decide_tac) >>
  `p+32+delta < dimword(:256)` by decide_tac >>
  fs[w2n_n2w] >> decide_tac
QED

Theorem abi_array_element_setup_straight:
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di abi_sz mem_sz st = (ops,last) ==>
  last.cs_blocks = st.cs_blocks /\ last.cs_current_bb = st.cs_current_bb /\
  inst_extends st last /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st last)
Proof
  Cases_on `dec_info_needs_offset di` >> Cases_on `hi = Lit 0w` >>
  Cases_on `base_op = Lit 0w` >>
  simp[abi_decode_array_element_setup_def, abi_decode_indexed_coordinates_def,
    abi_decode_indexed_address_def,
    compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def,
    inst_extends_def, same_blocks_def, emitted_insts_def]
QED

Theorem abi_array_dynamic_element_setup_reject:
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di 32 mem_sz st = (ops,last) /\
  dec_info_needs_offset di /\ hi <> Lit 0w /\
  eval_operand ip s = SOME slotword /\ mload (w2n slotword) s = n2w j /\
  eval_operand src s = SOME(n2w p) /\ eval_operand base_op s = SOME(n2w B) /\
  eval_operand hi s = SOME(n2w H) /\
  abi_decode_load MLOAD (n2w(B+(p+32+j*32)):bytes32) s = n2w delta /\
  p+32 < dimword(:256) /\ H < dimword(:256) /\ LENGTH bs <= H /\
  is_dynamic (vyper_to_abi_type env ty) /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  delta = abi_head_word (DROP (j * abi_member_head_size (vyper_to_abi_type env ty))
    (DROP (p+32) bs)) /\
  (w2n(n2w(p+32+delta):bytes32) < p+32 \/
   H < w2n(n2w(p+32+delta):bytes32)+32) /\
  EVERY (abi_decoder_operand_live st.cs_next_var) [src;base_op;hi] /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st last fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?u. Dabort ctx fn s Revert_abort u) /\
  ~(?v. abi_decode_source_accepts env ty
    (abi_array_member_view (vyper_to_abi_type env ty) bs p j) v)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  reverse conj_tac
  >- (drule_all abi_array_dynamic_pointer_source_reject >>
      simp[abi_decode_source_accepts_def]) >>
  `32 < dimword(:256)` by simp[] >>
  drule_all abi_array_dynamic_element_setup_revert_reentry >> strip_tac >>
  drule abi_array_element_setup_straight >> strip_tac >>
  drule_all abi_decoder_run_sequence_abort >> strip_tac >>
  qpat_x_assum `!ctx. _` (qspec_then `ctx` strip_assume_tac) >>
  simp[Dabort_def] >> qexistsl_tac [`t with vs_inst_idx := n`, `0`] >> simp[]
QED

Theorem abi_array_pointer_check_bounds:
  data_base < dimword(:256) /\ delta < dimword(:256) /\
  H < dimword(:256) /\
  ~(w2n(n2w(data_base+delta):bytes32) < data_base \/
    H < w2n(n2w(data_base+delta):bytes32)+sz) ==>
  data_base+delta+sz <= H
Proof
  strip_tac >>
  Cases_on `data_base+delta < dimword(:256)`
  >- (fs[w2n_n2w] >> decide_tac) >>
  `data_base+delta-dimword(:256) < dimword(:256) /\
   data_base+delta-dimword(:256) < data_base` by decide_tac >>
  `data_base+delta = dimword(:256)+(data_base+delta-dimword(:256))` by decide_tac >>
  `w2n(n2w(data_base+delta):bytes32) = data_base+delta-dimword(:256)` by
    (pure_rewrite_tac[w2n_n2w] >>
     qpat_x_assum `data_base+delta = _`
       (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     asm_simp_tac bool_ss [ADD_MODULUS_RIGHT, LESS_MOD]) >>
  decide_tac
QED

Theorem abi_array_dynamic_element_setup_sequence_outcome:
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di abi_sz mem_sz st = (ops,last) /\
  dec_info_needs_offset di /\ hi <> Lit 0w /\
  eval_operand ip s = SOME slotword /\ mload (w2n slotword) s = n2w j /\
  eval_operand src s = SOME(n2w p) /\ eval_operand dst s = SOME(n2w d) /\
  eval_operand base_op s = SOME(n2w B) /\ eval_operand hi s = SOME(n2w H) /\
  abi_decode_load MLOAD (n2w(B+(p+32+j*abi_sz)):bytes32) s = n2w delta /\
  p+32 < dimword(:256) /\ delta < dimword(:256) /\
  abi_sz < dimword(:256) /\ H < dimword(:256) /\
  EVERY (abi_decoder_operand_live st.cs_next_var) [src;dst;base_op;hi] /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  (?t. run_inst_seq (emitted_insts st last) s = OK t /\
    p+32+delta+abi_sz <= H /\
    eval_operand (FST ops) t = SOME(n2w j) /\
    eval_operand (FST (SND ops)) t = SOME(n2w(p+32+delta)) /\
    eval_operand (SND (SND ops)) t = SOME(n2w(d+32+j*mem_sz)) /\
    EVERY (abi_decoder_operand_live last.cs_next_var)
      [FST ops; FST (SND ops); SND (SND ops)] /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st last) \/
  (?t. run_inst_seq (emitted_insts st last) s = Abort Revert_abort t /\
    (w2n(n2w(p+32+delta):bytes32) < p+32 \/
     H < w2n(n2w(p+32+delta):bytes32)+abi_sz) /\ inst_extends st last)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `w2n(n2w(p+32+delta):bytes32) < p+32 \/
    H < w2n(n2w(p+32+delta):bytes32)+abi_sz`
  >- (disj2_tac >>
      `EVERY (abi_decoder_operand_live st.cs_next_var) [src;base_op;hi]` by fs[] >>
      drule_all abi_array_dynamic_element_setup_revert_reentry >> metis_tac[]) >>
  disj1_tac >>
  `p+32+delta+abi_sz <= H` by
    (drule_all abi_array_pointer_check_bounds >> simp[]) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  SUBGOAL_THEN ``hi = Lit 0w \/ ?hb. eval_operand hi s = SOME(n2w hb) /\
    p+32+delta+abi_sz <= hb /\ hb < dimword(:256)`` assume_tac
  >- metis_tac[] >>
  qpat_x_assum `EVERY _ _` (strip_assume_tac o REWRITE_RULE [EVERY_DEF]) >>
  drule_all abi_decode_dynamic_element_setup_reentry >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

Theorem abi_array_element_setup_static_opcodes:
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di abi_sz mem_sz st = (ops,last) ==>
  EVERY (\i. abi_bytes_opcode i.inst_opcode \/ i.inst_opcode = MUL)
    (emitted_insts st last)
Proof
  Cases_on `dec_info_needs_offset di` >> Cases_on `hi = Lit 0w` >>
  Cases_on `base_op = Lit 0w` >>
  simp[abi_decode_array_element_setup_def, abi_decode_indexed_coordinates_def,
    abi_decode_indexed_address_def,
    compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, abi_bytes_opcode_def, abi_word_opcode_def]
QED

Theorem abi_array_element_setup_success_reach:
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di abi_sz mem_sz st = (ops,last) /\
  run_inst_seq (emitted_insts st last) s = OK u /\
  abi_decoder_address_frame st.cs_next_var s u /\
  fresh_vars_wrt limit_st u /\ decode_site_resources ctx func s /\
  fn_has_code st last fn /\ abi_decode_entry st s ==>
  ?t. Dreach ctx fn s t /\ abi_decode_entry last t /\
    t.vs_vars = u.vs_vars /\ t.vs_memory = u.vs_memory /\
    t.vs_labels = u.vs_labels /\ fresh_vars_wrt limit_st t /\
    abi_decoder_address_frame st.cs_next_var s t /\
    abi_decode_alloc_progress sites s t /\
    decode_site_effect ctx func st.cs_next_var writes s t
Proof
  strip_tac >>
  drule abi_array_element_setup_straight >> strip_tac >>
  drule abi_array_element_setup_static_opcodes >> strip_tac >>
  drule_all abi_decode_array_bulk_sequence_static >> strip_tac >>
  `decode_site_resources ctx func u` by
    (irule decode_site_resources_fields >> qexists_tac `s` >>
     fs[abi_decoder_address_frame_def, venom_state_component_equality]) >>
  `decode_site_effect ctx func st.cs_next_var writes s u` by
    (simp[decode_site_effect_def, decode_memory_frame_def] >>
     fs[abi_decoder_address_frame_def, decode_static_frame_def,
       venom_state_component_equality]) >>
  qpat_x_assum `u = s with <|vs_vars := _; vs_memory := _|>` kall_tac >>
  `~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by fs[abi_decode_entry_def] >>
  drule_all abi_decoder_run_sequence_prefix >> strip_tac >>
  qexists_tac `t` >>
  gvs[abi_decode_entry_def, abi_decoder_address_frame_def, fresh_vars_wrt_def,
    eval_op_inst_idx, abi_decode_alloc_progress_def] >>
  conj_tac >- (irule Dreach_straight_prefix >> simp[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem abi_array_member_setup_view:
  (is_dynamic at ==> delta = abi_head_word
    (DROP (j * abi_member_head_size at) (DROP (p+32) bs))) ==>
  abi_array_member_view at bs p j =
    abi_decode_source_view at bs
      (p+32 + if is_dynamic at then delta else j * abi_member_head_size at)
Proof
  strip_tac >> pure_rewrite_tac[abi_array_member_view_def] >>
  irule abi_decode_member_contextual_view >> first_assum ACCEPT_TAC
QED

Theorem abi_array_setup_child_context:
  abi_array_runtime_context ctx func ce env ty tv limit_st first
    scratch sites st dst src base_op hi B bs p d n s /\
  abi_decoder_address_frame st.cs_next_var s t /\
  decode_site_effect ctx func st.cs_next_var writes s t /\
  st.cs_next_var <= middle.cs_next_var /\ middle.cs_next_var <= limit_st.cs_next_var /\
  EVERY (abi_decoder_operand_live middle.cs_next_var) [child_dst;child_src] /\
  eval_operand child_src t = SOME(n2w pos) /\
  eval_operand child_dst t = SOME(n2w(d+32+j*type_memory_bytes ce ty)) /\
  fresh_vars_wrt limit_st t /\ abi_decode_entry middle t /\
  j < n /\ pos < dimword(:256) /\
  (!clamp. type_to_abi_dec_info ce.ce_struct_fields ce ty = DecPrimWord clamp ==>
    pos+32 <= LENGTH bs) /\
  child_scratch SUBSET scratch /\
  abi_decode_owned sites child_scratch (d+32+j*type_memory_bytes ce ty)
    (type_memory_bytes ce ty) t ==>
  abi_decode_context_pre ctx func ce env ty tv limit_st first
    (child_scratch UNION abi_array_cell d (type_memory_bytes ce ty) j) sites
    middle child_dst child_src base_op hi B bs pos
    (d+32+j*type_memory_bytes ce ty) t
Proof
  strip_tac >>
  qhdtm_x_assum `abi_array_runtime_context`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_array_runtime_context_def]) >>
  `j*type_memory_bytes ce ty+type_memory_bytes ce ty <= n*type_memory_bytes ce ty` by
    (`j*type_memory_bytes ce ty+type_memory_bytes ce ty =
      SUC j*type_memory_bytes ce ty` by
       (pure_rewrite_tac[MULT_CLAUSES] >> REFL_TAC) >>
     once_asm_rewrite_tac [] >>
     simp_tac bool_ss [LE_MULT_RCANCEL] >> decide_tac) >>
  `abi_decoder_operand_live middle.cs_next_var base_op /\
   abi_decoder_operand_live middle.cs_next_var hi` by
    (fs[] >> conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand base_op t = SOME(n2w B) /\
   eval_operand hi t = SOME(n2w(LENGTH bs))` by
    (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
  `abi_array_cell d (type_memory_bytes ce ty) j =
    {a | d+32+j*type_memory_bytes ce ty <= a /\
      a < d+32+j*type_memory_bytes ce ty+type_memory_bytes ce ty}` by
    simp_tac bool_ss [abi_array_cell_def, MULT_CLAUSES, RIGHT_ADD_DISTRIB, ADD_ASSOC] >>
  simp_tac bool_ss [abi_decode_context_pre_def] >>
  fs[abi_decoder_address_frame_def, decode_site_effect_def] >>
  simp[] >>
  conj_tac
  >- (fs[abi_footprint_disjoint_def] >> rpt strip_tac >>
      qpat_x_assum `!a. _ ==> _ /\ _`
        (qspec_then `MAX B d` mp_tac) >>
      Cases_on `B <= d` >> fs[MAX_DEF] >> decide_tac) >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (drule abi_decode_owned_writes >>
      simp_tac std_ss [SUBSET_DEF, IN_UNION, GSPECIFICATION,
        AC ADD_ASSOC ADD_COMM] >>
      disch_then ACCEPT_TAC) >>
  fs[SUBSET_DEF] >> rpt strip_tac >>
  qpat_x_assum `!a. _ ==> _ /\ _` (qspec_then `a` mp_tac) >>
  simp[] >> decide_tac
QED

Theorem abi_array_current_head_span:
  p+32+n*h <= LENGTH bs /\ j < n ==>
  p+32+j*h+h <= LENGTH bs
Proof
  strip_tac >>
  `j*h+h <= n*h` by
    (`j*h+h = SUC j*h` by (pure_rewrite_tac[MULT_CLAUSES] >> REFL_TAC) >>
     once_asm_rewrite_tac [] >> simp_tac bool_ss [LE_MULT_RCANCEL] >> decide_tac) >>
  decide_tac
QED

Theorem abi_array_ready_dynamic_offset_load:
  abi_array_ready ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s /\
  is_dynamic (vyper_to_abi_type env ty) /\ j < n /\
  p+32+n*abi_member_head_size (vyper_to_abi_type env ty) <= LENGTH bs ==>
  abi_decode_load MLOAD (n2w(B+(p+32+j*32)):bytes32) s =
    n2w(abi_head_word (DROP (j*32) (DROP (p+32) bs)))
Proof
  strip_tac >>
  `abi_member_head_size (vyper_to_abi_type env ty) = 32` by
    simp[abi_member_head_size_def] >>
  `p+32+j*32+32 <= LENGTH bs` by metis_tac[abi_array_current_head_span] >>
  simp_tac bool_ss [GSYM ADD_ASSOC] >>
  irule (REWRITE_RULE [GSYM ADD_ASSOC]
    (Q.INST [`p` |-> `p+32`, `ao` |-> `j*32`] abi_decode_member_offset_load)) >>
  fs[abi_array_ready_def, abi_array_runtime_context_def]
QED

Theorem abi_array_ready_dynamic_setup_outcome:
  abi_array_ready ctx func ce env ty tv limit_st first writes origin
    outer scratch sites idx slot ip st dst src base_op hi B bs p d n j vs s /\
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di 32
    (type_memory_bytes ce ty) st = (ops,middle) /\
  dec_info_needs_offset di /\ is_dynamic (vyper_to_abi_type env ty) /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  j < n /\ p+32+n*abi_member_head_size (vyper_to_abi_type env ty) <= LENGTH bs /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st middle fn ==>
  (?t pos. Dreach ctx fn s t /\ abi_decode_entry middle t /\
    eval_operand (FST ops) t = SOME(n2w j) /\
    eval_operand (FST (SND ops)) t = SOME(n2w pos) /\
    eval_operand (SND (SND ops)) t = SOME(n2w(d+32+j*type_memory_bytes ce ty)) /\
    EVERY (abi_decoder_operand_live middle.cs_next_var)
      [FST ops; FST (SND ops); SND (SND ops)] /\
    pos+32 <= LENGTH bs /\ fresh_vars_wrt limit_st t /\
    abi_decoder_address_frame st.cs_next_var s t /\
    decode_site_effect ctx func st.cs_next_var
      (abi_array_child_scratch sites origin UNION abi_array_cell d (type_memory_bytes ce ty) j) s t /\
    abi_decode_alloc_progress sites s t /\
    abi_array_member_view (vyper_to_abi_type env ty) bs p j =
      abi_decode_source_view (vyper_to_abi_type env ty) bs pos) \/
  (?u. Dabort ctx fn s Revert_abort u /\
    ~(?v. abi_decode_source_accepts env ty
      (abi_array_member_view (vyper_to_abi_type env ty) bs p j) v))
Proof
  strip_tac >>
  drule_all abi_array_ready_dynamic_offset_load >> strip_tac >>
  drule abi_array_ready_loop_data >> strip_tac >>
  drule abi_array_loop_data_slot >> strip_tac >>
  drule abi_array_ready_runtime_context >> strip_tac >>
  `abi_member_head_size (vyper_to_abi_type env ty) = 32` by
    simp[abi_member_head_size_def] >>
  qabbrev_tac `delta = abi_head_word (DROP (j*32) (DROP (p+32) bs))` >>
  `delta < dimword(:256)` by
    simp[Abbr `delta`, abi_head_word_def, dec_number_def, dest_NumV_def, w2n_lt] >>
  `p+32 < dimword(:256) /\ LENGTH bs < dimword(:256)` by
    (fs[abi_array_runtime_context_def] >> decide_tac) >>
  `w2n(n2w slot:bytes32) = slot` by
    fs[abi_array_loop_data_def, Ldata_def, alloca_inv_def] >>
  qhdtm_assum `abi_array_runtime_context`
    (strip_assume_tac o REWRITE_RULE [abi_array_runtime_context_def]) >>
  `EVERY (abi_decoder_operand_live st.cs_next_var) [src;dst;base_op;hi] /\
   EVERY (abi_decoder_operand_live st.cs_next_var) [src;base_op;hi]` by fs[] >>
  `mload (w2n(n2w slot:bytes32)) s = n2w j /\ LENGTH bs <= LENGTH bs /\
   32 < dimword(:256)` by simp[] >>
  Cases_on `w2n(n2w(p+32+delta):bytes32) < p+32 \/
    LENGTH bs < w2n(n2w(p+32+delta):bytes32)+32`
  >- (disj2_tac >>
      `delta = abi_head_word (DROP (j*abi_member_head_size (vyper_to_abi_type env ty))
        (DROP (p+32) bs))` by simp[Abbr `delta`] >>
      `~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
       s.vs_inst_idx = LENGTH st.cs_current_insts` by
        (drule abi_array_ready_entry >> simp_tac bool_ss [abi_decode_entry_def]) >>
      drule_all abi_array_dynamic_element_setup_reject >> metis_tac[]) >>
  drule_all abi_array_dynamic_element_setup_sequence_outcome >>
  disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- (disj1_tac >>
      `abi_decode_entry st s` by metis_tac[abi_array_ready_entry] >>
      drule_all abi_array_element_setup_success_reach >>
      disch_then (qspecl_then
        [`abi_array_child_scratch sites origin UNION abi_array_cell d (type_memory_bytes ce ty) j`,
         `sites`] strip_assume_tac) >>
      rename1 `Dreach ctx fn s actual` >>
      `!op. eval_operand op actual = eval_operand op t` by
        (Cases >> simp_tac bool_ss [eval_operand_def, lookup_var_def] >> asm_rewrite_tac []) >>
      qexistsl_tac [`actual`, `p+32+delta`] >> asm_simp_tac bool_ss [] >>
      mp_tac (Q.INST [`at` |-> `vyper_to_abi_type env ty`] abi_array_member_setup_view) >>
      asm_simp_tac bool_ss [] >> disch_then irule >> simp[Abbr `delta`]) >>
  fs[]
QED
