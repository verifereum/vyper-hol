(* Safe execution of the actual dynamic calldata loop shell. *)
Theory calldataDynStep
Ancestors
  valueEncodingDefs loweringStateRelDefs calldataDynInit calldataChildFrame calldataWordLeaf safeSequence calldataSafeIteration
  abiDecoderExecution abiDecoderContract abiDecoderLoopEmit abiDecoderFrame
  fragExec fragExecMem memSafeRun unitTransformDefs contextCodegenRel codegenRel
  emitHelperProps exprLoweringProps venomExecSemantics venomState venomInst
  words arithmetic list rich_list instIdxIndep abiDecoderIndexedAddress compileEnv emitHelper abiEncoder
  abiDecoderReentryAddress abiDecoderReentry abiDecoderGuards abiDecoderRange
  abiDecoderStaticLoopSetup abiDecoderDynamicLoopSetup abiDecoderLoopSetup
  abiDecoderArraySetupInputs valueEncodingProps valueEncodingProofs valueEncoding

Theorem calldata_element_setup_opcodes:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) hi di abi_sz mem_sz st =
    (ops,st') ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
    (emitted_insts st st')
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `dec_info_needs_offset di` >> Cases_on `hi = Lit 0w` >>
  asm_simp_tac bool_ss [abi_decode_array_element_setup_def,
    abi_decode_indexed_address_def, compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def,
    comp_bind_def, comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[emitted_insts_def, mk_inst_def, is_terminator_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp_tac bool_ss [DROP_LENGTH_APPEND, APPEND] >>
  simp[is_terminator_def, mk_inst_def]
QED

Theorem calldata_header_block_safe:
  s.vs_inst_idx = 0 /\ eval_operand ip s = SOME p /\
  w2n p + 32 <= s.vs_alloca_next ==>
  mem_safe_block fuel ctx
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts id ip src CALLDATALOAD iv cv cmp done body_lbl exit_lbl|> s
Proof
  strip_tac >>
  simp[Once mem_safe_block_def, get_instruction_def,
       abi_decode_header_insts_def] >>
  simp[mem_safe_step_non_invoke, mk_inst_def,
       inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def] >>
  BasicProvers.TOP_CASE_TAC >>
  simp[Once mem_safe_block_def, get_instruction_def,
       mem_safe_step_non_invoke, is_terminator_def,
       inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def] >>
  BasicProvers.TOP_CASE_TAC >>
  simp[Once mem_safe_block_def, get_instruction_def,
       mem_safe_step_non_invoke, is_terminator_def,
       inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def] >>
  BasicProvers.TOP_CASE_TAC >>
  simp[Once mem_safe_block_def, get_instruction_def,
       mem_safe_step_non_invoke, is_terminator_def,
       inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def] >>
  BasicProvers.TOP_CASE_TAC >>
  simp[Once mem_safe_block_def, get_instruction_def,
       mem_safe_step_non_invoke, is_terminator_def,
       inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

Theorem calldata_edge_safe_transfer:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!f. exec_block f ctx bb s = OK t) /\
  (!f. mem_safe_block f ctx bb s) /\ ~t.vs_halted /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 /\ t.vs_inst_idx = 0 ==>
  !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> qexists_tac `SUC fuel` >>
  `t with vs_inst_idx := 0 = t` by
    (Cases_on `t` >> gvs[]) >>
  conj_tac
  >- (drule_all run_blocks_run_from_no_phi >>
      disch_then (qspecl_then [`fuel`, `ctx`] assume_tac) >>
      pure_once_rewrite_tac[run_from_def] >>
      asm_simp_tac (srw_ss()) []) >>
  strip_tac >>
  `eval_phis t next_bb.bb_instructions = OK t` by
    (Cases_on `next_bb.bb_instructions` >>
     gvs[phi_prefix_length_def, eval_phis_def] >>
     Cases_on `h.inst_opcode = PHI` >> gvs[]) >>
  `mem_safe_blocks (SUC fuel) ctx fn t` by
    (drule_all mem_safe_blocks_run >>
     disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
     asm_rewrite_tac[]) >>
  simp[mem_safe_run_def]
QED

Theorem calldata_header_safe_transfer:
  lookup_block s.vs_current_bb fn.fn_blocks =
    SOME <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts id ip src CALLDATALOAD iv cv cmp done body_lbl exit_lbl|> /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  src <> Var iv /\ iv <> cv /\
  eval_operand ip s = SOME p /\ eval_operand src s = SOME srcaddr /\
  mload (w2n p) s = n2w j /\
  abi_decode_load CALLDATALOAD srcaddr s = n2w n /\
  j <= n /\ n < dimword (:256) /\ w2n p+32 <= s.vs_alloca_next /\
  lookup_block (if j<n then body_lbl else exit_lbl) fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 /\
  t = jump_to (if j<n then body_lbl else exit_lbl)
        (abi_decode_header_state iv cv cmp done j n s) ==>
  !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)
Proof
  strip_tac >>
  ho_match_mp_tac (GEN_ALL calldata_edge_safe_transfer) >>
  goal_assum (drule_at (Pos hd)) >>
  qexists_tac `next_bb` >> conj_tac
  >- (gen_tac >> asm_rewrite_tac[] >> irule abi_decode_header_control >>
      simp[abi_decode_source_opcode_def] >> metis_tac[]) >>
  conj_tac
  >- (gen_tac >> irule calldata_header_block_safe >> metis_tac[]) >>
  gvs[jump_to_def, abi_decode_header_state_def, update_var_def]
QED

Theorem calldata_backedge_block_safe:
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ j < n /\ n < dimword (:256) /\
  w2n p+32 <= s.vs_alloca_next ==>
  mem_safe_block fuel ctx bb s
Proof
  strip_tac >>
  `eval_operand ip (update_var nv (n2w (SUC j)) s) = SOME p` by
    (Cases_on `ip` >> gvs[eval_operand_def, lookup_var_update_var]) >>
  drule_all abi_decode_loop_increment_word >> strip_tac >>
  `step_inst_base (mk_inst id ADD [Var iv; Lit 1w] [nv]) s =
     OK (update_var nv (n2w (SUC j)) s)` by
    simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def, eval_operand_lit] >>
  simp[Once mem_safe_block_def, get_instruction_def, EL_APPEND_EQN,
       abi_decode_backedge_insts_def] >>
  fs[mk_inst_def] >>
  simp[step_inst_non_invoke, mem_safe_step_non_invoke, mk_inst_def, is_terminator_def,
       inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def] >>
  simp[Once mem_safe_block_def, get_instruction_def, EL_APPEND_EQN,
       abi_decode_backedge_insts_def] >>
  simp[mem_safe_step_non_invoke, mk_inst_def,
       inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       eval_op_inst_idx, eval_operand_update_var] >>
  simp[update_var_def] >>
  BasicProvers.TOP_CASE_TAC >>
  simp[Once mem_safe_block_def, get_instruction_def, EL_APPEND_EQN,
       abi_decode_backedge_insts_def, ADD1, is_terminator_def,
       mem_safe_step_non_invoke, mk_inst_def,
       inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

Theorem calldata_backedge_safe_transfer:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ j < n /\ n < dimword (:256) /\
  w2n p+32 <= s.vs_alloca_next /\
  lookup_block hdr fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 /\
  t = jump_to hdr
        (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)) ==>
  !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)
Proof
  strip_tac >>
  ho_match_mp_tac (GEN_ALL calldata_edge_safe_transfer) >>
  goal_assum (drule_at (Pos hd)) >>
  qexists_tac `next_bb` >> conj_tac
  >- (gen_tac >> asm_rewrite_tac[] >> irule abi_decode_backedge_control >>
      metis_tac[]) >>
  conj_tac
  >- (gen_tac >> irule calldata_backedge_block_safe >> metis_tac[]) >>
  gvs[jump_to_def, mstore_def, update_var_def]
QED

Theorem calldata_indexed_address_prefix_safe:
  !base idx stride st address st'.
  abi_decode_indexed_address base idx stride st = (address,st') ==>
  !pre i post u.
    emitted_insts st st' = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
    inst_mem_below_frontier i u
Proof
  rpt gen_tac >> strip_tac >> ho_match_mp_tac (GEN_ALL calldata_prefix_safe_every) >>
  qpat_x_assum `abi_decode_indexed_address _ _ _ _ = _` mp_tac >>
  simp[abi_decode_indexed_address_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  imp_res_tac emitted_insts_emit_op >>
  gvs[emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND,
      inst_mem_below_frontier_def, source_memory_read_ranges_def,
      source_memory_write_ranges_def, mk_inst_def]
QED

Theorem calldata_element_pointer_prefix_safe:
  !head data stride st ptr st'.
  compile_abi_decode_dyn_elem_ptr CALLDATALOAD (Lit 0w) head data (Lit 0w) stride st =
    (ptr,st') ==>
  !pre i post u.
    emitted_insts st st' = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
    inst_mem_below_frontier i u
Proof
  rpt gen_tac >> strip_tac >> ho_match_mp_tac (GEN_ALL calldata_prefix_safe_every) >>
  qpat_x_assum `compile_abi_decode_dyn_elem_ptr _ (Lit 0w) _ _ _ _ _ = _` mp_tac >>
  simp[compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  imp_res_tac emitted_insts_emit_op >>
  gvs[emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND,
      inst_mem_below_frontier_def, source_memory_read_ranges_def,
      source_memory_write_ranges_def, mk_inst_def]
QED

(* The loaded offset and addition remain word operations: no source-side
   canonical encoding or nonwrapping premise is used. *)
Theorem calldata_element_pointer_reentry:
  !head data stride st ptr st' s hp dp limit_st.
  compile_abi_decode_dyn_elem_ptr CALLDATALOAD (Lit 0w) head data (Lit 0w) stride st =
    (ptr,st') /\
  eval_operand head s = SOME hp /\ eval_operand data s = SOME dp /\
  abi_decoder_operand_live st.cs_next_var data /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand ptr t = SOME (dp + abi_decode_load CALLDATALOAD hp s) /\
    fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st st'
Proof
  rpt gen_tac >>
  simp[compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [head] st = (off,c1)` >>
  imp_res_tac emitted_insts_emit_op >>
  `c1.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_read_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand data s1 = SOME dp` by metis_tac[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] abi_decoder_binary_reentry)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  qexists_tac `t` >>
  conj_tac >- simp[] >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >>
        qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]) >>
  gvs[update_var_def]
QED

Theorem calldata_element_setup_reentry:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di
    abi_sz mem_sz st = (ops,st') /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand (FST (SND ops)) t =
      SOME (if dec_info_needs_offset di then
        n2w (sb + 32 + w2n (abi_decode_load CALLDATALOAD
          (n2w (sb + 32 + j * abi_sz) : bytes32) s))
        else n2w (sb + 32 + j * abi_sz)) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d + 32 + j * mem_sz)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st'
Proof
  strip_tac >> Cases_on `dec_info_needs_offset di`
  >- (`abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
      `abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
        simp[abi_decoder_operand_live_def] >>
      `abi_decode_load CALLDATALOAD (n2w (sb+32+j*abi_sz) : bytes32) s =
        n2w (w2n (abi_decode_load CALLDATALOAD (n2w (sb+32+j*abi_sz) : bytes32) s))` by
        simp[] >>
      drule_all (SIMP_RULE (srw_ss()) [eval_operand_def]
        (Q.INST [`hi` |-> `Lit 0w`, `base_op` |-> `Lit 0w`, `B` |-> `0`]
          abi_decode_dynamic_element_setup_reentry)) >>
      strip_tac >> qexists_tac `t` >> simp[]) >>
  drule_all abi_decode_static_element_setup_reentry >> strip_tac >>
  qexists_tac `t` >> simp[abi_decoder_address_frame_def]
QED

Theorem calldata_read_pure_tail_prefix_safe[local]:
  inst_mem_below_frontier h s /\ EVERY (\i. !u. inst_mem_below_frontier i u) xs ==>
  !pre i post u. h::xs = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
    inst_mem_below_frontier i u
Proof
  rpt strip_tac >> Cases_on `pre` >> gvs[run_inst_seq_def] >>
  gvs[EVERY_MEM] >> first_x_assum irule >> simp[]
QED

Theorem calldata_element_setup_memory_shape:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di
    abi_sz mem_sz st = (ops,st') ==>
  ?out tail. emitted_insts st st' =
    mk_inst st.cs_next_id MLOAD [ip] [out] :: tail /\
    EVERY (\i. !u. inst_mem_below_frontier i u) tail
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `dec_info_needs_offset di` >>
  asm_simp_tac bool_ss [abi_decode_array_element_setup_def,
    abi_decode_indexed_address_def, compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def,
    comp_bind_def, comp_return_def, comp_ignore_bind_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  qexists_tac `STRING #"%" (toString st.cs_next_var)` >>
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, mk_inst_def]
QED

Theorem calldata_element_setup_prefix_safe:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di
    abi_sz mem_sz st = (ops,st') /\
  eval_operand ip s = SOME p /\ w2n p+32 <= s.vs_alloca_next ==>
  !pre i post u.
    emitted_insts st st' = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
    inst_mem_below_frontier i u
Proof
  strip_tac >> drule calldata_element_setup_memory_shape >> strip_tac >>
  asm_rewrite_tac[] >>
  ho_match_mp_tac (GEN_ALL calldata_read_pure_tail_prefix_safe) >>
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, mk_inst_def]
QED

Theorem calldata_element_setup_frag_mem:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di
    abi_sz mem_sz st = (ops,st') /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  w2n p+32 <= initial.vs_alloca_next ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. eval_operand (FST ops) t = SOME (n2w j) /\
      eval_operand (FST (SND ops)) t =
        SOME (if dec_info_needs_offset di then
          n2w (sb+32+w2n (abi_decode_load CALLDATALOAD
            (n2w (sb+32+j*abi_sz) : bytes32) initial))
          else n2w (sb+32+j*abi_sz)) /\
      eval_operand (SND (SND ops)) t = SOME (n2w (d+32+j*mem_sz)) /\
      fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t)
    (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule_all calldata_element_setup_reentry >> strip_tac >>
  drule calldata_element_setup_opcodes >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> fs[inst_extends_def] >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_element_setup_prefix_safe) >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  gvs[fresh_vars_wrt_def, eval_op_inst_idx, abi_decoder_address_frame_def]
QED

(* Pointwise prefixes keep the final array count separate from progress. *)
Theorem calldata_prefix_window_transport:
  stride = type_memory_size tv /\ LENGTH vs = j /\
  EVERY (val_wf tv) vs /\
  (!k. k < j ==> val_in_memory tv (EL k vs)
    (dst+32+k*stride) s.vs_memory) /\
  mem_bytes_at dst (32+j*stride) t.vs_memory =
    mem_bytes_at dst (32+j*stride) s.vs_memory
  ==>
  mem_word_at dst t.vs_memory = mem_word_at dst s.vs_memory /\
  (!k. k < j ==> val_in_memory tv (EL k vs)
    (dst+32+k*stride) t.vs_memory)
Proof
  rpt strip_tac >>
  drule mem_bytes_at_agree_window >> strip_tac
  >- (first_x_assum (qspec_then `dst` mp_tac) >> simp[]) >>
  irule val_in_memory_mem_agree >> conj_tac
  >- metis_tac[EVERY_EL] >>
  qexistsl_tac [`stride`, `s.vs_memory`] >>
  simp[] >>
  first_x_assum irule >> simp[] >>
  `SUC k <= j` by simp[] >>
  `SUC k * stride <= j * stride` by simp[] >>
  qpat_x_assum `SUC k * stride <= _` mp_tac >>
  pure_rewrite_tac [MULT_CLAUSES] >> pure_asm_rewrite_tac [] >> decide_tac
QED

Theorem calldata_prefix_snoc:
  LENGTH vs = j /\ EVERY P vs /\ EVERY (val_wf tv) vs /\
  (!k. k < j ==> val_in_memory tv (EL k vs) (dst+32+k*stride) mem) /\
  P v /\ val_wf tv v /\ val_in_memory tv v (dst+32+j*stride) mem
  ==>
  LENGTH (vs ++ [v]) = SUC j /\ EVERY P (vs ++ [v]) /\
  EVERY (val_wf tv) (vs ++ [v]) /\
  (!k. k < SUC j ==> val_in_memory tv (EL k (vs ++ [v]))
    (dst+32+k*stride) mem)
Proof
  strip_tac >> simp[] >> rpt strip_tac >>
  Cases_on `k < j`
  >- gvs[EL_APPEND1] >>
  `k = j` by decide_tac >> gvs[EL_APPEND2]
QED

Theorem calldata_prefix_counter_store:
  stride = type_memory_size tv /\ LENGTH vs = j /\
  EVERY (val_wf tv) vs /\
  (!k. k < j ==> val_in_memory tv (EL k vs)
    (dst+32+k*stride) s.vs_memory) /\
  (counter+32 <= dst \/ dst+32+j*stride <= counter)
  ==>
  mem_word_at dst (mstore counter w s).vs_memory = mem_word_at dst s.vs_memory /\
  (!k. k < j ==> val_in_memory tv (EL k vs)
    (dst+32+k*stride) (mstore counter w s).vs_memory)
Proof
  strip_tac >> irule calldata_prefix_window_transport >>
  goal_assum (drule_at Any) >> simp[] >>
  irule mstore_mem_bytes_at_disjoint >> gvs[]
QED

Theorem calldata_typed_prefix_finite_iteration:
  !bound i H P tv dst Q ctx fn R s.
  i <= bound /\ H i s /\
  (?vs. LENGTH vs = i /\ EVERY P vs /\ EVERY (val_wf tv) vs /\
    (!k. k < i ==> val_in_memory tv (EL k vs)
      (dst+32+k*type_memory_size tv) s.vs_memory)) /\
  (!j u vs. j < bound /\ H j u /\ LENGTH vs = j /\
    EVERY P vs /\ EVERY (val_wf tv) vs /\
    (!k. k < j ==> val_in_memory tv (EL k vs)
      (dst+32+k*type_memory_size tv) u.vs_memory) ==>
    (?fuel r. run_from fuel ctx fn u = r /\ exit_result r /\ R r /\
      mem_safe_run fuel ctx fn u) \/
    ?v x. H (SUC j) v /\ P x /\ val_wf tv x /\
      val_in_memory tv x (dst+32+j*type_memory_size tv) v.vs_memory /\
      mem_bytes_at dst (32+j*type_memory_size tv) v.vs_memory =
        mem_bytes_at dst (32+j*type_memory_size tv) u.vs_memory /\
      (!fuel r. run_from fuel ctx fn v = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn u = r /\
          (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u))) /\
  (!u. H bound u ==>
    (?fuel r. run_from fuel ctx fn u = r /\ exit_result r /\ R r /\
      mem_safe_run fuel ctx fn u) \/
    ?v. Q v /\
      !fuel r. run_from fuel ctx fn v = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn u = r /\
          (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)) ==>
  (?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\ R r /\
    mem_safe_run fuel ctx fn s) \/
  ?t. Q t /\
    !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)
Proof
  rpt gen_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  strip_tac >>
  irule (SIMP_RULE (pure_ss ++ boolSimps.LET_ss) [] calldata_safe_finite_iteration) >>
  qexists_tac `\j u. H j u /\ ?vs. LENGTH vs = j /\ EVERY P vs /\
    EVERY (val_wf tv) vs /\
    (!k. k < j ==> val_in_memory tv (EL k vs)
      (dst+32+k*type_memory_size tv) u.vs_memory)` >>
  qexistsl_tac [`bound`, `i`] >>
  simp_tac pure_ss [] >>
  rpt conj_tac
  >- (rpt strip_tac >> gvs[] >>
      qpat_x_assum `!u vs. _` drule_all >> strip_tac
      >- metis_tac[] >>
      disj2_tac >> goal_assum (drule_at Any) >> simp[] >>
      qexists_tac `vs' ++ [x]` >>
      simp[] >> ho_match_mp_tac (GEN_ALL (SIMP_RULE (boss_ss()) [] (cj 4 calldata_prefix_snoc))) >>
      qexists_tac `P` >> simp[] >>
      ho_match_mp_tac (GEN_ALL (SIMP_RULE (boss_ss()) []
        (cj 2 calldata_prefix_window_transport))) >>
      qexistsl_tac [`type_memory_size tv`, `u`] >> simp[])
  >- metis_tac[]
  >- metis_tac[]
  >- simp[]
QED

(* Unlike the earlier interface, the terminal callback receives the decoded
   prefix, so it can assemble the final array without duplicating it in H. *)
Theorem calldata_typed_prefix_finite_iteration_terminal:
  !bound i H P tv dst Q ctx fn R s.
  i <= bound /\ H i s /\
  (?vs. LENGTH vs = i /\ EVERY P vs /\ EVERY (val_wf tv) vs /\
    (!k. k < i ==> val_in_memory tv (EL k vs)
      (dst+32+k*type_memory_size tv) s.vs_memory)) /\
  (!j u vs. j < bound /\ H j u /\ LENGTH vs = j /\
    EVERY P vs /\ EVERY (val_wf tv) vs /\
    (!k. k < j ==> val_in_memory tv (EL k vs)
      (dst+32+k*type_memory_size tv) u.vs_memory) ==>
    (?fuel r. run_from fuel ctx fn u = r /\ exit_result r /\ R r /\
      mem_safe_run fuel ctx fn u) \/
    ?v x. H (SUC j) v /\ P x /\ val_wf tv x /\
      val_in_memory tv x (dst+32+j*type_memory_size tv) v.vs_memory /\
      mem_bytes_at dst (32+j*type_memory_size tv) v.vs_memory =
        mem_bytes_at dst (32+j*type_memory_size tv) u.vs_memory /\
      (!fuel r. run_from fuel ctx fn v = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn u = r /\
          (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u))) /\
  (!u vs. H bound u /\ LENGTH vs = bound /\ EVERY P vs /\
    EVERY (val_wf tv) vs /\
    (!k. k < bound ==> val_in_memory tv (EL k vs)
      (dst+32+k*type_memory_size tv) u.vs_memory) ==>
    (?fuel r. run_from fuel ctx fn u = r /\ exit_result r /\ R r /\
      mem_safe_run fuel ctx fn u) \/
    ?v. Q v /\
      !fuel r. run_from fuel ctx fn v = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn u = r /\
          (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)) ==>
  (?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\ R r /\
    mem_safe_run fuel ctx fn s) \/
  ?t. Q t /\
    !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)
Proof
  rpt gen_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  strip_tac >>
  irule (SIMP_RULE (pure_ss ++ boolSimps.LET_ss) [] calldata_safe_finite_iteration) >>
  qexists_tac `\j u. H j u /\ ?vs. LENGTH vs = j /\ EVERY P vs /\
    EVERY (val_wf tv) vs /\
    (!k. k < j ==> val_in_memory tv (EL k vs)
      (dst+32+k*type_memory_size tv) u.vs_memory)` >>
  qexistsl_tac [`bound`, `i`] >>
  simp_tac pure_ss [] >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >>
      qpat_x_assum `!u vs. _` drule_all >> strip_tac
      >- metis_tac[] >>
      disj2_tac >> goal_assum (drule_at Any) >> simp[] >>
      qexists_tac `vs' ++ [x]` >>
      simp[] >> ho_match_mp_tac (GEN_ALL (SIMP_RULE (boss_ss()) [] (cj 4 calldata_prefix_snoc))) >>
      qexists_tac `P` >> simp[] >>
      ho_match_mp_tac (GEN_ALL (SIMP_RULE (boss_ss()) []
        (cj 2 calldata_prefix_window_transport))) >>
      qexistsl_tac [`type_memory_size tv`, `u`] >> simp[])
  >- (rpt strip_tac >> gvs[] >> metis_tac[])
  >- metis_tac[]
  >- simp[]
QED
