(* Nonwriting bytes prefix retains both resolved source and checked count. *)
Theory abiDecoderBytesPrefix
Ancestors
  abiDecoderBytesPhases abiDecoderComposition abiDecoderRange abiDecoderGuards
  abiDecoderBytesBound abiDecoderContract abiEncoder compileEnv emitHelper
  exprLoweringProps emitHelperProps venomInst list rich_list
  venomExecSemantics venomState words

Definition abi_decode_bytes_position_prefix_def:
  abi_decode_bytes_position_prefix pos opc base_op hi n =
    do head <- abi_decode_bytes_head pos hi;
       addr <- compile_abi_dec_addr base_op pos;
       cnt <- abi_decode_count_guard opc addr n;
       abi_decode_bytes_payload_guard head cnt hi;
       return (addr,cnt)
    od
End

Theorem abi_decode_bytes_position_prefix_trace:
  abi_decode_bytes_position_prefix pos opc base_op hi n st = ((addr,cnt),st') <=>
  ?head head_st addr_st count_st.
    abi_decode_bytes_head pos hi st = (head,head_st) /\
    compile_abi_dec_addr base_op pos head_st = (addr,addr_st) /\
    abi_decode_count_guard opc addr n addr_st = (cnt,count_st) /\
    abi_decode_bytes_payload_guard head cnt hi count_st = ((),st')
Proof
  simp[abi_decode_bytes_position_prefix_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  eq_tac >> rpt strip_tac >> gvs[] >>
  metis_tac[pairTheory.PAIR, pairTheory.pair_CASES, oneTheory.one]
QED

Theorem abi_decode_bytes_position_prefix_shape:
  abi_decode_bytes_position_prefix pos opc base_op hi n st = ((addr,cnt),st') /\
  abi_decode_source_opcode opc ==>
  inst_extends st st' /\ st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  st.cs_next_var <= st'.cs_next_var /\ st.cs_next_id <= st'.cs_next_id /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    ~is_alloca_op i.inst_opcode) (emitted_insts st st')
Proof
  strip_tac >> Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  gvs[abi_decode_bytes_position_prefix_def, abi_decode_bytes_head_def,
      compile_abi_dec_addr_def, abi_decode_count_guard_def,
      abi_decode_bytes_payload_guard_def, compile_abi_decode_range_check_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
      inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, abi_decode_source_opcode_def,
      is_terminator_def, is_alloca_op_def, mk_inst_def]
QED

Theorem abi_decode_bytes_prefix_phases:
  abi_decode_source_opcode opc ==>
  compile_abi_decode_to_buf dst pos opc base_op hi (DecBytestring n) =
    do ac <- abi_decode_bytes_position_prefix pos opc base_op hi n;
       if base_op = Lit 0w then
         emit_void (abi_decode_copy_opcode opc)
           [dst; pos; Lit (n2w (32+32*((n+31) DIV 32)))]
       else abi_decode_bytes_runtime_tail dst (FST ac) (SND ac)
    od
Proof
  strip_tac >> asm_simp_tac bool_ss [abi_decode_bytes_position_phases] >>
  simp[FUN_EQ_THM, abi_decode_bytes_position_prefix_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_decode_bytes_position_prefix_unbounded:
  abi_decode_bytes_position_prefix pos opc base_op (Lit 0w) n =
  do addr <- compile_abi_dec_addr base_op pos;
     cnt <- abi_decode_count_guard opc addr n;
     return (addr,cnt)
  od
Proof
  simp[abi_decode_bytes_position_prefix_def, abi_decode_bytes_head_def,
       abi_decode_bytes_payload_guard_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, FUN_EQ_THM]
QED

Theorem abi_decode_bytes_position_prefix_sequence:
  abi_decode_bytes_position_prefix pos opc base_op hi n st = ((addr,cnt),st') /\
  abi_decode_source_opcode opc /\ eval_operand pos s = SOME (n2w p) /\
  eval_operand base_op s = SOME (n2w b) /\
  abi_decode_load opc (n2w (b+p) : bytes32) s = n2w c /\
  c <= n /\ n < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
                     p + 32 + c <= h /\ h < dimword (:256)) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand addr t = SOME (n2w (b+p)) /\
    eval_operand cnt t = SOME (n2w c) /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  Cases_on `hi = Lit 0w`
  >- suspend "unbounded"
  >> suspend "bounded"
QED

Resume abi_decode_bytes_position_prefix_sequence[unbounded]:
  gvs[abi_decode_bytes_position_prefix_unbounded, comp_bind_def,
      comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_abi_dec_addr base_op pos st = (addr,c1)` >>
  drule_all compile_abi_dec_addr_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `abi_decode_load opc (n2w (b+p) : bytes32) s1 = n2w c` by
    gvs[abi_decode_load_def, abi_decode_source_def, mload_def] >>
  drule_all abi_decode_count_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  `inst_extends st c1` by
    (Cases_on `base_op = Lit 0w` >>
     gvs[compile_abi_dec_addr_def, comp_return_def, inst_extends_refl] >>
     metis_tac[inst_extends_emit_op]) >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

Resume abi_decode_bytes_position_prefix_sequence[bounded]:
  strip_tac >> gvs[] >>
  qpat_x_assum `abi_decode_bytes_position_prefix _ _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[abi_decode_bytes_position_prefix_trace] >> strip_tac >>
  `p + 32 <= h` by decide_tac >>
  drule_all abi_decode_bytes_head_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st head_st) s = OK s1` >>
  `eval_operand base_op s1 = SOME (n2w b) /\
   eval_operand pos s1 = SOME (n2w p)` by metis_tac[] >>
  drule_all compile_abi_dec_addr_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts head_st addr_st) s1 = OK s2` >>
  `abi_decode_load opc (n2w (b+p) : bytes32) s2 = n2w c` by
    gvs[abi_decode_load_def, abi_decode_source_def, mload_def] >>
  drule_all abi_decode_count_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts addr_st count_st) s2 = OK s3` >>
  `eval_operand head s3 = SOME (n2w (p+32)) /\
   eval_operand hi s3 = SOME (n2w h)` by metis_tac[] >>
  drule abi_decode_bytes_payload_guard_sequence >>
  disch_then (qspecl_then [`s3`, `p+32`, `c`] mp_tac) >>
  (impl_tac >- (simp[] >> qexists_tac `h` >> simp[])) >>
  strip_tac >>
  rename1 `run_inst_seq (emitted_insts count_st st') s3 = OK t` >>
  `inst_extends head_st addr_st` by
    (Cases_on `base_op = Lit 0w` >>
     gvs[compile_abi_dec_addr_def, comp_return_def, inst_extends_refl] >>
     metis_tac[inst_extends_emit_op]) >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  `run_inst_seq (emitted_insts st addr_st) s = OK s2 /\
   inst_extends st addr_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `head_st`] >> simp[]) >>
  `run_inst_seq (emitted_insts st count_st) s = OK s3 /\
   inst_extends st count_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`, `addr_st`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s3`, `count_st`] >> simp[]) >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

Finalise abi_decode_bytes_position_prefix_sequence
