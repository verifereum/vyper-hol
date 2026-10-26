Theory abiEncoderArrayAddress
Ancestors
  abiEncoderArrayCode abiDecoderDynamicLoopSetup abiDecoderReentryAddress abiDecoderReentry
  abiDecoderGuards abiDecoderContract abiDecoderArrayHeader emitHelperProps exprLoweringProps
  compileEnv emitHelper venomExecSemantics venomState venomInst words list rich_list arithmetic
  abiDecoderLoop fragExec instIdxIndep

(* ===== Encoder Array Address ===== *)

(* Execute the shared seven-instruction encoder body address prefix. *)

Theorem abi_encode_array_addresses_shape:
  abi_encode_array_addresses ip src dst asz msz st = (coords,st') ==>
  st'.cs_next_var = st.cs_next_var+7 /\ st'.cs_next_id = st.cs_next_id+7 /\
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  abi_decoder_operand_live st'.cs_next_var (FST (FST coords)) /\
  abi_decoder_operand_live st'.cs_next_var (SND (FST coords)) /\
  abi_decoder_operand_live st'.cs_next_var (FST (SND coords)) /\
  abi_decoder_operand_live st'.cs_next_var (SND (SND coords)) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')
Proof
  simp[abi_encode_array_addresses_def, abi_decode_array_head_setup_def, abi_decode_indexed_coordinates_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND, abi_decoder_operand_live_def,
    abi_decoder_older_vars_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def] >>
  rpt strip_tac >> decide_tac
QED

Theorem abi_encode_array_addresses_sequence:
  abi_encode_array_addresses ip src dst asz msz st = (coords,st') /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    eval_operand (FST (FST coords)) actual = SOME (n2w j) /\
    eval_operand (SND (FST coords)) actual = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) actual = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) actual = SOME (n2w (d+32+j*asz)) /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_address_frame st.cs_next_var initial actual /\
    inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encode_array_addresses_trace >> strip_tac >>
  drule abi_decode_array_head_setup_counters >> strip_tac >>
  drule abi_decode_indexed_coordinates_counters >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= middle.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `st'` |-> `middle`, `ops` |-> `src_ops`,
    `abi_sz` |-> `msz:num`, `i` |-> `j:num`] abi_decode_array_head_setup_reentry) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st middle) initial = OK ready` >>
  `eval_operand dst ready = SOME (n2w d)` by
    (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`st` |-> `middle`, `base_op` |-> `dst`, `idx` |-> `FST (src_ops:operand # operand # operand)`,
    `stride` |-> `asz:num`, `s` |-> `ready:venom_state`, `i` |-> `j:num`,
    `sb` |-> `d:num`, `ops` |-> `dst_ops`] abi_decode_indexed_coordinates_reentry) >>
  impl_tac >- full_simp_tac bool_ss [] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts middle st') ready = OK actual` >>
  `eval_operand (FST src_ops) actual = SOME (n2w j) /\
    eval_operand (SND (SND src_ops)) actual = SOME (n2w (sb+32+j*msz))` by
    (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts st st') initial = OK actual /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`ready`, `middle`] >> simp[]) >>
  `abi_decoder_address_frame st.cs_next_var initial actual` by
    (irule abi_decoder_address_frame_trans >> qexistsl_tac [`middle.cs_next_var`, `ready`] >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) []
QED

(* ===== Reach ===== *)

(* The shared encoder body address prefix reaches its real instruction endpoint. *)

Theorem abi_encode_array_addresses_from_state:
  abi_encode_array_addresses ip src dst asz msz st = (coords,st') /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. eval_operand (FST (FST coords)) t = SOME (n2w j) /\
      eval_operand (SND (FST coords)) t = SOME (n2w (sb+32+j*msz)) /\
      eval_operand (FST (SND coords)) t = SOME (n2w (d+32)) /\
      eval_operand (SND (SND coords)) t = SOME (n2w (d+32+j*asz)) /\
      fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t) (K F)
Proof
  strip_tac >> drule abi_encode_array_addresses_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by fs[inst_extends_def, IS_PREFIX_APPEND] >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_encode_array_addresses_sequence >> strip_tac >> qexists_tac `actual` >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem abi_encode_array_addresses_reach:
  abi_encode_array_addresses ip src dst asz msz st = (coords,st') /\ fn_has_code st st' func /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. eval_operand (FST (FST coords)) t = SOME (n2w j) /\
    eval_operand (SND (FST coords)) t = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) t = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) t = SOME (n2w (d+32+j*asz)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_addresses_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `~actual.vs_halted` by fs[abi_decoder_address_frame_def] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
