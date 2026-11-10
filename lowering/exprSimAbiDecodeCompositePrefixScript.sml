(* Arbitrary-position execution of the composite decoder head guard. *)
Theory exprSimAbiDecodeCompositePrefix
Ancestors
  loweringStateRelDefs
  abiDecoderComplexGuard abiDecoderSequenceReach abiDecoderReservation
  abiDecoderDynamicLoopSetup abiDecoderMemberBound abiDecoderContract
  abiEncoder emitHelper venomInst
  abiDecoderBytesBound abiDecoderGuard abiDecoderRange instIdxIndep
  abiDecoderComplexHead compileEnv venomState emitHelperProps exprLoweringProps
  venomExecSemantics venomExecProofs venomInstProofs words arithmetic rich_list list

Theorem abi_decode_complex_head_guard_revert:
  abi_decode_complex_head_guard src hi k st = ((),st') /\
  hi <> Lit 0w /\ eval_operand src s = SOME (n2w p) /\
  eval_operand hi s = SOME (n2w H) /\
  p < dimword(:256) /\ k < dimword(:256) /\ H < dimword(:256) /\
  H < p+k /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  Cases_on `hi = Lit 0w` >- simp[] >>
  simp[abi_decode_complex_head_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [src; Lit (n2w k)] st = (e,c1)` >>
  `eval_operand (Lit (n2w k)) s = SOME (n2w k)` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME (n2w p) /\
   eval_operand hi s1 = SOME (n2w H)` by metis_tac[] >>
  `w2n (n2w (p+k) : bytes32) < w2n (n2w p : bytes32) \/
   w2n (n2w H : bytes32) < w2n (n2w (p+k) : bytes32)` by
    (Cases_on `p+k < dimword(:256)` >> simp[w2n_n2w] >>
     `p+k < 2 * dimword(:256)` by decide_tac >>
     ` (k+p) MOD dimword(:256) = k+p-dimword(:256)` by
       (irule MOD_UNIQUE >> qexists_tac `1` >> decide_tac) >>
     simp[Once ADD_COMM] >> decide_tac) >>
  rule_assum_tac (REWRITE_RULE [word_add_n2w]) >>
  `?t. run_inst_seq (emitted_insts c1 st') s1 = Abort Revert_abort t` by
    (irule abi_decode_range_check_revert >>
     simp[] >> qexistsl_tac [`e`, `n2w H`, `hi`, `n2w p`, `n2w (p+k)`, `src`] >> simp[]) >>
  drule compile_abi_decode_range_check_shape >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> simp[]
QED

Theorem abi_decode_complex_head_guard_prefix_shape:
  abi_decode_complex_head_guard src hi k st = ((),st') ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  strip_tac >> drule abi_decoder_complex_guard_code >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  `inst_extends st st'` by
    (gvs[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  simp[] >> fs[EVERY_MEM]
QED

Theorem composite_prefix_halted[local]:
  !is s t. EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is /\
  run_inst_seq is s = OK t ==> t.vs_halted = s.vs_halted
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  metis_tac[step_preserves_halted, step_inst_non_invoke]
QED

Theorem abi_decode_complex_head_guard_fetched_outcome:
  abi_decode_complex_head_guard src hi k st = ((),st') /\
  hi <> Lit 0w /\ eval_operand src s = SOME (n2w p) /\
  eval_operand hi s = SOME (n2w H) /\
  p < dimword(:256) /\ k < dimword(:256) /\ H < dimword(:256) /\
  fresh_vars_wrt st s /\ fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (p+k <= H /\ ?t. decoder_straight_prefix func s t /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    abi_decoder_address_frame st.cs_next_var s t) \/
  (H < p+k /\ ?encoded ix.
    run_inst_seq (emitted_insts st st') s = Abort Revert_abort encoded /\
    run_from 0 ctx func s = Abort Revert_abort (encoded with vs_inst_idx := ix))
Proof
  strip_tac >> drule abi_decode_complex_head_guard_prefix_shape >> strip_tac >>
  Cases_on `p+k <= H`
  >- (disj1_tac >> simp[] >>
      `?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
        (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
        t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
        t.vs_data_section = s.vs_data_section /\ inst_extends st st'` by
        (irule abi_decode_complex_head_guard_sequence >>
         simp[] >> qexistsl_tac [`k`, `hi`, `p`, `src`] >> simp[] >>
         qexists_tac `H` >> simp[]) >>
      drule abi_decode_complex_head_guard_shape >> strip_tac >>
      drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
      drule_all composite_prefix_halted >> strip_tac >>
      drule_all abi_decoder_run_sequence_prefix >> strip_tac >>
      qexists_tac `t'` >>
      gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]) >>
  disj2_tac >> `H < p+k` by decide_tac >> simp[] >>
  drule_all abi_decode_complex_head_guard_revert >> strip_tac >>
  drule_all abi_decoder_run_sequence_abort >> strip_tac >>
  metis_tac[]
QED

Theorem abi_decode_dynamic_member_pointer_revert:
  compile_getelemptr_abi src T off opc base_op hi st = (member_op,st') /\
  hi <> Lit 0w /\ abi_decode_source_opcode opc /\
  eval_operand src s = SOME (n2w p) /\ eval_operand base_op s = SOME (n2w B) /\
  abi_decode_load opc (n2w (B+(p+off)):bytes32) s = n2w delta /\
  p < dimword(:256) /\ delta < dimword(:256) /\ dimword(:256) <= p+delta /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  strip_tac >>
  qpat_x_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bounded_member_phases, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src T off opc base_op (Lit 0w) st = (member_op,c1)` >>
  rename1 `abi_decode_ge_guard member_op src c1 = (u,st')` >>
  Cases_on `u` >> gvs[] >>
  mp_tac (Q.INST [`st'` |-> `c1`, `sb` |-> `p`, `src_base` |-> `B`,
    `payload_off` |-> `delta`] abi_decode_dynamic_member_pointer_sentinel) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME (n2w p)` by metis_tac[] >>
  `w2n (n2w (p+delta):bytes32) < w2n (n2w p:bytes32)` by
    (`p+delta < 2*dimword(:256)` by decide_tac >>
     `(delta+p) MOD dimword(:256) = delta+p-dimword(:256)` by
       (irule MOD_UNIQUE >> qexists_tac `1` >> decide_tac) >>
     simp[w2n_n2w] >> decide_tac) >>
  drule_all abi_decode_ge_guard_revert >> strip_tac >>
  drule abi_decode_ge_guard_shape >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> simp[]
QED

Theorem abi_decode_member_pointer_prefix_shape:
  compile_getelemptr_abi src dyn off MLOAD base_op hi st = (member_op,st') ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    ~is_alloca_op i.inst_opcode) (emitted_insts st st')
Proof
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  simp[compile_getelemptr_abi_def, compile_abi_dec_addr_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def,
    inst_extends_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, is_terminator_def, is_alloca_op_def, mk_inst_def]
QED

Theorem composite_pointer_sequence_fetched[local]:
  compile_getelemptr_abi src dyn off MLOAD base_op hi st = (member_op,st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  eval_operand member_op t = SOME w /\ fresh_vars_wrt st' t /\
  (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_data_section = s.vs_data_section /\ fn_has_code st st' func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. decoder_straight_prefix func s u /\
    u.vs_current_bb = st'.cs_current_bb /\ u.vs_inst_idx = LENGTH st'.cs_current_insts /\
    eval_operand member_op u = SOME w /\ fresh_vars_wrt st' u /\
    (!op v. eval_operand op s = SOME v ==> eval_operand op u = SOME v) /\
    abi_decoder_address_frame st.cs_next_var s u
Proof
  strip_tac >> drule abi_decode_member_pointer_prefix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st') /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_MEM] >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  drule_all composite_prefix_halted >> strip_tac >>
  drule_all abi_decoder_run_sequence_prefix >> strip_tac >>
  qexists_tac `t'` >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem abi_decode_complex_static_child_pointer_fetched:
  compile_getelemptr_abi src F off MLOAD base_op hi st = (member_op,st') /\
  eval_operand src s = SOME (n2w p) /\ p+off < dimword(:256) /\
  fresh_vars_wrt st s /\ fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. decoder_straight_prefix func s t /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    eval_operand member_op t = SOME (n2w (p+off)) /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    abi_decoder_address_frame st.cs_next_var s t
Proof
  strip_tac >> drule_all abi_decode_static_member_pointer >> strip_tac >>
  drule_all composite_pointer_sequence_fetched >> simp[]
QED

Theorem abi_decode_complex_dynamic_child_pointer_fetched:
  compile_getelemptr_abi src T off MLOAD base_op hi st = (member_op,st') /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand src s = SOME(n2w p) /\ eval_operand base_op s = SOME(n2w B) /\
  eval_operand hi s = SOME(n2w H) /\ p+off+32 <= H /\ B+H < dimword(:256) /\
  delta = w2n (abi_decode_load MLOAD (n2w (B+p+off):bytes32) s) /\
  fresh_vars_wrt st s /\ fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (p+delta < dimword(:256) /\ ?t. decoder_straight_prefix func s t /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    eval_operand member_op t = SOME(n2w (p+delta)) /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    abi_decoder_address_frame st.cs_next_var s t) \/
  (dimword(:256) <= p+delta /\ ?encoded ix.
    run_inst_seq (emitted_insts st st') s = Abort Revert_abort encoded /\
    run_from 0 ctx func s = Abort Revert_abort (encoded with vs_inst_idx := ix))
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `abi_decode_load MLOAD (n2w (B+(p+off)):bytes32) s = n2w delta` by
    asm_simp_tac bool_ss [ADD_ASSOC, n2w_w2n] >>
  `p < dimword(:256) /\ delta < dimword(:256)` by
    (conj_tac >- decide_tac >> asm_simp_tac bool_ss [w2n_lt]) >>
  Cases_on `p+delta < dimword(:256)`
  >- (disj1_tac >> simp[] >>
      mp_tac (Q.INST [`sb` |-> `p`, `src_base` |-> `B`, `payload_off` |-> `delta`,
        `opc` |-> `MLOAD`]
        abi_decode_dynamic_member_pointer) >>
      (impl_tac >- simp[]) >> strip_tac >>
      drule_all composite_pointer_sequence_fetched >> simp[]) >>
  disj2_tac >> `dimword(:256) <= p+delta` by decide_tac >> simp[] >>
  drule_all abi_decode_dynamic_member_pointer_revert >> strip_tac >>
  drule abi_decode_member_pointer_prefix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_MEM] >>
  drule_all abi_decoder_run_sequence_abort >> strip_tac >> metis_tac[]
QED

Theorem abi_decode_complex_child_pointer_fetched_outcome:
  compile_getelemptr_abi src dyn off MLOAD base_op hi st = (member_op,st') /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand src s = SOME(n2w p) /\ eval_operand base_op s = SOME(n2w B) /\
  eval_operand hi s = SOME(n2w H) /\ p+off+32 <= H /\ B+H < dimword(:256) /\
  fresh_vars_wrt st s /\ fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  let delta = w2n(abi_decode_load MLOAD (n2w(B+p+off):bytes32) s);
      q = if dyn then p+delta else p+off
  in
  ((~dyn \/ p+delta < dimword(:256)) /\ ?t. decoder_straight_prefix func s t /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    eval_operand member_op t = SOME(n2w q) /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    abi_decoder_address_frame st.cs_next_var s t) \/
  (dyn /\ dimword(:256) <= p+delta /\ ?encoded ix.
    run_inst_seq (emitted_insts st st') s = Abort Revert_abort encoded /\
    run_from 0 ctx func s = Abort Revert_abort (encoded with vs_inst_idx := ix))
Proof
  strip_tac >> Cases_on `dyn`
  >- (asm_simp_tac bool_ss [LET_THM] >>
      irule abi_decode_complex_dynamic_child_pointer_fetched >>
      simp[] >> qexistsl_tac [`B`, `H`, `base_op`, `hi`, `off`, `src`] >> simp[]) >>
  asm_simp_tac bool_ss [LET_THM] >>
  irule abi_decode_complex_static_child_pointer_fetched >>
  `p+off < dimword(:256)` by decide_tac >> simp[] >>
  qexistsl_tac [`base_op`, `hi`, `src`] >> simp[]
QED
