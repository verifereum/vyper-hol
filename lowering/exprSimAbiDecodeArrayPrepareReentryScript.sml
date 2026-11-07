(* Guard-first preparation tolerates stale temporaries on array reentry. *)
Theory exprSimAbiDecodeArrayPrepareReentry
Ancestors
  exprSimAbiDecodeAbortReentry exprSimAbiDecodeArraySetup
  exprSimAbiDecodeArrayPrefix exprSimAbiDecodeArrayFetched
  abiDecoderBytestringOutcome abiDecoderWordOutcome abiDecoderFiniteControl
  exprSimAbiDecodeCompositePrefix exprSimAbiDecodeMemberExecute instIdxIndep
  abiDecoderReentry abiDecoderVarSequence
  abiDecoderVarExtend abiDecoderReentryPointer abiDecoderArrayInitExec abiDecoderArrayLoopInit
  abiDecoderDynarrayPrefix abiDecoderDynarrayBound
  abiDecoderBytesBound abiDecoderGuards abiDecoderArrayHeader abiDecoderSequenceReach
  abiDecoderSiteEffect actualDecoderSites valueEncodingProps
  abiDecoderContract abiDecoderFrame valueEncoding abiEncoder compileEnv emitHelper emitHelperProps
  exprLoweringProps venomState venomInst words list rich_list arithmetic
  vyperABI vyperValue contractABI

Theorem abi_decode_array_prefix_guard_opcodes[local]:
  abi_decode_dynarray_position_prefix src MLOAD base_op hi maxn abi_sz st = (addr,st') ==>
  EVERY (\i. MEM i.inst_opcode [ADD; MUL; LT; GT; AND; ISZERO; MLOAD; ASSERT])
    (emitted_insts st st')
Proof
  Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  simp[abi_decode_dynarray_position_prefix_def, abi_decode_bytes_head_def,
    compile_abi_dec_addr_def, abi_decode_count_guard_def,
    abi_decode_dynarray_payload_guard_def, compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_decode_dynarray_memory_prefix_reject_reentry:
  abi_decode_dynarray_position_prefix src MLOAD base_op hi maxn
    (abi_member_head_size at) st = (addr,st') /\ hi <> Lit 0w /\
  eval_operand src s = SOME(n2w p) /\
  eval_operand base_op s = SOME(n2w b) /\ eval_operand hi s = SOME(n2w h) /\
  n = w2n (mem_word_at (b+p) s.vs_memory) /\
  bs = mem_bytes_at (b+p) (h-p) s.vs_memory /\
  p < dimword(:256) /\ h < dimword(:256) /\ b+h < dimword(:256) /\
  maxn < dimword(:256) /\
  (n <= maxn ==> n*abi_member_head_size at < dimword(:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var hi /\
  ~(n <= maxn /\ p+32+n*abi_member_head_size at <= h) ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t /\
    ~(vyper_decode_valid_enc (Array NONE at) bs /\
      ?v. abi_to_vyper env (ArrayT ty (Dynamic maxn))
        (dec (Array NONE at) bs) = SOME v)
Proof
  strip_tac >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s)` by
    irule abi_decoder_prune_fresh >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w p) /\
   eval_operand base_op (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w b) /\
   eval_operand hi (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w h)` by
    asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  `n = w2n (mem_word_at (b+p) (abi_decoder_prune_vars st.cs_next_var s).vs_memory) /\
   bs = mem_bytes_at (b+p) (h-p) (abi_decoder_prune_vars st.cs_next_var s).vs_memory` by
    simp[abi_decoder_prune_vars_def] >>
  drule_all abi_decode_dynarray_memory_prefix_source_outcome >>
  disch_then (qspecl_then [`ty`, `env`] strip_assume_tac) >- gvs[] >>
  `abi_decoder_vars_extend s.vs_vars (abi_decoder_prune_vars st.cs_next_var s) s` by
    irule abi_decoder_prune_extension >>
  drule abi_decode_array_prefix_guard_opcodes >> strip_tac >>
  drule_all abi_decode_guard_sequence_vars_extend_abort >>
  strip_tac >> goal_assum (drule_at Any) >> asm_rewrite_tac[]
QED

Theorem abi_decode_array_prepare_reentry_opcodes[local]:
  abi_decode_dynarray_position_prefix src MLOAD base_op hi maxn abi_sz st = (addr,guard_st) /\
  abi_decode_array_header dst addr MLOAD guard_st = (cnt,header_st) ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st header_st) /\
  EVERY (\i. abi_bytes_opcode i.inst_opcode \/ i.inst_opcode = MUL)
    (emitted_insts st header_st)
Proof
  Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  simp[abi_decode_dynarray_position_prefix_def, abi_decode_bytes_head_def,
    compile_abi_dec_addr_def, abi_decode_count_guard_def,
    abi_decode_dynarray_payload_guard_def, compile_abi_decode_range_check_def,
    abi_decode_array_header_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def,
    abi_bytes_opcode_def, abi_word_opcode_def]
QED

Theorem abi_decode_dynarray_prepare_sequence_reentry:
  abi_decode_dynarray_position_prefix src MLOAD base_op hi maxn abi_sz st = (addr,guard_st) /\
  abi_decode_array_header dst addr MLOAD guard_st = (cnt,header_st) /\
  hi <> Lit 0w /\
  eval_operand src s = SOME(n2w p) /\ eval_operand dst s = SOME(n2w d) /\
  eval_operand base_op s = SOME(n2w b) /\ eval_operand hi s = SOME(n2w h) /\
  d < dimword(:256) /\ h < dimword(:256) /\ b+h < dimword(:256) /\
  n = w2n (mem_word_at (b+p) s.vs_memory) /\
  n <= maxn /\ maxn < dimword(:256) /\ p+32+n*abi_sz <= h /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var hi /\
  header_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st header_st) s = OK t /\
    eval_operand cnt t = SOME(n2w n) /\ mem_word_at d t.vs_memory = n2w n /\
    fresh_vars_wrt limit_st t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    abi_decode_frame d 32 s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st header_st
Proof
  strip_tac >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s)` by
    irule abi_decoder_prune_fresh >>
  `b+p < dimword(:256)` by decide_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w p) /\
   eval_operand dst (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w d) /\
   eval_operand base_op (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w b) /\
   eval_operand hi (abi_decoder_prune_vars st.cs_next_var s) = SOME(n2w h)` by
    asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  `abi_decode_load MLOAD (n2w (b+p):bytes32)
    (abi_decoder_prune_vars st.cs_next_var s) = n2w n` by
    simp[abi_decode_load_def, abi_decode_source_def, mload_def,
      mem_word_at_def, mem_bytes_at_def, abi_decoder_prune_vars_def] >>
  mp_tac (Q.INST [`s` |-> `abi_decoder_prune_vars st.cs_next_var s`,
    `sb` |-> `p`, `B` |-> `b`, `opc` |-> `MLOAD`] abi_decode_array_prepare_sequence) >>
  (impl_tac >- (asm_rewrite_tac[] >> qexists `h` >>
    gvs[])) >>
  strip_tac >>
  drule_all abi_decode_array_prepare_reentry_opcodes >> strip_tac >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  drule_all abi_decoder_vars_extend_eval >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  qexists `actual` >>
  gvs[abi_decode_frame_def, abi_decoder_prune_vars_def] >> metis_tac[]
QED

Theorem abi_decode_dynarray_memory_prepare_outcome_reentry:
  abi_decode_dynarray_position_prefix src MLOAD base_op hi maxn
    (abi_member_head_size at) st = (addr,guard_st) /\
  abi_decode_array_header dst addr MLOAD guard_st = (cnt,header_st) /\
  hi <> Lit 0w /\
  eval_operand src s = SOME(n2w p) /\ eval_operand dst s = SOME(n2w d) /\
  eval_operand base_op s = SOME(n2w b) /\ eval_operand hi s = SOME(n2w h) /\
  d < dimword(:256) /\ p < dimword(:256) /\ h < dimword(:256) /\ b+h < dimword(:256) /\
  n = w2n (mem_word_at (b+p) s.vs_memory) /\
  bs = mem_bytes_at (b+p) (h-p) s.vs_memory /\ maxn < dimword(:256) /\
  (n <= maxn ==> n*abi_member_head_size at < dimword(:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var hi /\
  header_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  (n <= maxn /\ p+32+n*abi_member_head_size at <= h /\
    ?t. run_inst_seq (emitted_insts st header_st) s = OK t /\
      eval_operand cnt t = SOME(n2w n) /\ mem_word_at d t.vs_memory = n2w n /\
      fresh_vars_wrt limit_st t /\
      (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
        eval_operand op t = SOME w) /\
      abi_decode_frame d 32 s t /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_halted = s.vs_halted /\ inst_extends st header_st) \/
  (?t. run_inst_seq (emitted_insts st header_st) s = Abort Revert_abort t /\
    ~(vyper_decode_valid_enc (Array NONE at) bs /\
      ?v. abi_to_vyper env (ArrayT ty (Dynamic maxn))
        (dec (Array NONE at) bs) = SOME v))
Proof
  strip_tac >> Cases_on `n <= maxn /\ p+32+n*abi_member_head_size at <= h`
  >- (qpat_x_assum `n <= maxn /\ _` strip_assume_tac >>
      drule_all abi_decode_dynarray_prepare_sequence_reentry >> strip_tac >>
      disj1_tac >> asm_rewrite_tac[] >> goal_assum (drule_at Any) >>
      asm_rewrite_tac[]) >>
  disj2_tac >>
  drule_all abi_decode_dynarray_memory_prefix_reject_reentry >>
  disch_then (qspecl_then [`ty`, `env`] strip_assume_tac) >>
  drule abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule abi_decode_array_header_shape >> strip_tac >>
  fs[abi_decode_source_opcode_def] >>
  metis_tac[run_inst_seq_abort_extends]
QED

Theorem abi_decode_dynarray_prepare_site_effect:
  abi_decode_dynarray_position_prefix src MLOAD base_op hi maxn abi_sz st = (addr,guard_st) /\
  abi_decode_array_header dst addr MLOAD guard_st = (cnt,header_st) /\
  run_inst_seq (emitted_insts st header_st) s = OK t /\
  abi_decode_frame d 32 s t /\ decode_site_resources ctx func s /\
  (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) ==>
  decode_site_effect ctx func st.cs_next_var {a | d <= a /\ a < d+32} s t
Proof
  strip_tac >> drule_all abi_decode_array_prepare_reentry_opcodes >> strip_tac >>
  drule_all abi_decode_array_bulk_sequence_static >> strip_tac >>
  `decode_site_resources ctx func t` by
    (irule decode_site_resources_fields >> qexists `s` >>
      fs[venom_state_component_equality]) >>
  `decode_memory_frame {a | d <= a /\ a < d+32} s t` by
    (irule abi_word_frame_memory >> qexists `d` >> simp[]) >>
  fs[decode_site_effect_def, decode_static_frame_def, venom_state_component_equality]
QED

Theorem abi_decode_dynarray_memory_prepare_fetched_reentry:
  abi_decode_dynarray_position_prefix src MLOAD base_op hi maxn
    (abi_member_head_size at) st = (addr,guard_st) /\
  abi_decode_array_header dst addr MLOAD guard_st = (cnt,header_st) /\
  hi <> Lit 0w /\
  eval_operand src s = SOME(n2w p) /\ eval_operand dst s = SOME(n2w d) /\
  eval_operand base_op s = SOME(n2w b) /\ eval_operand hi s = SOME(n2w h) /\
  d < dimword(:256) /\ p < dimword(:256) /\ h < dimword(:256) /\ b+h < dimword(:256) /\
  n = w2n (mem_word_at (b+p) s.vs_memory) /\
  bs = mem_bytes_at (b+p) (h-p) s.vs_memory /\ maxn < dimword(:256) /\
  (n <= maxn ==> n*abi_member_head_size at < dimword(:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var hi /\
  header_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  decode_site_resources ctx func s /\ fn_has_code st header_st fn /\
  abi_decode_entry st s ==>
  (n <= maxn /\ p+32+n*abi_member_head_size at <= h /\
    ?t. Dreach ctx fn s t /\ abi_decode_entry header_st t /\
      eval_operand cnt t = SOME(n2w n) /\ mem_word_at d t.vs_memory = n2w n /\
      fresh_vars_wrt limit_st t /\
      decode_site_effect ctx func st.cs_next_var {a | d <= a /\ a < d+32} s t /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) \/
  (?t. Dabort ctx fn s Revert_abort t /\
    ~(vyper_decode_valid_enc (Array NONE at) bs /\
      ?v. abi_to_vyper env (ArrayT ty (Dynamic maxn))
        (dec (Array NONE at) bs) = SOME v))
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  `inst_extends st header_st` by metis_tac[inst_extends_trans] >>
  `header_st.cs_blocks = st.cs_blocks /\
   header_st.cs_current_bb = st.cs_current_bb` by metis_tac[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st header_st)` by
    (`emitted_insts st header_st = emitted_insts st guard_st ++
       emitted_insts guard_st header_st` by
       (irule emitted_insts_append >> fs[inst_extends_def]) >>
     fs[EVERY_APPEND, EVERY_MEM] >> metis_tac[]) >>
  drule_all abi_decode_dynarray_memory_prepare_outcome_reentry >>
  disch_then (qspecl_then [`ty`, `env`] strip_assume_tac)
  >- (disj1_tac >> asm_rewrite_tac[] >>
      drule_all abi_decode_dynarray_prepare_site_effect >> strip_tac >>
      `~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
       s.vs_inst_idx = LENGTH st.cs_current_insts` by fs[abi_decode_entry_def] >>
      `inst_extends st header_st` by metis_tac[inst_extends_trans] >>
      drule_all abi_decoder_run_sequence_prefix >> strip_tac >>
      qexists `t'` >>
      conj_tac >- metis_tac[Dreach_straight_prefix] >>
      gvs[abi_decode_entry_def, eval_op_inst_idx, fresh_vars_wrt_def,
        decode_site_effect_inst_idx]) >>
  disj2_tac >>
  `~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by fs[abi_decode_entry_def] >>
  `inst_extends st header_st` by metis_tac[inst_extends_trans] >>
  drule_all abi_decoder_run_sequence_abort >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  simp_tac bool_ss [Dabort_def] >>
  qexists `t with vs_inst_idx := n'` >> conj_tac
  >- (qexists `0` >> asm_rewrite_tac[]) >> metis_tac[]
QED
