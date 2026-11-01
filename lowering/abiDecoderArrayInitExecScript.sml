Theory abiDecoderArrayInitExec
Ancestors
  abiDecoderArrayLoopInit abiDecoderDynarrayPrefix abiDecoderArrayHeader abiDecoderReservation
  abiDecoderReentryPointer abiDecoderGuards abiDecoderContract exprLoweringProps emitHelperProps
  compileEnv venomState words list arithmetic abiDecoderIndexInit abiDecoderAllocation
  abiDecoderReentry abiDecoderFrameCompose abiDecoderFrame abiDecoderPrimitiveLoopFrames
  valueEncoding pred_set
Libs
  Omega

(* Count validation and the output length store before scratch allocation. *)
Theorem abi_decoder_guard_sequence_fields:
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    ~is_alloca_op i.inst_opcode) insts /\ run_inst_seq insts s = OK t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_halted = s.vs_halted
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode) insts`
    by fs[EVERY_CONJ] >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  drule_all abi_decoder_sequence_halted >> simp[]
QED

Theorem abi_decode_array_prepare_sequence:
  abi_decode_dynarray_prefix src opc hi maxn abi_sz st = ((),guard_st) /\
  abi_decode_array_header dst src opc guard_st = (cnt,header_st) /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load opc (n2w sb:bytes32) s = n2w n /\ n <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    sb + 32 + n * abi_sz <= h /\ h < dimword (:256)) /\ fresh_vars_wrt st s ==>
  ?prepared. run_inst_seq (emitted_insts st header_st) s = OK prepared /\
    eval_operand cnt prepared = SOME (n2w n) /\
    mem_word_at d prepared.vs_memory = n2w n /\ fresh_vars_wrt header_st prepared /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op prepared = SOME w) /\
    abi_decode_frame d 32 s prepared /\
    prepared.vs_allocas = s.vs_allocas /\ prepared.vs_alloca_next = s.vs_alloca_next /\
    prepared.vs_halted = s.vs_halted /\ inst_extends st header_st
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule_all abi_decode_dynarray_prefix_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st guard_st) s = OK guarded` >>
  drule_all abi_decoder_guard_sequence_fields >> strip_tac >>
  `eval_operand src guarded = SOME (n2w sb) /\ eval_operand dst guarded = SOME (n2w d)`
    by metis_tac[] >>
  `abi_decode_load opc (n2w sb:bytes32) guarded = n2w n` by
    gvs[abi_decode_load_def, abi_decode_source_def, mload_def] >>
  drule_all abi_decode_array_header_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts guard_st header_st) guarded = OK prepared` >>
  mp_tac (Q.INST [`insts` |-> `emitted_insts guard_st header_st`,
    `s` |-> `guarded:venom_state`, `t` |-> `prepared:venom_state`]
    abi_decoder_guard_sequence_fields) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `run_inst_seq (emitted_insts st header_st) s = OK prepared /\
    inst_extends st header_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`guarded`, `guard_st`] >> simp[]) >>
  `!op w. eval_operand op s = SOME w ==> eval_operand op prepared = SOME w` by metis_tac[] >>
  `abi_decode_frame d 32 s prepared` by
    (gvs[abi_decode_frame_def] >> first_assum ACCEPT_TAC) >>
  qexists_tac `prepared` >> gvs[abi_decode_load_def, abi_decode_source_def, mload_def]
QED

(* Execute all straight-line initialization preceding a loop-based array decode. *)
Theorem abi_decoder_budget_transport:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  (abi_decoder_budget first last b cap t <=> abi_decoder_budget first last b cap s)
Proof
  strip_tac >> simp[abi_decoder_budget_def, abi_decoder_missing_def]
QED

Theorem abi_decoder_arena_disjoint:
  !d outsz b cap p sz:num.
  (d + outsz <= b \/ b + cap <= d) /\ b <= p /\ p + sz <= b + cap ==>
  p + sz <= d \/ d + outsz <= p
Proof
  Omega.OMEGA_TAC
QED

Theorem abi_decoder_array_init_frame:
  abi_decode_frame d 32 s prepared /\ abi_decode_frame p 32 prepared t /\
  b <= p /\ p + 32 <= b + cap ==>
  abi_decode_footprint_frame [(d,32);(b,cap)] s t
Proof
  strip_tac >>
  `abi_decode_frame b cap prepared t` by
    (irule abi_decode_frame_widen >> qexistsl_tac [`p`, `32`] >> simp[]) >>
  irule abi_decode_footprint_frame_trans >> qexists_tac `prepared` >> conj_tac
  >- (irule abi_decoder_frame_in_footprint >> qexistsl_tac [`d`, `32`] >> simp[]) >>
  irule abi_decoder_frame_in_footprint >> qexistsl_tac [`b`, `cap`] >> simp[]
QED

Theorem abi_decoder_array_init_exact_frame:
  abi_decode_frame d 32 s prepared /\ abi_decode_frame p 32 prepared t ==>
  abi_decode_footprint_frame [(d,32);(p,32)] s t
Proof
  strip_tac >> irule abi_decode_footprint_frame_trans >> qexists_tac `prepared` >> conj_tac
  >- (irule abi_decoder_frame_in_footprint >> qexistsl_tac [`d`, `32`] >> simp[]) >>
  irule abi_decoder_frame_in_footprint >> qexistsl_tac [`p`, `32`] >> simp[]
QED

Theorem abi_decode_array_loop_init_sequence:
  abi_decode_array_loop_init dst src opc hi maxn abi_sz st = (setup,loop_st) /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load opc (n2w sb:bytes32) s = n2w n /\ n <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    sb + 32 + n * abi_sz <= h /\ h < dimword (:256)) /\
  abi_decoder_budget first last b cap s /\ first <= st.cs_next_id /\ loop_st.cs_next_id <= last /\
  (d + 32 <= b \/ b + cap <= d) /\ fresh_vars_wrt st s ==>
  ?t p. run_inst_seq (emitted_insts st loop_st) s = OK t /\
    eval_operand (FST setup) t = SOME (n2w p) /\ eval_operand (SND setup) t = SOME (n2w n) /\
    mload p t = 0w /\ mem_word_at d t.vs_memory = n2w n /\ b <= p /\ p + 32 <= b + cap /\
    abi_decoder_budget first last b cap t /\ fresh_vars_wrt loop_st t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    abi_decode_footprint_frame [(d,32);(b,cap)] s t /\
    abi_decode_footprint_frame [(d,32);(p,32)] s t /\
    FLOOKUP t.vs_allocas (loop_st.cs_next_id - 2) = SOME (p,32) /\
    (!id. id <> loop_st.cs_next_id - 2 ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    t.vs_halted = s.vs_halted /\ inst_extends st loop_st
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decode_array_loop_init_trace >> strip_tac >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule_all abi_decode_array_prepare_sequence >> strip_tac >>
  `abi_decoder_budget first last b cap prepared` by
    (drule_all abi_decoder_budget_transport >> simp[]) >>
  `header_st.cs_next_id IN abi_decoder_ids first last` by
    (simp_tac std_ss [abi_decoder_ids_def, GSPECIFICATION] >> decide_tac) >>
  `fresh_vars_wrt loop_st prepared` by
    (mp_tac (Q.SPECL [`header_st`, `loop_st`, `prepared`] fresh_vars_wrt_mono) >>
     simp[GREATER_EQ]) >>
  mp_tac (Q.INST [`st` |-> `header_st`, `st'` |-> `loop_st`,
    `s` |-> `prepared:venom_state`, `limit_st` |-> `loop_st`]
    abi_decode_index_init_sequence) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts header_st loop_st) prepared = OK actual` >>
  `!op w. eval_operand op prepared = SOME w ==> abi_decoder_operand_live header_st.cs_next_var op`
    by metis_tac[abi_decoder_operand_live_fresh] >>
  `eval_operand cnt actual = SOME (n2w n)` by metis_tac[] >>
  `!op w. eval_operand op s = SOME w ==> eval_operand op actual = SOME w` by metis_tac[] >>
  `p + 32 <= d \/ d + 32 <= p` by
    (irule abi_decoder_arena_disjoint >> qexistsl_tac [`b`, `cap`] >> simp[]) >>
  `mem_word_at d actual.vs_memory = mem_word_at d prepared.vs_memory` by
    (irule abi_decode_frame_mem_word >> qexistsl_tac [`p`, `32`] >> simp[]) >>
  `abi_decode_footprint_frame [(d,32);(b,cap)] s actual` by
    (drule_all abi_decoder_array_init_frame >> simp[]) >>
  `abi_decode_footprint_frame [(d,32);(p,32)] s actual` by
    (drule_all abi_decoder_array_init_exact_frame >> simp[]) >>
  `run_inst_seq (emitted_insts st loop_st) s = OK actual /\ inst_extends st loop_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`prepared`, `header_st`] >> simp[]) >>
  qexistsl_tac [`actual`, `p`] >> gvs[]
QED
