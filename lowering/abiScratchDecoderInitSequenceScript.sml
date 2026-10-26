(* Physical output ownership keeps the real array count separate from its allocated index. *)
Theory abiScratchDecoderInitSequence
Ancestors
  abiScratchDecoderContract abiScratchSequence abiScratchFootprint abiDecoderFootprint
  abiDecoderArrayInitExec abiDecoderArrayPrepare abiDecoderArrayLoopInit abiDecoderIndexInit
  abiDecoderDynarrayPrefix abiDecoderArrayHeader abiDecoderAllocation abiDecoderReentry
  abiDecoderGuards abiDecoderContract abiDecoderFrameCompose abiDecoderFrame
  exprLoweringProps emitHelperProps compileEnv venomState valueEncoding words list arithmetic pred_set

Theorem abi_scratch_sequence_slot_disjoint:
  run_inst_seq insts initial = OK actual /\ abi_decoder_budget first last b cap actual /\
  abi_footprint_disjoint d outsz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  site IN abi_decoder_ids first last /\ FLOOKUP actual.vs_allocas site = SOME (slot,sz) ==>
  slot + sz <= d \/ d + outsz <= slot
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_budget_frontier >> strip_tac >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual` by
    (mp_tac (Q.SPECL [`insts`, `initial`, `actual`, `abi_decoder_ids first last`, `b`, `cap`]
      abi_scratch_sequence_evolution) >> asm_simp_tac bool_ss []) >>
  `initial.vs_alloca_next <= b + cap` by (fs[abi_scratch_evolution_def] >> decide_tac) >>
  drule_all abi_scratch_frontier_disjoint >> disch_then assume_tac >>
  mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`,
    `p` |-> `d:num`, `n` |-> `outsz:num`, `id` |-> `site:num`, `q` |-> `slot:num`,
    `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`] abi_scratch_slot_disjoint) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> disch_then assume_tac >> decide_tac
QED

Theorem abi_scratch_decoder_init_sequence:
  abi_decode_array_loop_init dst src opc hi maxn abi_sz st = (setup,loop_st) /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load opc (n2w sb:bytes32) s = n2w n /\ n <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    sb + 32 + n * abi_sz <= h /\ h < dimword (:256)) /\
  abi_decoder_budget first last b cap s /\ first <= st.cs_next_id /\ loop_st.cs_next_id <= last /\
  abi_footprint_disjoint d 32
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) /\
  fresh_vars_wrt st s ==>
  ?t p. run_inst_seq (emitted_insts st loop_st) s = OK t /\
    eval_operand (FST setup) t = SOME (n2w p) /\ eval_operand (SND setup) t = SOME (n2w n) /\
    mload p t = 0w /\ mem_word_at d t.vs_memory = n2w n /\ b <= p /\ p + 32 <= b + cap /\
    abi_decoder_budget first last b cap t /\ fresh_vars_wrt loop_st t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    abi_decode_footprint_frame [(d,32);(b,cap)] s t /\
    abi_decode_footprint_frame [(d,32);(p,32)] s t /\
    FLOOKUP t.vs_allocas (loop_st.cs_next_id-2) = SOME (p,32) /\
    (!id. id <> loop_st.cs_next_id-2 ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
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
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  `fresh_vars_wrt loop_st prepared` by
    (mp_tac (Q.SPECL [`header_st`, `loop_st`, `prepared`] fresh_vars_wrt_mono) >> simp[GREATER_EQ]) >>
  mp_tac (Q.INST [`st` |-> `header_st`, `st'` |-> `loop_st`,
    `s` |-> `prepared:venom_state`, `limit_st` |-> `loop_st`] abi_decode_index_init_sequence) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts header_st loop_st) prepared = OK actual` >>
  `!op w. eval_operand op prepared = SOME w ==> abi_decoder_operand_live header_st.cs_next_var op`
    by metis_tac[abi_decoder_operand_live_fresh] >>
  `eval_operand cnt actual = SOME (n2w n)` by metis_tac[] >>
  `!op w. eval_operand op s = SOME w ==> eval_operand op actual = SOME w` by metis_tac[] >>
  `abi_footprint_disjoint d 32
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap prepared)` by
    (qpat_x_assum `abi_footprint_disjoint d 32
       (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` mp_tac >>
     asm_simp_tac bool_ss [abi_decoder_child_scratch_def]) >>
  `p + 32 <= d \/ d + 32 <= p` by
    (drule_all abi_scratch_sequence_slot_disjoint >> simp[]) >>
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

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_INIT_SEQUENCE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical decoder initializer sequence not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderInitSequence");
