(* Count validation and the output length store before scratch allocation. *)
Theory abiDecoderArrayPrepare
Ancestors
  abiDecoderArrayLoopInit abiDecoderDynarrayPrefix abiDecoderArrayHeader
  abiDecoderReservation abiDecoderReentrySequence abiDecoderGuards abiDecoderContract
  exprLoweringProps emitHelperProps compileEnv venomState words list arithmetic

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

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_ARRAY_PREPARE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI array preparation not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderArrayPrepare");
