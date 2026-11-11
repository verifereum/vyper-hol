(* Same-endpoint memory continuation for the actual tuple producer. *)
Theory abiTupleEncodeMemoryReach
Ancestors
  abiTupleEncodePrepare abiBuiltinAllocation abiTupleEncodeMemory
  abiEncoderSequence abiDecoderContract abiDecoderReentry fragExecMem fragExec
  memContinuation compileEnv venomState venomExecSemantics instIdxIndep
  emitHelperProps exprLoweringProps words list arithmetic
  abiTupleEncodeAssembly abiTupleEncodeLayout abiEncoderWindow abiEncoderOpenInput
  abiEncoderInput contractABI valueEncoding

Theorem abi_tuple_encode_stage_fragment_mem[local]:
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 xs allocated = ((),staged) /\
  run_inst_seq (emitted_insts st staged) initial = OK encoded /\
  run_inst_seq_mem_ok (emitted_insts st staged) initial ==>
  frag_exec_mem ctx st staged (\s. s = initial)
    (\s. s = (encoded with vs_inst_idx := LENGTH staged.cs_current_insts)) (K F)
Proof
  strip_tac >> drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  irule fragExecMemTheory.frag_exec_mem_run_inst_seq >> simp[] >>
  rpt strip_tac >> gvs[] >> disj1_tac >> qexists_tac `encoded` >> simp[]
QED

Theorem abi_tuple_encode_stage_reach_mem:
  compile_alloc_buffer (abi_tuple_bytes ce xs) st = (source_buf,allocated) /\
  compile_store_abi_tuple ce source_buf.buf_operand 0 xs allocated = ((),staged) /\
  fn_has_code st staged func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,abi_tuple_bytes ce xs)) /\
  sb+abi_tuple_bytes ce xs < dimword (:256) /\
  abi_tuple_encode_inputs sf ce xs ats avs st.cs_next_var sb (sb+abi_tuple_bytes ce xs) initial /\
  staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts st staged) initial ==>
  ?actual. eval_operand source_buf.buf_operand actual = SOME (n2w sb) /\
    abi_tuple_encode_memory sf ce xs ats avs sb actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
    abi_decode_frame sb (abi_tuple_bytes ce xs) initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = staged.cs_current_bb /\ actual.vs_inst_idx = LENGTH staged.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\ mem_cont_sim ctx func initial actual
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  drule_all abi_tuple_encode_stage_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st staged) initial = OK encoded` >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_tuple_encode_stage_fragment_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule mem_cont_sim_from_fragment >> disch_then (qspec_then `initial` mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `encoded with vs_inst_idx := LENGTH staged.cs_current_insts` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx] >> first_assum ACCEPT_TAC
QED

Theorem abi_tuple_encode_window_input:
  abi_tuple_encode_memory sf ce xs ats avs d mem /\ abi_tuple_encode_layout ce xs ats /\
  has_type (Tuple ats) (ListV avs) ==>
  abi_encoder_window_input (type_to_abi_enc_info sf ce (TupleT (MAP SND xs)))
    (Tuple ats) (ListV avs) d (abi_tuple_bytes ce xs) mem
Proof
  strip_tac >> drule_all abi_tuple_encode_input >> strip_tac >>
  drule abi_encoder_input_open >> strip_tac >>
  drule abi_encoder_open_input_window >> simp[]
QED
