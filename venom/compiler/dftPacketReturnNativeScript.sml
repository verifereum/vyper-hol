Theory dftPacketReturnNative
Ancestors
  dftGasFromListTraceDefs venomExecSemantics venomInst rich_list arithmetic

Theorem dft_packet_native_return_concat:
  get_instruction bb b0.vs_inst_idx = SOME c /\
  c.inst_opcode = INVOKE /\
  decode_invoke c = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME child /\
  eval_operands ops b0 = SOME args /\
  setup_callee child args b0 = SOME ent /\
  run_blocks fuel C child ent = IntRet ir out /\
  bind_outputs c.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state b0 out)) = SOME post ==>
  trace_block a e fuel C parent bb b0 =
    [((a,e,c.inst_id),parent,c,b0)] ++
    trace_blocks ((e,c.inst_id)::a) e fuel C child ent ++
    trace_block a e fuel C parent bb
      (post with vs_inst_idx := SUC b0.vs_inst_idx)
Proof
  strip_tac >>
  drule_then assume_tac trace_block_visit >>
  drule_all trace_step_invoke >> strip_tac >>
  `step_inst fuel C c b0 = OK post` by simp[Once step_inst_def] >>
  gvs[is_terminator_def]
QED

Theorem dft_packet_native_return_next:
  get_instruction bb b0.vs_inst_idx = SOME c /\
  c.inst_opcode = INVOKE /\
  decode_invoke c = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME child /\
  eval_operands ops b0 = SOME args /\
  setup_callee child args b0 = SOME ent /\
  run_blocks fuel C child ent = IntRet ir out /\
  bind_outputs c.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state b0 out)) = SOME post /\
  get_instruction bb (SUC b0.vs_inst_idx) = SOME next ==>
  SUC (LENGTH (trace_blocks ((e,c.inst_id)::a) e fuel C child ent)) <
    LENGTH (trace_block a e fuel C parent bb b0) /\
  EL (SUC (LENGTH (trace_blocks ((e,c.inst_id)::a) e fuel C child ent)))
    (trace_block a e fuel C parent bb b0) =
      ((a,e,next.inst_id),parent,next,
        post with vs_inst_idx := SUC b0.vs_inst_idx)
Proof
  strip_tac >>
  drule_all dft_packet_native_return_concat >> strip_tac >>
  `get_instruction bb (post with vs_inst_idx := SUC b0.vs_inst_idx).vs_inst_idx =
    SOME next` by simp[] >>
  drule_then assume_tac trace_block_visit >>
  simp[EL_APPEND]
QED
