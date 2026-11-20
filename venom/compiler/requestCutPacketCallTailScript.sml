Theory requestCutPacketCallTail
Ancestors
  requestCutNativeBoundary dftGasFromListTraceDefs gasEvents
  venomExecSemantics venomInst venomState list

Theorem request_cut_packet_call_tail:
  bb.bb_instructions = ps ++ xs /\
  q < LENGTH xs /\ caller.vs_inst_idx = LENGTH ps + q /\
  inst = EL q xs /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops caller = SOME args /\
  setup_callee callee args caller = SOME child /\
  run_blocks f C callee child = stopped /\
  ~(?u. stopped = OK u) /\ ~(?ir u. stopped = IntRet ir u) ==>
  exec_block f C bb caller = stopped /\
  MAP FST (trace_gas (trace_block a e f C sf bb caller)) =
    MAP FST (trace_gas (trace_blocks ((e,inst.inst_id)::a) e f C callee child))
Proof
  strip_tac >>
  `get_instruction bb caller.vs_inst_idx = SOME inst` by
    simp[get_instruction_def,EL_APPEND_EQN] >>
  drule_all request_cut_native_invoke_stopped >>
  disch_then (qspecl_then [`a`,`e`,`sf`] strip_assume_tac) >>
  asm_rewrite_tac[]
QED
