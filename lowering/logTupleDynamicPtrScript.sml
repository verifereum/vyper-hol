(* Dynamic scalar tuple encoding: compose actual cursor entry and finished members. *)
Theory logTupleDynamicPtr
Ancestors
  logTupleShapePtr logTupleEntryPtr logTupleFinishPtr logCursorAllocPtr
  abiBuiltinAllocation abiDecoderFrame abiEncoderComplexCode abiEncoderComplexPrefix
  abiDecoderArrayHeader valueEncodingProps abiDecoderContract
  emitHelperProps exprLoweringProps compileEnv context fragExec fragGasSeqPtr
  venomExecSemantics venomState venomInst words list arithmetic finite_map pred_set

(* The allocation ownership certificate frames non-memory observations; the
   literal initialization adds only the cursor cell to the memory footprint. *)
Theorem log_cursor_prefix_effect_frame:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;Lit w] sm = ((),sb) /\
  run_inst_seq (emitted_insts sa sm) s = OK u /\
  run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK t /\
  lookup_var dp u = SOME (n2w p) /\ buf.buf_operand = Var dp /\
  p < dimword(:256) /\
  abi_builtin_allocation_frame sa.cs_next_var sa.cs_next_id 32 s u ==>
  abi_decode_footprint_frame [(p,32)] s t /\
  t.vs_allocas = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas /\
  t.vs_alloca_next = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_alloca_next /\
  t.vs_halted = s.vs_halted
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  qpat_x_assum `step_inst_base _ u = OK t` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_write2_def,
       eval_operand_def] >> strip_tac >>
  `abi_decode_frame p 32 u (mstore p w u)` by irule abi_decode_mstore_frame >>
  gvs[abi_builtin_allocation_frame_def, abi_decode_frame_def,
      abi_decode_footprint_frame_def, abi_footprint_disjoint_def, mstore_def] >>
  first_assum ACCEPT_TAC
QED

