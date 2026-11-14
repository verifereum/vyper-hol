Theory bodyPtrTypeBuiltinsExtract32Read
Ancestors
  extract32Certificate
  bodyPtrTypeBuiltinsExtract32BoundsPtr rawCallBufferPtr
  immutableRegionLoadPtr storageCopyBodyRaisePtr assignBasePtrBytesPrefix
  instSeqComposePtr ghostPcTransportPtr bodyPtrDefs ptrDiscipline
  venomInst venomState venomExecSemantics instIdxIndep fragExec fragGasSeqPtr
  compileEnv loweringStateRelDefs words list finite_map pred_set exprLoweringProps emitHelperProps
  decoderGhostFramePtr bodyPtrTypeBuiltinsBounds builtinBytes emitHelper rich_list
  augAssignPtrScalarCertificate augAssignPtrScalarRun

(* An interior address retains the source provenance. Only the loaded word
   is provenance-free; clean_add_checked_uniform deliberately preserves it. *)
Theorem extract32_load_normal_ptr_path:
  compile_extract32_load len data offset sa = (raw,sb) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 H th
    (OK (t with vs_inst_idx := s.vs_inst_idx + 8))
Proof
  strip_tac >> drule extract32_load_code_shape >> strip_tac >>
  drule compile_assert_slice_bounds_shape >> strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s
    (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb))) H th
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)))` by
    (irule run_inst_seq_gas_path_ptr >> gvs[mk_inst_def, is_terminator_def]) >>
  gvs[mk_inst_def]
QED

Theorem extract32_load_abort_ptr_path:
  compile_extract32_load len data offset sa = (raw,sb) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t ==>
  ?n j. gas_path_ptr D 0 ctx fn PG G tn s n H th
    (Abort err (t with vs_inst_idx := j))
Proof
  strip_tac >> irule run_inst_seq_abort_gas_path_ptr >> simp[] >>
  qexists_tac `emitted_insts sa sb` >> simp[] >>
  drule extract32_load_code_shape >> strip_tac >>
  drule compile_assert_slice_bounds_shape >> simp[mk_inst_def, is_terminator_def]
QED
