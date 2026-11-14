Theory bodyPtrTypeBuiltinsExtract32Suffix
Ancestors
  extract32Certificate
  bodyPtrTypeBuiltinsExtract32Read bodyPtrTypeBuiltinsExtract32Clamp
  exprSimExtract32Read exprSimExtract32Post exprLoweringProps emitHelperProps
  builtinBytes compileEnv loweringStateRelDefs freshWrites instSeqComposePtr fragGasSeqPtr ptrDiscipline
  venomInst venomState venomExecSemantics list pred_set finite_map words
  augAssignPtrScalarCertificate

Theorem extract32_tail_normal_ptr_path:
  compile_extract32_load len data offset sa = (raw,sm) /\
  compile_clamp_basetype raw typ sm = (result,sb) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 H th
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)))
Proof
  strip_tac >> drule_all extract32_tail_code_cuts >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (gvs[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  gvs[EVERY_CONJ] >>
  drule_all (SRULE [EVERY_CONJ, EVERY_APPEND] (Q.SPEC `xs ++ ys` run_inst_seq_gas_path_ptr)) >> simp[]
QED

Theorem extract32_tail_abort_ptr_path:
  compile_extract32_load len data offset sa = (raw,sm) /\
  compile_clamp_basetype raw typ sm = (result,sb) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t ==>
  ?n j. gas_path_ptr D 0 ctx fn PG G tn s n H th
    (Abort err (t with vs_inst_idx := j))
Proof
  strip_tac >> drule_all extract32_tail_code_cuts >> strip_tac >>
  gvs[EVERY_CONJ] >>
  drule_all (SRULE [EVERY_CONJ, EVERY_APPEND]
    (Q.SPEC `xs ++ ys` run_inst_seq_abort_gas_path_ptr)) >> simp[]
QED
