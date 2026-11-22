(* The keyword pointers allocated before a group's selector checks. *)
Theory groupedKeywordAllocas
Ancestors
  moduleLowering context bodyFullAllocaFresh bodyFullHashKeccakFixed
  bodyPtrMakeArrayAllocBuffer exprLoweringProps exprSimHash loweringHalt
  fragExec fragGasOriginPtr fragGasOriginPtrLoop fragGasSeqPtr ptrDiscipline bodyPtrDefs
  abiBuiltinAllocation bufferAllocationExecution exprPtrUnwrapAllocation
  emitHelperProps emitHelper sourceValueFrames venomExecSemantics
  stmtFragPtr loweringStateRelDefs compileEnv venomState venomInst finite_map list pair words arithmetic

Theorem compile_create_kwarg_allocas_mono:
  !specs ce sa. ci_mono sa (SND (compile_create_kwarg_allocas ce specs sa))
Proof
  Induct >- simp[compile_create_kwarg_allocas_def, ci_mono_comp_return] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  PURE_ONCE_REWRITE_TAC [compile_create_kwarg_allocas_def] >>
  irule ci_mono_bind >> simp[ci_mono_compile_alloc_buffer] >>
  gen_tac >> irule ci_mono_bind >> simp[ci_mono_comp_return]
QED
