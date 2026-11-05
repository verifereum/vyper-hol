(* Memory-safe compilation of local names whose type is a word type without a
   word value (address, bytesM): the lowering loads the slot with MLOAD. *)
Theory bodyNameWordTypeMemory
Ancestors
  bodyNameMemoryFacts
  exprSimSource exprSimHypsDefs exprSimDefs exprSimProps bodyMemoryDefs
  exprSimMemoryValues exprSimMemoryStack exprSimMemoryRead fragGasSeqMem
  fragGasPathMem gasNormalPrefix gasSummary gasContext gasCount fragGasMode
  loweringPosts exprSimNameWord exprSimNameValue loweringSlice exprLowering
  exprLoweringProps fragExec fragExecMem allocaHistoryFragment instMemFrontier
  emitHelperProps emitHelper compileEnv context venomInst venomState
  venomExecSemantics venomMemDefs vyperInterpreter vyperState vyperAST
  vyperTypeEnv vyperTypeSystem vyperTypeInvariants valueEncoding valueEncodingProofs
  list rich_list finite_map words arithmetic

Theorem compile_name_wordtype_body_sim_mem:
  !ctx func ce cx env ty ann id es.
    expr_sim_pre ce cx env (Name ann id) es /\
    is_word_type ann /\ ~word_value_type ann ==>
    expr_sim_mem ctx func ce cx ty (Name ann id) es
Proof
  cheat
QED
