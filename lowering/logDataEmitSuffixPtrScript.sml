(* Successful Log suffix after topic hashing; compiler branches stay separate. *)
Theory logDataEmitSuffixPtr
Ancestors
  logStoreEncodeRunPtr logEmitPtr logGhostFramePtr stmtSimLogTrace logEventCodePtr
  stmtSimLogSuffixActual stmtSimLogArgs stmtSimLogDataRun stmtSimLogStoreFresh
  bodyPtrDefs stmtFragPtr fragGasPathPtr compileEnv loweringStateRelDefs context stmtLowering
  emitHelperProps exprLoweringProps venomState venomInst ptrDiscipline
  list arithmetic words rich_list vyperABI valueEncoding valueEncodingDefs contractABI abiDecoderReentry

Theorem eval_operands_list_rel:
  !ops ws. LIST_REL (\op w. eval_operand op s = SOME w) ops ws <=>
    eval_operands ops s = SOME ws
Proof
  Induct >> Cases_on `ws` >> simp[eval_operands_def, AllCaseEqs()] >> metis_tac[]
QED
