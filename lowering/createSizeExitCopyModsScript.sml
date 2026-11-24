Theory createSizeExitCopyMods
Ancestors
  createSizeExitCopy createExprSizeExitDefsMods
  abiEncoderProps e2eDefs fragExec fragGasOrigin gasExplicitSites s1PrefixDefs venomInst
  venomState vyperCreate relation list words createMarkedPath pair builtinCreate arithmetic
  createSizeDispatch exprLowering vfmConstants externalEntryShape compileEnv
  createSizeItinerary exprLoweringProps exprBodyPreProps rich_list vyperTypeSystem vyperAST
  createSizeStraightPrefix createSizeIndexedRun createSizeCopyLength createSizeCopyScalarCode ghostPcTransportPtr
  exprSimSend integer_word loweringStateRelDefs createExprSizeExitDefs
  createSizePrefixReplayMods createSizeCopyReplayMods createSizePrefixCutsMods

Theorem create_size_exit_copy_mods:
  !mods exps cx ann has_salt rof ks args dflt.
    EVERY (create_operand_completed_ok_mods mods exps cx) (create_operand_order CreateCopyOf has_salt args) ==>
    create_expr_size_exit_mods mods exps cx (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args dflt)
Proof
  cheat
QED
