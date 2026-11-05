(* Counted memory simulation of a struct field on a local Name. *)
Theory bodyFieldValueMemory
Ancestors
  bodyFieldMemoryProps bodyNameValueMemory bodyNameMemoryFacts
  exprSimFieldLayout exprSimAttributeProps exprSimVVFrame exprSimProps
  exprSimSource exprSimHypsDefs exprSimMemDefs exprSimDefs loweringPosts
  exprSimMemoryStack exprSimMemoryValues exprSimMemoryPath exprSimUnwrapProps
  gasNormalPrefix gasSummary gasSummaryCompose gasContext gasCount fragGasMode
  fragGasPathMem fragGasSeqMem gasExemptCert
  bodyMemoryDefs emitHelperProps fragExecMem instMemFrontier allocaHistoryFragment
  exprLoweringProps emitHelper venomInst venomState words list rich_list finite_map
  compileEnv fragExec valueEncoding vyperValue vyperAST venomExecSemantics
  loweringSlice exprLowering vyperState vyperExprNoControl
  freshWrites varsExt vyperTyping vyperTypeSystem vyperTypeInvariants
  allocLimits context vyperInterpreter vyperTypeExprSoundness

Theorem compile_attribute_name_body_vv_sim_mem:
  !ctx func cenv cx env ty ann sid id fld es.
    expr_body_pre cenv cx env (Attribute ann (Name (StructT sid) id) fld) es ==>
    expr_vv_sim_mem ctx func cenv cx ty
      (Attribute ann (Name (StructT sid) id) fld) es
Proof
  cheat
QED
