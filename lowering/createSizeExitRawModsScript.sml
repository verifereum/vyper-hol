Theory createSizeExitRawMods
Ancestors
  createSizeExitRaw createExprSizeExitDefsMods
  bodySingletonCallSupport[qualified,ignore_grammar]
  exprSimFullBundleProps fragExec gasExplicitSites s1PrefixDefs venomExecSemantics venomInst
  venomState vyperCreate vyperState relation list words pair bodyFullIfExpReach
  builtinCreate arithmetic createSizeDispatch exprLowering vfmConstants externalEntryShape
  compileEnv createSizeItinerary exprLoweringProps exprBodyPreProps rich_list
  exprSimHypsDefs vyperTypeSystem bodyPtrDefs loweringPosts context createSizeRawSourceMods
  bodyInvCodeProps vyperAST allocLimits vyperTypeCallGraph exprSimSend integer_word
  createCtorSegmentArrival bodyFullExtCallPosAggregate loweringStateRelDefs
  dallocaBlueprintArgs createSizeRawPairedCode createSizeRawExtent createOperandSizeReject
  createExprSizeExitDefs createSizePrefixCutsMods createSizeRawReplayMods createSizeRawDataEntryMods
  createSizeRawObserved createSizeRawPayloadReplayMods createSizeOperandPreMods

Theorem raw_payload_snapshot_no_copy_mods[local]:
  compile_expr ce (expr_type e) e ca = (v,cm) /\
    expr_body_pre_mods mods ce cx env e p /\
    ~exprs_can_mutate ce rest /\
    ~is_word_type (lowered_value_type ce e) /\
    compile_snapshot_vv ce (exprs_can_mutate ce rest)
      (ext_call_arg_value (lowered_value_type ce e) v) cm = (saved,cn) ==>
    cm = cn
Proof
  cheat
QED

Theorem create_size_exit_raw_mods:
  !mods exps cx ann hs rof ks args df.
    EVERY (create_operand_completed_ok_mods mods exps cx) (create_operand_order RawCreate hs args) ==>
    create_expr_size_exit_mods mods exps cx (Call ann (CreateTarget RawCreate hs rof ks) args df)
Proof
  cheat
QED
