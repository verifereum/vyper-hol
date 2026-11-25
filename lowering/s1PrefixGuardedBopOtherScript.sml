(* Request-prefix companion for the nonmembership binary operators. *)
Theory s1PrefixGuardedBopOther
Ancestors
  s1PrefixDefs s1PrefixPreds s1PrefixReturnSome s1PrefixReturnNone s1PrefixExits
  s1PrefixStmtZero s1PrefixExprStmt s1PrefixNames s1PrefixLiteralWord
  s1PrefixAssertReason s1PrefixMsgGas s1PrefixFrame stmtExprAllocationPreProps bodyInvCodeProps
  compileUnit vyperStorageTrace vyperState alist
  allocLimits allocLimitsProps bodyExprPreFacts bodySim
  exprSimHypsDefs gasContext gasShadow supportedExprs supportedStmts
  supportedExprTraverse supportedStmtTraverse
  vyperAST vyperContext vyperInterpreter vyperTypeSystem vyperTypeCallGraph
  bodyFullCases exprSimBuiltins bodyFullBuiltinEnvAccountRun bodyFullBuiltinEnvBlockHashSuffix bodyFullBuiltinEnvBlobHashSuffix exprSimSource exprBopLowering bodySimFullMain[qualified] s1PrefixRaiseCustomError[qualified] s1PrefixAssertCustomError[qualified] s1PrefixBuiltinECArithCompose s1PrefixIfExpPrepare s1PrefixWordArgs
  s1PrefixPrecompile gasShadowStmtEnv gasShadowCompileStmtHelpers s1PrefixBuiltinEnvAccountCompose s1PrefixBuiltinEnvHashCompose vyperTypeCallStackSoundness s1PrefixRawRevertValue s1PrefixAssertBare s1PrefixOfVV immutableDeployAssignRanges s1PrefixBopRestWordCompose exprSimOperators exprSimHyps exprLowering exprSimAccounts builtinSystem compileEnv s1PrefixIf bodyFullPreds s1PrefixStmtsCons s1PrefixStmtFullApply bodyFullIfExpReach stmtLoweringMono exprLoweringProps bodyFullShared bodyFullBopWordLayout exprSimBopInLiteralWord bodyFullWordArgs exprSimWordArgs exprSimUnopProps gasShadowState exprBopSimProps fragExec exprSimLen vyperStatePreservation gasShadowCompilePure bodyFullRawRevertCompiledTail bodyFullRawRevertInterfaces vyperSystemControl selfdestructHalt exprBodyPreProps bodyInvExecutionProps bodySingletonCallSupport
  s1PrefixRawLogCompose bodyFullRawLog exprSimCallRawLog
  s1PrefixAugAssign s1PrefixIfExpChildren
  s1PrefixRawCallCalldata
  s1PrefixFor s1PrefixRawCall s1PrefixAnnAssign s1PrefixMakeArray gasShadowCompile gasShadowCompileHelpers bodySimFull s1PrefixLog s1PrefixBuiltinLeaves s1PrefixAnnAssignEmptyRhs s1PrefixTypeBuiltinExtract32 s1PrefixAbiDecodeExprConditional s1PrefixAbiEncodeTupleFull s1PrefixAbiEncodeNonwordFull s1PrefixAbiEncodeWordFull s1PrefixConvertBytesJoint s1PrefixConvertDynamicJoint s1PrefixConvertScalarJoint exprSimAbiEncodeRuntimeInputs exprSimConvert stmtLowering list s1PrefixPop s1PrefixBopBytestringEq s1PrefixBopWordPair exprSimBopRestWordFacts exprSimHash exprSimUnwrap s1PrefixRaiseReason
  s1PrefixBuiltinWord s1PrefixAppendSourceChildren s1PrefixAppendCodeCuts s1PrefixAppendToplevelEntry s1PrefixAppendReplayRhs s1PrefixTarget bodyPtrPopTargetFragTransport bodyAppendResolvedPre bodyFullTarget bodyFullTargetDefs loweringPosts gasOutcomeFullCompose stmtSimDefs targetPlaceSimCases vyperExprNoControl exprSimDefs emitHelper quantHeuristics bodyFullSubscript[qualified,ignore_grammar] bodyFullSubscriptMapBase bodyFullSimProjection bodySimExprCases exprSimPlaces exprSimTuple exprSimSubscriptMap exprSimMapDefs s1PrefixSubscriptMapBase s1PrefixSubscriptMap s1PrefixSubscriptTuple s1PrefixSubscriptArrayCode s1PrefixSubscriptArrayMemory s1PrefixSubscriptUnframedArray s1PrefixExtCallRequestStage s1PrefixExtCallCallStage s1PrefixExtCallReturnTrace bodyFullExtCallReadyReturn bodyFullExtCallReturn abiDecodeValidJoint abiDecodeRejectJoint exprSimExtCallCase s1PrefixBuiltinCalldataSlice s1PrefixBuiltinConcat s1PrefixBuiltinSlice s1PrefixBuiltinUint2Str s1PrefixAssignTuple s1PrefixAssign s1PrefixBoolChainSelectedLocalAssign finite_map exprSimAggregateLayout contractInvContextProps s1PrefixHash
Libs
  pairLib

Theorem bop_expr_prefix_ok:
  !cx ty bop es.
  bop <> In /\
  bop <> NotIn /\
  (builtin_args_length_ok (Bop bop) (LENGTH es) ==> body_exprs_full_ok cx es) /\
  (builtin_args_length_ok (Bop bop) (LENGTH es) ==> body_exprs_prefix_ok cx es) ==>
  body_expr_prefix_ok cx (Builtin ty (Bop bop) es)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[Once body_expr_prefix_ok_def] >> rpt gen_tac >> strip_tac >>
  drule expr_body_pre_bop_args >>
  disch_then (qx_choose_then `e1` (qx_choose_then `e2` SUBST_ALL_TAC)) >>
  `body_exprs_full_ok cx [e1;e2] /\ body_exprs_prefix_ok cx [e1;e2]` by
    fs[builtin_args_length_ok_def] >>
  drule expr_body_pre_bop >> strip_tac >>
  conj_asm1_tac
  >- (Cases_on `(bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1)`
      >- (irule bop_bytestring_eqne_value_prefix >> simp[] >> metis_tac[]) >>
      `is_word_type ty /\ is_word_type (expr_type e1) /\
       is_word_type (expr_type e2)` by
        (Cases_on `word_value_type (expr_type e1) /\ word_value_type (expr_type e2)`
         >- metis_tac[exprSimSourceTheory.word_value_type_word,
                      well_typed_binop_word_result] >>
         `?tv. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv` by
           (qpat_assum `expr_body_pre _ _ _ e1 _`
              (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
            simp[optionTheory.IS_SOME_EXISTS]) >>
         Cases_on `(bop = Eq \/ bop = NotEq) /\
                   (expr_type e1 = BaseT AddressT \/
                    ?m. expr_type e1 = BaseT (BytesT (Fixed m)))`
         >- (gvs[well_typed_binop_def, is_word_type_def,
                 vyperValueTheory.evaluate_type_def, optionTheory.IF_EQUALS_OPTION] >>
             qpat_x_assum `BaseT _ = expr_type e2` (SUBST_ALL_TAC o SYM) >>
             gvs[is_word_type_def, vyperValueTheory.evaluate_type_def,
                 optionTheory.IF_EQUALS_OPTION]) >>
         `?m. expr_type e1 = BaseT (BytesT (Fixed m)) /\
              MEM bop [And;Or;XOr;ShL;ShR]` by
           metis_tac[rest_word_typed_membership] >>
         qpat_x_assum `expr_type e1 = BaseT (BytesT (Fixed _))` SUBST_ALL_TAC >>
         gvs[well_typed_binop_def, is_int_type_def, is_word_type_def,
             vyperValueTheory.evaluate_type_def, optionTheory.IF_EQUALS_OPTION] >>
         Cases_on `expr_type e2` >> gvs[is_int_type_def, is_word_type_def] >>
         rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
         gvs[is_int_type_def, is_word_type_def]) >>
      irule bop_word_pair_value_prefix >> simp[] >> metis_tac[]) >>
  irule expr_vv_sim_stack_prefix >> simp[compile_bop_stack] >>
  metis_tac[eval_expr_builtin_value]
QED
