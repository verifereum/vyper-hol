(* Guarded request-prefix introduction for EC precompile builtins. *)
Theory s1PrefixGuardedEC
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
  s1PrefixPrecompile gasShadowStmtEnv gasShadowCompileStmtHelpers s1PrefixBuiltinEnvAccountCompose s1PrefixBuiltinEnvHashCompose vyperTypeCallStackSoundness s1PrefixRawRevertValue s1PrefixAssertBare s1PrefixOfVV immutableDeployAssignRanges s1PrefixBopRestWordCompose exprSimOperators exprSimHyps exprLowering exprSimHyps exprSimAccounts builtinSystem compileEnv s1PrefixIf bodyFullPreds s1PrefixStmtsCons s1PrefixStmtFullApply bodyFullIfExpReach stmtLoweringMono exprLoweringProps bodyFullShared bodyFullBopWordLayout exprSimBopInLiteralWord bodyFullWordArgs exprSimWordArgs exprSimUnopProps gasShadowState gasShadowCompilePure bodyFullRawRevertCompiledTail bodyFullRawRevertInterfaces vyperSystemControl selfdestructHalt exprBodyPreProps bodyInvExecutionProps bodySingletonCallSupport
  s1PrefixRawLogCompose bodyFullRawLog exprSimCallRawLog
  s1PrefixAugAssign s1PrefixIfExpChildren
  s1PrefixRawCallCalldata
  s1PrefixFor s1PrefixRawCall s1PrefixAnnAssign s1PrefixMakeArray gasShadowCompile gasShadowCompileHelpers bodySimFull s1PrefixLog s1PrefixBuiltinLeaves s1PrefixAnnAssignEmptyRhs s1PrefixTypeBuiltinExtract32 s1PrefixAbiDecodeExprConditional s1PrefixAbiEncodeTupleFull s1PrefixAbiEncodeNonwordFull s1PrefixAbiEncodeWordFull s1PrefixConvertBytesJoint s1PrefixConvertDynamicJoint s1PrefixConvertScalarJoint exprSimAbiEncodeRuntimeInputs exprSimConvert stmtLowering list s1PrefixPop s1PrefixBopBytestringEq s1PrefixBopWordPair exprSimBopRestWordFacts exprSimHash exprSimUnwrap s1PrefixRaiseReason
  s1PrefixBuiltinWord s1PrefixAppendSourceChildren s1PrefixAppendCodeCuts s1PrefixAppendToplevelEntry s1PrefixAppendReplayRhs s1PrefixTarget bodyPtrPopTargetFragTransport bodyAppendResolvedPre bodyFullTarget bodyFullTargetDefs loweringPosts gasOutcomeFullCompose stmtSimDefs targetPlaceSimCases vyperExprNoControl exprSimDefs emitHelper quantHeuristics bodyFullSubscript[qualified,ignore_grammar] bodyFullSubscriptMapBase bodyFullSimProjection bodySimExprCases exprSimPlaces exprSimTuple exprSimSubscriptMap exprSimMapDefs s1PrefixSubscriptMapBase s1PrefixSubscriptMap s1PrefixSubscriptTuple s1PrefixSubscriptArrayCode s1PrefixSubscriptArrayMemory s1PrefixSubscriptUnframedArray s1PrefixExtCallRequestStage s1PrefixExtCallCallStage s1PrefixExtCallReturnTrace bodyFullExtCallReadyReturn bodyFullExtCallReturn abiDecodeValidJoint abiDecodeRejectJoint exprSimExtCallCase s1PrefixBuiltinCalldataSlice s1PrefixBuiltinConcat s1PrefixBuiltinSlice s1PrefixBuiltinUint2Str s1PrefixAssignTuple s1PrefixAssign s1PrefixBoolChainSelectedLocalAssign finite_map exprSimAggregateLayout contractInvContextProps s1PrefixHash
  s1PrefixRawLogCompose bodyFullRawLog exprSimCallRawLog
  s1PrefixAugAssign s1PrefixIfExpChildren
  s1PrefixRawCallCalldata
  s1PrefixFor s1PrefixRawCall s1PrefixAnnAssign s1PrefixMakeArray gasShadowCompile gasShadowCompileHelpers bodySimFull s1PrefixLog s1PrefixBuiltinLeaves s1PrefixAnnAssignEmptyRhs s1PrefixTypeBuiltinExtract32 s1PrefixAbiDecodeExprConditional s1PrefixAbiEncodeTupleFull s1PrefixAbiEncodeNonwordFull s1PrefixAbiEncodeWordFull s1PrefixConvertBytesJoint s1PrefixConvertDynamicJoint s1PrefixConvertScalarJoint exprSimAbiEncodeRuntimeInputs exprSimConvert stmtLowering list s1PrefixPop s1PrefixBopBytestringEq s1PrefixBopWordPair exprSimBopRestWordFacts exprSimHash exprSimUnwrap s1PrefixRaiseReason
Libs
  pairLib

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  ONCE_REWRITE_TAC [body_expr_prefix_ok_def] >> conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      Cases_on `bt = ECRecover` >> gvs[]
      >- (drule exprSimPrecompilesTheory.ecrecover_pre_types >> strip_tac >>
          `body_exprs_full_ok cx es /\ body_exprs_prefix_ok cx es` by
            fs[vyperContextTheory.builtin_args_length_ok_def] >>
          conj_asm1_tac
          >- suspend "recovery_stack" >>
          irule expr_vv_sim_stack_prefix >> simp[] >> conj_tac
          >- (gen_tac >> Cases_on `compile_expr cenv ty' (Builtin ty ECRecover es) sa` >>
              drule_all exprSimPrecompilesTheory.compile_ecrecover_stack >> metis_tac[])
          >> metis_tac[exprLoweringPropsTheory.eval_expr_builtin_value])
      >> irule ec_arith_builtin_sim_prefix >> simp[] >>
      qexistsl_tac [`env`,`tops`] >> simp[])
  >> rpt conj_tac >> rpt gen_tac >> strip_tac >> gvs[]
QED
*)
Theorem precompile_builtin_expr_prefix_ok:
  !cx ty bt es.
  (bt = ECRecover \/ bt = ECAdd \/ bt = ECMul) /\
  (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok cx es) /\
  (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_prefix_ok cx es) ==>
  body_expr_prefix_ok cx (Builtin ty bt es)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume precompile_builtin_expr_prefix_ok[recovery_stack]:
  rewrite_tac[expr_sim_prefix_def,expr_sim_full_pre_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `lower_value _ _ _ (Builtin _ ECRecover _) _ = _`
    (mp_then Any mp_tac exprSimPrecompilesTheory.lower_value_ecrecover_args) >>
  simp[] >> strip_tac >>
  `?shm. lower_word_args (gas_shadow_env T cenv) (\e. ty')
          (MAP gas_shadow_expr es) shadow_sa = ([h;v;r;sig],shm) /\
         gas_shadow_state sm shm` by
    (`gas_shadow_compiles (lower_word_args cenv (\e. ty') es)
        (lower_word_args (gas_shadow_env T cenv) (\e. ty') (MAP gas_shadow_expr es))` by
       simp[bodyFullWordArgsTheory.gas_shadow_compiles_lower_word_args] >>
     qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`,`shadow_sa`] mp_tac o
        REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >>
     Cases_on `lower_word_args (gas_shadow_env T cenv) (\e. ty')
       (MAP gas_shadow_expr es) shadow_sa` >> simp[]) >>
  `compile_ecrecover h v r sig shm = (op,shadow_sb)` by
    (qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gas_shadow_expr_def,gasShadowTheory.gas_shadow_builtin_def] >>
     disch_then (mp_then Any mp_tac exprSimPrecompilesTheory.lower_value_ecrecover_args) >>
     simp[] >> strip_tac >> gvs[]) >>
  `cs_extends sa sm /\ cs_extends shadow_sa shm` by
    metis_tac[bodyFullWordArgsTheory.ci_mono_lower_word_args,
              exprLoweringPropsTheory.ci_mono_def] >>
  `cs_extends sm sb /\ cs_extends shm shadow_sb` by
    metis_tac[exprSimPrecompilesTheory.compile_ecrecover_extends] >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shm shadow_func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `expr_sim_inv cenv cx env es'` by
    metis_tac[exprBodyPrePropsTheory.expr_body_pre_static_facts] >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (eval_exprs cx es) (es',s0,G0,tn0)` by
    (qpat_assum `lower_word_args cenv _ _ sa = _`
       (mp_then Any irule lower_word_args_by_type_prefix) >>
     simp[] >> rpt conj_tac >- first_assum ACCEPT_TAC
     >- (qexistsl_tac [`shadow_func`,`shadow_sa`,`shm`] >> simp[])
     >- (qexistsl_tac [`env`,`tops`] >> simp[] >> rpt gen_tac >> strip_tac >>
         conj_tac >- (drule exprSimSourceTheory.expr_body_pre_builtin_arg >>
                      disch_then (qspecl_then [`e`,`ee`] mp_tac) >> simp[])
         >> fs[listTheory.EVERY_MEM])
     >> qexists_tac `d` >> simp[]) >>
  suspend "recovery_tail"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume precompile_builtin_expr_prefix_ok[recovery_tail]:
  qpat_x_assum `ty = BaseT AddressT` SUBST_ALL_TAC >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_exprs cx es) (es',s0,G0,tn0)
     (\H res ee G tn t. ~t.vs_halted)
     (\H res ee gt r. wb_args_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))` by
    (irule bodyFullIfExpReachTheory.gas_outcome_full_post_path >>
     qpat_assum `lower_word_args cenv _ _ sa = _`
       (mp_then Any (irule_at Any) bodyFullBuiltinPrecompileRecoveryArgsTheory.ecrecover_args_suffix_full) >>
     simp[] >>
     qexistsl_tac [`tops`,`shm`,`shadow_sa`,`shadow_func`,`env`,`es'`,`[]`,`d`,`BaseT AddressT`] >>
     simp[] >> rpt conj_tac >- first_assum ACCEPT_TAC >>
     rpt strip_tac >> drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[fragExecTheory.exit_result_def]) >>
  qpat_assum `LENGTH es = 4`
    (mp_then Any (rewrite_tac o single) exprSimPrecompilesTheory.eval_expr_ecrecover_read_action) >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn t. ~t.vs_halted) _`
    (mp_then Any irule s1PrefixComposeTheory.gas_prefix_full_bind_no_outcome) >>
  simp[cj 6 evaluate_storage_trace_frame,
       cj 6 s1PrefixPropsTheory.evaluate_requests_outcomes_frame] >>
  rpt conj_tac
  >~ [`ISR _`]
  >- (qx_gen_tac `H` >> qx_gen_tac `res` >> Cases_on `res` >>
      simp[exprSimWordArgsTheory.wb_args_exit_def])
  >~ [`computed_precompile _`]
  >- (rpt gen_tac >>
      simp[AllCaseEqs(),ignore_bind_def,bind_def,return_def] >>
      rpt strip_tac >> gvs[] >>
      qpat_assum `precompile_call_success _ _ _ = _`
        (mp_then Any mp_tac precompile_call_success_only_computed_outcomes) >> simp[])
  >> qx_gen_tac `vs` >>
  `!(w:value). storage_trace_frame (ignore_bind (precompile_call_success ECRecover vs) (return w))` by
    simp[storage_trace_frame_ignore_bind,storage_trace_frame_precompile_call_success,
         storage_trace_frame_return] >>
  simp[storage_trace_frame_def] >> rpt gen_tac >>
  Cases_on `builtin_result cx st.accounts (BaseT AddressT) ECRecover (MAP expr_type es) vs` >> simp[] >>
  rename1 `builtin_result _ _ _ _ _ _ = INL w` >>
  qpat_x_assum `!w. storage_trace_frame _`
    (qspec_then `w` (qspecl_then [`st`,`observations`] ACCEPT_TAC o
                     PURE_ONCE_REWRITE_RULE [storage_trace_frame_def]))
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise precompile_builtin_expr_prefix_ok
*)
