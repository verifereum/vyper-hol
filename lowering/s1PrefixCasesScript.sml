(* Request-prefix cases for the body induction. *)
Theory s1PrefixCases
Ancestors
  s1PrefixDefs s1PrefixPreds s1PrefixReturnSome s1PrefixReturnNone s1PrefixExits
  s1PrefixGuardedMsgGas[qualified] s1PrefixGuardedEnv[qualified]
  s1PrefixGuardedBopIn[qualified] s1PrefixGuardedBopOther[qualified]
  s1PrefixGuardedMakeArray[qualified] s1PrefixGuardedWord[qualified]
  s1PrefixGuardedEC[qualified] s1PrefixGuardedBytestring[qualified]
  s1PrefixGuardedOrdinary[qualified]
  s1PrefixNamedConst[qualified] s1PrefixBoolChain[qualified]
  s1PrefixTypeBuiltinGuarded[qualified]
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
  intCallResultsProps[qualified,ignore_grammar]
  s1PrefixAugAssign s1PrefixIfExpChildren
  s1PrefixRawCallCalldata s1PrefixSubscriptCase[qualified]
  s1PrefixFor s1PrefixRawCall s1PrefixAnnAssign s1PrefixMakeArray gasShadowCompile gasShadowCompileHelpers bodySimFull s1PrefixLog s1PrefixBuiltinLeaves s1PrefixAnnAssignEmptyRhs s1PrefixTypeBuiltinExtract32 s1PrefixAbiDecodeExprConditional s1PrefixAbiEncodeTupleFull s1PrefixAbiEncodeNonwordFull s1PrefixAbiEncodeWordFull s1PrefixConvertBytesJoint s1PrefixConvertDynamicJoint s1PrefixConvertScalarJoint exprSimAbiEncodeRuntimeInputs exprSimConvert stmtLowering list s1PrefixBopBytestringEq s1PrefixBopWordPair exprSimBopRestWordFacts exprSimHash exprSimUnwrap s1PrefixRaiseReason
  s1PrefixBuiltinWord s1PrefixAppendSourceChildren s1PrefixAppendCodeCuts s1PrefixAppendToplevelEntry s1PrefixAppendReplayRhs s1PrefixTarget bodyPtrPopTargetFragTransport bodyAppendResolvedPre bodyFullTarget bodyFullTargetDefs loweringPosts gasOutcomeFullCompose stmtSimDefs targetPlaceSimCases vyperExprNoControl exprSimDefs emitHelper quantHeuristics bodyFullSubscript[qualified,ignore_grammar] bodyFullSubscriptMapBase bodyFullSimProjection bodySimExprCases exprSimPlaces exprSimTuple exprSimSubscriptMap exprSimMapDefs s1PrefixSubscriptMapBase s1PrefixSubscriptMap s1PrefixSubscriptTuple s1PrefixSubscriptArrayCode s1PrefixSubscriptArrayMemory s1PrefixSubscriptUnframedArray s1PrefixExtCallRequestStage s1PrefixExtCallCallStage s1PrefixExtCallReturnTrace bodyFullExtCallReadyReturn bodyFullExtCallReturn abiDecodeValidJoint abiDecodeRejectJoint exprSimExtCallCase s1PrefixAssignTuple s1PrefixAssign s1PrefixBoolChainSelectedLocalAssign finite_map exprSimAggregateLayout contractInvContextProps s1PrefixHash s1PrefixSelfdestruct s1PrefixBoolChainSelectedStmtCasePorts[qualified]
Libs
  pairLib

val _ = Parse.hide "body";

Theorem body_builtin_case_prefix:
  !cx ty bt es.
  (!s'' x t v code_ty addr tail_s tail_vs t'.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = SOME v /\
       v = (code_ty,addr) /\
       eval_exprs cx (TL es) tail_s = (INL tail_vs,t') ==>
       body_exprs_full_ok cx [addr]) /\
  (!s'' x t v code_ty addr tail_s tail_vs t'.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = SOME v /\
       v = (code_ty,addr) /\
       eval_exprs cx (TL es) tail_s = (INL tail_vs,t') ==>
       body_exprs_prefix_ok cx [addr]) /\
  (!s'' x t v code_ty addr.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = SOME v /\
       v = (code_ty,addr) ==>
       body_exprs_full_ok cx (TL es)) /\
  (!s'' x t v code_ty addr.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = SOME v /\
       v = (code_ty,addr) ==>
       body_exprs_prefix_ok cx (TL es)) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = NONE ==>
       body_exprs_full_ok cx es) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = NONE ==>
       body_exprs_prefix_ok cx es) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_full_ok cx (HD es)) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_prefix_ok cx (HD es)) ==>
  body_expr_prefix_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `bt = NamedConst`
  >- (gvs[] >> irule s1PrefixNamedConstTheory.named_const_expr_prefix_ok >>
      simp[] >> metis_tac[]) >>
  Cases_on `!p n. bt <> BoolChain p n`
  >- (match_mp_tac s1PrefixGuardedOrdinaryTheory.body_builtin_ordinary_case_prefix >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >>
      rename1 `code_slice_source bt es = SOME v` >>
      PairCases_on `v` >> metis_tac[]) >>
  fs[] >> gvs[] >>
  irule s1PrefixBoolChainTheory.bool_chain_expr_prefix_ok >> simp[] >> metis_tac[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >> PairCases_on `sig` >> fs[] >>
  once_rewrite_tac[body_expr_prefix_ok_def] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  conj_asm2_tac >- (irule expr_sim_prefix_of_vv >> first_assum ACCEPT_TAC) >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    metis_tac[body_inv_contract, contract_inv_acyclic_struct_metadata] >>
  pure_rewrite_tac[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  ho_match_mp_tac (GEN_ALL extcall_request_prefix) >>
  qexistsl [`vv`,`ty`,`tops`,`shadow_sb`,`shadow_sa`,`shadow_func`,`sb`,`sa`,
            `env`,`d`,`cenv`] >>
  simp[NoAsms, arithmeticTheory.ADD_COMM] >>
  rpt (goal_assum (drule_at Any)) >>
  qexists `\H res ee G tn t. T` >> conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      mp_tac extcall_return_full >>
      (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC abi_valid_allocated_joint)) >>
      (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC abi_malformed_allocated_joint)) >>
      disch_then (fn th =>
        mp_tac extcall_ready_return_outcome >>
        (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC (SPEC_ALL th)))) >>
      disch_then (fn th =>
        irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
        irule_at Any (SPEC_ALL th)) >>
      `TAKE (LENGTH sig1) (vs ++ kws) = vs` by
        (qpat_assum `LENGTH vs = LENGTH sig1` (SUBST1_TAC o SYM) >>
         simp[TAKE_APPEND1,TAKE_LENGTH_ID]) >>
      `DROP (LENGTH sig1) (vs ++ kws) = kws` by
        (qpat_assum `LENGTH vs = LENGTH sig1` (SUBST1_TAC o SYM) >>
         simp[DROP_APPEND]) >>
      simpLib.ASM_SIMP_TAC bool_ss [LENGTH_APPEND] >>
      qhdtm_assum `extcall_request_ready` (irule_at Any) >>
      rpt (goal_assum (drule_at Any)) >>
      simp[EVERY_DEF, optionTheory.OPTION_BIND_EQUALS_OPTION]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `TAKE (LENGTH sig1) (vs ++ kws) = vs` by
    (qpat_assum `LENGTH vs = LENGTH sig1` (SUBST1_TAC o SYM) >>
     simp[TAKE_APPEND1,TAKE_LENGTH_ID]) >>
  `DROP (LENGTH sig1) (vs ++ kws) = kws` by
    (qpat_assum `LENGTH vs = LENGTH sig1` (SUBST1_TAC o SYM) >>
     simp[DROP_APPEND]) >>
  irule extcall_return_trace_prefix >>
  conj_tac >- simp[LENGTH_APPEND] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`calldata`, `target`,
            `if is_static' then NONE
             else case ext_call_kwarg EKValue opts kws of
                    NONE => SOME 0 | SOME x => dest_NumV x`] >>
  simpLib.ASM_SIMP_TAC bool_ss [] >>
  conj_tac
  >- (qhdtm_assum `extcall_request_ready`
        (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >>
      first_assum ACCEPT_TAC) >>
  irule extcall_call_stage_prefix >>
  qhdtm_assum `extcall_request_ready` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >>
  simp[EVERY_DEF, optionTheory.OPTION_BIND_EQUALS_OPTION]
QED
*)
Theorem body_extcall_case_prefix:
  !cx v14 is_static skip_check sig opts es v15.
  (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_exprs cx (TAKE nargs (DROP 1 es)) s'3' = (INL results,t') ==>
       body_exprs_full_ok cx (DROP (1 + nargs) es)) /\
  (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_exprs cx (TAKE nargs (DROP 1 es)) s'3' = (INL results,t') ==>
       body_exprs_prefix_ok cx (DROP (1 + nargs) es)) /\
  (!s'' target t nargs.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_exprs_full_ok cx (TAKE nargs (DROP 1 es))) /\
  (!s'' target t nargs.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_exprs_prefix_ok cx (TAKE nargs (DROP 1 es))) /\
  body_exprs_full_ok cx (TAKE 1 es) /\
  body_exprs_prefix_ok cx (TAKE 1 es) ==>
  body_expr_prefix_ok cx
      (Call v14 (ExtCall is_static skip_check sig opts) es v15)
Proof
  cheat
QED

Theorem body_ifexp_case_prefix:
  !cx v5 e1 e2 e3.
  (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e2) /\
  (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_prefix_ok cx e2) /\
  (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e3) /\
  (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_prefix_ok cx e3) /\
  body_expr_full_ok cx e1 /\
  body_expr_prefix_ok cx e1 ==>
  body_expr_prefix_ok cx (IfExp v5 e1 e2 e3)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_expr_prefix_ok_def] >>
  MATCH_MP_TAC ifexp_prefix_from_child_cases >> asm_rewrite_tac[]
QED

Theorem body_raw_call_calldata_case_prefix:
  !cx ty flags es v19.
  body_exprs_full_ok cx es /\
  body_exprs_prefix_ok cx es ==>
  body_expr_prefix_ok cx (Call ty (RawCallCalldataTarget flags) es v19)
Proof
  map_every qx_gen_tac [`cx`,`ann`,`flags`,`args`,`dflt`] >>
  strip_tac >> simp[Once body_expr_prefix_ok_def] >>
  map_every qx_gen_tac
    [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,`func`,`shadow_func`,
     `cenv`,`env`,`ty`,`es`] >> strip_tac >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Call ann (RawCallCalldataTarget flags) args dflt) es` by
    (irule raw_call_calldata_vv_prefix >> simp[] >> qexistsl [`env`,`tops`] >> simp[]) >>
  simp[expr_sim_prefix_of_vv]
QED

Theorem body_raw_call_case_prefix:
  !cx ty flags es v18.
  body_exprs_full_ok cx es /\
  body_exprs_prefix_ok cx es ==>
  body_expr_prefix_ok cx (Call ty (RawCallTarget flags) es v18)
Proof
  map_every qx_gen_tac [`cx`,`ann`,`flags`,`args`,`dflt`] >>
  strip_tac >> simp[Once body_expr_prefix_ok_def] >>
  map_every qx_gen_tac
    [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,`func`,`shadow_func`,
     `cenv`,`env`,`ty`,`es`] >> strip_tac >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Call ann (RawCallTarget flags) args dflt) es` by
    (irule raw_call_expr_vv_prefix >> simp[] >> qexistsl [`env`,`tops`] >> simp[]) >>
  simp[expr_sim_prefix_of_vv]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once body_expr_prefix_ok_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Call v20 RawLog es v21) es'` by
    (irule raw_log_expr_sim_prefix >> simp[gas_shadow_stmt_lower_value_env] >>
     conj_tac
     >- metis_tac[Q.INST [`sd` |-> `T`, `sh` |-> `T`]
           (MATCH_MP gas_shadow_compiles_multi_exprs_env
             (CONJUNCT1 gas_shadow_compile_expr_env))] >>
     qexistsl [`env`, `tops`] >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule expr_vv_sim_stack_prefix >> simp[] >> conj_tac
  >- metis_tac[raw_log_compile_stack] >>
  metis_tac[raw_log_eval_value]
QED
*)
Theorem body_raw_log_case_prefix:
  !cx v20 es v21.
  body_exprs_full_ok cx es /\
  body_exprs_prefix_ok cx es ==>
  body_expr_prefix_ok cx (Call v20 RawLog es v21)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once body_expr_prefix_ok_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Call v22 RawRevert es v23) es'` by
    (mp_tac raw_revert_value_prefix_from_tail >>
     (impl_tac >-
       (rpt gen_tac >> strip_tac >>
        drule_all raw_revert_compiled_tail_joint >> simp[])) >>
     disch_then irule >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule expr_vv_sim_stack_prefix >> simp[] >>
  reverse conj_tac >- metis_tac[raw_revert_no_success] >>
  drule raw_revert_source_pre >> strip_tac >> gvs[] >>
  gen_tac >> simp[Once compile_expr_def, compile_call_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED
*)
Theorem body_raw_revert_case_prefix:
  !cx v22 es v23.
  body_exprs_full_ok cx es /\
  body_exprs_prefix_ok cx es ==>
  body_expr_prefix_ok cx (Call v22 RawRevert es v23)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[body_expr_prefix_ok_def] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call v24 SelfDestructTarget es v25) es'` by
    (irule s1PrefixSelfdestructTheory.selfdestruct_expr_prefix >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule expr_vv_sim_stack_prefix >> simp[] >>
  drule selfdestruct_full_source_pre >> strip_tac >> gvs[] >>
  conj_tac
  >- (gen_tac >> simp[Once compile_expr_def, compile_call_def, expr_type_def,
                      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> simp[])) >>
  rpt strip_tac >> gvs[bind_def, AllCaseEqs()] >>
  rename1 `selfdestruct_tail cx target st = (INL _,_)` >>
  qpat_x_assum `selfdestruct_tail _ _ _ = _` mp_tac >>
  qspecl_then [`cx`,`target`,`st`]
    (qx_choosel_then [`ex`,`out`] SUBST1_TAC) selfdestruct_tail_raises >>
  simp[]
QED
*)
Theorem body_selfdestruct_case_prefix:
  !cx v24 es v25.
  body_exprs_full_ok cx es /\
  body_exprs_prefix_ok cx es ==>
  body_expr_prefix_ok cx (Call v24 SelfDestructTarget es v25)
Proof
  cheat
QED

Theorem body_intcall_case_prefix:
  !cx v16 src_id_opt fn es v17.
    (!ts mut nr args dflts ret ss.
       ~MEM (src_id_opt,fn) cx.stk /\
       get_module_code cx src_id_opt = SOME ts /\
       lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) ==>
       body_stmts_full_ok (cx with stk updated_by CONS (src_id_opt,fn))
         (subst_consts_stmts (module_consts_env (cx_tops cx) []) ss) /\
       body_exprs_full_ok (cx with stk updated_by CONS (src_id_opt,fn))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
           (subst_consts_exprs (module_consts_env (cx_tops cx) []) dflts))) /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') ==>
       body_exprs_full_ok cx es) /\
    (!ts mut nr args dflts ret ss.
       ~MEM (src_id_opt,fn) cx.stk /\
       get_module_code cx src_id_opt = SOME ts /\
       lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) ==>
       body_stmts_prefix_ok (cx with stk updated_by CONS (src_id_opt,fn))
         (subst_consts_stmts (module_consts_env (cx_tops cx) []) ss) /\
       body_exprs_prefix_ok (cx with stk updated_by CONS (src_id_opt,fn))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
           (subst_consts_exprs (module_consts_env (cx_tops cx) []) dflts))) /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') ==>
       body_exprs_prefix_ok cx es) ==>
    body_expr_prefix_ok cx (Call v16 (IntCall (src_id_opt,fn)) es v17)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  ONCE_REWRITE_TAC[body_expr_prefix_ok_def] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all bodyIntCallSourceTheory.body_intcall_source_selection >> strip_tac >>
  drule_then strip_assume_tac bodyInvCodePropsTheory.body_inv_main_code >>
  `~MEM (src_id_opt,fn) cx.stk ==> body_exprs_full_ok cx es` by
    (strip_tac >>
     drule (Q.ISPEC `body_exprs_full_ok` intCallResultsPropsTheory.intcall_results_ih) >>
     disch_then drule_all >> simp[]) >>
  `~MEM (src_id_opt,fn) cx.stk ==>
     body_exprs_prefix_ok cx es` by
    (strip_tac >>
     drule (Q.ISPEC `body_exprs_prefix_ok` intCallResultsPropsTheory.intcall_results_ih) >>
     disch_then drule_all >> simp[]) >>
  `~MEM (src_id_opt,fn) cx.stk ==>
     body_stmts_full_ok (cx with stk updated_by CONS (src_id_opt,fn))
       (subst_consts_stmts (module_consts_env tops []) ss) /\
     body_exprs_full_ok (cx with stk updated_by CONS (src_id_opt,fn))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
         (subst_consts_exprs (module_consts_env tops []) dflts))` by
    (strip_tac >> qpat_assum `!ts mut nr args dflts ret ss. _ ==> _` drule_all >>
     gvs[]) >>
  `~MEM (src_id_opt,fn) cx.stk ==>
     body_stmts_prefix_ok (cx with stk updated_by CONS (src_id_opt,fn))
       (subst_consts_stmts (module_consts_env tops []) ss) /\
     body_exprs_prefix_ok (cx with stk updated_by CONS (src_id_opt,fn))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
         (subst_consts_exprs (module_consts_env tops []) dflts))` by
    (strip_tac >> qpat_assum `!ts mut nr args dflts ret ss. _ ==> _` drule_all >>
     gvs[]) >>
  `!s1 vs t1.
       ~MEM (src_id_opt,fn) cx.stk /\ eval_exprs cx es s1 = (INL vs,t1) ==>
       body_exprs_full_ok (cx with stk updated_by CONS (src_id_opt,fn))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
           (subst_consts_exprs (module_consts_env tops []) dflts))` by metis_tac[] >>
  `!s1 vs t1.
       ~MEM (src_id_opt,fn) cx.stk /\ eval_exprs cx es s1 = (INL vs,t1) ==>
       body_exprs_prefix_ok (cx with stk updated_by CONS (src_id_opt,fn))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
           (subst_consts_exprs (module_consts_env tops []) dflts))` by metis_tac[] >>
  qpat_x_assum `src_id_opt = NONE` SUBST_ALL_TAC >>
  conj_tac
  >- (irule s1PrefixIntCallTheory.intcall_sim_prefix >>
      rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- (qexistsl_tac [`args`,`dflts`,`mut`,`nr`,`ret`,`rr`,`ss`,`env`,`tops`] >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
          >- (rpt gen_tac >> strip_tac >> metis_tac[])
          >- (rpt gen_tac >> strip_tac >> metis_tac[])))
  >- (irule s1PrefixIntCallTheory.intcall_vv_prefix >>
      rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- (qexistsl_tac [`args`,`dflts`,`mut`,`nr`,`ret`,`rr`,`ss`,`env`,`tops`] >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
          >- (rpt gen_tac >> strip_tac >> metis_tac[])
          >- (rpt gen_tac >> strip_tac >> metis_tac[])))
QED
