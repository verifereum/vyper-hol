(*
 * Assignment to a base target over the finite-horizon joint judgment.
 * Stated over the finite-horizon full family (bodySimFull), one sub-shape
 * per S1 dispatch arm of bodySimStmtCases/bodySimDeclCases, so the case in
 * bodyFullCases closes by the same case split.
 *
 * TOP-LEVEL: the body_*_full sub-shape theorems below.
 *)
Theory bodyFullAssign
Ancestors bodySingletonCallSupport immutableBytestringPath bodyImmutableStoreMemory[qualified,ignore_grammar]
  placeDestinationBounds[qualified,ignore_grammar]
  assignPlaceProvenance[qualified,ignore_grammar]
  exprSimLayoutTransport[qualified,ignore_grammar]
  exprSimIfExpWidenedAggregate[qualified,ignore_grammar]
  bodyFullShadowBodyInv bodyFullIfExpReach bodyFullAssignImmutableEmpty
  immutableWordStorePath[qualified,ignore_grammar]
  bodyFullPreds bodySimFull bodyFullShared gasShadow bodySim exprSimHypsDefs supportedStmts
  compileEnv exprLowering stmtLowering vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map
  bodyFullAssignAttrStorage bodyExprPreFacts bodyStorageMetadata bodyTypedTargetScope
  bodyInvCodeProps bodyInvExecutionProps bodyInvMetadataProps bodyInvIntCallPinsProps
  bodyInvSplit contractInvContextProps exprBodyPreProps exprBodyPreCallSafetyProps
  compileUnit linkedStorageMetadataProps stmtExprAllocationPreProps
  immutableRegionFrameProps immutableRegionTypingProps moduleVariableKeyProps
  bodyFullAssignToplevelSetup bodyFullAssignToplevelTail bodyFullAssignTopCopyTail
  augAssignFullTargetRoutes[qualified,ignore_grammar]
  bodyFullAssignToplevelCode bodyFullAssignToplevelSource exprSimSliceCompose
  gasOutcomeFullCompose exprSimTopLevelProps vyperStorageFootprint
  vyperStorageTrace exprLoweringProps loweringStateRelDefs
  bodyFullAssignLocalSetup bodyFullAssignLocalSource bodyFullAssignLocalTail
  bodyFullMemoryFrames bodyFullMemoryCopy bodyFullMemoryStore
  bodyFullLocalCopy bodyFullMemoryStage bodyFullAssignMemoryCompose
  bodyFullAssignMemoryValue assignRelayoutCaller assignRelayoutFrag
  assignBasePtrLocalBodyFacts stmtSimAssign stmtSimAssignStore
  gasShadowCompileStmtHelpers gasShadowState stmtSimAssignSource loweringPosts
  stmtSimAssignAttr exprSimFieldLayout exprSimHyps exprSimSource
  supportedExprForms supportedExprs supportedExprTraverse supportedStmtTraverse
  vyperTypeEnv vyperTypeInvariants vyperTypeContractStaticMaps
  compileVyper supportedDecls gasContext vyperTypeCallGraph
  allocationPtr annassignRelayoutFrag annassignRelayoutSource arithmetic
  assignRelayoutSource bodyFullHashKeccakFixed exprOpenTerminals
  exprOperandVar exprSimAggregateChildren exprSimProps freshWrites
  memoryLocalRhsProps pair stmtLoweringMono stmtSimDeclTypedCode stmtSimProps
  sum venomState memoryPlaceStorePost stateRelProj
  stmtSimAssignStorage augAssignFullStore augAssignFullWriteback[qualified,ignore_grammar] bodyPtrDefs stmtSimDefs
  ptrDiscipline wordLoadStorePtr vyperStorageBackend
  placeMemoryFieldRebuild assignTuplePtrStoreWord stmtSimDeclStore targetPlaceSim
  tupleTargetStoreProps
  bodyMemoryDefs fragExec fragGasOriginPtrExec exprSimDefs haltExitProj
  valueEncodingProps fragGasOriginPtr venomInst memSafeRun vyperLookup
  vyperTypeStatePreservation valueEncodingProofs
  bodyFullAttributeAdd bodyFullUnwrapWord bodyFullUnwrapRun exprSimVVFrame
  exprSimMemDefs assignBasePtrOffset emitHelperProps emitHelper fragGasSeqPtr
  exprPtrUnwrapCopyEdges instMemFrontier context venomExecSemantics
  valueEncoding representationCleanPtr targetPlaceSimCasesBase gasOutcomeFull gasStorage
  vyperTypeExprResult vyperTypeExprSoundness vyperTypeValues vyperTyping bodyMemAssignTopCopyFacts bodySimStmtFacts
  stmtSimAssignStorageCopy supportedProgram vyperLookupStorage option bodyDeclMemoryCore[qualified,ignore_grammar] stmtSimAssignStorageSparse[qualified,ignore_grammar]
  vyperStoragePlaceRegion[qualified,ignore_grammar]
  bodyFullAssignLocalEmpty bodyFullAssignLocalCopyFrame bodyFullAssignMemoryPlace
  abiEncodeArgsSim aggregateEvaluatedLayout assignBasePtrBoundary[qualified,ignore_grammar]
  bodyFullPathHistory bodyFullStructLitPhysical bodyFullTargetDefs
  bodyFullImmutablePathStore
  bodyPtrTypeBuiltinsMemoryBounds[qualified,ignore_grammar] exprSafeOperand
  exprSimExtract32Post[qualified,ignore_grammar] exprSimWordArgs immutableDeployAssignRanges
  immutableDeployPhysicalSource placeMemoryCopyEffect reasonCopySourcePtr stmtSimAssignMem
  stmtSimDeclMem typedCopyCompatibility[qualified,ignore_grammar] typedMemoryCopy
  typedStoreCode[qualified,ignore_grammar] valueCopyBytes valueEncodingTyping vfmConstants
  words
  stmtSimAugAssignPlaceStorage[qualified,ignore_grammar]
  bodySimAugPlaceLoad[qualified,ignore_grammar]
  bodyFullStoreSlotsPath
  bodyFullStoreSlotsStatic
  stateRelProjStorage
  gasExemptCert
  exprSimUnwrap
  stmtSimAssignStorageFacts
  placeStore
  venomMemProofs
  bodyPtrPrecompileBuiltinsArithmeticValue
  vyperTypeDefaults
  annassignRelayoutCode
  assignRelayoutFrame
  bodyMemBopRestWordPath
  fragGasOrigin
  fragGasMode
  fragGasPath
  assignTuplePtrCopyLen
  localPtrsProps
  venomMemDefs
  assignPlaceDirectCopy
  placeMemoryStateRebuild
  placeMemoryPathRebuild
  placeMemoryLiveRegion
  immutableWordExecution immutableRepSensitivity[qualified,ignore_grammar]
  decoderGhostFramePtr
  ghostPcTransportPtr
  bodyFullGhostFrame
  allocaHistory
  ASCIInumbers
  pred_set
  venomExecProofs
  rich_list
  bodyFullUnwrap
  assignEffectfulIndexPhysical
  stmtSimLogCompose
  bodyMemSnapshotSourceLocation
  ctorDeployDeadSectionFrame
  ctorDeployDeadSection
  immSectionDead
  typedCopyOriginPtrBase
  exprSimStorageCopy
  codegenRel
  exprPtrCtorImmStore
  bodyBinopFragMemory
  exprSimCopy
  fragGasOriginPtrDead
  typedCopyOriginPtrDynArray
  stmtReasonLitFragMemory
  immutableDeployOperandTransfer
  immutableCopyExecution
  fragExecMem
  unitTransformDefs
  contextCodegenRel
  bodyPtrBytestringBuiltinsUintGhost
  allocaFootprint
  bytestringCopyExecution
  decoderSetupStepPtr
  ptrSafeRun
  memLocDefs
  abiEncoderWindowLookup[qualified,ignore_grammar]
  exprReasonOperand
  valueEncodingDefs
  alist
  typedCopyOriginPtr
  robustCopyTransportPtr
  exprSimAlloc
  abiDecodeStaticProps
  assignPlaceLayout
  bodyPtrMakeArrayCopyStateFrame
  exprSimPtrLiteralBuffer
  exprSimAggregateEncoding
  bodyDynArraySource
  vyperTypeArgFits
  immutableAssignCompose immutableDeployAssignPathGhost immutableCopyWordsPath
  immutableAssignStore
  immutableDeployAssignRestore
  immutableBytestringFootprint
  immutableDeployAssignTransfer
  immutableBytestringRuntime
  fragGasCopyLoop
  fragGasSeqAbort
  immutableAssignEmpty
  abiEncoderProps
  immutableDeployAssignFacts
  bodyPtrBytestringBuiltinsWindowGhost
  abiCanonicalHeadSize
  abiStaticAggregateProps
  bodyFullToplevelCtorSourceLayout
  immutableDeployAssignSourceFrame
  bodyImmutableAugAssignStore
  bodyImmutableAugAssignExec
  immutableAssignCode
  immutableAssignMetadata
  assignEffectfulIndexCode[qualified]
  gasShadowCompileStmtBase
  immutableRelation
  vyperPlaceFrames
  structFieldsProps
  byte
  bodyFullAllocaFresh
  abiEncodeMaterialize
  allocLimits
  bodyPtrIfExpAllocSource
  bodyPtrBopRepresentationFrame
  logValueFramePtr
  revertReasonPrefixPtr
  immutableDeployAssignAdmissible
  ghostObservationPtr
  immutableDeployAssignBytes
  bodyFullAllocGeneric
  bodyCopyMemoryBase
  exprSimBufferStore
  bodyPtrIfExpCopyHeader
  bodyPtrIfExpBytesPost
  bytesCopyCode
  eventTopicValueProps
  valueTypingMemoryProps
  memoryValueEncoding
  tuplePlaceStep
  assignTuplePtrLocalFixedCopy
  reasonTupleCopyPtr
  fragGasSeqPtrContext
  logInstSeqPtr[qualified,ignore_grammar]
  exprPtrUnwrapScalarEdges
  exprPtrUnwrapScalarSegments
  exprPtrUnwrapOffsetSegment
  exprPtrUnwrapLoopInvariant
  instSeqComposePtr
  instIdxIndep
  typedCopyPtr
  ssaOperandFrame
  exprPtrCtorCodeLoad
  vyperFiniteStoragePreservation
  vyperTypeSoundness
  vyperTypeExtCallCore
  accountsRelProps
  vyperStoragePlaceObserved
  entryStateRel
  bodyAugPlaceTarget
  vyperPlaceMutationSoundness
  exprSimPopNestedBase
  vyperPlaceResultTyping
  exprPtrUnwrapStorageFacts
  sourceUnitExecution
  bool[qualified,ignore_grammar]
  exprPtrUnwrapFrames[qualified,ignore_grammar]
  exprBopSimProps
  targetPureWalkSource
  targetPureWalkScopes
  targetPurePostTransport
  supportedTypes
  gasShadowCompilePure
  immutableDeployAssignExecution[qualified,ignore_grammar]
  varsExt[qualified,ignore_grammar]
  forPtrAllocationFrame[qualified,ignore_grammar]
  bodyLiteralBufferMemory
  ctorAbiActualObservations
  wordArgsPtr
  gasOriginPtrLabels
  bodyFullTarget
  gasOutcomeFullGuarded
  popTargetPre
  exprSimMemorySource
  targetPlaceSimCases
  vyperExprNoControl
  supportedTargets
  allocLimitsProps
  vyperTypeCallStackSoundness
  targetPlaceLive
  gasShadowCompileHelpers[qualified]
  gasShadowCompileConvert[qualified]
  gasSummary
  placeStoreStorage
  fragGasOriginPtrLoop
Libs
  monadsyntax

val _ = Parse.hide "body";

(* The successful Assign RHS determines both the source local layout and
   the scalar operand used by the joint tail. *)

Theorem body_assign_local_word_full_rhs[local]:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\ expr_body_pre cenv cx env e es /\
  FLOOKUP env.var_types id = SOME (expr_type e) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  is_word_type (expr_type e) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gs ++ tail) = (INL v,mid with gas_obs := tail)) /\
  expr_post H ctx func cenv cx e es sa sm s0 (mid with gas_obs := []) v op t /\
  ptr_val_ok cx (expr_type e) v op G tn t ==>
  ?pre sc entry rest dst.
    find_containing_scope id mid.scopes = SOME (pre,sc,entry,rest) /\
    entry.assignable /\ store_lays_out entry.type entry.type v /\
    eval_operand op t = SOME (typed_val_to_w256 entry.type v) /\
    op_taint tn op = {} /\ lookup_var p t = SOME dst
Proof
  strip_tac >> drule_all assign_local_continuation_all_tails >> strip_tac >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs ++ [])` by simp[] >>
  drule exprSimSourceTheory.expr_body_pre_eval >>
  disch_then (qspecl_then [`INL v`,`mid with gas_obs := []`] mp_tac) >>
  (impl_tac >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
    qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[])) >> strip_tac >>
  `lookup_scopes id mid.scopes = SOME entry` by
    metis_tac[vyperLookupTheory.find_containing_scope_lookup] >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME entry.type` by
    (drule_all targetPlaceSimTheory.expr_sim_inv_local >> simp[] >> metis_tac[]) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
  `value_has_type entry.type v` by
    fs[vyperTypeExprResultTheory.expr_result_typed_def,
       vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
       vyperTypeInvariantsTheory.value_result_typed_def] >>
  `store_lays_out entry.type entry.type v` by
    metis_tac[stmtSimDeclStoreTheory.store_lays_out_typed] >>
  `post_value_type cenv e = expr_type e` by simp[] >>
  `eval_operand op t = SOME (typed_val_to_w256 entry.type v)` by
    (fs[expr_post_def,expr_val_rel_def] >> metis_tac[]) >>
  `op_taint tn op = {}` by fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  `local_ptrs_rel func cenv mid.scopes t` by
    (fs[expr_post_def] >>
     metis_tac[stmt_state_rel_local_ptrs_alloca]) >>
  `?dst. lookup_var p t = SOME dst` by
    metis_tac[allocaFootprintTheory.local_ptr_below_frontier] >>
  rename1 `find_containing_scope _ _ = SOME (_,sc,_,_)` >>
  qexistsl_tac [`pre`,`sc`,`entry`,`rest`,`dst`] >> simp[]
QED

(* A single RHS endpoint is extended by the same scalar store at every horizon. *)

Theorem body_assign_local_word_full_continue[local]:
  stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e) sa = (cenv,sb) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  cenv.ce_var_type id = SOME (expr_type e) /\ is_word_type (expr_type e) /\
  FLOOKUP env.var_types id = SOME (expr_type e) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  expr_body_pre cenv cx env e es /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel (H0 : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s0 /\
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (res,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) marks (OK t,G1,tn1) /\
    (?v. res = INL v /\ expr_post H ctx func cenv cx e es sa sm s0
       (mid with gas_obs := []) v op t /\
      expr_store_bound cx (expr_type e) v op t /\
      t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G1 tn1 t /\
      ptr_val_ok cx (expr_type e) v op G1 tn1 t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1) /\
    (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?ce.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
      cenv_top_ext cenv ce ee.scopes /\ stmt_state_rel H ctx func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d ce sb t /\
      alloca_history func t /\ return_buf_sep d ce ee t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 ce ee t /\
      (!aid off sz i.
        FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
          off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)) R
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  simp[NoAsms] >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  drule_all body_assign_local_word_full_rhs >> strip_tac >>
  rename1 `find_containing_scope _ _ = SOME (pre,sc,entry,rest)` >>
  `~t.vs_halted` by
    (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[fragExecTheory.exit_result_def]) >>
  irule body_assign_local_word_full_normal >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`G1`,`mid`,`entry`,`marks`,`pre`,`rest`,`t`,`sc`,
    `(mstore (w2n dst) (typed_val_to_w256 entry.type v) t) with
      vs_inst_idx := SUC t.vs_inst_idx`,
    `step_taint (mk_inst sm.cs_next_id MSTORE [Var p;op] []) t
      (mstore (w2n dst) (typed_val_to_w256 entry.type v) t) tn1`,`tn1`,`v`] >>
  simp[] >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  simp[NoAsms] >> (impl_tac >- simp[]) >> strip_tac >>
  `dead_lo_ok H (DF H) lo cenv cx` by simp[] >>
  `find_containing_scope id (mid with gas_obs := []).scopes = SOME (pre,sc,entry,rest)` by simp[] >>
  drule_all body_assign_local_word_full_tail >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  strip_tac >> gvs[vyperStateTheory.evaluation_state_fupdcanon] >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
       (qspec_then `[]` (mp_then Any mp_tac eval_read_preserves_scopes_dom)) >>
     simp[]) >>
  `MAP FDOM (pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) =
     MAP FDOM es.scopes` by
    (qpat_assum `find_containing_scope id mid.scopes = SOME (pre,sc,entry,rest)`
       (mp_then Any mp_tac tupleTargetStorePropsTheory.tuple_target_local_domain_frame) >>
     disch_then (qspec_then `v` mp_tac) >> simp[]) >>
  `return_buf_sep d ce
     (mid with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
     ((mstore (w2n dst) (typed_val_to_w256 entry.type v) t) with
       vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
     conj_tac
     >- (simp_tac (srw_ss()) [allocas_from_def, mstore_def] >>
         qpat_assum `!bw cap. d = SOME (bw,cap) ==> allocas_from (cap + w2n bw) t`
           (ACCEPT_TAC o REWRITE_RULE [allocas_from_def] o
            ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM])) >>
     qexistsl_tac [`H0`, `ctx`, `cx`, `es`, `func`, `s0`, `sa`] >>
     fs[expr_post_def, lookup_var_def, mstore_def]) >>
  `(mid with <|scopes := pre ++ (sc |+
       (id,entry with <|value := v; popped := []|>)) :: rest; gas_obs := []|>) =
    (mid with scopes := pre ++ (sc |+
       (id,entry with <|value := v; popped := []|>)) :: rest) with gas_obs := []` by
    simp[vyperStateTheory.evaluation_state_fupdcanon] >>
  `return_buf_sep d ce
     (mid with <|scopes := pre ++ (sc |+
       (id,entry with <|value := v; popped := []|>)) :: rest; gas_obs := []|>)
     ((mstore (w2n dst) (typed_val_to_w256 entry.type v) t) with
       vs_inst_idx := SUC (LENGTH sm.cs_current_insts))` by
    (qpat_assum `_ = (mid with scopes := _) with gas_obs := []` SUBST1_TAC >>
     qpat_assum `t.vs_inst_idx = LENGTH sm.cs_current_insts` (fn eq =>
       qpat_assum `return_buf_sep d ce (mid with scopes := _) _`
         (mp_tac o PURE_REWRITE_RULE [eq])) >>
     simp[return_buf_sep_gas_obs]) >>
  asm_rewrite_tac[] >>
  reverse conj_tac
  >- (drule_all wordLoadStorePtrTheory.mstore_ghost_frame >> strip_tac >>
      fs[bodyPtrDefsTheory.ghost_kept_at_def, pred_setTheory.IN_DIFF] >>
      rpt strip_tac >>
      qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
        (qspecl_then [`aid`,`off`,`sz'`,`i`] mp_tac) >>
      simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `alloca_frame ce es sa s0 ce (mid with gas_obs := []) t` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ _`
       (mp_then Any irule stmtSimDefsTheory.alloca_frame_of_mem_frame) >>
     fs[expr_post_def] >> first_assum ACCEPT_TAC) >>
  `lookup_scopes id mid.scopes = SOME entry` by
    metis_tac[vyperLookupTheory.find_containing_scope_lookup] >>
  `local_ptrs_rel func ce mid.scopes t` by
    (fs[expr_post_def] >> metis_tac[stmt_state_rel_local_ptrs_alloca]) >>
  `32 <= sz` by
    (fs[local_ptrs_rel_def, stmtSimDeclStoreTheory.store_lays_out_def] >>
     first_x_assum (qspecl_then [`id`,`entry`,`p`,`sz`] mp_tac) >> simp[]) >>
  `local_region ce (mid with gas_obs := []).scopes t id (w2n dst) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  irule stmtSimDefsTheory.alloca_frame_region_write >>
  goal_assum (drule_at Any) >>
  simp[] >>
  conj_tac >- simp[venomStateTheory.mstore_def, venomStateTheory.lookup_var_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> decide_tac) >>
  qpat_assum `MAP FDOM (pre ++ (sc |+ _) :: rest) = MAP FDOM es.scopes` mp_tac >>
  simp[]
QED

(* A word local. *)
Theorem body_assign_local_word_full:
  !cx id ty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (NameTarget id)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME ty /\
    is_word_type ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_local_rhs_pre >> strip_tac >>
  `expr_type e = ty` by metis_tac[type_widens_to_word] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty e es` by metis_tac[body_expr_full_ok_def] >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    metis_tac[expr_sim_inv_def] >>
  `cenv.ce_var_type id = SOME ty` by metis_tac[expr_sim_inv_def] >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  conj_tac >- simp[] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by
    metis_tac[] >>
  `is_word_type (expr_type e)` by simp[] >>
  gvs[] >> drule_all assign_local_word_code_parts >> strip_tac >> gvs[] >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (op,sm)` >>
  `?shadow_sm. lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa = (op,shadow_sm) /\
       gas_shadow_state sm shadow_sm` by
    (`FST (lower_value compile_expr cenv (expr_type e) e sa) =
       FST (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
         (gas_shadow_expr e) shadow_sa) /\
       gas_shadow_state (SND (lower_value compile_expr cenv (expr_type e) e sa))
         (SND (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
           (gas_shadow_expr e) shadow_sa))` by
       (irule (REWRITE_RULE [gas_shadow_compiles_def]
          (Q.INST [`sd` |-> `T`] gas_shadow_stmt_lower_value_env)) >> simp[]) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa` >> gvs[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     simp[gas_shadow_stmt_def,gas_shadow_assignment_def,gas_shadow_expr_def] >> strip_tac >>
     qpat_x_assum `stmt_env _ _ _ (Assign _ e) sa = _` kall_tac >>
     `is_word_type (expr_type (gas_shadow_expr e))` by simp[gas_shadow_expr_type] >>
     `FLOOKUP (gas_shadow_env T cenv).ce_vars id = SOME (PtrVar (Var p) sz)` by simp[] >>
     `(gas_shadow_env T cenv).ce_var_type id = SOME (expr_type (gas_shadow_expr e))` by
       simp[gas_shadow_expr_type] >>
     drule_all assign_local_word_code_parts >> strip_tac >> gvs[gas_shadow_expr_type] >>
     metis_tac[]) >>
  `gas_shadow_state sm shadow_sm` by first_assum ACCEPT_TAC >>
  drule assign_local_admissible_rhs >> strip_tac >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,
    `op`,`s0`,`G0`,`tn0`] mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (fn outcome =>
    qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
      qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
        assume_tac (MATCH_MP gas_outcome_full_return_buf_allocas
          (LIST_CONJ [outcome,frame,sep]))))) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q1 _` >>
  irule body_assign_local_word_full_source >>
  conj_tac >- metis_tac[] >> qexists_tac `Q1` >>
  reverse conj_tac >- (irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
    goal_assum (drule_at Any) >> simp[] >> rpt gen_tac >>
    POP_ASSUM_LIST (K all_tac) >> strip_tac >>
    Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def] >>
    Cases_on `y` >> Cases_on `r` >>
    gvs[bodyPtrDefsTheory.stmt_exit_ptr_def,exprSimDefsTheory.expr_exit_def,
        exprSimDefsTheory.halt_exit_def] >>
    rename1 `Error err` >> Cases_on `err` >>
    gvs[exprSimDefsTheory.expr_exit_def]) >>
  rpt gen_tac >> strip_tac >>
  irule body_assign_local_word_full_continue >>
  goal_assum (drule_at Any) >> simp[Abbr `Q1`] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (qexistsl_tac [`G1`,`marks`,`mid`,`res`,`t`,`tn1`] >>
      asm_rewrite_tac[] >> qx_gen_tac `H'` >> disch_tac >>
      qpat_assum `valid_horizon cx st0 H' mid.storage_trace` (fn vh =>
        qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> _`
          (qspec_then `H'` (mp_tac o BETA_RULE o C MP vh))) >>
      simp_tac (srw_ss()) [arithmeticTheory.ADD_COMM]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexists_tac `storage_trace_horizon es.storage_trace` >> metis_tac[]
QED

fun assign_main_keys inv =
  MATCH_MP contract_inv_module_distinct_keys
    (CONJ (MATCH_MP body_inv_contract inv) (MATCH_MP body_inv_module inv))

Theorem body_assign_main_type_env[local]:
  body_inv tops ctx cenv cx ==> get_tenv cx = type_env tops
Proof
  disch_then (mp_tac o MATCH_MP contract_inv_type_env o MATCH_MP body_inv_contract) >>
  simp[type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2]
QED

Theorem body_assign_widened_success_resources[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  expr_body_pre cenv cx env e es /\ supported_expr tops e /\
  FLOOKUP env.var_types id = SOME ty /\
  type_widens_to env.type_defs (expr_type e) ty /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\
  post_value_type cenv e = lowered_value_type cenv e /\
  lowered_value_type cenv e <> expr_type e /\
  ~is_word_type (lowered_value_type cenv e) /\
  ~is_bytestring_type (lowered_value_type cenv e) /\
  0 < type_memory_size stv /\ type_memory_size stv <= type_memory_size dtv /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sB) /\
  local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix ++ tail) =
     (INL v,mid with gas_obs := tail)) /\ mid.gas_obs = [] /\
  expr_post H ctx func cenv cx e es sa sB s0 mid v op u /\
  ptr_val_ok cx (post_value_type cenv e) v op Gi ti u /\
  ghost_inv_at D lo d cenv cx mid Gi ti u /\ dead_lo_ok H D lo cenv cx ==>
  ?pre sc ent rest xs sw dw.
    find_containing_scope id mid.scopes = SOME (pre,sc,ent,rest) /\
    ent.assignable /\ ent.type = dtv /\
    (!tail. write_place cx (MemoryPlace id []) v (mid with gas_obs := tail) =
      (INL (), (mid with scopes := pre ++ (sc |+ (id,ent with <|value := v; popped := []|>)) :: rest)
         with gas_obs := tail)) /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    op = Var xs /\ not_fresh_at sB xs /\ not_fresh_at sB p /\
    lookup_var xs u = SOME sw /\ lookup_var p u = SOME dw /\
    (!mem. mem_agree_outside ti.t_mem u.vs_memory mem ==> val_in_memory stv v (w2n sw) mem) /\
    ptr_covers Gi ti xs u (type_memory_size stv) /\
    ptr_covers Gi ti p u (type_memory_size dtv) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
    (w2n sw + type_memory_size stv <= w2n dw \/ w2n dw + type_memory_size dtv <= w2n sw) /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\ lo <= w2n dw /\
    type_memory_size dtv <= cap /\ local_ptrs_reserved cenv sB /\
    expr_val_at cenv cx (lowered_value_type cenv e) sa sB mid v (Var xs) u /\
    (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sB x) /\
    (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sB x)
Proof
  strip_tac >>
  drule_all assign_local_continuation_all_tails >>
  disch_then (qx_choosel_then [`pre`,`sc`,`ent`,`rest`] strip_assume_tac) >>
  `lookup_scopes id mid.scopes = SOME ent` by
    metis_tac[find_containing_scope_lookup] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid)` by
    (`mid with gas_obs := [] = mid` by
       simp[evaluation_state_component_equality] >>
     qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[]) >>
  `ent.type = dtv` by
    metis_tac[memory_rhs_read_local_type, exprSimSourceTheory.expr_body_pre_gas_obs, ETA_THM] >>
  `value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
   val_footprint stv v = type_memory_size stv` by
    (drule_then strip_assume_tac body_inv_main_support >>
     drule_then (assume_tac o SIMP_RULE (srw_ss()) [build_func_return_type_mods_singleton] o
       MATCH_MP contract_inv_return_types) body_inv_contract >>
     drule_all (REWRITE_RULE [ETA_THM] annassign_relayout_read_layout) >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx mid u` by fs[expr_post_def] >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  qpat_assum `local_ptrs_rel func cenv mid.scopes u`
    (mp_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
  disch_then (qspecl_then [`id`,`ent`,`p`,`cap`] mp_tac o CONJUNCT1) >>
  simp[] >> disch_then (qx_choose_then `dw` strip_assume_tac) >>
  drule_all expr_post_live_destination_source >>
  disch_then (qx_choose_then `sw` assume_tac) >>
  RULE_L_ASSUM_TAC CONJUNCTS >>
  `(!mem. mem_agree_outside ti.t_mem u.vs_memory mem ==> val_in_memory stv v (w2n sw) mem) /\
   ?xs b n. op = Var xs /\ FLOOKUP Gi xs = SOME (b,n) /\
     b <= w2n sw /\ w2n sw + val_store_size stv v <= b + n` by
    (qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
     simp[ptr_val_ok_def] >> disch_then (mp_tac o CONJUNCT2) >>
     rewrite_tac[ptr_mem_ok_def] >>
     disch_then (qspecl_then [`stv`,`sw`] mp_tac) >> simp[]) >>
  qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
  `lookup_var xs u = SOME sw` by fs[eval_operand_def] >>
  `val_store_size stv v = type_memory_size stv` by
    metis_tac[bodyDeclMemoryCoreTheory.val_store_size_non_bytestring] >>
  `ptr_covers Gi ti xs u (type_memory_size stv)` by
    (simp[ptr_covers_def] >> metis_tac[ptr_val_ok_def]) >>
  `ptr_covers Gi ti p u cap /\ allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[ghost_inv_at_def] >> metis_tac[]) >>
  `ptr_covers Gi ti p u (type_memory_size dtv)` by
    (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_MONO_ADD_EQ]) >>
  `expr_val_at cenv cx (lowered_value_type cenv e) sa sB mid v (Var xs) u` by
    metis_tac[expr_post_def] >>
  `!i. w2n sw <= i /\ i < w2n sw + type_memory_size stv ==> i < u.vs_alloca_next` by
    metis_tac[expr_val_at_below_frontier] >>
  `w2n sw + type_memory_size stv <= u.vs_alloca_next /\
   w2n dw + type_memory_size dtv <= u.vs_alloca_next` by
    (first_x_assum (qspec_then `w2n sw + type_memory_size stv - 1` mp_tac) >>
     simp[] >> decide_tac) >>
  `local_region cenv mid.scopes u id (w2n dw) cap` by
    (simp[local_region_def] >> metis_tac[]) >>
  `lo <= w2n dw` by
    (`0 < cap` by decide_tac >> drule_all body_full_local_region_lower_bound >> simp[]) >>
  `sa.cs_next_var <= sB.cs_next_var` by
    (qspec_then `sa` mp_tac
       (Q.SPECL [`cenv`,`expr_type e`,`e`] ci_mono_lower_value_compile_expr) >>
     simp[ci_mono_def]) >>
  `local_ptrs_reserved cenv sB` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `not_fresh_at sB p` by metis_tac[local_ptrs_reserved_def] >>
  `not_fresh_at sB xs` by metis_tac[compile_lower_value_var] >>
  qexistsl_tac [`xs`,`sw`,`dw`] >> simp[] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem body_assign_widened_frame_compose[local]:
  expr_post H ctx func cenv cx e es sa sB s0 mid v op u /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM mid.scopes = MAP FDOM es.scopes /\
  sa.cs_next_id <= sB.cs_next_id /\
  alloca_frame cenv mid sB u cenv ff t /\
  (!aid off sz i.
     FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
     (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                off + sz <= b \/ b + sz' <= off) /\
     off <= i /\ i < off + sz /\ i IN ti.t_mem ==> i IN tn0.t_mem) /\
  (!aid off sz i.
     FLOOKUP u.vs_allocas aid = SOME (off, sz) /\ aid < sB.cs_next_id /\
     (!n b sz'. local_region cenv mid.scopes u n b sz' ==>
                off + sz <= b \/ b + sz' <= off) /\
     off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN ti.t_mem) ==>
  alloca_frame cenv es sa s0 cenv ff t /\
  (!aid off sz i.
     FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
     (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                off + sz <= b \/ b + sz' <= off) /\
     off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tn0.t_mem)
Proof
  strip_tac >>
  drule_all_then assume_tac expr_post_alloca_frame >>
  qhdtm_x_assum `expr_post`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  conj_tac >- (irule alloca_frame_trans >> metis_tac[]) >>
  MATCH_MP_TAC (GEN_ALL alloca_taint_kept_trans) >>
  goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `_ <= _`)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem body_assign_widened_layout_ready[local]:
  !cx id ty e tops bindings ctx cenv env env' ret_ty es.
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    FLOOKUP env.var_types id = SOME ty /\
    ~is_word_type ty /\
    0 < type_memory_bytes cenv ty /\
    ~(lowered_value_type cenv e = expr_type e \/
      is_bytestring_type (expr_type e) /\
      is_bytestring_type (lowered_value_type cenv e) /\
      arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    post_value_type cenv e = lowered_value_type cenv e /\
    ~is_word_type (lowered_value_type cenv e) /\
    ~is_bytestring_type (lowered_value_type cenv e) /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty /\
    ?stv dtv.
      evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
      evaluate_type (get_tenv cx) ty = SOME dtv /\
      type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
      type_memory_bytes cenv ty = type_memory_size dtv /\
      0 < type_memory_size stv /\
      type_memory_size stv <= type_memory_size dtv /\
      type_memory_size dtv < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_local_rhs_pre >> strip_tac >>
  drule_all assign_relayout_source_classify >> strip_tac >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by metis_tac[] >>
  `type_memory_bytes cenv ty < 2 ** 64` by metis_tac[locals_alloc_ok_def] >>
  drule_all widening_memory_layout_bound >> strip_tac >>
  `0 < type_memory_size stv` by
    (drule_all widening_zero_memory_size >> simp[] >> decide_tac) >>
  simp[] >> gvs[wordsTheory.dimword_def] >> decide_tac
QED

(* A memory local whose source has a widened physical layout. *)
Theorem body_assign_local_widened_full:
  !cx id ty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (NameTarget id)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME ty /\
    ~is_word_type ty /\
    0 < type_memory_bytes cenv ty /\
    (expr_type e = ty \/ lowered_value_type cenv e = ty \/ is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    ~(lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `post_value_type cenv e = lowered_value_type cenv e /\
   ~is_word_type (lowered_value_type cenv e) /\
   ~is_bytestring_type (lowered_value_type cenv e) /\
   type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty /\
   ?stv dtv.
     evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
     evaluate_type (get_tenv cx) ty = SOME dtv /\
     type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
     type_memory_bytes cenv ty = type_memory_size dtv /\
     0 < type_memory_size stv /\
     type_memory_size stv <= type_memory_size dtv /\
     type_memory_size dtv < dimword (:256)` by
    (MATCH_MP_TAC body_assign_widened_layout_ready >>
     goal_assum (drule_at (Pat `type_stmt _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `supported_stmt _ _ _`)) >>
     qexistsl_tac [`ctx`,`es`] >>
     qpat_assum `~(lowered_value_type _ _ = _ \/ _)` mp_tac >>
     simp[DE_MORGAN_THM]) >>
  drule_all assign_base_local_rhs_pre >> strip_tac >>
  drule_all targetPlaceSimTheory.expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  `lowered_value_type cenv e <> expr_type e` by metis_tac[] >>
  `~(has_length_word (expr_type e) /\ is_empty_value_expr e)` by
    (Cases_on `e` >> gvs[is_empty_value_expr_def, lowered_value_type_def, expr_type_def]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by metis_tac[body_expr_full_ok_def] >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[cj 1 vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  conj_tac >- simp[] >> strip_tac >>
  drule_all assign_local_relayout_code_parts >> strip_tac >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `?shadow_sB. lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
     (gas_shadow_expr e) shadow_sa = (op,shadow_sB) /\ gas_shadow_state sB shadow_sB` by
    (`FST (lower_value compile_expr cenv (expr_type e) e sa) =
       FST (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
         (gas_shadow_expr e) shadow_sa) /\
       gas_shadow_state (SND (lower_value compile_expr cenv (expr_type e) e sa))
         (SND (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
           (gas_shadow_expr e) shadow_sa))` by
       (irule (REWRITE_RULE [gas_shadow_compiles_def]
          (Q.INST [`sd` |-> `T`] gas_shadow_stmt_lower_value_env)) >> simp[]) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa` >> gvs[]) >>
  `fn_has_code shadow_sa shadow_sB shadow_func` by suspend "shadow" >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  drule_then assume_tac assign_local_admissible_rhs >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sB`,`shadow_sa`,`shadow_sB`,`op`,
    `s0`,`G0`,`tn0`] mp_tac) >> simp[] >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (fn outcome =>
    qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
      qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
        mp_tac (MATCH_MP gas_outcome_full_return_buf_allocas
          (LIST_CONJ [outcome,frame,sep]))))) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ _` >>
  irule assign_local_memory_full_outcome >>
  conj_tac >- (qexists_tac `lctx` >> first_assum ACCEPT_TAC) >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "continue" >>
  conj_tac >- (simp[Abbr `childQ`] >> metis_tac[]) >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]
QED

Resume body_assign_local_widened_full[shadow]:
  qpat_x_assum `stmt_env _ _ _ (Assign _ e) sa = _` kall_tac >>
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
  pure_rewrite_tac[gas_shadow_stmt_def, gas_shadow_assignment_def,
                   gas_shadow_expr_def] >> strip_tac >>
  `expr_type (gas_shadow_expr e) = expr_type e` by simp[] >>
  `~(has_length_word (expr_type (gas_shadow_expr e)) /\
      is_empty_value_expr (gas_shadow_expr e))` by
    (Cases_on `e` >> gvs[is_empty_value_expr_def, gas_shadow_expr_def, expr_type_def]) >>
  `FLOOKUP (gas_shadow_env T cenv).ce_vars id = SOME (PtrVar (Var p) sz)` by simp[] >>
  `(gas_shadow_env T cenv).ce_var_type id = SOME ty` by simp[] >>
  drule_all assign_local_relayout_code_parts >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr e) _ = _` mp_tac >> simp[]
QED

Resume body_assign_local_widened_full[continue]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  qunabbrev_tac `childQ` >> rule_assum_tac BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `INL v = INL _` (SUBST_ALL_TAC o REWRITE_RULE [INL_11]) >>
  rename1 `expr_store_bound cx _ v op u` >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `ptr_val_ok cx (post_value_type cenv e) v op Gi ti u` by simp[] >>
  `dead_lo_ok H0 (DF H0) lo cenv cx` by simp[] >>
  drule_all body_assign_widened_success_resources >>
  disch_then (qx_choosel_then [`pre`,`sc`,`ent`,`rest`,`xs`,`sw`,`dw`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
  drule_all residual_call_compile_location >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    drule_then (ACCEPT_TAC o MATCH_MP contract_inv_acyclic_struct_metadata) body_inv_contract >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       sz = type_memory_size tv) fields)` by
    (qpat_assum `expr_sim_inv _ _ _ _`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_sim_inv_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel H0 ctx func cenv cx mid u` by fs[expr_post_def] >>
  `type_memory_size stv < dimword (:256)` by decide_tac >>
  qabbrev_tac `ff = mid with scopes := pre ++ (sc |+ (id,ent with <|value := v; popped := []|>)) :: rest` >>
  `?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (u,Gi,ti) [] (OK t,Gf,tf)) /\
    (!(H : (bool # 256 word # type_value) list # num list) D d.
      stmt_state_rel H ctx func cenv cx mid u /\
      ghost_inv_at D lo d cenv cx mid Gi ti u ==>
      stmt_state_rel H ctx func cenv cx ff t /\ ghost_inv_at D lo d cenv cx ff Gf tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ u.vs_alloca_next <= t.vs_alloca_next /\
    (!aid ent. FLOOKUP u.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!x. not_fresh_at sB x ==>
      lookup_var x t = lookup_var x u /\ FLOOKUP Gf x = FLOOKUP Gi x /\
      op_taint tf (Var x) = op_taint ti (Var x)) /\
    alloca_frame cenv mid sB u cenv ff t /\
    (!aid off sz i. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ aid < sB.cs_next_id /\
      (!name a len. local_region cenv mid.scopes u name a len ==> off+sz <= a \/ a+len <= off) /\
      off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN ti.t_mem)` by
    (qunabbrev_tac `ff` >>
     irule (INST_TYPE [alpha |-> ``:256``] body_full_assign_local_memory_value_frame_path) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- (qexists_tac `H0` >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`type_memory_bytes cenv ty`,`sz`,`dtv`,`ty`,`dw`,
       `vv_location vv`,`p`,`sa`,`stv`,`lowered_value_type cenv e`,`sw`,`xs`] >>
     simp[]) >>
  `ff.storage_trace = mid.storage_trace /\ ff with gas_obs := [] = ff` by
    simp[Abbr `ff`,evaluation_state_component_equality] >>
  qexistsl_tac [`ff`,`t`,`Gf`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac
  >- first_assum (irule o SPEC_ALL) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `ff.storage_trace = mid.storage_trace` (fn eq =>
       qpat_assum `valid_horizon cx st0 H ff.storage_trace`
         (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) []))) >>
  qpat_assum `!tail. bind (eval_expr _ _) _ _ = _`
    (qspec_then `[]` assume_tac) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       simp[storage_trace_frame_bind_all,cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
         storage_trace_frame_read_result] >>
     drule valid_horizon_frame >> disch_then drule >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (drule eval_read_preserves_scopes_dom >> simp[]) >>
  `ci_mono sa sB` by metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND] >>
  `ci_mono sB sb` by metis_tac[cj 1 ci_mono_stmt_helpers,pairTheory.SND] >>
  suspend "post"
QED

Resume body_assign_local_widened_full[post]:
  BETA_TAC >>
  qpat_assum `ff with gas_obs := [] = ff` SUBST1_TAC >>
  qexists_tac `cenv` >>
  qpat_assum `expr_post H ctx func cenv cx e es sa sB s0 mid v (Var xs) u`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_post_def]) >>
  `stmt_state_rel H ctx func cenv cx ff t /\
   ghost_inv_at (DF H) lo d cenv cx ff Gf tf t` by
    (qpat_assum `!J D k. _ J D k ==>
          stmt_state_rel J _ _ _ _ ff t /\ ghost_inv_at D _ k _ _ ff _ _ t`
       (qspecl_then [`H`,`DF H`,`d`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `stmt_state_rel H _ _ _ _ ff t`
       (mp_tac o MATCH_MP stmt_state_rel_allocas_below_fmp) >> simp[]) >>
  `~block_is_terminated sb` by
    (`~block_is_terminated sB` by
       (drule_all_then ACCEPT_TAC exprOpenTerminalsTheory.unwrap_value_open) >>
     drule_all_then ACCEPT_TAC stmtSimDeclTypedCodeTheory.compile_assign_value_typed_open) >>
  `storage_well_formed_on cx ff (FST H)` by suspend "storage" >>
  `sa.cs_next_var <= sB.cs_next_var /\ sa.cs_next_id <= sB.cs_next_id /\
   sB.cs_next_var <= sb.cs_next_var` by fs[ci_mono_def] >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sB x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sB x ==> lookup_var x t = _ /\ _`
       (qspec_then `x` mp_tac) >> simp[] >>
     qpat_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  `return_buf_frame d cenv sB u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  `!bw cap. d = SOME (bw, cap) ==> allocas_from (w2n bw + cap) t` by
    (qpat_assum `!D. gas_origin_ptr_path _ (u,Gi,ti) [] (OK t,Gf,tf)`
       (qspec_then `DF H` (fn path =>
         qpat_assum `return_buf_frame d cenv sB u` (fn frame =>
           qpat_assum `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) u` (fn floor =>
             mp_tac (MATCH_MP return_buf_allocas_suffix (LIST_CONJ [path,frame,floor])))))) >>
     simp[]) >>
  `MAP FDOM ff.scopes = MAP FDOM es.scopes` by
    (simp[Abbr `ff`] >>
     qpat_assum `find_containing_scope id mid.scopes = SOME (pre,sc,ent,rest)`
       (mp_then Any mp_tac tupleTargetStorePropsTheory.tuple_target_local_domain_frame) >>
     disch_then (qspec_then `v` mp_tac) >> simp[]) >>
  `return_buf_sep d cenv ff t` by
    (irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
     conj_tac >- fs[] >>
     qexistsl_tac [`H`,`ctx`,`cx`,`es`, `func`,`s0`,`sa`] >> simp[]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b` by
    (rpt strip_tac >>
     qpat_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _`
       (drule_then assume_tac) >> first_x_assum (drule_then ACCEPT_TAC)) >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Gi ti`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [ghost_kept_at_def]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
                             op_taint tf (Var x) = op_taint tn0 (Var x)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sB x ==> lookup_var x t = _ /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP Gi x = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  simp[stmt_lands_def, stmtSimPropsTheory.cenv_top_ext_refl] >>
  drule_all_then ACCEPT_TAC body_assign_widened_frame_compose
QED

Resume body_assign_local_widened_full[storage]:
  `!b. get_storage cx ff b = get_storage cx mid b` by
    (gen_tac >> Cases_on `b` >> simp[Abbr `ff`, get_storage_def]) >>
  pure_rewrite_tac[storage_well_formed_on_def] >>
  qpat_assum `!b. get_storage cx ff b = _` (pure_rewrite_tac o single) >>
  qpat_assum `storage_well_formed_on cx mid (FST H)`
    (ACCEPT_TAC o PURE_REWRITE_RULE [storage_well_formed_on_def])
QED

Finalise body_assign_local_widened_full

(* Compose a normal forced RHS with the actual top-level storage action. *)
Theorem body_assign_toplevel_word_full_normal[local]:
  get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL v,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) marks (OK t,G1,tn1)) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (ignore_bind (record_storage_event (StorageRoot tr slot tvt))
      (write_storage_slot cx tr (n2w slot) tvt v))
    (mid with gas_obs := [],t,G1,tn1) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e))
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  `gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn u. res = INL v /\ ee = mid with gas_obs := [] /\
      G = G1 /\ tn = tn1 /\ u = t)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r)` by
    (irule gas_outcome_full_intro >>
     qexistsl_tac [`G1`,`mid`,`marks`,`OK t`,`INL v`,`tn1`] >> simp[]) >>
  drule_all stmtSimAssignStorageTheory.eval_assign_toplevel_action >>
  disch_then (qspec_then `e` SUBST1_TAC) >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid'`,`t'`,`v'`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> fs[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_event,storage_trace_frame_ignore_bind,
      storage_trace_frame_write_storage_slot] >>
  qpat_assum `gas_outcome_full _ _ _ _ (bind _ _) _ _ _` (irule_at Any) >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace) mid'.storage_trace`
    by fs[storage_trace_domain_def] >>
  first_x_assum drule >> strip_tac >> gvs[] >> disj1_tac >> simp[]
QED

(* Pull the Assign store precondition back through its forced RHS. *)

Theorem body_assign_toplevel_word_full_store_pre[local]:
  s0.vs_alloca_next <= t.vs_alloca_next /\
  sa.cs_next_var <= sm.cs_next_var /\
  return_buf_frame d cenv sa s0 /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL v,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e es sa sm s0 (mid with gas_obs := []) v op t /\
    ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G1 tn1 t) ==>
  return_buf_frame d cenv sm t /\
  (!H. valid_horizon cx st0 H (mid.storage_trace ++ [StorageRoot tr slot tvt]) ==>
    expr_post H ctx func cenv cx e es sa sm s0 (mid with gas_obs := []) v op t /\
    stmt_state_rel H ctx func cenv cx es s0 /\ dead_lo_ok H (DF H) lo cenv cx /\
    ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G1 tn1 t)
Proof
  strip_tac >> conj_tac
  >- (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
        by fs[storage_trace_domain_def] >>
      first_x_assum drule >> strip_tac >>
      irule bodyMemoryDefsTheory.return_buf_frame_frame >>
      qexistsl_tac [`cenv`,`s0`,`sa`] >> fs[expr_post_def]) >>
  gen_tac >> strip_tac >> drule gasOutcomeFullTheory.valid_horizon_append >> strip_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
         storage_trace_frame_read_result] >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule valid_horizon_frame >> disch_then drule >> simp[]) >>
  first_x_assum drule >> simp[]
QED

(* Complete the Assign store for both valid and invalid extended traces. *)

(* The normal RHS endpoint feeds the joint top-level store. *)

(* The rejected write still evaluates the RHS and records its root. *)

Theorem body_assign_toplevel_word_full_static_rhs[local]:
  cx.txn.is_static /\ get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\ is_word_type (expr_type e) /\
  emit_void (if tr then TSTORE else SSTORE) [Lit (n2w slot);op] sm = ((),sb) /\
  fn_has_code sm sb func /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (res,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s0,G0,tn0) marks (OK t,G1,tn1) /\
    ?v. res = INL v /\
      expr_post H ctx func cenv cx e es sa sm s0
        (mid with gas_obs := []) v op t /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts /\
      ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G1 tn1 t /\
      ptr_val_ok cx (expr_type e) v op G1 tn1 t) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e))
    (es,s0,G0,tn0) Q
    (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==>
       !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  simp[NoAsms] >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  `~t.vs_halted` by
    (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[fragExecTheory.exit_result_def]) >>
  `?w. eval_operand op t = SOME w` by
    (gvs[expr_post_def, expr_val_rel_def, post_value_type_word] >> metis_tac[]) >>
  `op_taint tn1 op = {}` by fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  irule body_assign_toplevel_word_full_normal >>
  qpat_assum `find_var_decl_by_name _ _ = _` (irule_at Any) >>
  qpat_assum `lookup_var_slot_from_layout _ _ _ _ = _` (irule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`v`,`tn1`,`t`,`marks`,`G1`] >> simp[] >>
  irule body_assign_toplevel_word_full_static_store >> simp[] >>
  conj_tac
  >- (qexists_tac `cenv` >> rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==>
        gas_origin_ptr_path _ _ _ _ /\ _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      gvs[expr_post_def, stmt_state_rel_start_gas_obs,
          bodyPtrDefsTheory.ghost_inv_at_def]) >>
  qexistsl_tac [`op`,`sm`,`sb`,`w`] >> simp[]
QED

Theorem body_assign_toplevel_word_full_residual_frame[local]:
  ~cx.txn.is_static /\ get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (StorageVarDecl tr (expr_type e),id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
  is_word_type (expr_type e) /\ type_slot_size tvt = 1 /\ value_has_type tvt v /\
  encode_value tvt v = SOME [(0,typed_val_to_w256 tvt v)] /\
  emit_void (if tr then TSTORE else SSTORE) [Lit (n2w slot);op] sm = ((),sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ MAP FDOM mid.scopes = MAP FDOM es.scopes /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\ op_taint tn1 op = {} /\
  return_buf_frame d cenv sm t /\ alloca_history func t /\
  return_buf_sep d cenv es s0 /\
  (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  (!H. valid_horizon cx st0 H (mid.storage_trace ++ [StorageRoot tr slot tvt]) ==>
    expr_post H ctx func cenv cx e es sa sm s0 (mid with gas_obs := []) v op t /\
    stmt_state_rel H ctx func cenv cx es s0 /\ dead_lo_ok H (DF H) lo cenv cx /\
    ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G1 tn1 t) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (ignore_bind (record_storage_event (StorageRoot tr slot tvt))
      (write_storage_slot cx tr (n2w slot) tvt v)) (mid with gas_obs := [],t,G1,tn1)
    (\H res ee G tn t. ?ce.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
      cenv_top_ext cenv ce ee.scopes /\ stmt_state_rel H ctx func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d ce sb t /\
      alloca_history func t /\ return_buf_sep d ce ee t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 ce ee t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)) R
Proof
  strip_tac >>
  Cases_on `storage_trace_domain cx st0 (mid.storage_trace ++ [StorageRoot tr slot tvt])`
  >- (
    `valid_horizon cx st0 (storage_trace_horizon (mid.storage_trace ++ [StorageRoot tr slot tvt]))
      (mid.storage_trace ++ [StorageRoot tr slot tvt])` by fs[storage_trace_domain_def] >>
    `~t.vs_call_ctx.cc_static` by
      (first_x_assum drule >> strip_tac >>
       `stmt_state_rel (storage_trace_horizon (mid.storage_trace ++ [StorageRoot tr slot tvt]))
          ctx func cenv cx (mid with gas_obs := []) t` by fs[expr_post_def] >>
       drule stmt_state_rel_state_rel >> strip_tac >> drule state_rel_call_ctx_rel >>
       simp[call_ctx_rel_def]) >>
    Cases_on `write_storage_slot cx tr (n2w slot) tvt v (mid with gas_obs := [])` >>
    rename1 `write_storage_slot _ _ _ _ _ _ = (res,ef)` >>
    `res = INL ()` by
      (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >> simp[write_storage_slot_eq]) >>
    gvs[] >>
    `ef.storage_trace = mid.storage_trace` by
      (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
       simp[write_storage_slot_eq] >> Cases_on `tr` >> simp[set_storage_def] >> strip_tac >> gvs[]) >>
    irule gas_outcome_full_intro >>
    qexistsl [`G1`, `ef with storage_trace := mid.storage_trace ++ [StorageRoot tr slot tvt]`, `[]`,
      `OK ((if tr then tstore (n2w slot) (typed_val_to_w256 tvt v) t
           else sstore (n2w slot) (typed_val_to_w256 tvt v) t)
          with vs_inst_idx := LENGTH sb.cs_current_insts)`, `INL ()`,
      `if tr then tn1 with t_trans := key_update tn1.t_trans (n2w slot) {}
       else tn1 with t_stor := key_update tn1.t_stor (n2w slot) {}`] >>
    simp[] >> conj_tac
    >- (simp[ignore_bind_def,record_storage_event_def,return_def,bind_def] >>
        gen_tac >> drule write_storage_slot_storage_trace >>
        disch_then (qspec_then `mid.storage_trace ++ [StorageRoot tr slot tvt]` assume_tac) >>
        gvs[write_storage_slot_eq] >> Cases_on `tr` >>
        gvs[set_storage_def,get_storage_def,evaluation_state_component_equality]) >>
    qx_gen_tac `H` >> strip_tac >> first_x_assum drule >> strip_tac >>
    `eval_operand op t = SOME (typed_val_to_w256 tvt v)` by
      (gvs[expr_post_def,expr_val_rel_def,post_value_type_word] >> metis_tac[]) >>
    `stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) t` by fs[expr_post_def] >>
    `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
      (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
    conj_tac
    >- (irule storage_word_store_origin_ptr >> simp[] >>
        conj_tac >- fs[ghost_inv_at_def] >>
        conj_tac >- fs[ghost_inv_at_def] >>
        qexistsl [`Lit (n2w slot)`,`op`,`sm`] >> simp[eval_operand_def,op_taint_def]) >>
    `ef.gas_obs = []` by
      (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
       simp[write_storage_slot_eq] >> Cases_on `tr` >> simp[set_storage_def] >> strip_tac >> gvs[]) >>
    `MEM (tr,n2w slot,tvt) (FST H) /\ regions_consistent (FST H)` by
      (qpat_x_assum `valid_horizon cx st0 H _` mp_tac >>
       simp[valid_horizon_def,storage_observations_ok_def,storage_trace_regions_def,
            MAP_APPEND,FLAT_APPEND,EVERY_APPEND]) >>
    `MAP FDOM (mid with gas_obs := []).scopes = MAP FDOM es.scopes` by simp[] >>
    drule_all body_assign_toplevel_word_full_store_post >>
    `ef.scopes = mid.scopes` by
      (drule vyperScopePreservationTheory.write_storage_slot_scopes >> simp[]) >>
    `return_buf_sep d cenv
       (ef with <|gas_obs := [];
         storage_trace := mid.storage_trace ++ [StorageRoot tr slot tvt]|>)
       ((if tr then tstore (n2w slot) (typed_val_to_w256 tvt v) t
         else sstore (n2w slot) (typed_val_to_w256 tvt v) t)
        with vs_inst_idx := LENGTH sb.cs_current_insts)` by
      (irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
       conj_tac
       >- (Cases_on `tr` >>
           simp[tstore_def, sstore_def, allocas_from_def] >>
           rpt strip_tac >>
           qpat_assum `!bw cap. d = SOME (bw,cap) ==> allocas_from _ t`
             (qspecl_then [`bw:256 word`,`capacity`] (mp_tac o
                REWRITE_RULE [allocas_from_def])) >>
           asm_rewrite_tac[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
       qexistsl_tac [`H`, `ctx`, `cx`, `es`, `func`, `s0`, `sa`] >>
       Cases_on `tr` >> fs[expr_post_def, tstore_def, sstore_def, lookup_var_def]) >>
    disch_then (qspec_then `lctx` strip_assume_tac) >>
    disj1_tac >> pure_once_rewrite_tac[GSYM evaluation_state_fupdcanon] >>
    `(ef with gas_obs := []) = ef` by simp[evaluation_state_component_equality] >>
    simp[stmt_post_storage_trace,stmtSimPropsTheory.cenv_top_ext_refl] >>
    fs[stmt_post_def] >>
    conj_tac
    >- (qpat_assum `storage_well_formed_on cx ef _` mp_tac >>
        rewrite_tac[storage_well_formed_on_def] >> strip_tac >>
        rpt strip_tac >> first_x_assum drule >> Cases_on `b` >> simp[get_storage_def]) >>
    conj_tac
    >- (gvs[alloca_frame_def] >> first_assum ACCEPT_TAC) >>
    Cases_on `tr` >> gvs[ghost_kept_at_def] >> metis_tac[]) >>
  irule gas_outcome_full_bad_nil >> simp[] >>
  simp[ignore_bind_def,record_storage_event_def,bind_def,return_def,write_storage_slot_eq] >>
  Cases_on `cx.txn.is_static` >> Cases_on `tr` >> simp[set_storage_def]
QED

Theorem body_assign_toplevel_word_full_after_rhs_frame[local]:
  ~cx.txn.is_static /\ get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (StorageVarDecl tr (expr_type e),id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
  is_word_type (expr_type e) /\
  emit_void (if tr then TSTORE else SSTORE) [Lit (n2w slot);op] sm = ((),sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  sa.cs_next_var <= sm.cs_next_var /\
  expr_body_pre cenv cx env e es /\ local_ptrs_reserved cenv sa /\
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (res,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) marks (OK t,G1,tn1) /\
    (?v. res = INL v /\ expr_post H ctx func cenv cx e es sa sm s0
      (mid with gas_obs := []) v op t /\
      expr_store_bound cx (expr_type e) v op t /\
      t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G1 tn1 t /\
      ptr_val_ok cx (expr_type e) v op G1 tn1 t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?ce.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
      cenv_top_ext cenv ce ee.scopes /\ stmt_state_rel H ctx func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d ce sb t /\
      alloca_history func t /\ return_buf_sep d ce ee t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 ce ee t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)) R
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  simp[NoAsms] >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  `~t.vs_halted` by
    (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[fragExecTheory.exit_result_def]) >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
  `expr_body_pre cenv cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
  drule exprSimSourceTheory.expr_body_pre_eval >>
  disch_then (qspecl_then [`INL v`,`mid with gas_obs := []`] mp_tac) >>
  (impl_tac >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
    qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[])) >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    drule_then ACCEPT_TAC expr_body_pre_env_type_defs >>
  `value_has_type tvt v` by
    (fs[vyperTypeExprResultTheory.expr_result_typed_def,
       vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
       vyperTypeInvariantsTheory.value_result_typed_def] >> gvs[]) >>
  `encode_value tvt v = SOME [(0,typed_val_to_w256 tvt v)]` by
    metis_tac[stmtSimAssignStorageFactsTheory.encode_value_word_typed] >>
  `type_slot_size tvt = 1` by metis_tac[exprSimUnwrapTheory.word_type_slot_size] >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (drule stmtSimDefsTheory.eval_read_preserves_scopes_dom >> simp[]) >>
  `return_buf_frame d cenv sm t /\
    (!H. valid_horizon cx st0 H (mid.storage_trace ++ [StorageRoot tr slot tvt]) ==>
      expr_post H ctx func cenv cx e es sa sm s0 (mid with gas_obs := []) v op t /\
      stmt_state_rel H ctx func cenv cx es s0 /\ dead_lo_ok H (DF H) lo cenv cx /\
      ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G1 tn1 t)` by
    (irule body_assign_toplevel_word_full_store_pre >>
     goal_assum (drule_at Any) >> simp[] >>
     conj_tac >- metis_tac[] >> gen_tac >> strip_tac >> first_x_assum drule >> simp[]) >>
  `op_taint tn1 op = {}` by fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t,G1,tn1)` (fn path =>
       qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
         qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
           mp_tac (MATCH_MP return_buf_allocas_path (LIST_CONJ [path,frame,sep]))))) >>
     simp[]) >>
  irule body_assign_toplevel_word_full_normal >>
  qpat_assum `find_var_decl_by_name _ _ = _` (irule_at Any) >>
  qpat_assum `lookup_var_slot_from_layout _ _ _ _ = _` (irule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`v`,`tn1`,`t`,`marks`,`G1`] >> simp[] >>
  irule body_assign_toplevel_word_full_residual_frame >>
  qpat_assum `find_var_decl_by_name _ _ = _` (irule_at Any) >>
  qpat_assum `emit_void _ _ _ = _` (irule_at Any) >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

(* Instantiate the RHS judgment in the paired Assign frame. *)
Theorem body_assign_toplevel_word_full_framed_frame[local]:
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es /\ expr_body_pre cenv cx env e es /\
  get_module_code cx NONE = SOME tops /\
  find_var_decl_by_name id tops = SOME (StorageVarDecl tr (expr_type e),id) /\
  lookup_var_slot_from_layout cx tr NONE id = SOME slot /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
  cenv.ce_hashmap_info (NONE,id) = NONE /\
  cenv.ce_module_var_type (NONE,id) = SOME (expr_type e) /\
  is_word_type (expr_type e) /\
  stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget (NONE,id))) e) sa = (ce,sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ret_ty
    (gas_shadow_stmt (Assign (BaseTarget (TopLevelNameTarget (NONE,id))) e)) shadow_sa =
      (gas_shadow_env T ce,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~block_is_terminated sa /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (NONE,id))) e))
    (stmt_res_ok lctx) es /\
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  storage_trace_domain cx st0 es.storage_trace ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (NONE,id))) e)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?ce'.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ ce' = ce) /\
      cenv_top_ext cenv ce' ee.scopes /\ stmt_state_rel H ctx func ce' cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d ce' sb t /\
      alloca_history func t /\ return_buf_sep d ce' ee t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce' cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 ce' ee t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem))
    (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==>
       !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >>
  `?H. valid_horizon cx st0 H es.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    metis_tac[stmt_state_rel_vars_rels] >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  drule_all assign_storage_word_code_parts >> strip_tac >> gvs[] >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (op,sm)` >>
  `?shadow_sm. lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa = (op,shadow_sm) /\
       gas_shadow_state sm shadow_sm` by
    (`FST (lower_value compile_expr cenv (expr_type e) e sa) =
       FST (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
         (gas_shadow_expr e) shadow_sa) /\
       gas_shadow_state (SND (lower_value compile_expr cenv (expr_type e) e sa))
         (SND (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
           (gas_shadow_expr e) shadow_sa))` by
       (irule (REWRITE_RULE [gas_shadow_compiles_def]
          (Q.INST [`sd` |-> `T`] gas_shadow_stmt_lower_value_env)) >> simp[]) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa` >> gvs[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     simp[gas_shadow_stmt_def,gas_shadow_assignment_def,gas_shadow_expr_def] >> strip_tac >>
     qpat_x_assum `stmt_env _ _ _ (Assign _ e) sa = _` kall_tac >>
     `is_word_type (expr_type (gas_shadow_expr e))` by simp[gas_shadow_expr_type] >>
     `FLOOKUP (gas_shadow_env T cenv).ce_module_vars (NONE,id) =
        SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by simp[] >>
     `(gas_shadow_env T cenv).ce_hashmap_info (NONE,id) = NONE` by simp[] >>
     `(gas_shadow_env T cenv).ce_module_var_type (NONE,id) =
        SOME (expr_type (gas_shadow_expr e))` by simp[gas_shadow_expr_type] >>
     drule_all assign_storage_word_code_parts >> strip_tac >>
     gvs[gas_shadow_expr_type] >> metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`]
       mp_tac ci_mono_lower_value_compile_expr >> simp[ci_mono_def]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,
    `op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q1 _` >>
  irule body_assign_toplevel_word_full_source >>
  conj_tac >- (qexists_tac `lctx` >> simp[]) >> qexists_tac `Q1` >>
  reverse conj_tac >- (irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
    goal_assum (drule_at Any) >> simp[] >> rpt gen_tac >>
    POP_ASSUM_LIST (K all_tac) >> strip_tac >>
    Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def] >>
    Cases_on `y` >> Cases_on `r` >>
    gvs[bodyPtrDefsTheory.stmt_exit_ptr_def,exprSimDefsTheory.expr_exit_def,
        exprSimDefsTheory.halt_exit_def] >>
    rename1 `Error err` >> Cases_on `err` >>
    gvs[exprSimDefsTheory.expr_exit_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `cx.txn.is_static`
  >- (irule body_assign_toplevel_word_full_static_rhs >> simp[Abbr `Q1`, post_value_type_word] >>
      qpat_assum `emit_void _ _ _ = _` (irule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`tn1`,`t`,`sa`,`res`,`marks`,`d`,`cenv`,`G1`] >>
      simp[] >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==>
        gas_origin_ptr_path _ _ _ _ /\ _` mp_tac >>
      simp[post_value_type_word] >> POP_ASSUM_LIST (K all_tac) >>
      metis_tac[]) >>
  irule body_assign_toplevel_word_full_after_rhs_frame >>
  simp[cs_extends_def,Abbr `Q1`,post_value_type_word] >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`G1`,`marks`,`mid`,`op`,`res`,`sm`,`t`,`tn1`] >>
  simp[] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==>
    gas_origin_ptr_path _ _ _ _ /\ _` mp_tac >>
  simp[post_value_type_word] >> POP_ASSUM_LIST (K all_tac) >>
  metis_tac[]
QED

(* A scalar top-level variable. *)
Theorem body_assign_toplevel_word_full:
  !cx nsid e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (TopLevelNameTarget nsid)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (TopLevelNameTarget nsid)) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    supported_scalar_target tops nsid /\
    (?dty. type_place_target env (TopLevelNameTarget nsid) = SOME (Type dty) /\
           is_word_type dty) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all body_assign_toplevel_word_full_setup >> strip_tac >> gvs[] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by metis_tac[body_expr_full_ok_def] >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[evaluate_storage_trace_frame] >>
  conj_tac >- simp[] >> strip_tac >>
  irule body_assign_toplevel_word_full_framed_frame >>
  simp[] >> metis_tac[]
QED

Theorem body_assign_toplevel_copy_after_rhs_frame[local]:
  get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (StorageVarDecl tr (expr_type e),id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  0 < type_memory_bytes cenv (expr_type e) /\
  lowered_value_type cenv e = expr_type e /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
                            sz = type_memory_size rt) fields) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
  compile_store_slots cenv op (Lit (n2w slot)) (expr_type e) tr sm = ((),sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  expr_body_pre cenv cx env e es /\ local_ptrs_reserved cenv sa /\
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL v,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) marks (OK t,G1,tn1) /\
    expr_post H ctx func cenv cx e es sa sm s0 (mid with gas_obs := []) v op t /\
    expr_store_bound cx (expr_type e) v op t /\
    t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G1 tn1 t /\
    ptr_val_ok cx (expr_type e) v op G1 tn1 t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?ce.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
      cenv_top_ext cenv ce ee.scopes /\ stmt_state_rel H ctx func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d ce sb t /\
      alloca_history func t /\ return_buf_sep d ce ee t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 ce ee t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem))
    (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==>
       !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  simp[NoAsms] >> (impl_tac >- simp[]) >> strip_tac >>
  `~t.vs_halted` by
    (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[fragExecTheory.exit_result_def]) >>
  irule body_assign_toplevel_word_full_normal >>
  qpat_assum `find_var_decl_by_name _ _ = _` (irule_at Any) >>
  qpat_assum `lookup_var_slot_from_layout _ _ _ _ = _` (irule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`v`,`tn1`,`t`,`marks`,`G1`] >> simp[] >>
  reverse (Cases_on `storage_trace_domain cx st0 (mid.storage_trace ++ [StorageRoot tr slot tv])`)
  >- (irule gas_outcome_full_bad_nil >> simp[] >>
      simp[ignore_bind_def,record_storage_event_def,bind_def,return_def,write_storage_slot_eq] >>
      Cases_on `cx.txn.is_static` >> Cases_on `encode_value tv v` >>
      Cases_on `tr` >> simp[set_storage_def]) >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
  `expr_body_pre cenv cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
  drule exprSimSourceTheory.expr_body_pre_eval >>
  disch_then (qspecl_then [`INL v`,`mid with gas_obs := []`] mp_tac) >>
  (impl_tac >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
    qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[])) >> strip_tac >>
  `expr_sim_inv cenv cx env es` by
    drule_then (ACCEPT_TAC o cj 1) expr_body_pre_static_facts >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
  `value_has_type tv v` by
    gvs[vyperTypeExprResultTheory.expr_result_typed_def,
        vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
        vyperTypeInvariantsTheory.value_result_typed_def,
        vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  `?writes. encode_value tv v = SOME writes` by
    metis_tac[cj 1 vyperTypingTheory.value_has_type_equiv,optionTheory.IS_SOME_EXISTS] >>
  `type_memory_bytes cenv (expr_type e) = type_memory_size tv` by
    (irule expr_sim_inv_memory_size >> goal_assum (drule_at Any) >> simp[]) >>
  `0 < type_memory_size tv /\ 0 < type_slot_size tv` by fs[type_memory_size_slots] >>
  `?sw. eval_operand op t = SOME sw` by fs[expr_post_def,expr_val_rel_def] >>
  `val_footprint tv v = type_memory_size tv` by
    metis_tac[nonbytes_evaluated_val_footprint] >>
  `val_store_size tv v = type_memory_size tv` by
    metis_tac[bodyDeclMemoryCoreTheory.val_store_size_non_bytestring] >>
  `op_taint tn1 op = {} /\
   (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==> val_in_memory tv v (w2n sw) mem) /\
   ?x. op = Var x /\ ptr_covers G1 tn1 x t (type_memory_size tv)` by
    (`op_taint tn1 op = {} /\ ptr_mem_ok cx (expr_type e) v op G1 tn1 t` by
       fs[ptr_val_ok_def] >>
     qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _`
       (qspecl_then [`tv`,`sw`] mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >>
     simp[] >> strip_tac >> simp[] >>
     gvs[ptr_covers_def,eval_operand_def] >> qexists `sz` >> simp[]) >>
  `w2n sw + type_memory_size tv <= t.vs_alloca_next` by
    (qpat_assum `expr_store_bound _ _ _ _ _`
       (qspecl_then [`tv`,`sw`] mp_tac o REWRITE_RULE [expr_store_bound_def]) >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx
    (mid with gas_obs := []) t` by fs[expr_post_def] >>
  `w2n sw + type_memory_size tv < dimword (:256)` by
    (drule stmt_state_rel_alloca_room >> simp[alloca_room_def] >> decide_tac) >>
  `alloca_inv t` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `t.vs_call_ctx.cc_static = cx.txn.is_static` by
    (drule stmt_state_rel_state_rel >> disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >>
     simp[call_ctx_rel_def]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `slot + type_slot_size tv <= dimword (:256)` by
    gvs[storage_trace_domain_def,valid_horizon_def,storage_observations_ok_def,
        storage_roots_fit_def,EVERY_APPEND] >>
  `w2n (n2w slot : bytes32) + type_slot_size tv <= dimword (:256)` by
    (`slot < dimword (:256)` by decide_tac >> simp[arithmeticTheory.LESS_MOD]) >>
  `!x. op = Var x ==> not_fresh_at sm x` by metis_tac[compile_lower_value_var] >>
  `ci_mono sa sm` by
    (qspec_then `sa` mp_tac
       (Q.SPECL [`cenv`,`expr_type e`,`e`] ci_mono_lower_value_compile_expr) >> simp[]) >>
  `ci_mono sm sb` by
    (qspecl_then [`cenv`,`op`,`Lit (n2w slot)`,`expr_type e`,`tr`,`sm`] mp_tac
       (cj 1 ci_mono_compile_store_slots) >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sb.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sm /\
   (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sm x) /\
   (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sm x) /\
   (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sm x)` by
    metis_tac[local_ptrs_reserved_next_var,freshWritesTheory.not_fresh_at_mono] >>
  `return_buf_frame d cenv sm t /\
    (!H. valid_horizon cx st0 H (mid.storage_trace ++ [StorageRoot tr slot tv]) ==>
      expr_post H ctx func cenv cx e es sa sm s0 (mid with gas_obs := []) v op t /\
      stmt_state_rel H ctx func cenv cx es s0 /\ dead_lo_ok H (DF H) lo cenv cx /\
      ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G1 tn1 t)` by
    (irule body_assign_toplevel_word_full_store_pre >>
     goal_assum (drule_at Any) >> simp[] >> qexists `marks` >> simp[]) >>
  Cases_on `cx.txn.is_static` >- suspend "static" >> suspend "normal"
QED

Resume body_assign_toplevel_copy_after_rhs_frame[static]:
  `type_slot_size tv <> 0` by decide_tac >>
  qabbrev_tac `ef = mid with <|gas_obs := [];
    storage_trace := mid.storage_trace ++ [StorageRoot tr slot tv]|>` >>
  mp_tac (Q.INST [`s` |-> `t`,`sa` |-> `sm`,`src` |-> `op`,
    `dst` |-> `Lit (n2w slot)`,`ty` |-> `expr_type e`,`dw` |-> `n2w slot`,
    `G` |-> `G1`,`tn` |-> `tn1`,`ee` |-> `ef`]
    (SPEC_ALL body_assign_slots_full_static_exit)) >>
  impl_tac
  >- (asm_rewrite_tac[] >> simp[eval_operand_def,op_taint_def] >> metis_tac[]) >>
  simp[] >>
  disch_then (qx_choose_then `u` (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac))) >>
  irule gas_outcome_full_intro >>
  qexistsl [`Gf`,`ef`,`[]`,`Abort ExHalt_abort (halt_state (set_returndata [] u))`,
           `INR (Error (RuntimeError "write in static context"))`,`tnf`] >>
  simp[Abbr `ef`,ignore_bind_def,record_storage_event_def,return_def,bind_def,write_storage_slot_eq] >>
  simp[stmt_exit_ptr_def,exprSimDefsTheory.expr_exit_def,halt_exit_not_halt]
QED

Resume body_assign_toplevel_copy_after_rhs_frame[normal]:
  mp_tac (Q.INST [`s` |-> `t`,`sa` |-> `sm`,`src` |-> `op`,
    `dst` |-> `Lit (n2w slot)`,`ty` |-> `expr_type e`,`dw` |-> `n2w slot`,
    `G` |-> `G1`,`tn` |-> `tn1`]
    (SPEC_ALL body_assign_slots_full_frame_path)) >>
  impl_tac
  >- (asm_rewrite_tac[] >> simp[eval_operand_def,op_taint_def] >> metis_tac[]) >>
  disch_then (qx_choose_then `u` (qx_choose_then `ks` (qx_choose_then `Gf`
    (qx_choose_then `tnf` (REPEAT_TCL CONJUNCTS_THEN assume_tac))))) >>
  qabbrev_tac `ee = mid with gas_obs := []` >>
  qabbrev_tac `ef = set_storage cx ee tr (apply_writes (n2w slot) writes (get_storage cx ee tr))` >>
  `write_storage_slot cx tr (n2w slot) tv v ee = (INL (),ef)` by
    simp[Abbr `ef`,write_storage_slot_eq] >>
  `ef.gas_obs = [] /\ ef.scopes = mid.scopes` by
    (Cases_on `tr` >> simp[Abbr `ef`, Abbr `ee`,set_storage_def]) >>
  `MAP FDOM ef.scopes = MAP FDOM es.scopes` by
    (drule stmtSimDefsTheory.eval_read_preserves_scopes_dom >> simp[Abbr `ee`]) >>
  `!bw cap. d = SOME (bw, cap) ==> allocas_from (w2n bw + cap) u` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t,G1,tn1)` (fn path =>
       qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
         qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
           mp_tac (MATCH_MP return_buf_allocas_path (LIST_CONJ [path,frame,sep]))))) >>
     simp[allocas_from_def]) >>
  `~block_is_terminated sb` by (drule (cj 1 stmtSimAssignStorageSparseTheory.store_slots_open) >> simp[]) >>
  irule gas_outcome_full_intro >>
  qexistsl [`Gf`,`ef with storage_trace := mid.storage_trace ++ [StorageRoot tr slot tv]`,
            `[]`,`OK u`,`INL ()`,`tnf`] >>
  simp[] >> conj_tac
  >- (gen_tac >> simp[ignore_bind_def,record_storage_event_def,return_def,bind_def] >>
      drule write_storage_slot_storage_trace >>
      disch_then (qspec_then `mid.storage_trace ++ [StorageRoot tr slot tv]` assume_tac) >>
      qpat_assum `write_storage_slot _ _ _ _ _ (ee with storage_trace := _) = _`
        (mp_tac o Q.AP_TERM `\p. (FST p,SND p with gas_obs := tail)`) >>
      simp[Abbr `ee`,GSYM write_storage_slot_gas_obs]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H (_ ++ _) ==> _` (drule_then strip_assume_tac) >>
  `MEM (tr,n2w slot,tv) (FST H) /\ regions_consistent (FST H) /\
   storage_locks_separated (FST H) (SND H)` by
    gvs[valid_horizon_def,storage_observations_ok_def,storage_trace_regions_def,
        MAP_APPEND,FLAT_APPEND,EVERY_APPEND] >>
  `stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H)` by
    fs[expr_post_def] >>
  qpat_assum `!H ee env rootk root path delta. _ ==> _`
    (qspecl_then [`H`,`ee`,`env`,`n2w slot`,`tv`,`[]`,`0`] mp_tac) >>
  (impl_tac >- simp[vyperStoragePlaceRegionTheory.storage_subregion_def]) >>
  disch_then (qx_choose_then `ef'` strip_assume_tac) >>
  `ef' = ef` by metis_tac[pairTheory.PAIR_EQ] >>
  `well_formed_type_value tv` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `storage_well_formed_on cx ef (FST H)` by
    (irule typed_write_preserves_storage_well_formed_on >>
     conj_tac >- simp[] >>
     qexistsl [`tr`,`n2w slot`,`ee`,`tv`,`v`] >> simp[]) >>
  qpat_x_assum `ef' = ef` SUBST_ALL_TAC >>
  `!y. not_fresh_at sa y ==> not_fresh_at sm y` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!y w. not_fresh_at sa y /\ lookup_var y s0 = SOME w ==> lookup_var y u = SOME w` by
    (fs[expr_post_def] >> metis_tac[]) >>
  qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_post_def]) >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ G1 tn1`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [ghost_kept_at_def]) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by metis_tac[] >>
  `return_buf_sep d cenv
      (ef with <|gas_obs := []; storage_trace := mid.storage_trace ++ [StorageRoot tr slot tv]|>) u` by
    (irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
     conj_tac >- fs[] >>
     qexistsl_tac [`H`,`ctx`,`cx`,`es`, `func`,`s0`,`sa`] >> simp[]) >>
  disj1_tac >> pure_once_rewrite_tac[GSYM evaluation_state_fupdcanon] >>
  `(ef with gas_obs := []) = ef` by simp[evaluation_state_component_equality] >>
  simp[stmt_lands_def,cenv_top_ext_refl,storage_well_formed_on_def] >>
  conj_tac >- fs[storage_well_formed_on_def] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
    (mp_then Any irule alloca_frame_of_mem_frame) >>
  simp[] >> metis_tac[]
QED

Finalise body_assign_toplevel_copy_after_rhs_frame

Theorem body_assign_topcopy_frontend[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) ==>
    occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) /\
  call_evaluation_safe cx
    (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget (src,id))) e)) /\
  supported_variable_decl tops (src,id) = SOME (Private, mut, ty, SOME ast_slot) /\
  (mut = Storage \/ mut = Transient) /\
  ~is_bytestring_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
  expr_type e = ty ==>
  expr_body_pre cenv cx env e es /\
  ~is_bytestring_type ty /\ ~has_length_word ty
Proof
  strip_tac >>
  `supported_expr tops e` by
    gvs[Once supported_stmt_def, supported_assignment_def] >>
  `expr_body_pre cenv cx env e es` by
    metis_tac[topcopy_rhs_pre_supported] >>
  Cases_on `ty` >> gvs[has_length_word_def] >>
  rename1 `ArrayT _ bd` >> Cases_on `bd` >> gvs[has_length_word_def]
QED

Theorem body_assign_topcopy_slots_code[local]:
  stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e)
    sa = (ce,sb) /\
  FLOOKUP cenv.ce_module_vars nsid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  cenv.ce_hashmap_info nsid = NONE /\ cenv.ce_module_var_type nsid = SOME ty /\
  ~is_word_type ty /\ expr_type e = ty /\ ~has_length_word ty /\
  lowered_value_type cenv e = expr_type e /\ fn_has_code sa sb func ==>
  ce = cenv /\ ?op sm.
    lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
    compile_store_slots cenv op (Lit slot) ty tr sm = ((),sb) /\
    ci_mono sa sm /\ ci_mono sm sb /\
    fn_has_code sa sm func /\ fn_has_code sm sb func
Proof
  strip_tac >>
  `~(has_length_word (expr_type e) /\ is_empty_value_expr e)` by simp[] >>
  drule_all assign_storage_copy_code_parts >> strip_tac >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (op,sm)` >>
  `compile_store_slots cenv op (Lit slot) ty tr sm = ((),sb)` by
    (qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `tr` >> gvs[compile_assign_value_def, comp_bind_def, comp_return_def]) >>
  `ci_mono sa sm` by
    (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`]
       mp_tac ci_mono_lower_value_compile_expr >> simp[]) >>
  `ci_mono sm sb` by
    (qspecl_then [`cenv`,`op`,`Lit slot`,`ty`,`tr`,`sm`]
       mp_tac (cj 1 ci_mono_compile_store_slots) >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  simp[] >> qexistsl_tac [`op`,`sm`] >> simp[]
QED

Theorem body_assign_toplevel_copy_entry[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Assign (BaseTarget (TopLevelNameTarget nsid)) e) ==>
    occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
  call_evaluation_safe cx
    (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) /\
  supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME ast_slot) /\
  (mut = Storage \/ mut = Transient) /\ ~is_word_type ty /\
  ~is_bytestring_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
  0 < type_memory_bytes cenv ty /\ expr_type e = ty /\
  lowered_value_type cenv e = expr_type e /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e)
    sa = (ce,sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ret_ty
    (gas_shadow_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
    shadow_sa = (gas_shadow_env T ce,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func ==>
  ce = cenv /\ expr_body_pre cenv cx env e es /\
  ~is_bytestring_type ty /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  ?id tr id_str slot tv op sm shadow_sm.
    nsid = (NONE,id) /\ get_module_code cx NONE = SOME tops /\
    find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,id_str) /\
    lookup_var_slot_from_layout cx tr NONE id_str = SOME slot /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    storage_var_info cx NONE id = SOME (tr,slot,tv) /\
    type_memory_bytes cenv ty = type_memory_size tv /\ 0 < type_slot_size tv /\
    lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa =
      (op,shadow_sm) /\
    gas_shadow_state sm shadow_sm /\
    compile_store_slots cenv op (Lit (n2w slot)) ty tr sm = ((),sb) /\
    ci_mono sa sm /\ ci_mono sm sb /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code shadow_sa shadow_sm shadow_func
Proof
  Cases_on `nsid` >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all body_assign_topcopy_frontend >> strip_tac >>
  drule_all topcopy_target >> strip_tac >> gvs[] >>
  drule_all topcopy_memory_size >> strip_tac >>
  drule stmt_state_rel_vars_rels >> strip_tac >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  drule body_assign_topcopy_slots_code >>
  disch_then (qspecl_then [`expr_type e`,`tr`,`n2w off`,`func`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[] >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (op,sm)` >>
  `?shadow_sm. lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa = (op,shadow_sm) /\
       gas_shadow_state sm shadow_sm` by
    (`FST (lower_value compile_expr cenv (expr_type e) e sa) =
       FST (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
         (gas_shadow_expr e) shadow_sa) /\
       gas_shadow_state (SND (lower_value compile_expr cenv (expr_type e) e sa))
         (SND (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
           (gas_shadow_expr e) shadow_sa))` by
       (irule (REWRITE_RULE [gas_shadow_compiles_def]
          (Q.INST [`sd` |-> `T`] gas_shadow_stmt_lower_value_env)) >> simp[]) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa` >> gvs[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     simp[gas_shadow_stmt_def, gas_shadow_assignment_def, gas_shadow_expr_def] >> strip_tac >>
     qpat_x_assum `stmt_env _ _ _ (Assign _ e) sa = _` kall_tac >>
     `expr_type (gas_shadow_expr e) = expr_type e` by simp[gas_shadow_expr_type] >>
     `lowered_value_type (gas_shadow_env T cenv) (gas_shadow_expr e) =
        expr_type (gas_shadow_expr e)` by simp[gas_shadow_expr_type] >>
     `FLOOKUP (gas_shadow_env T cenv).ce_module_vars (NONE,r) =
        SOME (if tr then TransientLoc (n2w off) else StorageLoc (n2w off))` by simp[] >>
     `(gas_shadow_env T cenv).ce_hashmap_info (NONE,r) = NONE` by simp[] >>
     `(gas_shadow_env T cenv).ce_module_var_type (NONE,r) =
        SOME (expr_type (gas_shadow_expr e))` by simp[gas_shadow_expr_type] >>
     drule body_assign_topcopy_slots_code >>
     disch_then (qspecl_then [`expr_type (gas_shadow_expr e)`,`tr`,`n2w off`,`shadow_func`] mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     gvs[gas_shadow_expr_type]) >>
  drule_then assume_tac expr_body_pre_gas_admissible >>
  simp[storage_var_info_def] >>
  qexistsl_tac [`op`,`sm`,`shadow_sm`] >> simp[]
QED

(* The RHS of a supported base-target assignment. *)
Theorem body_assign_rhs_pre_mods[local]:
  contract_inv mods exps ctx cenv cx /\
  supported_stmt (main_module mods) bindings (Assign (BaseTarget t) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (BaseTarget t) e) ==> occurs_abi_decode_target target (main_module mods)) /\
  expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e /\
  stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
  ~supported_expr_exists (unallocated_bare_global_root cenv env) e ==>
  expr_body_pre_mods mods cenv cx env e es
Proof
  strip_tac >>
  drule_then assume_tac contract_inv_cenv_modules >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
     simp[int_calls_stmt_def, int_calls_atarget_def] >>
     metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right]) >>
  mp_tac (Q.INST [`ctx` |-> `ctx`, `exps` |-> `exps`]
                  stmt_expr_body_pre_main_alloc_mods) >>
  fs[stmt_exprs_ok_def, Once supported_stmt_def, supported_assignment_def,
     supported_stmt_expr_exists_def, supported_assignment_exists_def,
     alloc_limits_stmt_def]
QED

Theorem body_assign_empty_target_rhs_pre[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget t) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (BaseTarget t) e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
  stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) ==>
  expr_body_pre cenv cx env e es
Proof
  strip_tac >>
  mp_tac (Q.INST [`tops` |-> `tops`, `ctx` |-> `ctx`,
                  `s` |-> `Assign (BaseTarget t) e`]
          body_inv_stmt_expr_pre_singleton) >>
  simp[supported_stmt_expr_exists_def, supported_assignment_exists_def] >>
  disch_then irule >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`,
                  `ctx` |-> `ctx`, `bindings` |-> `bindings`, `t` |-> `t`]
          body_assign_rhs_pre_mods) >>
  simp[main_module_def, alistTheory.ALOOKUP_def]
QED

Theorem body_assign_expr_vv_full[local]:
  body_expr_full_ok cx e ==>
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env e es ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  simp[Once body_expr_full_ok_def] >> metis_tac[]
QED

(* A word field of a storage struct. *)
Theorem body_assign_attr_storage_full:
  !cx nsid fld fty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (AttributeTarget (TopLevelNameTarget nsid) fld)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    supported_storage_field_write tops nsid fld /\
    type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
      SOME (Type fty) /\
    is_word_type fty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e)))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e)) es
Proof
  rpt gen_tac >> strip_tac >> PairCases_on `nsid` >>
  rename1 `supported_storage_field_write tops (src,id) fld` >>
  `well_typed_expr env e /\ expr_type e = fty` by
    (gvs[type_stmt_def, atarget_accepts_def] >> metis_tac[type_widens_to_word]) >>
  `src = NONE` by metis_tac[body_inv_toplevel_target_main,
    type_place_target_AttributeTarget, optionTheory.IS_SOME_EXISTS] >>
  `src = NONE /\ find_var_decl_by_name id tops <> NONE /\
   ?vis mut sid slot. MEM (VariableDecl vis mut id (StructT sid) slot) tops` by
    (drule_all supported_storage_field_write_decl >> simp[]) >>
  gvs[] >>
  drule_then strip_assume_tac body_inv_main_support >>
  drule_then assume_tac body_inv_contract >>
  `ALOOKUP [((NONE:num option),tops)] NONE = SOME tops` by
    simp[alistTheory.ALOOKUP_def] >>
  `cenv.ce_hashmap_info (NONE,id) = NONE /\
   cenv.ce_module_var_type (NONE,id) = SOME (StructT sid)` by
    drule_all_then (fn th => simp[th]) contract_inv_variable_metadata >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  gvs[type_place_target_AttributeTarget, type_place_target_TopLevelNameTarget]
  >- (`?ts. get_module_code cx NONE = SOME ts /\
              find_var_decl_by_name id ts = NONE` by
        (fs[env_consistent_def, env_context_consistent_def] >>
         first_x_assum drule >> strip_tac >>
         metis_tac[optionTheory.SOME_11]) >>
      metis_tac[optionTheory.SOME_11]) >>
  drule_all env_consistent_toplevel_storage_static >> strip_tac >>
  `ts = tops` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `ts = tops` SUBST_ALL_TAC >>
  `ALOOKUP [((NONE:num option),tops)] NONE = SOME tops` by
    simp[alistTheory.ALOOKUP_def] >>
  drule_all_then strip_assume_tac body_inv_storage_var_types_mods >> gvs[] >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
              fld = SOME (expr_type e,fsz)` by
    metis_tac[attribute_type_struct_field] >>
  `expr_body_pre cenv cx env e es` by
    drule_all_then ACCEPT_TAC body_assign_empty_target_rhs_pre >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (drule body_assign_expr_vv_full >>
     disch_then (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`,
       `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `expr_type e`, `es`]
       mp_tac) >> simp[]) >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  irule compile_assign_attr_storage_full >> simp[] >> metis_tac[]
QED

(* Assignment to a word field of a memory struct local. *)

Theorem body_assign_field_robust_update:
  !fs vals fld off ftv v dirty s b.
  value_has_type (StructTV fs) (StructV vals) /\
  mem_field_offset fs fld = SOME (off,ftv) /\
  store_lays_out ftv ftv v /\
  (!mem. mem_agree_outside dirty s.vs_memory mem ==>
    val_in_memory (StructTV fs) (StructV vals) b mem)
  ==>
  !mem. mem_agree_outside
    (dirty DIFF {i | b+off <= i /\ i < b+off+32})
    (mstore (b+off) (typed_val_to_w256 ftv v) s).vs_memory mem ==>
    val_in_memory (StructTV fs)
      (StructV (AFUPDKEY fld (K v) vals)) b mem
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  qabbrev_tac `h = (write_memory_with_expansion (b+off)
    (mem_bytes_at (b+off) 32 s.vs_memory)
    (s with vs_memory := mem)).vs_memory` >>
  `mem_bytes_at (b+off) 32 h = mem_bytes_at (b+off) 32 s.vs_memory` by
    (qspecl_then [`b+off`, `mem_bytes_at (b+off) 32 s.vs_memory`,
       `s with vs_memory := mem`] mp_tac write_memory_mem_bytes_at_same >>
     simp[LENGTH_mem_bytes_at_proof, Abbr `h`]) >>
  `!a n. a+n <= b+off \/ b+off+32 <= a ==>
    mem_bytes_at a n h = mem_bytes_at a n mem` by
    (rpt strip_tac >>
     simp[Abbr `h`, write_memory_mem_bytes_at_disjoint,
          LENGTH_mem_bytes_at_proof]) >>
  `mem_agree_outside dirty s.vs_memory h` by
    (simp[mem_agree_outside_def] >> rpt strip_tac >>
     Cases_on `b+off <= i /\ i < b+off+32`
     >- metis_tac[mem_bytes_at_eq_byte] >>
     `i+1 <= b+off \/ b+off+32 <= i` by decide_tac >>
     `mem_bytes_at i 1 h = mem_bytes_at i 1 mem` by metis_tac[] >>
     `mem_bytes_at i 1 (mstore (b+off) (typed_val_to_w256 ftv v) s).vs_memory =
      mem_bytes_at i 1 s.vs_memory` by
       (irule mstore_mem_bytes_at_disjoint_proof >> simp[]) >>
     fs[mem_agree_outside_def] >> metis_tac[]) >>
  `val_in_memory (StructTV fs) (StructV vals) b h` by metis_tac[] >>
  `val_in_memory ftv v (b+off) mem` by
    (drule store_lays_out_robust_ptr >> disch_then irule >>
     goal_assum (drule_at Any)) >>
  `type_memory_size ftv = 32` by fs[store_lays_out_def] >>
  irule struct_update_bounded_frame >>
  simp[] >> qexists `h` >>
  simp[] >> rpt strip_tac >> metis_tac[ADD_ASSOC]
QED

Theorem body_assign_field_prefix_joint:
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  is_word_type (expr_type e) /\
  emit_op ADD [Var p; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value cenv vv sn = (op,su) /\
  fn_has_code sm sn func /\ fn_has_code sn su func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee raw vv s /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\
  (!v. read_result cx raw ee = (INL v,ee) ==> value_has_type rty v) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee raw vv s /\
  ptr_vv_ok cx (post_value_type cenv e) raw vv ee G tn s /\
  (!t pp. vv = LocatedValue t pp /\ pp.ptr_location = LocMemory ==>
           ptr_buf_ok cenv e pp.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?v. read_result cx raw ee = (INL v,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
              eval_operand (vv_operand vv) s = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                     val_in_memory rt v (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_covers G tn p s capacity /\ lookup_var p s = SOME w0 /\
  FLOOKUP G p = SOME (b0,cap) /\
  w2n w0 + off < dimword(:256) /\ off + 32 <= capacity ==>
  ?out q HG tf v z G' tn'.
    dst = Var out /\ not_fresh_at sn out /\
    q = (update_var out (w0 + n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
    q.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\
    read_result cx raw ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (OK q,HG,tf) /\
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (q,HG,tf) [] (OK z,G',tn') /\
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (OK z,G',tn') /\
       expr_post H ctx func cenv cx e es sa su s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    z.vs_current_bb = su.cs_current_bb /\
    z.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    wb_frame cenv ee ee sn q z /\ ghost_kept_at lo cenv ee sn HG tf q G' tn' /\
    lookup_var out z = SOME (w0 + n2w off) /\
    FLOOKUP G' out = SOME (b0,cap) /\ op_taint tn' dst = {} /\
    ptr_covers G' tn' out z 32
Proof
  strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `i = mk_inst sm.cs_next_id ADD [Var p; Lit (n2w off)] [out]` >>
  qabbrev_tac `u = update_var out (w0 + n2w off) s` >>
  qabbrev_tac `q = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `HG = step_prov PG G i u` >>
  qabbrev_tac `tf = step_taint i s u tn` >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >> conj_tac
     >- fs[ghost_inv_at_def] >>
     `stmt_state_rel (storage_trace_horizon ee.storage_trace)
        ctx func cenv cx ee s` by fs[vv_post_def] >>
     drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `dst = Var out /\
   (!D lo' explicit'. allocas_from lo' s ==>
     gas_origin_ptr_path (D,lo',explicit',ctx,func,PG) (s,G,tn) [] (OK q,HG,tf)) /\
   FLOOKUP HG out = op_prov G (Var p) /\
   op_taint tf dst = {} /\ tf.t_mem = tn.t_mem /\
   tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
   (!x. x <> out ==> FLOOKUP HG x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x))` by
    (irule attribute_add_full_frame >>
     simp[Abbr `out`, Abbr `i`, Abbr `u`, Abbr `q`, Abbr `HG`, Abbr `tf`,
          eval_operand_def] >>
     conj_tac >- fs[ptr_covers_def] >>
     qexistsl_tac [`n2w off`, `sm`, `sn`] >> simp[]) >>
  `~not_fresh_at sm out /\
   (!x. not_fresh_at sm x ==> x <> out) /\
   (!x. not_fresh_at sa x ==> not_fresh_at sm x)` by
    (simp[Abbr `out`, not_fresh_at_def, ASCIInumbersTheory.toString_11] >>
     metis_tac[LESS_LESS_EQ_TRANS]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
   sn.cs_current_bb = sm.cs_current_bb /\
   sn.cs_current_insts = sm.cs_current_insts ++ [i] /\ not_fresh_at sn out` by
    (gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def, Abbr `i`, Abbr `out`,
        not_fresh_at_def, ASCIInumbersTheory.toString_11, mk_inst_def]) >>
  `q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
   q.vs_memory = s.vs_memory /\ q.vs_accounts = s.vs_accounts /\
   q.vs_transient = s.vs_transient /\ q.vs_call_ctx = s.vs_call_ctx /\
   ~q.vs_halted /\ q.vs_current_bb = sn.cs_current_bb /\
   q.vs_inst_idx = LENGTH sn.cs_current_insts` by
    simp[Abbr `q`, Abbr `u`, update_var_def] >>
  `!x. not_fresh_at sm x ==>
    lookup_var x q = lookup_var x s /\ FLOOKUP HG x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[Abbr `q`, Abbr `u`, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
   op_taint tf (vv_operand vv) = op_taint tn (vv_operand vv) /\
   op_prov HG (vv_operand vv) = op_prov G (vv_operand vv)` by
    (Cases_on `vv_operand vv` >>
     gvs[eval_operand_def, op_taint_def, op_prov_def,
         Abbr `q`, Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx e es sa sm s0 ee raw vv q /\
    ghost_inv_at (DF H) lo d cenv cx ee HG tf q` by
    (qx_gen_tac `H` >> strip_tac >> conj_tac
     >- (simp[Abbr `q`, Abbr `u`] >> irule vv_post_update_var >>
         simp[] >> qexists_tac `sm` >> simp[] >> metis_tac[]) >>
     mp_tac (Q.INST [`tn'` |-> `tf`, `G'` |-> `HG`,
       `w` |-> `w0 + n2w off`, `n` |-> `SUC s.vs_inst_idx`]
       attribute_fresh_full_ghost_update) >>
     simp[Abbr `out`] >>
     strip_tac >> fs[Abbr `q`, Abbr `u`, ADD1] >> metis_tac[]) >>
  `vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee raw vv q` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`vv_store_bound _ _ _ _ _ _ s`,
        `eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s`,
        `q.vs_alloca_next = s.vs_alloca_next`] >>
     rpt (pop_assum kall_tac) >> Cases_on `vv` >>
     simp[vv_store_bound_def, vv_operand_def] >>
     rpt strip_tac >> metis_tac[]) >>
  `!x. vv_operand vv = Var x ==> FLOOKUP HG x = FLOOKUP G x` by metis_tac[] >>
  `ptr_vv_ok cx (post_value_type cenv e) raw vv ee HG tf q` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_vv_ok _ _ _ _ _ G tn s`,
        `eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s`,
        `op_taint tf (vv_operand vv) = op_taint tn (vv_operand vv)`,
        `op_prov HG (vv_operand vv) = op_prov G (vv_operand vv)`,
        `!x. vv_operand vv = Var x ==> FLOOKUP HG x = FLOOKUP G x`,
        `tf.t_mem = tn.t_mem`, `tf.t_stor = tn.t_stor`,
        `tf.t_trans = tn.t_trans`, `q.vs_memory = s.vs_memory`,
        `q.vs_accounts = s.vs_accounts`, `q.vs_transient = s.vs_transient`,
        `q.vs_call_ctx = s.vs_call_ctx`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `vv` >>
     fs[ptr_vv_ok_def, ptr_val_ok_def, ptr_mem_ok_def, vv_operand_def] >>
     metis_tac[]) >>
  `ghost_kept_at lo cenv es sa Gi ti s0 HG tf` by
    (irule ghost_kept_at_clean_suffix >> simp[] >>
     qexistsl_tac [`G`, `tn`] >> simp[] >> metis_tac[]) >>
  `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?v. read_result cx raw ee = (INL v,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
              eval_operand (vv_operand vv) q = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tf.t_mem q.vs_memory mem ==>
                     val_in_memory rt v (w2n w) mem)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _`,
        `eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s`,
        `tf.t_mem = tn.t_mem`, `q.vs_memory = s.vs_memory`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     qpat_assum `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _` drule_all >>
     strip_tac >> qexists_tac `v` >> fs[]) >>
  `(!t pp. vv = LocatedValue t pp /\ pp.ptr_location = LocMemory ==>
       ptr_buf_ok cenv e pp.ptr_operand HG q)` by
    (rpt strip_tac >>
     `ptr_buf_ok cenv e (vv_operand vv) G s` by
       metis_tac[vv_operand_def] >>
     `ptr_buf_ok cenv e (vv_operand vv) HG q` by
       (fs[ptr_buf_ok_def] >> metis_tac[]) >>
     gvs[vv_operand_def]) >>
  `alloca_inv s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     `stmt_state_rel (storage_trace_horizon ee.storage_trace)
        ctx func cenv cx ee s` by fs[vv_post_def] >>
     metis_tac[stmt_state_rel_local_ptrs_alloca]) >>
  `alloca_history func q` by
    (qspecl_then [`[i]`, `sm`, `sn`, `s`, `u`] mp_tac emitted_alloca_history >>
     (impl_tac >-
       simp[Abbr `i`, Abbr `u`, mk_inst_def, is_terminator_def,
            run_inst_seq_def, step_inst_base_def, exec_pure2_def,
            eval_operand_def]) >> simp[Abbr `q`, ADD1]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
    simp[Abbr `q`, Abbr `u`, allocas_below_fmp_def, update_var_def] >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  mp_tac (Q.INST [`sb` |-> `sn`, `s` |-> `q`, `G` |-> `HG`,
      `tn` |-> `tf`, `tv` |-> `raw`, `sc` |-> `su`, `ty` |-> `expr_type e`]
    unwrap_word_value_origin_ptr) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  strip_tac >>
  `lookup_var out q = SOME (w0 + n2w off)` by
    simp[Abbr `q`, Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `lookup_var out z = SOME (w0 + n2w off) /\
   FLOOKUP G' out = SOME (b0,cap) /\ op_taint tn' (Var out) = {}` by
    (qpat_assum `!x. not_fresh_at sn x ==> _` (qspec_then `out` mp_tac) >>
     simp[op_prov_def] >> metis_tac[]) >>
  `ptr_covers G' tn' out z 32` by
    (irule assign_base_ptr_covers_offset_address >> simp[] >>
     qexistsl_tac [`G`, `off`, `p`, `s`, `tn`, `capacity`, `w0`] >>
     simp[]) >>
  qexistsl_tac [`out`, `q`, `HG`, `tf`, `v`, `z`, `G'`, `tn'`] >>
  simp[] >> conj_tac
  >- simp[Abbr `q`, Abbr `u`] >>
  qx_gen_tac `H` >> strip_tac >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK q,HG,tf)` by metis_tac[] >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (q,HG,tf) [] (OK z,G',tn')` by metis_tac[] >>
  simp[] >>
  qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK q,HG,tf)`
    (mp_then Any mp_tac gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`q`, `HG`, `tf`, `[]`, `OK z`, `G'`, `tn'`] mp_tac) >>
  simp[]
QED

Theorem body_assign_field_store_joint_frame:
  emit_void MSTORE [Var dst;op] su = ((),sf) /\ fn_has_code su sf func /\
  fn_inst_ids_distinct func /\ ~z.vs_halted /\
  z.vs_current_bb = su.cs_current_bb /\
  z.vs_inst_idx = LENGTH su.cs_current_insts /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  lookup_var p z = SOME w0 /\ lookup_var dst z = SOME (w0 + n2w off) /\
  eval_operand op z = SOME (typed_val_to_w256 ftv v) /\ op_taint tn op = {} /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout flds fs /\ struct_has_type fs vals /\ ALOOKUP fs fld = SOME ftv /\
  store_lays_out ftv ftv v /\ off = struct_field_offset flds fld /\
  off + 32 <= sz /\ lo <= w2n w0 /\ ptr_covers G tn dst z 32 /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  P H0 /\
  (!H. P H ==> stmt_state_rel H ctx func cenv cx es z /\
     ghost_inv_at (DF H) lo d cenv cx es G tn z) /\
  (!mem. mem_agree_outside
      (tn.t_mem DIFF {i | w2n w0 + off <= i /\ i < w2n w0 + off + 32})
      (mstore (w2n w0 + off) (typed_val_to_w256 ftv v) z).vs_memory mem ==>
    val_in_memory entry.type (StructV (AFUPDKEY fld (K v) vals)) (w2n w0) mem) /\
  alloca_history func z /\ return_buf_frame d cenv su z /\
  alloca_frame c0 es0 sa s0 cenv es z /\
  (!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa.cs_next_id /\
    (!name b cap. local_region c0 es0.scopes s0 name b cap ==>
      a+n <= b \/ b+cap <= a) /\ a <= i /\ i < a+n /\ i IN tn.t_mem ==>
    i IN tn0.t_mem) ==>
  ?t tf.
    t = (mstore (w2n w0 + off) (typed_val_to_w256 ftv v) z) with
      vs_inst_idx := SUC z.vs_inst_idx /\
    tf = step_taint (mk_inst su.cs_next_id MSTORE [Var dst;op] []) z
      (mstore (w2n w0 + off) (typed_val_to_w256 ftv v) z) tn /\
    step_prov PG G (mk_inst su.cs_next_id MSTORE [Var dst;op] [])
      (mstore (w2n w0 + off) (typed_val_to_w256 ftv v) z) = G /\
    (!H. P H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (z,G,tn) [] (OK t,G,tf) /\
      stmt_state_rel H ctx func cenv cx
        (es with scopes := pre ++ (sc |+ (id,entry with
          <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) t /\
      ghost_inv_at (DF H) lo d cenv cx
        (es with scopes := pre ++ (sc |+ (id,entry with
          <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) G tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\
    return_buf_frame d cenv sf t /\ alloca_history func t /\
    alloca_frame c0 es0 sa s0 cenv
      (es with scopes := pre ++ (sc |+ (id,entry with
        <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) t /\
    t.vs_allocas = z.vs_allocas /\ t.vs_alloca_next = z.vs_alloca_next /\
    (!x. lookup_var x t = lookup_var x z) /\
    tf.t_var = tn.t_var /\ tf.t_mem = tn.t_mem DIFF
      {i | w2n w0 + off <= i /\ i < w2n w0 + off + 32} /\
    (!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa.cs_next_id /\
      (!name b cap. local_region c0 es0.scopes s0 name b cap ==>
        a+n <= b \/ b+cap <= a) /\ a <= i /\ i < a+n /\ i IN tf.t_mem ==>
      i IN tn0.t_mem)
Proof
  strip_tac >> qpat_x_assum `off = _` SUBST_ALL_TAC >>
  qabbrev_tac `off = struct_field_offset flds fld` >>
  `stmt_state_rel H0 ctx func cenv cx es z /\
   ghost_inv_at (DF H0) lo d cenv cx es G tn z` by metis_tac[] >>
  `local_ptrs_rel func cenv es.scopes z /\ alloca_inv z` by
    metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `w2n w0 + sz <= z.vs_alloca_next` by
    (fs[local_ptrs_rel_def] >> first_x_assum drule_all >> simp[]) >>
  `z.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_alloca_room,alloca_room_next_lt] >>
  `w2n (w0 + n2w off) = w2n w0 + off` by
    (irule buffer_offset_no_wrap >> qexists_tac `sz` >> simp[]) >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`,`G`,`su.cs_next_id`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `tf.t_var = tn.t_var` >>
  qabbrev_tac `t = (mstore (w2n w0 + off) (typed_val_to_w256 ftv v) z) with
    vs_inst_idx := SUC z.vs_inst_idx` >>
  `sf.cs_current_bb = su.cs_current_bb /\
   sf.cs_current_insts = su.cs_current_insts ++
     [mk_inst su.cs_next_id MSTORE [Var dst;op] []] /\
   sf.cs_next_var = su.cs_next_var` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def,comp_bind_def,comp_ignore_bind_def,fresh_id_def,
          emit_def,comp_return_def] >> strip_tac >> gvs[]) >>
  `t.vs_allocas = z.vs_allocas /\ t.vs_alloca_next = z.vs_alloca_next /\
   (!x. lookup_var x t = lookup_var x z)` by
    simp[Abbr `t`,mstore_def,lookup_var_def] >>
  qexistsl_tac [`t`,`tf`] >> gvs[Abbr `t`,Abbr `tf`] >>
  conj_tac >- suspend "family" >>
  TRY (conj_tac >- (qmatch_goalsub_rename_tac `~u.vs_halted` >> simp[mstore_def])) >>
  conj_tac >- suspend "return" >>
  conj_tac >- suspend "history" >>
  conj_tac >- suspend "frame" >>
  rpt strip_tac >> first_x_assum irule >> metis_tac[]
QED

Resume body_assign_field_store_joint_frame[family]:
  gen_tac >> disch_tac >>
  `stmt_state_rel H ctx func cenv cx es z /\
   ghost_inv_at (DF H) lo d cenv cx es G tn z` by metis_tac[] >>
  conj_tac >- suspend "edge" >>
  conj_tac >- (simp[stmt_state_rel_inst_idx,Abbr `off`] >>
    drule_all stmt_state_rel_write_field >> simp[arithmeticTheory.ADD_COMM]) >>
  suspend "ghost"
QED

Resume body_assign_field_store_joint_frame[edge]:
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `allocas_from lo z` by fs[ghost_inv_at_def] >>
  `?bb. lookup_block z.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb z.vs_inst_idx =
      SOME (mk_inst su.cs_next_id MSTORE [Var dst;op] [])` by
    (drule emitted_insts_emit_void >> strip_tac >>
     drule emit_void_same_blocks >> simp[same_blocks_def] >> strip_tac >>
     drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> simp[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `ptr_inst_ok (DF H) lo 0 ctx func G tn
    (mk_inst su.cs_next_id MSTORE [Var dst;op] []) z` by
    (irule ptr_inst_ok_mstore_tainted >> simp[]) >>
  `step_inst_base (mk_inst su.cs_next_id MSTORE [Var dst;op] []) z =
    OK (mstore (off + w2n w0) (typed_val_to_w256 ftv v) z)` by
    (qspecl_then [`Var dst`,`op`] mp_tac step_MSTORE >>
     simp[eval_operand_def] >> metis_tac[]) >>
  `inst_mem_below_frontier (mk_inst su.cs_next_id MSTORE [Var dst;op] []) z /\
   inst_dload_in_section (mk_inst su.cs_next_id MSTORE [Var dst;op] []) z /\
   (mk_inst su.cs_next_id MSTORE [Var dst;op] []).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst su.cs_next_id MSTORE [Var dst;op] []).inst_opcode` by
    (simp[mk_inst_def,is_terminator_def,below_frontier_MSTORE,
      eval_operand_def,inst_dload_in_section_def] >> decide_tac) >>
  `ctx_has_dalloca ctx ==>
   dalloca_no_wrap (mk_inst su.cs_next_id MSTORE [Var dst;op] []) z` by
    simp[mk_inst_def,dalloca_no_wrap_non_dalloca] >>
  drule_all straight_line_origin_ptr_edge >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >> simp[] >> strip_tac >>
  `~((mstore (off + w2n w0) (typed_val_to_w256 ftv v) z) with
      vs_inst_idx := SUC z.vs_inst_idx).vs_halted` by simp[mstore_def] >>
  metis_tac[gas_origin_ptr_path_rules,APPEND]
QED

Resume body_assign_field_store_joint_frame[ghost]:
  qmatch_goalsub_abbrev_tac `ghost_inv_at (DF H) lo d cenv cx ee G tf t` >>
  `t.vs_allocas = z.vs_allocas /\ t.vs_alloca_next = z.vs_alloca_next /\
   t.vs_memory = (mstore (off + w2n w0) (typed_val_to_w256 ftv v) z).vs_memory /\
   (!x. lookup_var x t = lookup_var x z)` by
    simp[Abbr `t`,mstore_def,lookup_var_def] >>
  `allocas_from lo t` by (fs[ghost_inv_at_def,allocas_from_def] >> metis_tac[]) >>
  `stor_taint_ok_at (DF H) tf t` by
    (fs[ghost_inv_at_def,stor_taint_ok_at_def] >>
     simp[Abbr `tf`,Abbr `t`,mstore_def,contract_storage_def,contract_transient_def,
          step_taint_def,imm_taint_def,mk_inst_def]) >>
  `local_region cenv es.scopes z id (w2n w0) sz` by simp[local_region_def] >>
  simp[Abbr `ee`] >>
  irule (body_full_local_scope_ghost_post |> Q.INST [`n` |-> `sz`]) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`G`,`func`,`sa`,`tn`] >> simp[op_taint_def] >>
  conj_tac
  >- (rpt strip_tac >> simp[Abbr `t`] >>
      irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Resume body_assign_field_store_joint_frame[return]:
  irule return_buf_frame_frame >> goal_assum (drule_at Any) >>
  simp[mstore_def,lookup_var_def]
QED

Resume body_assign_field_store_joint_frame[history]:
  `step_inst_base (mk_inst su.cs_next_id MSTORE [Var dst;op] []) z =
    OK (mstore (off + w2n w0) (typed_val_to_w256 ftv v) z)` by
    (qspecl_then [`Var dst`,`op`] mp_tac step_MSTORE >>
     simp[eval_operand_def] >> metis_tac[]) >>
  `run_inst_seq [mk_inst su.cs_next_id MSTORE [Var dst;op] []] z =
    OK (mstore (off + w2n w0) (typed_val_to_w256 ftv v) z)` by
    simp[run_inst_seq_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    [mk_inst su.cs_next_id MSTORE [Var dst;op] []]` by
    simp[mk_inst_def,is_terminator_def] >>
  drule_all emitted_alloca_history >> simp[arithmeticTheory.ADD1]
QED

Resume body_assign_field_store_joint_frame[frame]:
  `local_region cenv es.scopes z id (w2n w0) sz` by simp[local_region_def] >>
  irule alloca_frame_region_write >> goal_assum (drule_at Any) >> simp[] >>
  drule find_containing_scope_structure >> strip_tac >>
  `id IN FDOM sc` by fs[FLOOKUP_DEF] >>
  simp[pred_setTheory.ABSORPTION_RWT] >>
  rpt strip_tac >> irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
  decide_tac
QED

Finalise body_assign_field_store_joint_frame

(* A word field of a memory struct local. *)
Theorem body_assign_attr_local_rhs_pre[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) ==>
    occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  attribute_type env.type_defs (StructT sid) fld = SOME fty /\ is_word_type fty ==>
  expr_type e = fty /\ expr_body_pre cenv cx env e es
Proof
  strip_tac >>
  `well_typed_expr env e /\ type_widens_to env.type_defs (expr_type e) fty` by
    (qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
     simp[Once type_stmt_def, atarget_accepts_def] >>
     Cases_on `type_place_target env (AttributeTarget (NameTarget id) fld)` >> simp[] >>
     rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> simp[] >>
     gvs[type_place_target_AttributeTarget, type_place_target_NameTarget] >>
     strip_tac >> gvs[]) >>
  `expr_type e = fty` by metis_tac[type_widens_to_word] >> simp[] >>
  drule_all_then ACCEPT_TAC body_assign_empty_target_rhs_pre
QED

Theorem body_assign_attr_local_full:
  !cx id fld sid fty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (AttributeTarget (NameTarget id) fld)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    attribute_type env.type_defs (StructT sid) fld = SOME fty /\
    is_word_type fty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  drule_all body_assign_attr_local_rhs_pre >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld = SOME (fty,fsz)` by
    metis_tac[attribute_type_struct_field] >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    metis_tac[expr_sim_inv_def] >>
  `cenv.ce_var_type id = SOME (StructT sid)` by metis_tac[expr_sim_inv_def] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by metis_tac[body_expr_full_ok_def] >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  simp[CONJUNCT1 evaluate_storage_trace_frame] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by metis_tac[] >>
  `is_word_type (expr_type e)` by simp[] >>
  drule_all assign_attr_local_code_parts >> strip_tac >> gvs[] >>
  rename1 `emit_void MSTORE _ su = ((),sb)` >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn su /\ ci_mono su sb` by
    metis_tac[compile_expr_ci_mono,ci_mono_emit_op,ci_mono_unwrap_value,ci_mono_emit_void,SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn su func /\ fn_has_code su sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split,cs_extends_trans]) >>
  `?shadow_sm. compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) shadow_sa = (vv,shadow_sm) /\
    gas_shadow_state sm shadow_sm` by
    (`FST (compile_expr cenv (expr_type e) e sa) =
       FST (compile_expr (gas_shadow_env T cenv) (expr_type e)
         (gas_shadow_expr e) shadow_sa) /\
       gas_shadow_state (SND (compile_expr cenv (expr_type e) e sa))
         (SND (compile_expr (gas_shadow_env T cenv) (expr_type e)
           (gas_shadow_expr e) shadow_sa))` by
       (irule (REWRITE_RULE [gas_shadow_compiles_def]
          (Q.INST [`sd` |-> `T`] gas_shadow_stmt_compile_expr_env)) >> simp[]) >>
     Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa` >> gvs[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by suspend "shadow" >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x` by fs[ret_pc_ok_def] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by metis_tac[expr_body_pre_vv_gas_admissible] >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (strip_assume_tac o BETA_RULE o ONCE_REWRITE_RULE [gas_outcome_full_def])
  >- (rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
      disj1_tac >> conj_tac
      >- (drule assign_attr_local_admissible_run >>
          disch_then (fn th => PURE_REWRITE_TAC [gas_bad_storage_at_def, th]) >>
          pure_rewrite_tac[GSYM gas_bad_storage_at_def] >>
          ntac 2 (irule gas_bad_storage_at_bind_left >> simp[storage_trace_frame_bind,
            storage_trace_frame_write_place,storage_trace_frame_read_result])) >>
      metis_tac[])
  >- suspend "normal"
  >> rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
     disj2_tac >> disj2_tac >>
     qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
     conj_tac >- (irule assign_attr_local_exempt >> simp[]) >> metis_tac[]
QED

Resume body_assign_attr_local_full[shadow]:
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
  simp[gas_shadow_stmt_def,gas_shadow_assignment_def,gas_shadow_expr_def] >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ (Assign _ e) sa = _` kall_tac >>
  `is_word_type (expr_type (gas_shadow_expr e))` by simp[gas_shadow_expr_type] >>
  `FLOOKUP (gas_shadow_env T cenv).ce_vars id = SOME (PtrVar (Var p) sz)` by simp[] >>
  `(gas_shadow_env T cenv).ce_var_type id = SOME (StructT sid)` by simp[] >>
  `ALOOKUP (get_struct_fields (gas_shadow_env T cenv).ce_struct_fields
      (nsid_to_string sid)) fld = SOME (expr_type (gas_shadow_expr e),fsz)` by
    simp[gas_shadow_expr_type] >>
  drule_all assign_attr_local_code_parts >> strip_tac >> gvs[gas_shadow_expr_type] >>
  `ci_mono shadow_sa shadow_sm /\ ci_mono shadow_sm sn' /\
   ci_mono sn' su' /\ ci_mono su' shadow_sb` by
    metis_tac[compile_expr_ci_mono,ci_mono_emit_op,ci_mono_unwrap_value,ci_mono_emit_void,SND] >>
  fs[ci_mono_def] >> metis_tac[fn_has_code_split,cs_extends_trans]
QED

Resume body_assign_attr_local_full[normal]:
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  Cases_on `?t. r = OK t`
  >- (gvs[exit_result_def] >> suspend "success") >>
  `exit_result r /\ expr_exit res r` by metis_tac[] >>
  `?exc. res = INR exc` by (Cases_on `res` >> fs[expr_exit_def]) >> gvs[] >>
  irule gas_outcome_full_intro >>
  qexistsl_tac [`G'`,`ee`,`marks`,`r`,`INR exc`,`tn'`] >>
  conj_tac
  >- (drule assign_attr_local_admissible_run >> strip_tac >>
      simp[bind_def]) >>
  simp[] >> rpt strip_tac >> first_x_assum drule >> simp[] >> strip_tac >>
  fs[stmt_exit_ptr_def,
     INST_TYPE [alpha |-> ``:unit``, beta |-> ``:eval_result``]
       stmtSimPropsTheory.expr_exit_INR_type,
     INST_TYPE [alpha |-> ``:unit``, beta |-> ``:eval_result``]
       haltExitProjTheory.halt_exit_INR_type] >>
  rpt strip_tac >> fs[expr_exit_def]
QED

Resume body_assign_attr_local_full[success]:
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[] >>
  rename1 `vv_post _ _ _ _ _ _ _ _ _ s0 _ raw vv t` >>
  `~t.vs_halted` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (qpat_assum `eval_expr _ _ _ = (INL raw,_)`
       (mp_tac o MATCH_MP vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom) >> simp[]) >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >> strip_tac >>
  `expr_sim_inv cenv cx env (ee with gas_obs := [])` by
    (drule_all exprSimSourceTheory.expr_body_pre_eval_result >> simp[]) >>
  qabbrev_tac `er = ee with gas_obs := []` >>
  qabbrev_tac `flds = get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)` >>
  qabbrev_tac `off = struct_field_offset flds fld` >>
  drule_all targetPlaceSimTheory.expr_sim_inv_local >> strip_tac >>
  gvs[] >>
  rename1 `lookup_scopes id _ = SOME loc` >>
  `evaluate_type (get_tenv cx) (StructT sid) = SOME loc.type` by
    (first_x_assum drule >> simp[]) >>
  drule_all exprSimFieldLayoutTheory.struct_fields_layout >> strip_tac >>
  rename1 `fields_layout _ fs` >>
  `fields_layout flds fs` by simp[Abbr `flds`] >>
  `ALOOKUP fs fld = SOME tvt` by
    (fs[Abbr `flds`] >> metis_tac[exprSimAttributeFieldsTheory.struct_field_type]) >>
  `off + 32 <= type_memory_size loc.type` by
    (drule_all exprSimAttributeFieldsTheory.mem_field_offset_layout >>
     disch_then (mp_tac o MATCH_MP exprSimPropsTheory.mem_field_offset_sound) >>
     `type_memory_size tvt = 32` by metis_tac[abiValueEncodingTheory.abi_word_type_size] >>
     simp[Abbr `off`,valueEncodingTheory.type_memory_size_def]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx er t /\
   ghost_inv_at (DF (storage_trace_horizon ee.storage_trace)) lo d cenv cx er G' tn' t` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> fs[vv_post_def]) >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `?w0. lookup_var p t = SOME w0 /\ w2n w0 + sz <= t.vs_alloca_next /\
      type_memory_size loc.type <= sz` by
    (qpat_assum `local_ptrs_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_rel_def]) >>
     first_x_assum drule_all >> metis_tac[]) >>
  `ptr_covers G' tn' p t sz` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ er G' tn' t`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     first_x_assum drule_all >> simp[]) >>
  `?b0 cap. FLOOKUP G' p = SOME (b0,cap)` by fs[ptr_covers_def] >>
  `t.vs_alloca_next < dimword(:256)` by
    metis_tac[stmt_state_rel_alloca_room,alloca_room_next_lt] >>
  `off + 32 <= sz /\ w2n w0 + off < dimword(:256)` by decide_tac >>
  `storage_trace_domain cx st0 er.storage_trace /\ MAP FDOM es.scopes = MAP FDOM er.scopes` by
    simp[Abbr `er`] >>
  `!H. valid_horizon cx st0 H er.storage_trace ==>
       vv_post H ctx func cenv cx e es sa sm s0 er raw vv t /\
       ghost_inv_at (DF H) lo d cenv cx er G' tn' t` by
    (simp[Abbr `er`] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by fs[ci_mono_def] >>
  `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx raw er = (INL v,er) /\
        !rt w. evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
               eval_operand (vv_operand vv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
                 val_in_memory rt v (w2n w) mem)` by simp[arithmeticTheory.ADD_COMM] >>
  drule_at (Pat `emit_op ADD _ _ = _`) body_assign_field_prefix_joint >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (_,_)`)) >>
  disch_then (drule_at (Pat `storage_trace_domain _ _ _`)) >>
  disch_then (fn th =>
    qpat_assum `fn_has_code sm sn func` (mp_then (Pat `fn_has_code _ _ _`) mp_tac th)) >>
  `post_value_type cenv e = expr_type e` by simp[] >>
  disch_then (fn th => qpat_assum `post_value_type cenv e = _` (fn eq =>
    drule_at (Pat `vv_store_bound _ _ _ _ _ _ _`) (REWRITE_RULE [eq] th))) >>
  disch_then (mp_tac o Q.INST [`rty` |-> `tvt`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] o SPEC_ALL) >>
  simp[] >> strip_tac >>
  rename1 `ptr_covers Gz tnz out z 32` >>
  qpat_x_assum `dst = Var out` SUBST_ALL_TAC >>
  `!tail. vyperState$bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL v,er with gas_obs := tail)` by
    (qpat_assum `read_result cx raw er = _`
       (mp_tac o MATCH_MP exprSimMemorySourceTheory.read_result_gas_obs) >>
     simp[Abbr `er`,bind_def]) >>
  qpat_assum `gas_admissible (eval_stmt _ _) _ _`
    (mp_then (Pat `gas_admissible _ _ _`) mp_tac assign_attr_local_continuation_all_tails) >>
  disch_then (mp_tac o Q.INST [`prefix` |-> `gas_explicit marks s0.vs_gas_readings`,
    `ee` |-> `er`] o SPEC_ALL) >> simp[] >> strip_tac >>
  rename1 `find_containing_scope id er.scopes = SOME (pre,sc,entry,rest)` >>
  `entry = loc` by (drule vyperLookupTheory.find_containing_scope_lookup >> simp[]) >>
  qpat_x_assum `entry = loc` SUBST_ALL_TAC >>
  `state_well_typed er` by fs[expr_sim_inv_def] >>
  `value_has_type (StructTV fs) (StructV vals)` by
    (drule_all vyperTypeStatePreservationTheory.lookup_scopes_state_well_typed_value_has_type >> simp[]) >>
  `struct_has_type fs vals` by
    (drule exprSimAttributeTheory.struct_value_shape >> simp[]) >>
  `value_has_type tvt v` by simp[] >>
  `store_lays_out tvt tvt v` by
    (irule stmtSimDeclStoreTheory.store_lays_out_typed >>
     simp[] >> qexistsl_tac [`expr_type e`,`get_tenv cx`] >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) er.storage_trace` by
    simp[Abbr `er`] >>
  qpat_assum `!H. valid_horizon _ _ H er.storage_trace ==> _ /\ _ /\ _ /\ expr_post H ctx func cenv cx e es sa su s0 er v op z /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  suspend "store"
QED

Resume body_assign_attr_local_full[store]:
  `not_fresh_at sa p` by
    (qpat_assum `local_ptrs_reserved cenv sa`
       (strip_assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
     first_x_assum drule >> simp[]) >>
  `p <> out` by
    metis_tac[bodyPtrMakeArrayEmissionTheory.emit_op_old_var_separate] >>
  `not_fresh_at sn p` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
     fs[ci_mono_def] >> decide_tac) >>
  qmatch_asmsub_abbrev_tac `wb_frame cenv er er sn q z` >>
  `lookup_var p q = SOME w0` by
    (qpat_assum `lookup_var p t = SOME w0` (mp_tac o REWRITE_RULE [lookup_var_def]) >>
     simp[Abbr `q`,lookup_var_def,update_var_def,FLOOKUP_UPDATE]) >>
  `lookup_var p z = SOME w0` by
    (qpat_assum `wb_frame cenv er er sn q z` (mp_then Any mp_tac exprSimWordArgsTheory.wb_frame_vars) >>
     disch_then (qspecl_then [`p`,`w0`] mp_tac) >> simp[]) >>
  `mem_field_offset fs fld = SOME (off,tvt)` by
    (drule_all exprSimAttributeFieldsTheory.mem_field_offset_layout >> simp[Abbr `off`]) >>
  `!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==>
     val_in_memory (StructTV fs) (StructV vals) (w2n w0) mem` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ er Gz tnz z`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [ghost_inv_at_def]) >>
     disch_then (qspecl_then [`id`,`loc`,`p`,`sz`] mp_tac) >> simp[]) >>
  drule_at (Pat `mem_field_offset _ _ = _`) body_assign_field_robust_update >>
  disch_then (drule_at (Pat `mem_agree_outside _ _ _ ==> _`)) >>
  simp[] >> strip_tac >>
  qpat_assum `expr_post _ _ _ _ _ _ es sa su s0 er v op z`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `eval_operand op z = SOME (typed_val_to_w256 tvt v)` by
    (irule exprBopSimPropsTheory.expr_val_rel_typed >>
     qexistsl_tac [`cx`,`post_value_type cenv e`] >>
     qpat_assum `expr_val_rel cx (post_value_type cenv e) v op z` mp_tac >> simp[]) >>
  `op_taint tnz op = {}` by fs[ptr_val_ok_def] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `alloca_frame cenv es sa s0 cenv er z` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx es s0`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule alloca_frame_of_mem_frame) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (sym_tac >> first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  `return_buf_frame d cenv su z` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     simp[] >> fs[ci_mono_def] >> decide_tac) >>
  `local_region cenv er.scopes z id (w2n w0) sz` by
    (simp[loweringStateRelDefsTheory.local_region_def] >>
     qexistsl_tac [`loc`,`p`,`w0`] >> simp[]) >>
  sg `lo <= w2n w0` >- suspend "field_lower_bound" >>
  suspend "field_store_ready"
QED

Resume body_assign_attr_local_full[field_lower_bound]:
  qpat_assum `stmt_state_rel _ ctx func cenv cx er z`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac
       bodyFullMemoryFramesTheory.body_full_local_region_lower_bound) >>
  disch_then (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then irule >> conj_tac >- decide_tac >>
  qexists_tac `DF (storage_trace_horizon ee.storage_trace)` >>
  qpat_assum `!H. dead_lo_ok H (DF H) lo cenv cx`
    (qspec_then `storage_trace_horizon ee.storage_trace` ACCEPT_TAC)
QED

Resume body_assign_attr_local_full[field_store_ready]:
  `~z.vs_halted` by
    (qpat_assum `gas_origin_ptr_path _ (t,G',tn') [] (OK z,Gz,tnz)`
       (mp_then Any mp_tac fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec) >>
     simp[exit_result_def] >> metis_tac[]) >>
  qabbrev_tac `liveH = \H. valid_horizon cx st0 H er.storage_trace` >>
  `!H. liveH H ==>
    stmt_state_rel H ctx func cenv cx er z /\ ghost_inv_at (DF H) lo d cenv cx er Gz tnz z` by
    (simp[Abbr `liveH`] >> gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H er.storage_trace ==> _ /\ _ /\ _ /\ expr_post H ctx func cenv cx e es sa su s0 er v op z /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `emit_void MSTORE [Var out;op] su = ((),sb)`
    (mp_then (Pat `emit_void MSTORE _ _ = _`) mp_tac
       (INST_TYPE [alpha |-> ``:256``] body_assign_field_store_joint_frame)) >>
  disch_then (drule_at (Pat `alloca_frame _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `find_containing_scope _ _ = _`)) >>
  disch_then (fn th =>
    qpat_assum `ptr_covers Gz tnz out z 32`
      (mp_then (Pat `ptr_covers _ _ _ _ _`) mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `eval_operand op z = SOME (typed_val_to_w256 tvt v)`
      (mp_then (Pat `eval_operand _ _ = SOME _`) mp_tac th)) >>
  disch_then (mp_tac o Q.INST [`P` |-> `liveH`,
    `H0` |-> `storage_trace_horizon ee.storage_trace`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] o SPEC_ALL) >>
  (impl_tac >-
    (simp[] >> conj_tac >- simp[Abbr `liveH`] >>
     qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tnz`
       (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [ghost_kept_at_def]))) >>
  strip_tac >> suspend "field_join"
QED

Resume body_assign_attr_local_full[field_join]:
  rename1 `fin.vs_inst_idx = LENGTH sb.cs_current_insts` >>
  rename1 `tnf.t_mem = _ DIFF _` >>
  qmatch_asmsub_abbrev_tac `alloca_frame cenv es sa s0 cenv ef fin` >>
  irule gas_outcome_full_intro >>
  qexistsl_tac [`Gz`,`ef`,`marks`,`OK fin`,`INL ()`,`tnf`] >>
  conj_tac
  >- (drule assign_attr_local_admissible_run >> strip_tac >>
      simp[bind_def,Abbr `ef`]) >>
  reverse conj_tac >- simp[Abbr `ef`] >>
  `ef.storage_trace = er.storage_trace` by simp[Abbr `ef`] >>
  qx_gen_tac `H` >> disch_tac >>
  `valid_horizon cx st0 H er.storage_trace` by
    (qpat_assum `ef.storage_trace = er.storage_trace` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `liveH H` by simp[Abbr `liveH`] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >-
    (qpat_assum `valid_horizon cx st0 H er.storage_trace` mp_tac >>
     simp[Abbr `er`] >> gvs[])) >>
  strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H er.storage_trace ==> gas_origin_ptr_path _ (t,G',tn') [] _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H. liveH H ==> gas_origin_ptr_path _ _ [] _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s0,G0,tn0) marks (OK fin,Gz,tnf)` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t,G',tn')`
        (mp_then Any mp_tac gas_origin_ptr_path_append) >>
      disch_then (qspecl_then [`t`,`G'`,`tn'`,`[]`,`OK fin`,`Gz`,`tnf`] mp_tac) >>
      rewrite_tac[APPEND_NIL] >> disch_then irule >>
      qpat_assum `gas_origin_ptr_path _ (t,G',tn') [] (OK z,Gz,tnz)`
        (mp_then Any mp_tac gas_origin_ptr_path_append) >>
      disch_then (qspecl_then [`z`,`Gz`,`tnz`,`[]`,`OK fin`,`Gz`,`tnf`] mp_tac) >>
      rewrite_tac[APPEND_NIL] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disj1_tac >> qexists_tac `fin` >>
  `~block_is_terminated sb` by
    (drule exprOpenPrimitivesTheory.emit_void_terminated >> simp[venomInstTheory.is_terminator_def]) >>
  `(ef with gas_obs := []) = ef` by simp[Abbr `ef`,Abbr `er`,evaluation_state_component_equality] >>
  `storage_well_formed_on cx ef (FST H)` by
    (`storage_well_formed_on cx er (FST H)` by
       (qpat_assum `expr_post H ctx func cenv cx e es sa su s0 er v op z`
          (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [expr_post_def])) >>
     `ef.accounts = er.accounts /\ ef.tStorage = er.tStorage` by simp[Abbr `ef`] >>
     `storage_well_formed_on cx ef (FST H) = storage_well_formed_on cx er (FST H)` by
       (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >> simp[]) >>
     simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp fin` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx ef fin`
       (mp_then Any ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `MAP FDOM ef.scopes = MAP FDOM es.scopes` by
    (`id IN FDOM sc` by
       (drule vyperLookupTheory.find_containing_scope_structure >>
        strip_tac >> fs[FLOOKUP_DEF]) >>
     drule vyperLookupTheory.find_containing_scope_structure >>
     strip_tac >> fs[Abbr `ef`, pred_setTheory.ABSORPTION_RWT]) >>
  `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) fin` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK fin,Gz,tnf)` (fn path =>
       qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
         qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
           mp_tac (MATCH_MP return_buf_allocas_path (LIST_CONJ [path,frame,sep]))))) >>
     simp[]) >>
  `return_buf_sep d cenv ef fin` by
    (irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`storage_trace_horizon es.storage_trace`, `ctx`, `cx`,
                   `es`, `func`, `s0`, `sa`] >>
     metis_tac[]) >>
  qpat_x_assum `fin = _` kall_tac >>
  qpat_x_assum `tnf = _` kall_tac >>
  qpat_x_assum `tnf.t_mem = _ DIFF _` kall_tac >>
  simp[stmt_lands_def,stmtSimPropsTheory.cenv_top_ext_refl] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tnz`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [ghost_kept_at_def]) >>
  simp[ptrDisciplineTheory.op_taint_def]
QED

Finalise body_assign_attr_local_full

Theorem body_assign_local_memory_nonempty_full[local]:
  !cx id ty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (NameTarget id)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME ty /\
    ~is_word_type ty /\
    0 < type_memory_bytes cenv ty /\
    (lowered_value_type cenv e = ty \/ is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all assign_base_local_rhs_pre >> strip_tac >>
  Q.SUBGOAL_THEN `lowered_value_type cenv e = ty \/ is_bytestring_type ty` assume_tac
  >- metis_tac[] >>
  `cx_tops cx = tops` by drule_then (ACCEPT_TAC o cj 2) body_inv_main_code >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (qpat_assum `body_expr_full_ok cx e`
       (mp_tac o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     strip_tac >>
     qpat_assum `!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
          _ ==> expr_sim_full _ _ _ _ _ _ /\ expr_vv_sim_full _ _ _ _ _ _`
       (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,
         `func`,`shadow_func`,`cenv`,`env`,`expr_type e`,`es`] mp_tac) >>
     simp[]) >>
  drule_all targetPlaceSimTheory.expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
  drule post_type_evaluates >> disch_then (qx_choose_then `rty` assume_tac) >>
  `!gs tv ee v. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
       read_result cx tv ee = (INL v,ee) ==> value_has_type rty v` by suspend "rhs_type" >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[cj 1 evaluate_storage_trace_frame] >>
  simp[] >> disch_tac >>
  drule_all assign_local_memory_widen_code_parts >> strip_tac >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  rename1 `compile_expr cenv (expr_type e) e sa = (vv,sV)` >>
  rename1 `unwrap_value cenv vv sV = (op,sB)` >>
  suspend "shadow"
QED

Resume body_assign_local_memory_nonempty_full[rhs_type]:
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by simp[bind_def] >>
  drule_all (SIMP_RULE (srw_ss() ++ ETA_ss) [] memory_rhs_read_post_typed) >>
  simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def]
QED

Resume body_assign_local_memory_nonempty_full[shadow]:
  qpat_assum `cx_tops cx = tops` (SUBST1_TAC o SYM) >>
  `?shadow_sB.
     lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa = (op,shadow_sB) /\
     gas_shadow_state sB shadow_sB` by
    (`FST (lower_value compile_expr cenv (expr_type e) e sa) =
       FST (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
         (gas_shadow_expr e) shadow_sa) /\
       gas_shadow_state (SND (lower_value compile_expr cenv (expr_type e) e sa))
         (SND (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
           (gas_shadow_expr e) shadow_sa))` by
       (irule (REWRITE_RULE [gas_shadow_compiles_def]
          (Q.INST [`sd` |-> `T`] gas_shadow_stmt_lower_value_env)) >> simp[]) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa` >> gvs[]) >>
  `fn_has_code shadow_sa shadow_sB shadow_func` by
    (qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     simp[gas_shadow_stmt_def,gas_shadow_assignment_def,gas_shadow_expr_def] >> strip_tac >>
     qpat_x_assum `stmt_env _ _ _ (Assign _ e) sa = _` kall_tac >>
     `~(has_length_word (expr_type (gas_shadow_expr e)) /\
         is_empty_value_expr (gas_shadow_expr e))` by gvs[gas_shadow_expr_type] >>
     Q.SUBGOAL_THEN `lowered_value_type (gas_shadow_env T cenv) (gas_shadow_expr e) = ty \/
                      is_bytestring_type ty` assume_tac >- simp[] >>
     `(gas_shadow_env T cenv).ce_var_type id = SOME ty` by simp[] >>
     `FLOOKUP (gas_shadow_env T cenv).ce_vars id = SOME (PtrVar (Var p) sz)` by simp[] >>
     drule_all assign_local_memory_widen_code_parts >> strip_tac >>
     gns[gas_shadow_expr_type] >> metis_tac[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by metis_tac[ret_pc_ok_def] >>
  drule assign_local_admissible_rhs >> strip_tac >>
  drule body_post_type_allocation_bound >> disch_tac >>
  drule_all body_assign_local_memory_rhs_frontier >> disch_tac >>
  suspend "compose"
QED

Resume body_assign_local_memory_nonempty_full[compose]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full cfg tops0 cx st0 src start Q R` >>
  `gas_outcome_full cfg tops0 cx st0 src start
     (\H res ee G tn t. Q H res ee G tn t /\
       (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t)) R` by
    (qunabbrev_tac `cfg` >> qunabbrev_tac `start` >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ Q R` (fn outcome =>
       qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
         qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
           ACCEPT_TAC (MATCH_MP gas_outcome_full_return_buf_allocas
             (LIST_CONJ [outcome,frame,sep])))))) >>
  `gas_outcome_full cfg tops0 cx st0 src start
     (\H res ee G tn t. (Q H res ee G tn t /\
       (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t)) /\
       ~t.vs_halted /\ ee.gas_obs = []) R` by
    (qunabbrev_tac `cfg` >> qunabbrev_tac `start` >>
     irule gas_outcome_full_post_source >>
     qpat_x_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn t. Q H res ee G tn t /\ _) R`
       (irule_at Any) >> simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ Q R` kall_tac >>
  qunabbrev_tac `cfg` >> qunabbrev_tac `tops0` >> qunabbrev_tac `src` >>
  qunabbrev_tac `start` >> qunabbrev_tac `R` >>
  irule assign_local_memory_full_outcome >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[Abbr `Q`] >>
  qexists_tac `lctx` >> simp[] >>
  conj_tac >- suspend "tail" >>
  rpt strip_tac >> metis_tac[]
QED

Resume body_assign_local_memory_nonempty_full[tail]:
  qx_genl_tac [`marks`,`v`,`mid`,`Gi`,`ti`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
      mid.storage_trace` by fs[storage_trace_domain_def] >>
  drule_all assign_local_continuation_all_tails >> strip_tac >>
  qmatch_asmsub_abbrev_tac `write_place _ _ _ _ = (INL (),ff with gas_obs := _)` >>
  `ff.storage_trace = mid.storage_trace` by simp[Abbr `ff`] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (fn th =>
       qpat_assum `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
         (map_every assume_tac o CONJUNCTS o MP th))) >>
  qabbrev_tac `gs = gas_explicit marks s0.vs_gas_readings` >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,mid)` by
    (qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
       (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid`
       (fn th => rewrite_tac[listTheory.APPEND_NIL,th])) >>
  `ff with gas_obs := [] = ff` by simp[Abbr `ff`, evaluation_state_component_equality] >>
  `write_place cx (MemoryPlace id []) v mid = (INL (),ff)` by
    (qpat_assum `!tail. write_place _ _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => rewrite_tac[th]) >>
     qpat_assum `ff with gas_obs := [] = ff` (fn th => rewrite_tac[th])) >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all (SIMP_RULE (srw_ss() ++ ETA_ss) [] immutable_rhs_physical_typed) >> strip_tac >>
  rename1 `find_containing_scope id mid.scopes = SOME (_,_,dst,_)` >>
  drule_then assume_tac find_containing_scope_lookup >>
  `value_runtime_typed env ty v` by
    (drule_all (SIMP_RULE (srw_ss() ++ ETA_ss) [] memory_rhs_read_destination_typed) >> simp[]) >>
  `?dtv. evaluate_type (get_tenv cx) ty = SOME dtv /\
         value_has_type dtv v /\ val_wf dtv v` by
    (qpat_assum `value_runtime_typed env ty v`
       (qx_choose_then `tv` strip_assume_tac o
        REWRITE_RULE [vyperTypeExprSoundnessTheory.value_runtime_typed_def]) >>
     qexists_tac `tv` >>
     qpat_assum `env.type_defs = get_tenv cx` (SUBST1_TAC o SYM) >>
     simp[cj 1 value_has_type_val_wf]) >>
  rename1 `evaluate_type (get_tenv cx) ty = SOME dtv` >>
  `dst.type = dtv` by
    (drule_all (SIMP_RULE (srw_ss() ++ ETA_ss) [] memory_rhs_read_local_type) >> simp[]) >>
  drule_then assume_tac exprSimWordArgsTheory.expr_post_state >>
  drule_then (map_every assume_tac o CONJUNCTS) stmt_state_rel_local_ptrs_alloca >>
  qpat_assum `local_ptrs_rel func cenv mid.scopes u`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [local_ptrs_rel_def]) >>
  disch_then (qspecl_then [`id`,`dst`,`p`,`sz`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `dw` strip_assume_tac) >>
  `local_region cenv mid.scopes u id (w2n dw) sz` by
    (simp[local_region_def] >> qexistsl_tac [`dst`,`p`,`dw`] >> simp[]) >>
  `type_memory_bytes cenv ty = type_memory_size dtv` by
    (drule_all expr_sim_inv_memory_size >> simp[]) >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty` by
    (irule typedCopyCompatibilityTheory.type_widens_to_trans >>
     qexists_tac `expr_type e` >> conj_tac
     >- (simp[type_widens_to_def] >>
         `well_formed_type env.type_defs (expr_type e)` by
           (irule exprSafeOperandTheory.well_typed_expr_type_well_formed >>
            simp[] >> metis_tac[expr_body_pre_var_types_well_formed]) >> metis_tac[]) >>
     metis_tac[]) >>
  suspend "rhs_resources"
QED

Resume body_assign_local_memory_nonempty_full[rhs_resources]:
  `~is_word_type (lowered_value_type cenv e)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source,is_bytestring_word_type] >>
  `~is_word_type (post_value_type cenv e)` by
    metis_tac[immutable_rhs_post_physical_classify,is_bytestring_word_type] >>
  `expr_val_at cenv cx (lowered_value_type cenv e) sa sB mid v op u` by
    (irule abi_args_expr_post_lowered_at >>
     conj_tac >- (strip_tac >> qexists_tac `stv` >> simp[]) >>
     conj_tac >- (qexistsl_tac [`env`,`es`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  `?sw. eval_operand op u = SOME sw /\
        !mem. mem_agree_outside ti.t_mem u.vs_memory mem ==>
              val_in_memory stv v (w2n sw) mem` by
    (`expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e
       (es with gas_obs := gs) sa sB s0 mid v op u` by
       simp[exprSimExtract32PostTheory.extract32_expr_post_start_gas_obs] >>
     drule_all (SIMP_RULE (srw_ss() ++ ETA_ss) [] structlit_child_physical_robust) >>
     simp[]) >>
  `0 < type_memory_size stv` by
    (Cases_on `is_bytestring_type ty`
     >- (`is_bytestring_type (lowered_value_type cenv e)` by
           metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source] >>
         `32 <= type_memory_bytes cenv (lowered_value_type cenv e)` by
           simp[bodyPtrTypeBuiltinsMemoryBoundsTheory.bytestring_memory_header_bound] >>
         fs[] >> decide_tac) >>
     `lowered_value_type cenv e = ty` by metis_tac[] >>
     gvs[]) >>
  `op_taint ti op = {}` by fs[ptr_val_ok_def] >>
  `ptr_buf_ok cenv e op Gi u` by simp[] >>
  `?xs. op = Var xs /\ ptr_covers Gi ti xs u (type_memory_size stv)` by
    (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
     simp[] >> qexistsl_tac [`cenv`,`e`] >> simp[]) >>
  `lookup_var xs u = SOME sw` by fs[venomStateTheory.eval_operand_def] >>
  `ptr_covers Gi ti p u sz /\ allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ mid Gi ti u` (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     metis_tac[]) >>
  `ptr_covers Gi ti p u (type_memory_size dtv)` by
    metis_tac[reasonCopySourcePtrTheory.ptr_covers_mono] >>
  `0 < sz` by decide_tac >>
  `lo <= w2n dw` by
    (`dead_lo_ok (storage_trace_horizon mid.storage_trace)
          (DF (storage_trace_horizon mid.storage_trace)) lo cenv cx` by simp[] >>
     drule_all bodyFullMemoryFramesTheory.body_full_local_region_lower_bound >> simp[]) >>
  `place_ptr_rel cenv cx u (PlaceR (MemoryPlace id [])) dw (SOME LocMemory) (Type ty)` by
    simp[place_ptr_rel_def,mem_path_offset_def,wordsTheory.WORD_ADD_0] >>
  `target_ptr_ok cenv (PlaceR (MemoryPlace id []))
       (Var p,SOME LocMemory,SOME (ValPT ty)) Gi ti u` by
    (simp[bodyFullTargetDefsTheory.target_ptr_ok_def,ptrDisciplineTheory.op_prov_def] >> fs[ptr_covers_def]) >>
  `expr_sim_inv cenv cx env mid` by
    (drule_all (SIMP_RULE (srw_ss() ++ ETA_ss) [] exprSimSourceTheory.expr_body_pre_eval) >> simp[]) >>
  `sa.cs_next_var <= sB.cs_next_var` by
    (qspec_then `sa` mp_tac (Q.SPECL [`cenv`,`expr_type e`,`e`] ci_mono_lower_value_compile_expr) >>
     simp[ci_mono_def]) >>
  `local_ptrs_reserved cenv sB` by metis_tac[local_ptrs_reserved_next_var] >>
  `not_fresh_at sB p /\ not_fresh_at sB xs` by
    (conj_tac
     >- (qpat_assum `local_ptrs_reserved cenv sB`
           (mp_tac o CONJUNCT1 o CONJUNCT2 o
            REWRITE_RULE [local_ptrs_reserved_def]) >>
         disch_then (qspecl_then [`id`,`id`,`p`,`sz`,`sz`] mp_tac) >>
         simp[]) >>
     drule_all compile_lower_value_var >> simp[]) >>
  `w2n (sw:bytes32) + type_memory_size stv <= u.vs_alloca_next` by
    (qpat_assum `~is_word_type (post_value_type cenv e) ==> !rt w. _`
       (qspecl_then [`stv`,`sw:bytes32`] mp_tac o UNDISCH) >>
     asm_rewrite_tac[] >>
     qpat_assum `0 < type_memory_size stv` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `u.vs_alloca_next < dimword (:256)` by
    (drule stmt_state_rel_alloca_room >>
     disch_then (ACCEPT_TAC o MATCH_MP alloca_room_next_lt)) >>
  `w2n (sw:bytes32) + type_memory_size stv < dimword (:256)` by decide_tac >>
  `w2n (dw:bytes32) + type_memory_size dtv <= u.vs_alloca_next` by decide_tac >>
  `w2n (dw:bytes32) + type_memory_size dtv < dimword (:256)` by decide_tac >>
  `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sB x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sB x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!entry. lookup_scopes id mid.scopes = SOME entry ==>
      evaluate_type (get_tenv cx) ty = SOME entry.type` by simp[] >>
  `~block_is_terminated sb` by
    (drule_all stmtSimDeclMemTheory.compile_assign_value_memory_widen_open >> simp[]) >>
  `?t Gf tf.
     (!D. gas_origin_ptr_path
        (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (u,Gi,ti) [] (OK t,Gf,tf)) /\
     ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
     t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
     u.vs_alloca_next <= t.vs_alloca_next /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
     (!d. return_buf_frame d cenv sB u ==> return_buf_frame d cenv sb t) /\
     (!aid ent. FLOOKUP u.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
     (!x. not_fresh_at sB x ==> lookup_var x t = lookup_var x u /\
           FLOOKUP Gf x = FLOOKUP Gi x /\ op_taint tf (Var x) = op_taint ti (Var x)) /\
     (!H. valid_horizon cx st0 H mid.storage_trace /\ stmt_state_rel H ctx func cenv cx mid u /\
          ghost_inv_at (DF H) lo d cenv cx mid Gi ti u ==>
          stmt_state_rel H ctx func cenv cx ff t /\ ghost_inv_at (DF H) lo d cenv cx ff Gf tf t /\
          alloca_frame cenv mid sB u cenv ff t /\
          (!aid off len i. FLOOKUP u.vs_allocas aid = SOME (off,len) /\ aid < sB.cs_next_id /\
            (!name a n. local_region cenv mid.scopes u name a n ==> off+len <= a \/ a+n <= off) /\
            off <= i /\ i < off+len /\ i IN tf.t_mem ==> i IN ti.t_mem))` by suspend "suffix" >>
  suspend "landing"
QED

Resume body_assign_local_memory_nonempty_full[suffix]:
  Cases_on `vv_location vv = SOME LocMemory`
  >- suspend "staged" >>
  suspend "direct"
QED

Resume body_assign_local_memory_nonempty_full[staged]:
  drule_all_then (map_every assume_tac o CONJUNCTS) immutable_assign_copy_metadata >>
  `type_memory_size stv < dimword (:256)` by decide_tac >>
  qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
  qpat_assum `vv_location vv = SOME LocMemory`
    (fn eq => qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`
      (assume_tac o REWRITE_RULE [eq])) >>
  Q.SUBGOAL_THEN
    `type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= u.vs_alloca_next`
    assume_tac >- simp[] >>
  `!j path entry t0. MemoryPlace id [] = MemoryPlace j path /\
     lookup_scopes j mid.scopes = SOME entry /\ cenv.ce_var_type j = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type` by simp[] >>
  mp_tac (Q.INST
    [`xd` |-> `p`, `loc` |-> `SOME LocMemory`, `dty` |-> `ty`,
     `sty` |-> `lowered_value_type cenv e`, `bytes` |-> `type_memory_bytes cenv ty`,
     `sa` |-> `sB`, `start` |-> `sa`, `s` |-> `u`, `ee` |-> `mid`,
     `H0` |-> `storage_trace_horizon mid.storage_trace`,
     `G` |-> `Gi`, `tn` |-> `ti`,
     `D0` |-> `DF (storage_trace_horizon mid.storage_trace)`, `d0` |-> `d`,
     `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (Q.INST [`p` |-> `MemoryPlace id []`]
       (horizonTypeLib.at_horizon_named "H0" body_assign_memory_place_joint))) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]]) >>
  strip_tac >> qexistsl_tac [`t`,`Gf`,`tf`] >> simp[] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H D d. _ ==> stmt_state_rel H _ _ _ _ ff t /\ _`
    (drule_all_then strip_assume_tac) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]] >>
  qpat_assum `!aid off len i. _ ==> i IN ti.t_mem` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ADD_COMM]
QED

Resume body_assign_local_memory_nonempty_full[direct]:
  qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
  `compile_store_memory cenv (Var xs) (Var p) ty (lowered_value_type cenv e) sB = ((),sb)` by
    (qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`
       (mp_tac o REWRITE_RULE [compile_assign_value_def]) >> simp[]) >>
  `?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
            (u,Gi,ti) [] (OK t,Gf,tf)) /\
    typed_copy_effect ctx func sB sb u t (w2n dw) (type_memory_size dtv) /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
         val_in_memory dtv v (w2n dw) m) /\
    (!x. not_fresh_at sB x ==> lookup_var x t = lookup_var x u /\
      FLOOKUP Gf x = FLOOKUP Gi x /\ op_taint tf (Var x) = op_taint ti (Var x)) /\
    tf.t_stor = ti.t_stor /\ tf.t_trans = ti.t_trans /\ tf.t_imm = ti.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
         (i IN tf.t_mem <=> i IN ti.t_mem))` by suspend "direct_effect" >>
  suspend "direct_post"
QED

Resume body_assign_local_memory_nonempty_full[direct_effect]:
  Cases_on `is_bytestring_type ty`
  >- suspend "direct_bytes" >>
  suspend "direct_flat"
QED

Resume body_assign_local_memory_nonempty_full[direct_flat]:
  `lowered_value_type cenv e = ty` by
    (qpat_assum `_ = ty \/ is_bytestring_type ty` mp_tac >>
     qpat_assum `~is_bytestring_type ty` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `stv = dtv` by
    (qpat_assum `lowered_value_type cenv e = ty` (fn eq =>
       qpat_assum `evaluate_type _ (lowered_value_type cenv e) = SOME stv`
         (mp_tac o REWRITE_RULE [eq])) >>
     asm_rewrite_tac[optionTheory.SOME_11] >> simp[]) >>
  qpat_x_assum `stv = dtv` SUBST_ALL_TAC >>
  `compile_copy_memory (Var p) (Var xs) (type_memory_size dtv) sB = ((),sb)` by
    (qpat_assum `compile_store_memory _ _ _ _ _ _ = _`
       (mp_tac o REWRITE_RULE [contextTheory.compile_store_memory_def]) >> simp[]) >>
  `val_footprint dtv v <= type_memory_size dtv` by simp[val_footprint_le] >>
  irule body_assign_local_memory_flat_copy_effect >>
  asm_rewrite_tac[] >>
  qexistsl_tac [`sw`,`p`,`xs`] >> simp[]
QED

Resume body_assign_local_memory_nonempty_full[direct_bytes]:
  `is_bytestring_type (lowered_value_type cenv e)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source] >>
  `compile_store_bytestring (Var xs) (Var p) sB = ((),sb)` by
    (qpat_assum `compile_store_memory _ _ _ _ _ _ = _`
       (mp_tac o REWRITE_RULE [contextTheory.compile_store_memory_def]) >> simp[]) >>
  Q.SUBGOAL_THEN
    `?len. ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
            (?str. v = StringV str /\ len = LENGTH str)) /\
           val_store_size stv v = 32 + 32 * word_size len`
    (qx_choose_then `len` (map_every assume_tac o CONJUNCTS))
  >- suspend "bytes_size" >>
  qabbrev_tac `n = 32 + 32 * word_size len` >>
  `val_store_size stv v = val_store_size dtv v` by
    (irule bytestring_val_store_size_eq >> simp[] >>
     qexistsl_tac [`lowered_value_type cenv e`,`ty`,`get_tenv cx`] >> simp[]) >>
  `n <= type_memory_size stv /\ n <= type_memory_size dtv` by
    (`val_store_size stv v <= type_memory_size stv /\
      val_store_size dtv v <= type_memory_size dtv` by simp[val_store_size_le] >>
     `n = 32 + 32 * word_size len` by simp[Abbr `n`] >> decide_tac) >>
  suspend "bytes_execute"
QED

Resume body_assign_local_memory_nonempty_full[bytes_size]:
  drule_all (Q.SPECL [`get_tenv cx`,`lowered_value_type cenv e`,`stv`] bytestring_type_value) >>
  qpat_x_assum `value_has_type stv v` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >> strip_tac >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def,val_store_size_def]
QED

Resume body_assign_local_memory_nonempty_full[bytes_execute]:
  `len <= 32 * word_size len` by simp[exprSimPropsTheory.le_word_size_mul] >>
  `n = 32 + 32 * word_size len` by simp[Abbr `n`] >>
  `len+31 < dimword (:256) /\ n < dimword (:256) /\
   w2n (sw:bytes32) + n <= u.vs_alloca_next /\
   w2n (dw:bytes32) + n <= u.vs_alloca_next` by decide_tac >>
  `n = 32 + 32 * ((len+31) DIV 32)` by simp[vfmConstantsTheory.word_size_def,Abbr `n`] >>
  `ptr_covers Gi ti xs u n /\ ptr_covers Gi ti p u n` by
    (conj_tac >> irule reasonCopySourcePtrTheory.ptr_covers_mono >-
       (qexists_tac `type_memory_size stv` >> simp[]) >>
     qexists_tac `type_memory_size dtv` >> simp[]) >>
  `?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (u,Gi,ti) [] (OK t,Gf,tf)) /\
    typed_copy_effect ctx func sB sb u t (w2n dw) (type_memory_size dtv) /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
         val_in_memory dtv v (w2n dw) m) /\
    (!x. not_fresh_at sB x ==> lookup_var x t = lookup_var x u /\
      FLOOKUP Gf x = FLOOKUP Gi x /\ op_taint tf (Var x) = op_taint ti (Var x)) /\
    tf.t_stor = ti.t_stor /\ tf.t_trans = ti.t_trans /\ tf.t_imm = ti.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+n) ==> (i IN tf.t_mem <=> i IN ti.t_mem))` by
    (irule body_assign_local_memory_bytes_copy_effect >> asm_rewrite_tac[] >>
     conj_tac >- (qexists_tac `len` >> simp[]) >>
     qexistsl_tac [`ty`,`stv`,`lowered_value_type cenv e`,`sw`,`get_tenv cx`,`p`,`xs`] >>
     qpat_assum `n = 32 + 32 * ((_+31) DIV 32)` (SUBST1_TAC o SYM) >>
     simp[]) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[] >>
  gen_tac >> strip_tac >>
  `~(w2n (dw:bytes32) <= i /\ i < w2n dw + n)` by decide_tac >>
  simp[]
QED

Resume body_assign_local_memory_nonempty_full[direct_post]:
  drule_then strip_assume_tac typed_copy_effect_endpoint >>
  drule_then assume_tac typed_copy_effect_allocas >>
  `t.vs_alloca_next = u.vs_alloca_next /\ t.vs_fmp = u.vs_fmp /\
   t.vs_initial_fmp = u.vs_initial_fmp` by
    (drule typed_copy_effect_record >> simp[venomStateTheory.venom_state_component_equality]) >>
  `alloca_history func t` by
    (qpat_assum `!D. gas_origin_ptr_path _ (u,Gi,ti) [] (OK t,Gf,tf)`
       (qspec_then `DF (storage_trace_horizon mid.storage_trace)` assume_tac) >>
     drule_at (Pat `gas_origin_ptr_path _ _ _ _`)
       bodyFullPathHistoryTheory.body_full_path_alloca_history >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (strip_tac >> simp[ptrDisciplineTheory.allocas_below_fmp_def] >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u`
       (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_below_fmp_def] o UNDISCH) >> simp[]) >>
  drule_then assume_tac typedStoreCodeTheory.compile_store_memory_next_var >>
  `!d. return_buf_frame d cenv sB u ==> return_buf_frame d cenv sb t` by
    (rpt strip_tac >> irule return_buf_frame_frame >> simp[] >>
     qexistsl_tac [`cenv`,`u`,`sB`] >> simp[] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sB x ==> _` drule >> simp[]) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[] >>
  gen_tac >> strip_tac >>
  `!j path entry t0. MemoryPlace id [] = MemoryPlace j path /\
     lookup_scopes j mid.scopes = SOME entry /\ cenv.ce_var_type j = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type` by simp[] >>
  drule_then
    (drule_at_then (Pat `stmt_state_rel _ _ _ _ _ _ _`)
      (drule_at_then (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)
        (drule_at_then (Pat `write_place _ _ _ _ = _`) mp_tac)))
    body_assign_memory_place_store_post >>
  disch_then (qspecl_then [`tf`,`env`,`ty`,`Gf`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]]) >>
  strip_tac >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]] >>
  qpat_assum `!aid off len i. _ ==> i IN ti.t_mem` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Resume body_assign_local_memory_nonempty_full[landing]:
  qexistsl_tac [`ff`,`t`,`Gf`,`tf`] >>
  simp[stmt_lands_def,stmtSimPropsTheory.cenv_top_ext_refl] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel H ctx func cenv cx mid u` by
    (drule exprSimWordArgsTheory.expr_post_state >> simp[]) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace /\ _ ==> _`
    (qspec_then `H` mp_tac) >> simp[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sB x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `storage_well_formed_on cx ff (FST H)` by
    (`storage_well_formed_on cx mid (FST H)` by
       (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
          (assume_tac o cj 2 o REWRITE_RULE [expr_post_def]) >> simp[]) >>
     `storage_well_formed_on cx ff (FST H) =
      storage_well_formed_on cx mid (FST H)` by
       (irule storage_well_formed_on_backends >> simp[Abbr `ff`]) >> simp[]) >>
  qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (fn th => let val facts = REWRITE_RULE [expr_post_def] th
              in map_every assume_tac [cj 6 facts,cj 7 facts] end) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w` by
    first_assum ACCEPT_TAC >>
  `return_buf_frame d cenv sB u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by (bossLib.simp []) >>
  `alloca_frame cenv es sa s0 cenv ff t /\
   (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
     (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off+sz <= b \/ b+sz' <= off) /\
     off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn0.t_mem)` by suspend "landing_alloca" >>
  `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) u` by
    (fs[arithmeticTheory.ADD_COMM]) >>
  `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t` by
    (qpat_assum `!D. gas_origin_ptr_path _ (u,Gi,ti) [] (OK t,Gf,tf)`
       (qspec_then `DF H` (fn path =>
         qpat_assum `return_buf_frame d cenv sB u` (fn frame =>
           qpat_assum `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) u` (fn floor =>
             mp_tac (MATCH_MP return_buf_allocas_suffix (LIST_CONJ [path,frame,floor])))))) >>
     simp[]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       simp[storage_trace_frame_bind_all,cj 5 evaluate_storage_trace_frame,
            storage_trace_frame_read_result] >>
     drule valid_horizon_frame >> disch_then drule >> simp[]) >>
  `MAP FDOM ff.scopes = MAP FDOM es.scopes` by
    (drule vyperScopePreservationTheory.write_place_scopes_dom >> strip_tac >>
     drule eval_read_preserves_scopes_dom >> simp[]) >>
  `return_buf_sep d cenv ff t` by
    (irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
     conj_tac >- fs[] >>
     qexistsl_tac [`H`,`ctx`,`cx`,`es`,`func`,`s0`,`sa`] >> simp[]) >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ Gi ti`
    (assume_tac o cj 1 o REWRITE_RULE [ghost_kept_at_def]) >>
  simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume body_assign_local_memory_nonempty_full[landing_alloca]:
  `valid_horizon cx st0 H es.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       simp[storage_trace_frame_bind_all,cj 5 evaluate_storage_trace_frame,
            storage_trace_frame_read_result] >>
     drule valid_horizon_frame >> disch_then drule >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by simp[] >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (drule eval_read_preserves_scopes_dom >> simp[]) >>
  `sa.cs_next_id <= sB.cs_next_id` by
    (qspec_then `sa` mp_tac (Q.SPECL [`cenv`,`expr_type e`,`e`] ci_mono_lower_value_compile_expr) >>
     simp[ci_mono_def]) >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ Gi ti`
    (assume_tac o cj 2 o REWRITE_RULE [ghost_kept_at_def]) >>
  qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac
       body_assign_widened_frame_compose) >>
  disch_then (qspecl_then [`tn0`,`ti`,`tf`,`t`,`ff`] mp_tac) >>
  impl_tac >-
    (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
      qpat_assum `!aid off len i. FLOOKUP u.vs_allocas aid = SOME (off,len) /\ _ ==> i IN ti.t_mem` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[arithmeticTheory.ADD_COMM]]) >>
  disch_then ACCEPT_TAC
QED

Finalise body_assign_local_memory_nonempty_full

(* A memory local whose source is stored at its own layout. *)
Theorem body_assign_local_memory_full:
  !cx id ty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (NameTarget id)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME ty /\
    ~is_word_type ty /\
    0 < type_memory_bytes cenv ty /\
    (lowered_value_type cenv e = ty \/ is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e`
  >- (irule body_assign_local_memory_empty_full >>
      simp[] >> rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- metis_tac[] >>
      qexistsl_tac [`env`, `env'`, `ty`] >> simp[]) >>
  irule body_assign_local_memory_nonempty_full >>
  simp[] >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- metis_tac[] >>
  qexistsl_tac [`bindings`, `env`, `env'`, `tops`, `ty`] >> simp[] >> metis_tac[]
QED


Theorem body_assign_snapshot_word_joint[local]:
  expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL pv,ee) /\ read_result cx pv ee = (INL v,ee) /\
  is_word_type (lowered_value_type ce e) /\
  compile_expr ce (expr_type e) e sa = (vv0,sm) /\
  compile_snapshot_vv ce T (vv_with_type (lowered_value_type ce e) vv0) sm = (snap,sb) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x. vv_operand vv0 = Var x ==> not_fresh_at sm x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func ce cx e es sa sm s0 ee pv vv0 s /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee pv vv0 s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_vv_ok cx (post_value_type ce e) pv vv0 ee G tn s /\
  (!t p. vv0 = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv0 = SOME LocCode ==>
    ?val. read_result cx pv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv0) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  return_buf_frame d ce sm s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?u Gf tnf tv.
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
    value_has_type tv v /\ val_wf tv v /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tnf) /\
      stmt_state_rel H ctx func ce cx ee u /\
      ghost_inv_at (DF H) lo d ce cx ee Gf tnf u) /\
    eval_operand (vv_operand snap) u = SOME (typed_val_to_w256 tv v) /\
    op_taint tnf (vv_operand snap) = {} /\
    vv_location snap = NONE /\ vv_type snap = lowered_value_type ce e /\
    (!x. vv_operand snap = Var x ==> not_fresh_at sb x) /\
    (!lbl. vv_operand snap <> Label lbl) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    s0.vs_alloca_next <= u.vs_alloca_next /\ return_buf_frame d ce sb u /\
    ghost_kept_at lo ce es sa Gi ti s0 Gf tnf /\
    ghost_kept_at lo ce ee sm G tn s Gf tnf /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    alloca_frame ce ee sm s ce ee u /\
    (!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sm.cs_next_id /\
      (!n b sz'. local_region ce ee.scopes s n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tnf.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >>
  `(do pv <- eval_expr cx e; read_result cx pv od) es = (INL v,ee)` by
    simp[vyperStateTheory.bind_def] >>
  drule_all immutable_rhs_physical_typed >> strip_tac >>
  `post_value_type ce e = lowered_value_type ce e` by
    metis_tac[immutable_rhs_post_physical_classify,is_bytestring_word_type] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `unwrap_value ce (vv_with_type (lowered_value_type ce e) vv0) = unwrap_value ce vv0` by
    (irule snapshot_retag_unwrap >>
     qexistsl_tac [`cx`,`ee`,`s`,`post_value_type ce e`,`pv`] >>
     fs[vv_post_def]) >>
  `vv_type (vv_with_type (lowered_value_type ce e) vv0) = lowered_value_type ce e` by
    (Cases_on `vv0` >> simp[vv_with_type_def,vv_type_def]) >>
  qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
  simp[compile_snapshot_vv_def,comp_bind_def,comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `unwrap_value ce vv0 sm = (op,sb)` >>
  `ptr_vv_ok cx (post_value_type ce e) pv vv0 ee G tn s` by simp[] >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) unwrap_word_value_origin_ptr >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `storage_trace_domain _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspec_then `stv` mp_tac) >>
  disch_then (qspec_then `explicit` mp_tac) >>
  disch_then (qspecl_then [`d`,`ctx`,`PG`,`DF`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  strip_tac >> gvs[] >>
  qexistsl_tac [`z`,`G'`,`tn'`] >>
  conj_tac >- metis_tac[expr_post_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `ci_mono sm sb` by metis_tac[ci_mono_unwrap_value,pairTheory.SND] >>
  `return_buf_frame d ce sb z` by
    (irule return_buf_frame_frame >>
     qexistsl_tac [`ce`,`s`,`sm`] >>
     fs[ci_mono_def,wb_frame_def]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >> fs[vv_post_def]) >>
  `alloca_frame ce ee sm s ce ee z` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >>
     fs[wb_frame_def] >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`storage_trace_horizon ee.storage_trace`,`ctx`,`cx`,`func`] >>
     simp[]) >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> irule compiler_unwrap_value_var >>
     qexistsl_tac [`ce`,`op`,`sm`,`vv0`] >> simp[] >>
     Cases_on `vv0` >> fs[vv_operand_def]) >>
  `lower_value compile_expr ce (expr_type e) e sa = (op,sb)` by
    simp[lower_value_def,comp_bind_def] >>
  `!lbl. op <> Label lbl` by
    (irule exprReasonOperandTheory.lower_compile_expr_not_label >>
     goal_assum (drule_at Any) >> qexists_tac `env` >>
     drule_then strip_assume_tac expr_body_pre_static_facts >>
     fs[expr_sim_inv_def]) >>
  `~z.vs_halted` by
    (drule gas_origin_ptr_path_projections >> strip_tac >>
     metis_tac[fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted]) >>
  simp[vv_operand_def,vv_location_def,vv_type_def] >>
  fs[expr_post_def,expr_val_rel_def,ptr_val_ok_def,wb_frame_def,ghost_kept_at_def] >>
  conj_tac >- metis_tac[] >> first_assum ACCEPT_TAC
QED

Theorem body_assign_observed_storage_read_live[local]:
  !env cx es e H es1 tr slot leaf raw.
    runtime_consistent env cx es /\ well_typed_expr env e /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    valid_horizon cx es H es1.storage_trace /\
    eval_expr cx e es = (INL (PlaceR (StoragePlace tr slot leaf)),es1) ==>
    storage_read_live H tr raw slot leaf
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `type_slot_size leaf = 0`
  >- simp[storage_read_live_def, wordsTheory.w2n_lt, arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  drule_all eval_expr_observed_region >> strip_tac >>
  `MEM (tr,n2w offset,tv) (FST H)` by
    (irule storage_observations_ok_root >>
     fs[valid_horizon_def] >> metis_tac[]) >>
  irule storage_place_observed_read_live >>
  simp[storage_place_observed_def] >>
  qexistsl [`n2w offset`, `tv`, `path`, `delta`] >> simp[]
QED

Theorem body_assign_representation_storage_live[local]:
  env.type_defs = get_tenv cx /\
  eval_result_typed (env,cx,es1) pv (Type ty) /\
  vv_place_ptr cenv cx es1 s pv vv /\
  (!t p. vv = LocatedValue t p /\
     (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
     t = ty /\ (!v. pv <> Value v)) /\
  (!tr slot leaf. pv = PlaceR (StoragePlace tr slot leaf) ==>
     storage_read_live H tr (get_storage cx es1 tr) slot leaf) ==>
  vv_storage_live H cx vv es1 s
Proof
  Cases_on `vv` >- simp[] >>
  rpt strip_tac >>
  rename1 `vv_place_ptr cenv cx es1 s pv (LocatedValue t p)` >>
  Cases_on `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient`
  >- (first_x_assum (qspecl_then [`t`, `p`] mp_tac) >>
      simp[] >> strip_tac >>
      Cases_on `pv` >> gvs[eval_result_typed_def] >>
      Cases_on `p'` >>
      gvs[vv_place_ptr_def, runtime_place_typed_def, place_type_value_def,
          slot_loc_def, vyperStateTheory.return_def] >>
      Cases_on `b` >> gvs[]) >>
  gvs[]
QED

Theorem body_assign_attribute_storage_origin:
  compile_attribute f cenv rt ty obj fld sa = (LocatedValue t p,sb) /\
  p.ptr_location <> LocMemory ==>
  t = rt /\
  vv_location (FST (f cenv ty obj sa)) = SOME p.ptr_location
Proof
  Cases_on `f cenv ty obj sa` >> Cases_on `vv_location q` >>
  simp[compile_attribute_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> simp[mk_ptr_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem body_assign_subscript_storage_origin:
  compile_subscript f cenv rt ty obj idx sa = (LocatedValue t p,sb) /\
  p.ptr_location <> LocMemory ==>
  t = rt /\ ~copies_subscript_base cenv obj idx /\
  vv_location (FST (f cenv ty obj sa)) = SOME p.ptr_location
Proof
  Cases_on `f cenv ty obj sa` >>
  simp[compile_subscript_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `copies_subscript_base cenv obj idx` >> gvs[comp_return_def]
  >- (`vv_with_type (vv_type q) q = q` by
        (Cases_on `q` >> simp[vv_with_type_def, vv_type_def]) >>
      qpat_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
      qpat_assum `vv_with_type _ _ = _`
        (fn th => once_rewrite_tac [GSYM th]) >>
      disch_then (mp_tac o MATCH_MP snapshot_saved_representation) >>
      strip_tac >> Cases_on `is_word_type (vv_type q)` >> gvs[] >>
      Cases_on `place_type cenv obj` >>
      rpt BasicProvers.TOP_CASE_TAC >>
      simp[comp_bind_def, comp_return_def, LET_THM] >>
      rpt (pairarg_tac >> gvs[]) >>
      gvs[mk_ptr_def, AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[mk_ptr_def]) >>
  rename1 `f cenv ty obj sa = (bv,bs)` >>
  Cases_on `vv_location bv` >> Cases_on `place_type cenv obj` >>
  rpt BasicProvers.TOP_CASE_TAC >>
  simp[comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[mk_ptr_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[mk_ptr_def]
QED

Theorem assign_storage_annotated_src_lookup[local]:
  !tops src vars key loc.
    (!off. loc <> ImmutableLoc off) /\
    FLOOKUP (add_annotated_immutables_src src tops vars) key = SOME loc ==>
    FLOOKUP vars key = SOME loc
Proof
  Induct >> simp[add_annotated_immutables_src_def] >>
  Cases >> simp[add_annotated_immutables_src_def] >>
  rpt gen_tac >> rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  strip_tac >> first_x_assum drule_all >>
  simp[FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[]
QED

Theorem assign_storage_annotated_mods_lookup[local]:
  !mods vars key loc.
    (!off. loc <> ImmutableLoc off) /\
    FLOOKUP (add_annotated_immutables_mods mods vars) key = SOME loc ==>
    FLOOKUP vars key = SOME loc
Proof
  Induct >> simp[add_annotated_immutables_mods_def] >>
  PairCases >> simp[add_annotated_immutables_mods_def] >>
  rpt strip_tac >>
  first_x_assum (drule_all_then assume_tac) >>
  drule_all_then ACCEPT_TAC assign_storage_annotated_src_lookup
QED

Theorem assign_storage_location_src_lookup[local]:
  !tops owner vars src id loc.
    FLOOKUP (add_module_var_locations_src owner tops vars) (src,id) = SOME loc ==>
    FLOOKUP vars (src,id) = SOME loc \/
    (src = owner /\ find_var_decl_by_name id tops <> NONE)
Proof
  Induct >> simp[add_module_var_locations_src_def] >>
  Cases >> simp[add_module_var_locations_src_def, find_var_decl_by_name_def] >>
  rpt gen_tac >> rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  strip_tac >> first_x_assum drule >>
  simp[FLOOKUP_UPDATE] >> rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem assign_storage_location_mods_lookup[local]:
  !mods vars src id loc.
    ALL_DISTINCT (MAP FST mods) /\
    FLOOKUP (add_module_var_locations_mods mods vars) (src,id) = SOME loc ==>
    FLOOKUP vars (src,id) = SOME loc \/
    ?tops. ALOOKUP mods src = SOME tops /\ find_var_decl_by_name id tops <> NONE
Proof
  Induct >> simp[add_module_var_locations_mods_def] >>
  PairCases >> simp[add_module_var_locations_mods_def] >>
  rename1 `MEM owner (MAP FST rest)` >>
  rpt strip_tac >>
  first_x_assum (drule_all_then strip_assume_tac)
  >- (drule_then strip_assume_tac assign_storage_location_src_lookup >> simp[]) >>
  Cases_on `owner = src` >> gvs[] >>
  `ALOOKUP rest owner = NONE` by simp[ALOOKUP_NONE] >> gvs[]
QED

Theorem assign_storage_unit_lookup[local]:
  FLOOKUP (add_immutable_locations_unit sft mods vars) key = SOME loc /\
  (!off. loc <> ImmutableLoc off) ==>
  FLOOKUP vars key = SOME loc
Proof
  Cases_on `mods`
  >- simp[add_immutable_locations_unit_def, add_annotated_immutables_mods_def] >>
  rename1 `FLOOKUP (add_immutable_locations_unit _ (entry::rest) _) _ = _` >>
  Cases_on `rest` >> PairCases_on `entry` >>
  rename1 `FLOOKUP (add_immutable_locations_unit _ ((owner,_)::_) _) _ = _` >>
  Cases_on `owner` >> simp[add_immutable_locations_unit_def] >>
  rpt strip_tac >>
  metis_tac[add_immutable_locations_FLOOKUP, assign_storage_annotated_mods_lookup]
QED

Theorem assign_storage_location_tables[local]:
  contract_inv mods exps ctx cenv cx ==>
  ALL_DISTINCT (MAP FST mods) /\
  cenv.ce_module_vars = add_immutable_locations_unit
    (get_struct_fields (make_struct_fields_map_mods mods)) mods
    (add_module_var_locations_mods mods FEMPTY)
Proof
  simp[contract_inv_def, cenv_module_pins_mods_def]
QED

Theorem body_assign_module_storage_decl_mods[local]:
  contract_inv mods exps ctx cenv cx /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME loc /\
  ((?slot. loc = StorageLoc slot) \/ (?slot. loc = TransientLoc slot)) ==>
  ?tops. ALOOKUP mods src = SOME tops /\ find_var_decl_by_name id tops <> NONE
Proof
  strip_tac >>
  `!off. loc <> ImmutableLoc off` by fs[] >>
  drule_then strip_assume_tac assign_storage_location_tables >>
  qpat_assum `cenv.ce_module_vars = _` (fn eq =>
    qpat_assum `FLOOKUP cenv.ce_module_vars _ = _`
      (assume_tac o REWRITE_RULE [eq])) >>
  drule_all_then assume_tac assign_storage_unit_lookup >>
  drule_all_then strip_assume_tac assign_storage_location_mods_lookup >> gvs[]
QED

Theorem body_assign_storage_target_root_mods[local]:
  !bt f cenv sa op loc pt sb mods exps ctx cx.
    contract_inv mods exps ctx cenv cx /\
    compile_get_target_ptr f cenv bt sa = ((op,SOME loc,pt),sb) /\
    (loc = LocStorage \/ loc = LocTransient) ==>
    ~immutable_root cx bt
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt`
  >- simp[immutable_root_def, target_root_def]
  >- (PairCases_on `p` >> rpt gen_tac >>
      simp[compile_get_target_ptr_def, LET_THM] >>
      rpt BasicProvers.TOP_CASE_TAC >> simp[comp_return_def] >>
      rpt strip_tac >> gvs[] >>
      `?tops. ALOOKUP mods p0 = SOME tops /\ find_var_decl_by_name p1 tops <> NONE` by
        (irule body_assign_module_storage_decl_mods >> metis_tac[]) >>
      `get_module_code cx p0 = SOME tops` by
        (drule_then (qspec_then `p0` assume_tac) contract_inv_module_codes >> simp[]) >>
      gvs[immutable_root_def, target_root_def]) >>
  simp[compile_get_target_ptr_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >>
  rpt BasicProvers.TOP_CASE_TAC >>
  gvs[comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  PairCases_on `result` >> gvs[] >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[expr_size_def] >>
  metis_tac[immutable_root_def, target_root_def]
QED

Theorem body_assign_storage_target_not_immutable_mods[local]:
  contract_inv mods exps ctx cenv cx /\
  compile_get_target_ptr f cenv bt sa = ((op,SOME loc,pt),sb) /\
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_target_place cx bt es = (INL p,es1) ==>
  !src id path. p <> ImmutablePlace src id path
Proof
  strip_tac >>
  `~immutable_root cx bt` by (irule body_assign_storage_target_root_mods >> metis_tac[]) >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  metis_tac[aug_place_base_immutable_origin]
QED

Theorem body_assign_pop_nonvalue[local]:
  (!src id path. p <> ImmutablePlace src id path) /\
  pop_place cx p es = (INL pv,es1) ==> !v. pv <> Value v
Proof
  Cases_on `p` >> simp[] >> strip_tac
  >~ [`pop_place _ (MemoryPlace _ _) _ = _`]
  >- (drule vyperPlaceMutationSoundnessTheory.pop_memory_place_success >>
      strip_tac >> gvs[]) >>
  qpat_x_assum `pop_place _ _ _ = _` mp_tac >>
  Cases_on `t` >> simp[pop_place_def, raise_def] >>
  rename1 `ArrayTV _ bd` >> Cases_on `bd` >>
  simp[pop_place_def, raise_def, bind_def, ignore_bind_def,
       return_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem body_assign_storage_base_result_mods[local]:
  contract_inv mods exps ctx cenv cx /\
  (case e of TopLevelName _ _ => T | Pop _ _ => T | _ => F) /\
  compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  eval_expr cx e es = (INL pv,es1) ==>
  t = expr_type e /\ (!v. pv <> Value v)
Proof
  Cases_on `e` >> simp[]
  >- (PairCases_on `p'` >> strip_tac >>
      qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[Once compile_expr_def] >>
      Cases_on `FLOOKUP cenv.ce_module_vars (p'0,p'1)` >>
      gvs[] >> rpt BasicProvers.TOP_CASE_TAC >>
      rpt (pairarg_tac >> gvs[]) >> disch_tac >> gvs[mk_ptr_def] >>
      `?tops. ALOOKUP mods p'0 = SOME tops /\ find_var_decl_by_name p'1 tops <> NONE` by
        (irule body_assign_module_storage_decl_mods >> metis_tac[]) >>
      `get_module_code cx p'0 = SOME tops` by
        (drule_then (qspec_then `p'0` assume_tac) contract_inv_module_codes >> simp[]) >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, lookup_global_def] >>
      Cases_on `find_var_decl_by_name p'1 tops` >> gvs[] >>
      PairCases_on `x` >> Cases_on `x0` >>
      simp[bind_def, ignore_bind_def, lift_option_type_def,
           return_def, raise_def, record_storage_event_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >- (strip_tac >>
      qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      rewrite_tac[nested_pop_compile_eq] >> simp[LET_THM] >>
      rpt (pairarg_tac >> gvs[]) >>
      Cases_on `loc_opt` >> simp[mk_ptr_def] >> strip_tac >> gvs[] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
      `!src id path. p <> ImmutablePlace src id path` by
        (irule body_assign_storage_target_not_immutable_mods >> metis_tac[]) >>
      simp[expr_type_def] >> irule body_assign_pop_nonvalue >> metis_tac[])
QED

Theorem body_assign_storage_expr_cases[local]:
  body_inv tops ctx cenv cx /\
  compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
  (case e of TopLevelName _ _ => T | Pop _ _ => T |
     Attribute _ _ _ => T | Subscript _ _ _ => T | _ => F)
Proof
  disch_then (CONJUNCTS_THEN2 kall_tac
    (CONJUNCTS_THEN2 mp_tac assume_tac)) >>
  Cases_on `e` >> simp[] >>
  pure_once_rewrite_tac [CONJUNCT1 compile_expr_raw_def]
  >~ [`compile_expr_body _ _ _ _ _ (Literal _ _) _`] >-
    (simp[compile_expr_body_def, expr_type_def] >>
     disch_then (mp_tac o MATCH_MP reason_compile_literal) >>
     gvs[reason_result_shape_def])
  >~ [`compile_expr_body _ _ _ _ _ (IfExp _ _ _ _) _`] >-
    (disch_then (mp_tac o MATCH_MP reason_compile_ifexp) >>
     gvs[reason_result_shape_def])
  >~ [`compile_expr_body _ _ _ _ _ (StructLit _ _ _) _`] >-
    (disch_then (mp_tac o MATCH_MP reason_compile_structlit) >>
     gvs[reason_result_shape_def])
  >~ [`compile_expr_body _ _ _ _ _ (Call _ _ _ _) _`] >-
    (simp[compile_expr_body_def, expr_type_def] >>
     disch_then (mp_tac o MATCH_MP reason_compile_call) >>
     gvs[reason_result_shape_def])
  >~ [`compile_expr_body _ _ _ _ _ (Builtin _ _ _) _`] >- suspend "builtin"
  >~ [`compile_expr_body _ _ _ _ _ (TypeBuiltin _ _ _ _) _`] >- suspend "typebuiltin" >>
  simp[compile_expr_body_def, expr_type_def, compile_name_vv_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, mk_ptr_def, AllCaseEqs()] >>
  rename1 `FLOOKUP cenv.ce_vars nm` >>
  Cases_on `FLOOKUP cenv.ce_vars nm`
  >- (gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> gvs[])) >>
  rename1 `FLOOKUP _ _ = SOME binding` >> Cases_on `binding` >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def, mk_ptr_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[]
QED

Resume body_assign_storage_expr_cases[builtin]:
  disch_then (mp_tac o MATCH_MP reason_compile_expr_builtin_shape_classify) >>
  gvs[reason_result_shape_def] >>
  (simp[exprCallBoundsTheory.builtin_child_callback_def] >>
   pure_once_rewrite_tac [CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)] >>
   rename1 `compile_builtin_dispatch_body _ _ _ _ bi _ _` >>
   Cases_on `bi` >> strip_tac
   >~ [`Acc item`] >- suspend "acc"
   >~ [`AsWeiValue denom`] >- suspend "wei"
   >~ [`Len`] >- (drule reason_builtin_len >> gvs[reason_result_shape_def])
   >~ [`Bop bop`] >- (drule reason_builtin_bop >> gvs[reason_result_shape_def])
   >~ [`MakeArray et bd`] >- (drule reason_builtin_makearray >> gvs[reason_result_shape_def])
   >~ [`MethodId`] >- (drule reason_builtin_method_id >> gvs[reason_result_shape_def])
   >~ [`Keccak256`] >- (drule_at Any reason_builtin_hash >> simp[reason_result_shape_def])
   >~ [`Sha256`] >- (drule_at Any reason_builtin_hash >> simp[reason_result_shape_def])
   >~ [`CalldataSlice n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`ECAdd`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`ECMul`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`Concat n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`Slice n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`Uint2Str n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`NamedConst`] >-
     (gvs[compile_builtin_dispatch_body_def, LET_THM] >>
      pairarg_tac >> gvs[] >>
      gvs[AllCaseEqs(), as_stack_val_def, as_ptr_val_def, mk_ptr_def])
   >~ [`BoolChain _ _`] >-
     (gvs[compile_builtin_dispatch_body_def, LET_THM] >>
      rpt (pairarg_tac >> gvs[])) >>
   drule_at Any reason_builtin_scalar >> simp[reason_result_shape_def])
QED

Resume body_assign_storage_expr_cases[typebuiltin]:
  simp[compile_expr_body_def, expr_type_def] >>
  simp[exprCallBoundsTheory.type_child_callback_def] >>
  pure_once_rewrite_tac [CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)] >>
  rename1 `compile_type_builtin_dispatch_body _ _ _ _ tb _ _ _` >>
  strip_tac >> Cases_on `tb` >> gvs[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), oneline as_stack_val_def, oneline as_ptr_val_def,
      mk_ptr_def, base_ptr_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), mk_ptr_def, base_ptr_def]
QED

Resume body_assign_storage_expr_cases[acc]:
  simp[markerTheory.resconj_def, markerTheory.suspendimp_def] >>
  rpt strip_tac >>
  gvs[compile_builtin_dispatch_body_def, oneline as_stack_val_def, AllCaseEqs()]
QED

Resume body_assign_storage_expr_cases[wei]:
  simp[markerTheory.resconj_def, markerTheory.suspendimp_def] >>
  rpt strip_tac >> gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), oneline as_stack_val_def]
QED

Finalise body_assign_storage_expr_cases

Theorem body_assign_select_nonvalue:
  (!v. raw <> Value v) /\
  select_result cx ty raw sub st = (INL out,st') ==>
  !v. out <> Value v
Proof
  Cases_on `raw` >> simp[select_result_def] >> rpt strip_tac >>
  drule extend_place_result_shape >> strip_tac >> gvs[]
QED

Theorem body_assign_storage_result_shape_from_cases[local]:
  body_inv tops ctx cenv cx /\
  (!e ty sa t p sb.
    compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
    (case e of TopLevelName _ _ => T | Pop _ _ => T |
       Attribute _ _ _ => T | Subscript _ _ _ => T | _ => F)) /\
  (!e ty sa t p sb es pv es1.
    (case e of TopLevelName _ _ => T | Pop _ _ => T | _ => F) /\
    compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    eval_expr cx e es = (INL pv,es1) ==>
    t = expr_type e /\ (!v. pv <> Value v)) ==>
  !e ty sa t p sb es pv es1.
    compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    eval_expr cx e es = (INL pv,es1) ==>
    t = expr_type e /\ (!v. pv <> Value v)
Proof
  strip_tac >> measureInduct_on `expr_size e` >>
  rpt gen_tac >> disch_tac >>
  `case e of TopLevelName _ _ => T | Pop _ _ => T |
     Attribute _ _ _ => T | Subscript _ _ _ => T | _ => F` by metis_tac[] >>
  Cases_on `case e of TopLevelName _ _ => T | Pop _ _ => T | _ => F`
  >- (qpat_x_assum `!e ty sa t p sb es pv es1. _` irule >>
      metis_tac[]) >>
  qpat_x_assum `!e ty sa t p sb es pv es1. _` kall_tac >>
  qpat_x_assum `!e ty sa t p sb. _` kall_tac >>
  Cases_on `e` >> gnvs[] >>
  qpat_x_assum `_ /\ _` (map_every assume_tac o CONJUNCTS)
  >- (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[Once compile_expr_def] >> strip_tac >>
      `p.ptr_location <> LocMemory` by
        (Cases_on `p.ptr_location` >> gvs[]) >>
      drule_all body_assign_subscript_storage_origin >>
      simp[] >> strip_tac >>
      `~subscript_reads_base cx e' e0` by
        metis_tac[body_inv_copies_subscript_base] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
      rpt strip_tac >>
      Cases_on `compile_expr cenv ty e' sa` >> Cases_on `q` >>
      gvs[vv_location_def] >>
      qpat_x_assum `!y. expr_size y < _ ==> _`
        (qspec_then `e'` mp_tac) >>
      (impl_tac >- simp[]) >> disch_then drule >>
      disch_then assume_tac >>
      `!v. res <> Value v` by metis_tac[] >>
      metis_tac[body_assign_select_nonvalue])
  >- (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[Once compile_expr_def] >> strip_tac >>
      `p.ptr_location <> LocMemory` by
        (Cases_on `p.ptr_location` >> gvs[]) >>
      drule_all body_assign_attribute_storage_origin >>
      simp[] >> strip_tac >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
      rpt strip_tac >>
      Cases_on `compile_expr cenv ty e' sa` >> Cases_on `q` >>
      gvs[vv_location_def] >>
      qpat_x_assum `!y. expr_size y < _ ==> _`
        (qspec_then `e'` mp_tac) >>
      (impl_tac >- simp[]) >> disch_then drule >>
      disch_then assume_tac >>
      `!v. res <> Value v` by metis_tac[] >>
      metis_tac[body_assign_select_nonvalue])
QED

Theorem body_assign_storage_result_shape:
  body_inv tops ctx cenv cx /\
  compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  eval_expr cx e es = (INL pv,es1) ==>
  t = expr_type e /\ (!v. pv <> Value v)
Proof
  strip_tac >>
  drule_then assume_tac body_inv_contract >>
  mp_tac body_assign_storage_result_shape_from_cases >>
  (impl_tac >-
    (rpt conj_tac >>
     metis_tac[body_assign_storage_expr_cases, body_assign_storage_base_result_mods])) >>
  disch_then drule >> metis_tac[]
QED

(* A storage-backed compiled result retains a source storage place.
   The actual source evaluation records its finite observed region even
   when the RHS has effects. *)
Theorem body_assign_rhs_storage_live:
  !tops ctx cenv cx env es e H es1 sa sb vv pv func s0 s.
    body_inv tops ctx cenv cx /\
    runtime_consistent env cx es /\ well_typed_expr env e /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    valid_horizon cx es H es1.storage_trace /\
    compile_expr cenv (expr_type e) e sa = (vv,sb) /\
    eval_expr cx e es = (INL pv,es1) /\
    vv_post H ctx func cenv cx e es sa sb s0 es1 pv vv s ==>
    vv_storage_live H cx vv es1 s
Proof
  rpt gen_tac >> strip_tac >>
  `eval_result_typed (env,cx,es1) pv (Type (expr_type e))` by
    (irule (cj 2 typed_expr_success_preserves_type) >>
     fs[runtime_consistent_def] >> metis_tac[]) >>
  `env.type_defs = get_tenv cx` by
    metis_tac[runtime_consistent_get_tenv] >>
  `vv_place_ptr cenv cx es1 s pv vv` by fs[vv_post_def] >>
  irule body_assign_representation_storage_live >>
  qexistsl [`cenv`, `env`, `pv`, `expr_type e`] >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      irule body_assign_observed_storage_read_live >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  irule body_assign_storage_result_shape >> metis_tac[]
QED

(* Rebase only the semantic entry of the saved RHS.  Its allocation
   witnesses still belong to the original compiler interval sa--sm. *)
Theorem body_assign_saved_rhs_rebased[local]:
  body_inv tops ctx cenv cx /\
  runtime_consistent env cx es /\ well_typed_expr env e /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e) /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  eval_expr cx e es = (INL tv,es1) /\ read_result cx tv es1 = (INL v,es1) /\
  ~expr_can_mutate cenv (target_to_expr bt) /\
  cenv.ce_func_mutability = build_func_mutability (cx_tops cx) /\
  (!vis mut nr rr fn args dflts ret body.
    MEM (FunctionDecl vis mut nr rr fn args dflts ret body) (cx_tops cx) ==>
    function_mutability_ok [(NONE,cx_tops cx)] vis mut nr dflts body) /\
  get_module_code cx NONE = SOME (cx_tops cx) /\
  EVERY (\c. FST c = NONE /\ supported_program (cx_tops cx) /\
             IS_SOME (supported_function_decl (cx_tops cx) c Internal))
    (int_calls_target bt) /\
  eval_base_place cx bt es1 = (INL pv,ee) /\
  valid_horizon cx st0 H ee.storage_trace /\ storage_well_formed_on cx es (FST H) /\
  vv_post H ctx func cenv cx e es sa sm s0 es1 tv vv s /\
  stmt_state_rel H ctx func cenv cx ee u /\
  storage_well_formed_on cx ee (FST H) /\
  wb_frame cenv es1 ee sm s u /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!l. vv_operand vv <> Label l) /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_id <= sb.cs_next_id /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm ==>
  read_result cx tv ee = (INL v,ee) /\
  vv_post H ctx func cenv cx e ee sa sm u ee tv vv u /\
  wb_frame cenv es ee sa s0 u /\
  ee = es1 with <|gas_obs := ee.gas_obs; outcomes := ee.outcomes;
    requests := ee.requests; logs := ee.logs; storage_trace := ee.storage_trace|> /\
  vv_storage_live H cx vv ee u
Proof
  strip_tac >>
  `valid_horizon cx st0 H es1.storage_trace` by
    (irule (INST_TYPE [alpha |-> ``:eval_result``] valid_horizon_frame) >>
     qexistsl [`eval_base_place cx bt`, `INL pv`, `ee`] >>
     simp[cj 7 evaluate_storage_trace_frame]) >>
  `valid_horizon cx es H es1.storage_trace` by fs[valid_horizon_def] >>
  drule_all body_assign_rhs_storage_live >> strip_tac >>
  drule_then assume_tac body_inv_qualified_module_absent >>
  drule_all target_walk_source_frame >> strip_tac >>
  drule_all target_walk_scopes >> strip_tac >>
  `ee = es1 with <|gas_obs := ee.gas_obs; outcomes := ee.outcomes;
    requests := ee.requests; logs := ee.logs; storage_trace := ee.storage_trace|>` by
    fs[vyperMachineFrameTheory.machine_frame_def, evaluation_state_component_equality] >>
  `read_result cx tv ee = (INL v,ee)` by
    (once_asm_rewrite_tac [] >> simp[target_saved_read_oracles]) >>
  drule_all (REWRITE_RULE [arithmeticTheory.LESS_EQ_REFL]
    (Q.INST [`sb` |-> `sm`] target_saved_post_transport_frame)) >> strip_tac >>
  `wb_frame cenv es1 es1 sm s u` by
    (gvs[wb_frame_def, locals_kept_def, popped_kept_def] >> metis_tac[]) >>
  qpat_x_assum `vv_post H ctx func cenv cx e es sa sm s0 es1 tv vv s`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  `local_ptrs_rel func cenv es1.scopes s` by
    (drule (cj 1 stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `!w. eval_operand (vv_operand vv) s = SOME w ==>
       eval_operand (vv_operand vv) u = SOME w` by
    (rpt strip_tac >> irule exprBopSimPropsTheory.eval_operand_frame >>
     simp[] >> qexistsl [`sm`, `s`] >> fs[wb_frame_def]) >>
  `vv_storage_live H cx vv es1 u` by
    (irule target_saved_storage_live_frame >> qexists `s` >> simp[] >>
     fs[vv_post_def] >> drule target_saved_operand_exists >> simp[]) >>
  `vv_storage_live H cx vv ee u` by
    (once_asm_rewrite_tac [] >> simp[SRULE [] target_saved_regions_oracles]) >>
  drule_all (SRULE [] (Q.INST [`sb` |-> `sm`] target_saved_value_region_frame)) >>
  disch_then (qspecl_then [`post_value_type cenv e`, `sa`, `tv`] strip_assume_tac) >>
  fs[vv_post_def] >> once_asm_rewrite_tac [] >>
  simp[SRULE [] target_saved_regions_oracles]
QED

Theorem body_assign_immutable_supported[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget t) e) /\
  immutable_root cx t /\ (?nsid. t = TopLevelNameTarget nsid) ==>
  ?nsid ity. t = TopLevelNameTarget nsid /\
    supported_immutable_type tops nsid = SOME ity
Proof
  strip_tac >> gvs[] >>
  `FST nsid = NONE` by
    (PairCases_on `nsid` >> fs[target_root_def] >>
     metis_tac[body_inv_immutable_target_main, target_root_def]) >>
  `~supported_scalar_target tops nsid` by
    metis_tac[augAssignFullTargetRoutesTheory.augassign_scalar_target_route] >>
  fs[Once supported_stmt_def, supported_assignment_def,
     supported_target_def, optionTheory.IS_SOME_EXISTS]
QED

Theorem body_assign_immutable_typed_mods[local]:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  supported_immutable_type tops (NONE,id) = SOME ity /\
  type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) = SOME env' ==>
  cx.in_deploy /\ ~cx_const_name_mods mods (src,id) /\
  assignable_type env.type_defs (expr_type e) /\
  type_widens_to env.type_defs (expr_type e) ity
Proof
  strip_tac >>
  drule_then assume_tac bodyInvModulePropsTheory.module_body_inv_lookup >>
  qpat_x_assum `supported_immutable_type _ _ = _` mp_tac >>
  simp[supported_immutable_type_def] >>
  Cases_on `supported_variable_decl tops (NONE,id)` >> simp[] >>
  rename1 `supported_variable_decl _ _ = SOME decl` >> PairCases_on `decl` >>
  Cases_on `decl1` >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_then strip_assume_tac supported_variable_decl_mem >>
  rename1 `MEM (VariableDecl _ Immutable id ity _) tops` >>
  `~cx_const_name_mods mods (src,id)` by
    (simp[cx_const_name_mods_def] >> strip_tac >> gvs[] >>
     `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
       (drule_then (qspecl_then [`src`,`tops`] mp_tac)
          contract_inv_unqualified_variable_keys >> simp[]) >>
     drule_all_then strip_assume_tac supportedNameRootTheory.distinct_module_consts_env_names_constant >>
     gvs[]) >>
  `FLOOKUP env.bare_globals (src,id) = SOME ity` by
    drule_all_then ACCEPT_TAC immutable_decl_bare_global_mods >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `get_module_code cx src = SOME tops` by
    (drule_then (assume_tac o SPEC_ALL) contract_inv_module_codes >> simp[]) >>
  `bare_global_assignable_complete env.bare_global_assignable cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  qpat_x_assum `type_stmt _ _ _ = SOME _` mp_tac >>
  simp[Once type_stmt_def, atarget_accepts_def] >> strip_tac >>
  Cases_on `type_place_target env (TopLevelNameTarget (src,id))` >> gvs[] >>
  Cases_on `x` >> gvs[type_place_target_TopLevelNameTarget] >>
  Cases_on `cx.in_deploy` >> gvs[bare_global_assignable_complete_def] >>
  qpat_assum `!src ts vis id ty init. _ ==> _` (drule_all_then assume_tac) >> gvs[]
QED

Theorem body_assign_immutable_typed[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  supported_immutable_type tops nsid = SOME ity /\
  type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) = SOME env' ==>
  cx.in_deploy /\ ~cx_const_name cx nsid /\
  assignable_type env.type_defs (expr_type e) /\
  type_widens_to env.type_defs (expr_type e) ity
Proof
  PairCases_on `nsid` >> strip_tac >>
  `nsid0 = NONE` by
    (Cases_on `nsid0` >>
     fs[supported_immutable_type_def, supported_lookup_other_module]) >>
  gvs[] >>
  drule_then assume_tac body_inv_contract >>
  drule_then assume_tac body_inv_module >>
  drule_then (assume_tac o cj 2) body_inv_main_code >>
  `expr_sim_inv_mods [(NONE,tops)] cenv cx env es` by gs[expr_sim_inv_split_def] >>
  drule_all body_assign_immutable_typed_mods >> simp[cx_const_name_split_def]
QED

Theorem body_assign_immutable_value_code[local]:
  stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e)
    sa = (ce,sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ret_ty
    (gas_shadow_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
    shadow_sa = (gas_shadow_env T ce,shadow_sb) /\
  compile_get_target_ptr compile_expr cenv (TopLevelNameTarget nsid) =
    comp_return (Lit (n2w off), SOME LocCode, SOME (ValPT ity)) /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ce = cenv /\
  ?vv sm op su shadow_su.
    compile_expr cenv (expr_type e) e sa = (vv,sm) /\
    unwrap_value cenv vv sm = (op,su) /\
    lower_value compile_expr cenv (expr_type e) e sa = (op,su) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa =
      (op,shadow_su) /\
    gas_shadow_state su shadow_su /\
    compile_assign_value cenv (Lit (n2w off)) LocCode op (is_word_type ity)
      (vv_location vv) ity (lowered_value_type cenv e)
      (type_memory_bytes cenv ity) su = ((),sb) /\
    cs_extends sa sm /\ cs_extends sm su /\ cs_extends su sb /\
    fn_has_code sa su func /\ fn_has_code su sb func /\
    fn_has_code shadow_sa shadow_su shadow_func
Proof
  strip_tac >>
  drule_all immutable_assign_code_parts >> strip_tac >> gvs[] >>
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
  simp[gas_shadow_stmt_def, gas_shadow_assignment_def, gas_shadow_expr_def] >>
  strip_tac >>
  `~(has_length_word (expr_type (gas_shadow_expr e)) /\
      is_empty_value_expr (gas_shadow_expr e))` by simp[gas_shadow_expr_type] >>
  qpat_x_assum `stmt_env _ _ _ (Assign _ e) sa = _` kall_tac >>
  `compile_get_target_ptr compile_expr (gas_shadow_env T ce)
      (TopLevelNameTarget nsid) =
      comp_return (Lit (n2w off), SOME LocCode, SOME (ValPT ity))` by
    (qpat_assum `compile_get_target_ptr compile_expr ce _ = _`
       (fn h => simp[compile_get_target_ptr_def] >>
          metis_tac[SIMP_RULE (srw_ss()) [compile_get_target_ptr_def] h])) >>
  drule_all immutable_assign_code_parts >> strip_tac >>
  gvs[gas_shadow_expr_type] >>
  rename [`lower_value compile_expr ce (expr_type e) e sa = (op,su)`,
          `lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
             (gas_shadow_expr e) shadow_sa = (shadow_op,shadow_su)`] >>
  `shadow_op = op /\ gas_shadow_state su shadow_su` by
    (`FST (lower_value compile_expr ce (expr_type e) e sa) =
       FST (lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
         (gas_shadow_expr e) shadow_sa) /\
       gas_shadow_state (SND (lower_value compile_expr ce (expr_type e) e sa))
         (SND (lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
           (gas_shadow_expr e) shadow_sa))` by
       (irule (REWRITE_RULE [gas_shadow_compiles_def]
          (Q.INST [`sd` |-> `T`] gas_shadow_stmt_lower_value_env)) >> simp[]) >>
     gvs[]) >>
  gvs[] >>
  `fn_has_code sa su func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  `fn_has_code shadow_sa shadow_su shadow_func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  simp[SF SFY_ss]
QED

Theorem body_assign_immutable_target_replay[local]:
  body_inv tops ctx cenv cx /\ cx.in_deploy /\
  supported_immutable_type tops (src,id) = SOME ity /\
  expr_body_pre cenv cx env e es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := xs ++ tail) = (INL v,ee with gas_obs := tail)) ==>
  !tail. expr_sim_inv cenv cx env (ee with gas_obs := tail) /\
    eval_target_place cx (TopLevelNameTarget (src,id))
      (ee with gas_obs := tail) =
    (INL (ImmutablePlace src id []),ee with gas_obs := tail)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> conj_asm1_tac
  >- (`expr_body_pre cenv cx env e (es with gas_obs := xs ++ tail)` by simp[] >>
      qpat_assum `!tail. bind _ _ _ = _` (qspec_then `tail` assume_tac) >>
      drule exprSimSourceTheory.expr_body_pre_eval >>
      disch_then (qspecl_then [`INL v`,`ee with gas_obs := tail`] mp_tac) >>
      (impl_tac >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[])) >> simp[]) >>
  drule_all immutable_target_place_state >> simp[]
QED

(* A source-only target lookup has no machine instructions or observations. *)
Theorem body_assign_immutable_pure_prefix[local]:
  (!tail. a (ee with gas_obs := tail) = (INL p,ee with gas_obs := tail)) /\
  ~z.vs_halted /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (k p) (ee with gas_obs := [],z,G,tn) P R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind a k) (ee with gas_obs := [],z,G,tn) P R
Proof
  simp[gas_outcome_full_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> gvs[gas_bad_storage_at_def,bind_def] >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee'`,`r`,`G'`,`tn'`] >> simp[bind_def]) >>
  disj2_tac >> disj2_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ _ (_,_) (leaf,zf)` >>
  qexistsl_tac [`err`,`ee'`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`zf`] >>
  reverse conj_tac >- metis_tac[] >>
  simp[ignore_bind_def,bind_assoc] >>
  irule gasExemptPurePrefixTheory.gas_exempt_cert_pure_prefix >>
  BETA_TAC >> gvs[ignore_bind_def] >> metis_tac[]
QED

Theorem body_assign_immutable_bind[local]:
  body_inv tops ctx cenv cx /\ cx.in_deploy /\
  supported_immutable_type tops (src,id) = SOME ity /\
  expr_body_pre cenv cx env e es /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn z. ?v. res = INL v /\ N H v ee G tn z)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!marks v ee G tn z.
    (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL v,ee with gas_obs := tail)) /\
    storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\ ~z.vs_halted /\
    (!tail. expr_sim_inv cenv cx env (ee with gas_obs := tail) /\
      eval_target_place cx (TopLevelNameTarget (src,id)) (ee with gas_obs := tail) =
        (INL (ImmutablePlace src id []),ee with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> N H v ee G tn z) ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
      (write_place cx (ImmutablePlace src id []) v) (ee,z,G,tn) P R) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e))
    (es,s0,G0,tn0) P R
Proof
  strip_tac >>
  `eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. bind (eval_target_place cx (TopLevelNameTarget (src,id)))
       (\p. write_place cx p v))` by simp[Once evaluate_def,bind_assoc] >>
  pop_assum SUBST1_TAC >> irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >> BETA_TAC >>
      qexistsl_tac [`mid`,`t`,`v`] >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- simp[storage_trace_frame_bind_all,cj 5 evaluate_storage_trace_frame,
          storage_trace_frame_read_result]
  >- simp[storage_trace_frame_bind_all,cj 8 evaluate_storage_trace_frame,
          storage_trace_frame_write_place] >>
  qexists `\H res ee G tn z. (?v. res = INL v /\ N H v ee G tn z) /\
                            ee.gas_obs = [] /\ ~z.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`z`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  first_assum drule >> strip_tac >> gvs[] >>
  drule_all_then assume_tac body_assign_immutable_target_replay >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `expr_sim_inv cenv cx env ee` by
    (qpat_assum `!tail. expr_sim_inv _ _ _ _ /\ _`
       (qspec_then `[]` (assume_tac o CONJUNCT1)) >> gvs[]) >>
  `gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
     (write_place cx (ImmutablePlace src id []) v) (ee,z,G,tn) P R` by
    (first_x_assum irule >> simp[] >> qexists `marks` >> simp[]) >>
  qpat_assum `ee with gas_obs := [] = ee`
    (fn eq => irule (REWRITE_RULE [eq]
      (Q.INST [`ee` |-> `ee`] body_assign_immutable_pure_prefix))) >>
  simp[] >> qexists `ImmutablePlace src id []` >> BETA_TAC >> metis_tac[]
QED

Theorem assign_outcome_scopes[local]:
  eval_stmt cx (Assign (BaseTarget bt) e) es = (res,ee) ==>
  MAP FDOM ee.scopes = MAP FDOM es.scopes /\
  res <> INR BreakException /\ res <> INR ContinueException
Proof
  pure_once_rewrite_tac[evaluate_def] >>
  simp[bind_def, AllCaseEqs()] >> strip_tac >>
  (conj_tac
  >- (imp_res_tac vyperEvalExprPreservesScopesDomTheory.eval_target_place_preserves_scopes_dom >>
      imp_res_tac vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >>
      imp_res_tac read_result_state >> imp_res_tac vyperScopePreservationTheory.write_place_scopes_dom >>
      gvs[] >> metis_tac[]) >>
  gvs[] >> rpt strip_tac >> gvs[] >>
  FIRST [
    qpat_assum `write_place _ _ _ _ = (INR _,_)`
      (mp_tac o MATCH_MP write_place_no_control),
    qpat_assum `read_result _ _ _ = (INR _,_)`
      (mp_tac o MATCH_MP read_result_no_control),
    qpat_assum `eval_expr _ _ _ = (INR _,_)`
      (mp_tac o MATCH_MP (cj 1 eval_expr_no_control)),
    qpat_assum `eval_target_place _ _ _ = (INR _,_)`
      (mp_tac o MATCH_MP eval_target_place_no_control)] >>
  simp[no_control_exc_def])
QED

Theorem assign_return_buf_sep[local]:
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  local_ptrs_reserved cenv sa /\ cenv' = cenv /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_stmt cx (Assign (BaseTarget bt) e)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv'' sb t /\ alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
           FLOOKUP G x = FLOOKUP G0 x /\
           op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 cenv'' ee t /\
      (!aid off sz i.
         FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
         (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                    off + sz <= b \/ b + sz' <= off) /\
         off <= i /\ i < off + sz /\ i IN tn.t_mem ==>
         i IN tn0.t_mem)) R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_stmt cx (Assign (BaseTarget bt) e)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv'' sb t /\ alloca_history func t /\
      return_buf_sep d cenv'' ee t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
           FLOOKUP G x = FLOOKUP G0 x /\
           op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 cenv'' ee t /\
      (!aid off sz i.
         FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
         (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                    off + sz <= b \/ b + sz' <= off) /\
         off <= i /\ i < off + sz /\ i IN tn.t_mem ==>
         i IN tn0.t_mem)) R
Proof
  strip_tac >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (fn outcome =>
    qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
      qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
        assume_tac (MATCH_MP gas_outcome_full_return_buf_allocas
          (LIST_CONJ [outcome,frame,sep]))))) >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn t. _ /\
       (!bw cap. d = SOME (bw,cap) ==> allocas_from _ t)) R` (irule_at Any) >>
  simp[] >> rpt gen_tac >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  `ee with gas_obs := [] = ee` by
    (qpat_x_assum `ee.gas_obs = []` (fn th => simp[GSYM th])) >>
  `eval_stmt cx (Assign (BaseTarget bt) e) (es with gas_obs := xs) = (res,ee)` by
    (qpat_assum `ee with gas_obs := [] = ee` (fn eq =>
       qpat_assum `!tail. eval_stmt _ _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [listTheory.APPEND_NIL,eq])))) >>
  drule_then strip_assume_tac assign_outcome_scopes >>
  `res = INL ()` by
    (qpat_assum `stmt_lands lctx sb res t`
       (strip_assume_tac o REWRITE_RULE [stmt_lands_def]) >> gvs[]) >>
  `cenv'' = cenv'` by fs[] >>
  `valid_horizon cx st0 H es.storage_trace` by
    (mp_tac (Q.INST [`st` |-> `es with gas_obs := xs`,
       `f` |-> `eval_stmt cx (Assign (BaseTarget bt) e)`,
       `res` |-> `res`, `st'` |-> `ee`, `H` |-> `H`,
       `st0` |-> `st0`, `cx` |-> `cx`]
       (INST_TYPE [alpha |-> oneSyntax.one_ty] valid_horizon_frame)) >>
     simp[evaluate_storage_trace_frame]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by metis_tac[] >>
  qexists_tac `cenv''` >> asm_rewrite_tac[] >>
  irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
  conj_tac >- fs[arithmeticTheory.ADD_COMM] >>
  qexistsl_tac [`H`,`ctx`,`cx`,`es`,`func`,`s0`,`sa`] >> simp[]
QED

(* The literal constructor target runs no machine code. The continuation
   starts at the one endpoint of the compiled RHS and its read. *)
Theorem body_assign_immutable_word_mem_ok[local]:
  compile_imm_store_word imm (Lit (n2w off)) op sa = ((),sb) /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
  off < dimword (:256) /\ off + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> Cases_on `imm` >>
  qpat_x_assum `compile_imm_store_word _ _ _ _ = _` mp_tac >>
  simp[compile_imm_store_word_def,emit_op_def,emit_void_def,
       fresh_id_def,fresh_var_def,emit_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def,DROP_APPEND] >>
  simp[run_inst_seq_mem_ok_def,inst_dload_in_section_def,
       below_frontier_ISTORE,inst_mem_below_frontier_def,mk_inst_def,
       step_inst_base_opcode_eqs,exec_pure2_def,eval_operand_def,
       update_var_def,lookup_var_def,FLOOKUP_UPDATE,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       arithmeticTheory.SUB_PLUS] >>
  simp[codegenRelTheory.fixed_source_write_range_def,
       eval_operand_def,lookup_var_def,FLOOKUP_UPDATE] >>
  rpt CASE_TAC >> gvs[WORD_ADD_0,w2n_n2w]
QED

Theorem body_assign_immutable_normalize_joint[local]:
  stmt_state_rel H0 ctx func cenv cx es s /\
  compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm) /\
  compile_store_memory_typed cenv buf.buf_operand dty (Var xs) sty sm = ((),sb) /\
  ~is_word_type dty /\ ~is_word_type sty /\ ~is_bytestring_type sty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func /\
  type_memory_size dtv < dimword (:256) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  not_fresh_at sa xs /\ lookup_var xs s = SOME sw /\
  expr_val_at cenv cx sty start sa es v (Var xs) s /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t root b Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    (!H. stmt_state_rel H ctx func cenv cx es s ==>
      stmt_state_rel H ctx func cenv cx es t) /\
    (!D d. ghost_inv_at D lo d cenv cx es G tn s ==>
      ghost_inv_at D lo d cenv cx es Gf tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    buf.buf_operand = Var root /\ not_fresh_at sb root /\
    lookup_var root t = SOME (n2w b) /\
    ptr_covers Gf tf root t (type_memory_size dtv) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,type_memory_size dtv) /\
    lo <= b /\ b+type_memory_size dtv < dimword (:256) /\
    b+type_memory_size dtv <= t.vs_alloca_next /\
    (!name a len. local_region cenv es.scopes t name a len ==>
      regions_disjoint b (type_memory_size dtv) a len) /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v b mem) /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
      FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!x. not_fresh_at sa x ==>
      not_fresh_at sb x /\ lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    alloca_frame cenv es sa s cenv es t /\
    ghost_kept_at lo cenv es sa G tn s Gf tf /\
    (!aid off sz i.
      FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!name a len. local_region cenv es.scopes s name a len ==>
        off+sz <= a \/ a+len <= off) /\
      off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all body_full_alloc_buffer_path >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] strip_assume_tac) >>
  `local_ptrs_reserved cenv sm /\ not_fresh_at sm xs /\
   lookup_var xs u = SOME sw` by metis_tac[] >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[nonbytes_evaluated_val_footprint] >>
  `!name a len. local_region cenv es.scopes u name a len <=>
    local_region cenv es.scopes s name a len` by
    (rw[local_region_def] >> metis_tac[local_ptrs_reserved_def]) >>
  `w2n sw+type_memory_size stv <= b \/
   b+type_memory_size dtv <= w2n sw` by suspend "separation" >>
  `!mem. mem_agree_outside tn1.t_mem u.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem` by suspend "source" >>
  `s.vs_alloca_next <= u.vs_alloca_next /\
   b+type_memory_size dtv <= u.vs_alloca_next` by suspend "frontier" >>
  `compile_store_memory_typed cenv (Var root) dty (Var xs) sty sm = ((),sb)` by
    metis_tac[] >>
  `ptr_covers G1 tn1 xs u (type_memory_size stv)` by metis_tac[] >>
  `w2n ((n2w b):bytes32) = b` by simp[] >>
  `w2n ((n2w b):bytes32) + type_memory_size dtv < dimword (:256)` by simp[] >>
  qpat_assum `compile_store_memory_typed cenv (Var root) _ _ _ _ = _`
    (mp_then Any mp_tac compile_store_memory_typed_origin_ptr_path) >>
  disch_then (drule_at (Pat `lookup_var xs _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ sty = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  disch_then (drule_at (Pat `lookup_var root _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ xs _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code sm sb _`)) >>
  disch_then (drule_at (Pat `value_has_type stv _`)) >>
  disch_then (qspecl_then [`lo`,`explicit`,`ctx`,`PG`] mp_tac) >>
  (impl_tac >- (simp[] >> gvs[])) >> strip_tac >>
  rename1 `typed_copy_state_frame sm _ _ u t` >>
  `ci_mono sm sb` by metis_tac[cj 1 ci_mono_typed_memory_family,pairTheory.SND] >>
  `!x. not_fresh_at sm x ==> not_fresh_at sb x` by
    (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  `t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (mp_tac o AP_TERM ``\z. (z.vs_allocas,z.vs_alloca_next)`` o
        CONJUNCT1 o REWRITE_RULE [typed_copy_state_frame_def]) >> simp[]) >>
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x u` by
    fs[typed_copy_state_frame_def] >>
  `lookup_var root t = SOME (n2w b) /\
   FLOOKUP Gf root = FLOOKUP G1 root /\
   op_taint tnf (Var root) = op_taint tn1 (Var root)` by metis_tac[] >>
  `ptr_covers Gf tnf root t (type_memory_size dtv)` by
    metis_tac[ptr_covers_lookup_frame] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (drule typed_copy_state_frame_allocas_below_fmp >> simp[]) >>
  `!name a len. local_region cenv es.scopes t name a len <=>
    local_region cenv es.scopes u name a len` by
    (rw[local_region_def] >> metis_tac[local_ptrs_reserved_def]) >>
  `!x. not_fresh_at sa x ==>
    not_fresh_at sb x /\ lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at sm x ==> _ /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  qpat_assum `w2n ((n2w b):bytes32) = b`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `allocas_from lo t` by (fs[allocas_from_def] >> metis_tac[]) >>
  `!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint b (type_memory_size dtv) a len` by metis_tac[] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,Gf,tnf)` by suspend "join" >>
  `alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next` by suspend "history" >>
  `alloca_frame cenv es sa s cenv es t` by suspend "frame" >>
  `!aid off sz i.
    FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!name a len. local_region cenv es.scopes s name a len ==>
      off+sz <= a \/ a+len <= off) /\ off <= i /\ i < off+sz /\
    i IN tnf.t_mem ==> i IN tn.t_mem` by suspend "taint" >>
  `!H : (bool # 'b word # type_value) list # num list.
    stmt_state_rel H ctx func cenv cx es s ==>
    stmt_state_rel H ctx func cenv cx es t` by suspend "state" >>
  `!D d. ghost_inv_at D lo d cenv cx es G tn s ==>
    ghost_inv_at D lo d cenv cx es Gf tnf t` by suspend "ghost" >>
  `ghost_kept_at lo cenv es sa G tn s Gf tnf` by suspend "kept" >>
  qexistsl_tac [`t`,`root`,`b`,`Gf`,`tnf`] >> simp[] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Resume body_assign_immutable_normalize_joint[separation]:
  qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _`
    (mp_tac o Q.SPEC `stv` o REWRITE_RULE [expr_val_at_def]) >>
  simp[eval_operand_def] >> strip_tac >>
  gvs[loweringStateRelDefsTheory.regions_disjoint_def]
  >- (qpat_assum `!aid a len. _` drule >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)
  >- (qpat_assum `!name a len. local_region _ _ s _ _ _ ==> _` drule >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `type_memory_size dtv = 0` by
    (spose_not_then assume_tac >>
     `0 < type_memory_size dtv` by decide_tac >>
     drule_all widening_source_memory_size_pos >> simp[]) >> simp[]
QED

Resume body_assign_immutable_normalize_joint[source]:
  markerLib.RESUME_TAC >>
  (rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
   (conj_tac >- metis_tac[]) >>
   qexistsl_tac [`s.vs_memory`,`u.vs_memory`,`tn.t_mem`,`tn1.t_mem`,
     `{i | b <= i /\ i < b+type_memory_size dtv}`] >> simp[] >>
   rpt strip_tac >> decide_tac)
QED

Resume body_assign_immutable_normalize_joint[frontier]:
  markerLib.RESUME_TAC >>
  (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
     (qspec_then `cx_dead H0 cx` mp_tac) >>
   disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
   drule gas_origin_path_erase >> strip_tac >>
   `alloca_inv s` by metis_tac[rest_word_state_alloca_inv] >>
   `alloca_inv u` by metis_tac[rest_word_marked_alloca] >>
   `s.vs_alloca_next <= u.vs_alloca_next` by
     (drule gas_marked_path_exec >> strip_tac >>
      drule rest_word_path_frontier >> simp[]) >>
   fs[alloca_inv_def,alloca_next_valid_def] >>
   qpat_assum `!aid base sz. FLOOKUP u.vs_allocas aid = SOME (base,sz) ==> _`
     (qspecl_then [`sa.cs_next_id`,`b`,`type_memory_size dtv`] mp_tac) >> simp[])
QED

Resume body_assign_immutable_normalize_joint[join]:
  markerLib.RESUME_TAC >>
  (gen_tac >>
   qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
     (qspec_then `D` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
   disch_then (qspecl_then [`u`,`G1`,`tn1`,`[]`,`OK t`,`Gf`,`tnf`] mp_tac) >> simp[])
QED

Resume body_assign_immutable_normalize_joint[history]:
  markerLib.RESUME_TAC >>
  (`alloca_inv s` by metis_tac[rest_word_state_alloca_inv] >>
   qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
     (qspec_then `cx_dead H0 cx` mp_tac) >>
   disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
   drule gas_origin_path_erase >> strip_tac >>
   drule_all rest_word_marked_allocation_posts >> simp[])
QED

Resume body_assign_immutable_normalize_joint[frame]:
  markerLib.RESUME_TAC >>
  (`!j k. j+k <= b \/ b+type_memory_size dtv <= j ==>
     mem_bytes_at j k t.vs_memory = mem_bytes_at j k u.vs_memory` by
     fs[typed_copy_state_frame_def,typed_copy_frame_def] >>
   rewrite_tac[alloca_frame_def] >>
   qx_genl_tac [`aid`,`off`,`sz`] >> strip_tac >> conj_tac
   >- (irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
       qx_gen_tac `i` >> strip_tac >>
       `regions_disjoint b (type_memory_size dtv) off sz` by metis_tac[] >>
       `i+1 <= b \/ b+type_memory_size dtv <= i` by
         (fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
       qpat_x_assum `!j k. _` (qspecl_then [`i`,`1`] mp_tac) >> simp[]) >>
   qx_genl_tac [`name`,`off'`,`sz'`] >> strip_tac >>
   `local_region cenv es.scopes s name off' sz'` by metis_tac[] >> metis_tac[])
QED

Resume body_assign_immutable_normalize_joint[taint]:
  markerLib.RESUME_TAC >>
  (qx_genl_tac [`aid`,`off`,`sz`,`i`] >> strip_tac >>
   `regions_disjoint b (type_memory_size dtv) off sz` by metis_tac[] >>
   `~(b <= i /\ i < b+type_memory_size dtv)` by
     (fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
   `i IN tn1.t_mem` by metis_tac[] >> metis_tac[])
QED

Resume body_assign_immutable_normalize_joint[state]:
  markerLib.RESUME_TAC >>
  (rpt strip_tac >>
   `copy_static t = copy_static u` by
     (qpat_assum `typed_copy_state_frame _ _ _ _ _`
        (mp_tac o AP_TERM ``copy_static`` o CONJUNCT1 o
         REWRITE_RULE [typed_copy_state_frame_def]) >> simp[copy_static_def]) >>
   `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size dtv))]
     [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
     metis_tac[buffer_alloc_code] >>
   qpat_assum `typed_copy_state_frame _ _ _ _ _`
     (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def,typed_copy_frame_def]) >>
   irule literal_copy_window_stmt_state_rel >>
   qexistsl_tac [`sa.cs_next_id`,`b`,`type_memory_size dtv`,
     `STRING #"%" (toString sa.cs_next_var)`,`sa`,`sm`,`u`] >>
   rpt conj_tac >> rpt strip_tac >> simp[] >> first_assum irule >> simp[] >>
   qexists_tac `name` >>
   qpat_assum `!name a len. local_region cenv es.scopes u name a len <=> _`
     (qspecl_then [`name`,`a`,`len`] mp_tac) >> simp[])
QED

Resume body_assign_immutable_normalize_joint[ghost]:
  markerLib.RESUME_TAC >>
  (rpt strip_tac >>
   `ghost_inv_at D lo d cenv cx es G1 tn1 u` by metis_tac[] >>
   `t.vs_call_ctx = u.vs_call_ctx /\ t.vs_immutables = u.vs_immutables /\
    t.vs_accounts = u.vs_accounts /\ t.vs_transient = u.vs_transient` by
     (qpat_assum `typed_copy_state_frame _ _ _ _ _`
        (mp_tac o AP_TERM ``\z. (z.vs_call_ctx,z.vs_immutables,
          z.vs_accounts,z.vs_transient)`` o CONJUNCT1 o
         REWRITE_RULE [typed_copy_state_frame_def]) >> simp[]) >>
   `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==>
     not_fresh_at sm x` by metis_tac[] >>
   `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==>
     not_fresh_at sm x` by metis_tac[] >>
   irule body_full_memory_ghost_frame >> simp[] >>
   qexistsl_tac [`G1`,`u`,`sm`,`tn1`,
     `{i | b <= i /\ i < b+type_memory_size dtv}`] >> simp[] >> rpt conj_tac
   >- (qx_genl_tac [`name`,`entry`,`p`,`cap`,`w`] >> strip_tac >>
       `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
       `lookup_var p s = SOME w` by metis_tac[] >>
       drule_all literal_ptr_local_footprint_exterior >> simp[])
   >- (qx_gen_tac `i` >> strip_tac >>
       qpat_assum `typed_copy_state_frame _ _ _ _ _`
         (strip_assume_tac o REWRITE_RULE
           [typed_copy_state_frame_def,typed_copy_frame_def]) >>
       qpat_assum `!a len. a+len <= b \/ b+type_memory_size dtv <= a ==> _`
         (qspecl_then [`i`,`1`] mp_tac) >>
       (impl_tac >- (simp[])) >> simp[])
   >- (qx_gen_tac `i` >> strip_tac >>
       `~(b <= i /\ i < b+type_memory_size dtv)` by simp[] >>
       metis_tac[])
   >- (qpat_assum `typed_copy_state_frame _ _ _ _ _`
         (strip_assume_tac o REWRITE_RULE
           [typed_copy_state_frame_def,typed_copy_frame_def]) >>
       qpat_assum `!a len. a+len <= b \/ b+type_memory_size dtv <= a ==> _`
         (qspecl_then [`0`,`lo`] mp_tac) >>
       (impl_tac >- simp[]) >> simp[]) >>
   fs[typed_copy_state_frame_def,venom_state_component_equality,allocas_from_def] >>
   metis_tac[])
QED

Resume body_assign_immutable_normalize_joint[kept]:
  markerLib.RESUME_TAC >>
  (rewrite_tac[ghost_kept_at_def] >> rpt conj_tac
   >- metis_tac[]
   >- first_assum MATCH_ACCEPT_TAC >>
   qx_genl_tac [`name`,`a`,`len`,`i`] >> strip_tac >>
   `regions_disjoint b (type_memory_size dtv) a len` by metis_tac[] >>
   `~(b <= i /\ i < b+type_memory_size dtv)` by
     (fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >> metis_tac[])
QED

Finalise body_assign_immutable_normalize_joint[local]

Theorem body_assign_snapshot_memory_unwrap_joint[local]:
  expr_body_pre ce cx env e es /\
  (do pv <- eval_expr cx e; read_result cx pv od) es = (INL v,ee) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  ~is_word_type (lowered_value_type ce e) /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  unwrap_value ce (vv_with_type (lowered_value_type ce e) vv) sn = (op,sk) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sn /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sn sk func /\ fn_inst_ids_distinct func /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty /\
  (!w. read_result cx tv ee = (INL w,ee) ==> value_has_type rty w) /\
  read_result cx tv ee = (INL v,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func ce cx e es sa sm s0 ee tv vv s /\
     ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val, ee) /\
     !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
       eval_operand (vv_operand vv) s = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  return_buf_frame d ce sn s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?u Gu tnu stv w.
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    value_has_type stv v /\ val_wf stv v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
    eval_operand op u = SOME w /\
    (!mem. mem_agree_outside tnu.t_mem u.vs_memory mem ==>
       val_in_memory stv v (w2n w) mem) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (OK u,Gu,tnu) /\
       expr_post H ctx func ce cx e es sa sk s0 ee v op u /\
       ghost_inv_at (DF H) lo d ce cx ee Gu tnu u) /\
    expr_store_bound cx (post_value_type ce e) v op u /\
    ptr_val_ok cx (post_value_type ce e) v op Gu tnu u /\
    ptr_buf_ok ce e op Gu u /\
    (type_memory_size stv = 0 \/ w2n w + type_memory_size stv <= u.vs_alloca_next) /\
    u.vs_current_bb = sk.cs_current_bb /\
    u.vs_inst_idx = LENGTH sk.cs_current_insts /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    return_buf_frame d ce sk u /\
    ghost_kept_at lo ce es sa Gi ti s0 Gu tnu /\
    (!x. not_fresh_at sn x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
      op_taint tnu (Var x) = op_taint tn (Var x)) /\
    wb_frame ce ee ee sn s u /\
    ghost_kept_at lo ce ee sn G tn s Gu tnu /\
    alloca_frame ce ee sn s ce ee u /\
    (!aid b n. FLOOKUP s.vs_allocas aid = SOME (b,n) /\ aid < sn.cs_next_id /\
      (!id base len. local_region ce ee.scopes s id base len ==>
         b+n <= base \/ base+len <= b) ==>
      FLOOKUP u.vs_allocas aid = SOME (b,n) /\
      mem_bytes_at b n u.vs_memory = mem_bytes_at b n s.vs_memory /\
      (!i. b <= i /\ i < b+n /\ i IN tnu.t_mem ==> i IN tn.t_mem))
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  `vv_holds ce cx (post_value_type ce e) tv vv ee s` by
    metis_tac[vv_post_def] >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[immutable_rhs_post_physical_classify, is_bytestring_word_type] >>
  `(vv_location vv <> NONE /\ vv_location vv <> SOME LocMemory ==>
     lowered_value_type ce e = post_value_type ce e)` by
    metis_tac[snapshot_changed_type_location] >>
  `unwrap_value ce (vv_with_type (lowered_value_type ce e) vv) =
     unwrap_value ce vv` by
    (irule snapshot_retag_unwrap >>
     goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
     metis_tac[immutable_rhs_post_physical_classify]) >>
  `unwrap_value ce vv sn = (op,sk)` by metis_tac[] >>
  `!rt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
     ~is_word_type (post_value_type ce e) ==>
     type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
     type_memory_size rt < 2**64` by
    metis_tac[body_post_type_allocation_bound] >>
  drule_all unwrap_value_origin_ptr >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  gnvs[] >>
  drule_all immutable_rhs_physical_typed >> strip_tac >>
  `expr_post (storage_trace_horizon ee.storage_trace) ctx func ce cx e
     es sa sk s0 ee v op z /\
   ghost_inv_at (DF (storage_trace_horizon ee.storage_trace)) lo d ce cx ee G' tn' z` by
    metis_tac[] >>
  drule_all structlit_child_physical_robust >> strip_tac >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee s` by
    metis_tac[vv_post_def] >>
  `alloca_frame ce ee sn s ce ee z` by
    (irule (INST_TYPE [alpha |-> ``:256``] log_wb_alloca_frame) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `sn.cs_next_var <= sk.cs_next_var` by
    (qspec_then `ce` (qspec_then `vv` (qspec_then `sn` mp_tac)) ci_mono_unwrap_value >>
     simp[ci_mono_def]) >>
  `return_buf_frame d ce sk z` by
    (irule return_buf_frame_frame >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  qexistsl [`z`,`G'`,`tn'`,`stv`,`w`] >> simp[] >>
  qpat_x_assum `wb_frame _ _ _ sn s z` mp_tac >>
  qpat_x_assum `ghost_kept_at _ _ ee sn G tn s G' tn'` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[wb_frame_def, ghost_kept_at_def] >>
  ntac 2 strip_tac >> rpt gen_tac >> strip_tac >>
  conj_tac >-
    (first_x_assum irule >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `aid` >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!aid off sz i. _` (qspecl_then [`aid`,`b`,`n`,`i`] mp_tac) >>
  impl_tac >- (simp[] >> first_assum ACCEPT_TAC) >> simp[]
QED

Theorem body_assign_empty_dead_value[local]:
  has_length_word ty /\ evaluate_type tenv ty = SOME tv /\
  mem_word_at off sec' = 0w /\ mem_dead_bytes sec off tv i ==>
  mem_dead_bytes sec' off tv i
Proof
  strip_tac >>
  `is_bytestring_type ty \/ ?et n. ty = ArrayT et (Dynamic n)` by
    (Cases_on `ty` >> gvs[has_length_word_def] >>
     rename1 `ArrayT _ bd` >> Cases_on `bd` >> gvs[has_length_word_def])
  >- (drule_all bytestring_type_value >> strip_tac >>
      gvs[mem_dead_bytes_def] >> decide_tac) >>
  gvs[evaluate_type_def, AllCaseEqs(), mem_dead_bytes_def] >>
  qexists_tac `k` >> simp[] >>
  Cases_on `k < w2n (mem_word_at off sec)` >> gvs[] >>
  drule (cj 1 mem_dead_bytes_range) >>
  simp[LEFT_ADD_DISTRIB] >> decide_tac
QED

Theorem body_assign_empty_immutable_dead[local]:
  struct_args_unique tops /\
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  evaluate_type (type_env tops) ty = SOME tv /\ has_length_word ty /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
  LENGTH sec = imm_len tops /\ off + type_memory_size tv <= LENGTH sec /\
  LENGTH sec' = LENGTH sec /\ mem_word_at off sec' = 0w /\
  (!i. ~(off <= i /\ i < off+32) ==>
     mem_bytes_at i 1 sec' = mem_bytes_at i 1 sec) ==>
  !i. imm_section_dead tops sec i ==> imm_section_dead tops sec' i
Proof
  strip_tac >> gen_tac >> rewrite_tac[imm_section_dead_def] >> strip_tac >>
  rename1 `evaluate_type (type_env tops) ty' = SOME tv'` >>
  qexistsl_tac [`pre'`,`vis'`,`name'`,`ty'`,`slot'`,`post'`,`tv'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  Cases_on `pre = pre'`
  >- (`ty = ty'` by
        (qpat_x_assum `tops = pre ++ _` mp_tac >>
         qpat_x_assum `tops = pre' ++ _` (fn th => rewrite_tac[th]) >>
         simp[]) >>
      `tv = tv'` by metis_tac[optionTheory.SOME_11] >>
      irule body_assign_empty_dead_value >> metis_tac[]) >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
     type_memory_size tv` by metis_tac[imm_frame_size] >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty' =
     type_memory_size tv'` by metis_tac[imm_frame_size] >>
  `32 <= type_memory_size tv` by metis_tac[memory_length_word_layout] >>
  `pre ++ VariableDecl vis Immutable name ty slot :: post =
   pre' ++ VariableDecl vis' Immutable name' ty' slot' :: post'` by metis_tac[] >>
  drule imm_frame_occurrence_separation >>
  disch_then (qspec_then `get_struct_fields (make_struct_fields_map tops)` mp_tac) >>
  strip_tac >>
  `mem_dead_bytes sec'
     (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre') tv' =
   mem_dead_bytes sec
     (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre') tv'` by
    (irule mem_dead_bytes_frame >> reverse conj_tac
     >- first_assum ACCEPT_TAC >>
     (rpt strip_tac >>
         `mem_bytes_at j 1 sec' = mem_bytes_at j 1 sec` by
           (qpat_x_assum `!i. ~(off <= i /\ i < off+32) ==> _` irule >>
            qpat_x_assum `tops = pre ++ _` kall_tac >>
            qpat_x_assum `tops = pre' ++ _` kall_tac >>
            fs[] >> decide_tac) >>
         `j < LENGTH sec'` by metis_tac[] >>
         metis_tac[mem_bytes_at_from_EL, listTheory.CONS_11]) >>
     simp[]) >>
  metis_tac[]
QED

Theorem body_assign_empty_immutable_ghost[local]:
  ghost_inv_at D lo d ce cx es G tn s /\
  dead_lo_ok H D lo ce cx /\
  body_inv tops ctx ce cx /\ struct_args_unique tops /\
  expr_sim_inv ce cx env es /\
  stmt_state_rel H ctx func ce cx es s /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x) /\
  ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ty /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ty /\
  has_length_word ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  write_place cx (ImmutablePlace ce.ce_module id []) (default_value tv) es =
    (INL (),ee) /\
  q.vs_memory = (mstore off 0w s).vs_memory /\
  (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==>
     lookup_var x q = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
     op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
  tf.t_imm = tn.t_imm /\ tf.t_mem SUBSET tn.t_mem /\
  (!i. off <= i /\ i < off+32 ==> i NOTIN tf.t_mem) ==>
  ghost_inv_at D lo d ce cx ee Gf tf q
Proof
  strip_tac >>
  `ce.ce_module = NONE /\ get_module_code cx NONE = SOME tops /\
   ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
   ce.ce_struct_fields = make_struct_fields_map tops` by
    (drule_then strip_assume_tac body_inv_module_locations >>
     drule_then strip_assume_tac body_inv_main_code >>
     drule_then (assume_tac o SIMP_RULE (srw_ss()) [make_struct_fields_map_mods_singleton] o
       MATCH_MP contract_inv_struct_fields) body_inv_contract >>
     drule_then (assume_tac o MATCH_MP contract_inv_singleton_source_modules)
       body_inv_contract >> simp[]) >>
  `cx_tops cx = tops` by metis_tac[cx_tops_module] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  drule body_inv_immutable_section_layout >>
  simp[immutable_section_layout_def] >>
  `FLOOKUP ce.ce_module_vars (NONE,id) = SOME (ImmutableLoc off)` by metis_tac[] >>
  disch_then (drule_then strip_assume_tac) >>
  `bare_globals_complete env.bare_globals cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  `FLOOKUP env.bare_globals (NONE,id) = SOME ty'` by
    (qpat_x_assum `bare_globals_complete _ _` mp_tac >>
     rewrite_tac[bare_globals_complete_def] >>
     disch_then (qspec_then `NONE` mp_tac) >>
     disch_then (qspec_then `tops` mp_tac) >> simp[] >>
     disch_then (qspec_then `vis` mp_tac) >>
     disch_then (qspec_then `Immutable` mp_tac) >>
     disch_then (qspec_then `id` mp_tac) >>
     disch_then (qspec_then `ty'` mp_tac) >>
     disch_then (qspec_then `slot` mp_tac) >> simp[]) >>
  `ty' = ty` by metis_tac[optionTheory.SOME_11] >>
  `get_tenv cx = type_env tops` by
    simp[get_tenv_def, type_env_all_modules_def, GSYM type_env_def] >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
     fs[expr_sim_inv_def] >> metis_tac[]) >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
   type_memory_size tv` by metis_tac[type_mem_bytes_type_memory_bytes] >>
  `lo = imm_len tops` by fs[dead_lo_ok_def] >>
  `off + type_memory_size tv <= lo` by
    (qpat_x_assum `lo = _` SUBST1_TAC >> simp[imm_len_def] >>
     qpat_assum `tops = _` (fn th => once_rewrite_tac[th]) >>
     simp[compute_immutables_len_append, compute_immutables_len_def] >> gvs[]) >>
  `32 <= type_memory_size tv` by
    (qspec_then `get_tenv cx` mp_tac memory_length_word_layout >>
     disch_then (qspecl_then [`ty`,`tv`,`off`,`(mstore off 0w s).vs_memory`] mp_tac) >>
     simp[mstore_mem_word_at_same]) >>
  `!mem a n. a+n <= lo ==>
     mem_bytes_at a n (mem_bytes_at 0 lo mem) = mem_bytes_at a n mem` by
    ((rpt strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
     rename1 `j < n` >> `a+j < lo` by decide_tac >> simp[EL_mem_bytes_at] >> (gvs[EL_mem_bytes_at, LIST_EQ]))) >>
  `mem_word_at off (mem_bytes_at 0 lo q.vs_memory) = 0w` by
    (`off+32 <= lo` by decide_tac >>
     `mem_bytes_at off 32 (mem_bytes_at 0 lo q.vs_memory) =
      word_to_bytes (0w:bytes32) T` by simp[mem_bytes_at_mstore_same] >>
     pure_rewrite_tac[mem_word_at_def, GSYM mem_bytes_at_def] >>
     pure_asm_rewrite_tac[] >> simp[word_of_bytes_word_to_bytes]) >>
  `!i. ~(off <= i /\ i < off+32) ==>
     mem_bytes_at i 1 q.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >> simp[] >> irule mstore_mem_bytes_at_disjoint >> (gvs[])) >>
  `!i. ~(off <= i /\ i < off+32) ==>
     mem_bytes_at i 1 (mem_bytes_at 0 lo q.vs_memory) =
     mem_bytes_at i 1 (mem_bytes_at 0 lo s.vs_memory)` by
    (rpt strip_tac >> Cases_on `i < lo` >- (simp[] >> (gvs[])) >>
     `DROP i (mem_bytes_at 0 lo q.vs_memory) = [] /\
      DROP i (mem_bytes_at 0 lo s.vs_memory) = []` by
       (simp[DROP_EQ_NIL, LENGTH_mem_bytes_at] >> gvs[]) >>
     pure_once_rewrite_tac[mem_bytes_at_def] >>
     qpat_x_assum `DROP i (mem_bytes_at 0 lo q.vs_memory) = []` (fn th => rewrite_tac[th]) >>
     qpat_x_assum `DROP i (mem_bytes_at 0 lo s.vs_memory) = []` (fn th => rewrite_tac[th])) >>
  `!i. imm_section_dead tops (mem_bytes_at 0 lo s.vs_memory) i ==>
     imm_section_dead tops (mem_bytes_at 0 lo q.vs_memory) i` by
    ((rpt strip_tac >> irule body_assign_empty_immutable_dead >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`id`,`off`,`post`,`pre`,`mem_bytes_at 0 lo s.vs_memory`,
                  `slot`,`tv`,`ty`,`vis`] >> gvs[] >> (gvs[body_assign_empty_immutable_dead]))) >>
  `local_ptrs_rel func ce es.scopes s` by
    metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `ee.scopes = es.scopes` by metis_tac[write_immutable_place_scopes] >>
  `!name b len. local_region ce es.scopes s name b len ==>
     mem_bytes_at b len q.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >> Cases_on `len = 0` >- simp[mem_bytes_at_def] >>
     `0 < len` by decide_tac >>
     `lo <= b` by (drule_all body_full_local_region_lower_bound >> simp[]) >>
     `off+32 <= b` by decide_tac >>
     simp[] >> irule mstore_mem_bytes_at_disjoint >> gvs[]) >>
  `!x sz. not_fresh_at sa x /\ ptr_covers G tn x s sz ==>
     ptr_covers Gf tf x q sz` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  `q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
   q.vs_call_ctx = s.vs_call_ctx /\ q.vs_allocas = s.vs_allocas /\
   q.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `q with <|vs_vars := _; vs_memory := _;
       vs_immutables := _; vs_prev_bb := _; vs_current_bb := _;
       vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  fs[ghost_inv_at_def] >> rpt conj_tac
  >- suspend "locals"
  >- suspend "return"
  >- suspend "storage"
  >- suspend "prefix"
  >- suspend "base"
  >> gvs[allocas_from_def] >> metis_tac[]
QED

Resume body_assign_empty_immutable_ghost[locals]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `ptr_covers G tn p s sz` by metis_tac[] >>
  `?w0. lookup_var p s = SOME w0` by fs[ptr_covers_def] >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= sz` by
    (drule val_footprint_le >> decide_tac) >>
  `local_region ce es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory entry.type entry.value (w2n w) m` by metis_tac[] >>
  `mem_bytes_at (w2n w) sz q.vs_memory =
   mem_bytes_at (w2n w) sz s.vs_memory` by metis_tac[] >>
  `!i. w2n w <= i /\ i < w2n w+sz /\ i IN tf.t_mem ==>
       i IN tn.t_mem` by (fs[SUBSET_DEF] >> metis_tac[]) >>
  irule robust_val_in_memory_window_transport >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`tn.t_mem`,`tf.t_mem`,`sz`,`s.vs_memory`,`q.vs_memory`] >>
  gvs[] >> metis_tac[]
QED

Resume body_assign_empty_immutable_ghost[return]:
  Cases_on `d` >> fs[return_buf_ptr_def] >>
  rename1 `return_buf_ptr (SOME bc)` >> PairCases_on `bc` >>
  fs[return_buf_ptr_def] >> metis_tac[]
QED

Resume body_assign_empty_immutable_ghost[storage]:
  fs[stor_taint_ok_at_def, dead_lo_ok_def]
QED

Resume body_assign_empty_immutable_ghost[prefix]:
  gvs[SUBSET_DEF] >> metis_tac[]
QED

Resume body_assign_empty_immutable_ghost[base]:
  metis_tac[local_ptrs_reserved_def]
QED

Finalise body_assign_empty_immutable_ghost[local]

Theorem body_assign_immutable_word_dead_frame[local]:
  struct_args_unique tops /\
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  evaluate_type (type_env tops) ty = SOME tv /\ is_word_type ty /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
  LENGTH sec2 = LENGTH sec1 /\
  (!j. j < LENGTH sec1 /\ ~(off <= j /\ j < off + 32) ==> EL j sec2 = EL j sec1) ==>
  imm_section_dead tops sec2 = imm_section_dead tops sec1
Proof
  strip_tac >>
  `!sec off j. ~mem_dead_bytes sec off tv j` by
    (Cases_on `ty` >> gvs[is_word_type_def,evaluate_type_def,AllCaseEqs(),mem_dead_bytes_def]) >>
  simp[FUN_EQ_THM] >> gen_tac >>
  rewrite_tac[imm_section_dead_def] >>
  `!pre' vis' name' ty' slot' post' tv'.
     tops = pre' ++ VariableDecl vis' Immutable name' ty' slot' :: post' /\
     evaluate_type (type_env tops) ty' = SOME tv' ==>
     mem_dead_bytes sec2
       (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre') tv' =
     mem_dead_bytes sec1
       (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre') tv'`
    by (rpt strip_tac >>
        `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty = 32`
          by metis_tac[imm_frame_size,word_tv_memory_size] >>
        `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty' =
          type_memory_size tv'` by metis_tac[imm_frame_size] >>
        `pre ++ VariableDecl vis Immutable name ty slot :: post =
         pre' ++ VariableDecl vis' Immutable name' ty' slot' :: post'`
          by metis_tac[] >>
        drule imm_frame_occurrence_separation >>
        disch_then (qspec_then `get_struct_fields (make_struct_fields_map tops)` mp_tac) >>
        strip_tac
        >- (fs[] >> gvs[FUN_EQ_THM]) >>
        irule mem_dead_bytes_frame >> reverse conj_tac >- simp[] >>
        ntac 2 (qpat_x_assum `tops = _` kall_tac) >>
        qpat_x_assum `_ ++ _ = _ ++ _` kall_tac >>
        rpt strip_tac >>
        simp[]) >>
  metis_tac[]
QED

Theorem body_assign_memory_place_lower_bound[local]:
  body_inv tops ctx cenv cx /\
  expr_sim_inv cenv cx env ee /\
  stmt_state_rel H ctx func cenv cx ee s /\
  dead_lo_ok H D lo cenv cx /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  0 < type_memory_size dtv /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) ==>
  lo <= w2n dw
Proof
  strip_tac >>
  drule_all memory_place_live_region >> strip_tac >>
  `0 < len` by decide_tac >>
  `lo <= b` by (irule body_full_local_region_lower_bound >> metis_tac[]) >>
  decide_tac
QED


Theorem body_assign_immutable_word_layout[local]:
  body_inv tops ctx ce cx /\ struct_args_unique tops /\
  expr_sim_inv ce cx env ee /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ity /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME itv /\ is_word_type ity /\
  (!H. dead_lo_ok H (DF H) lo ce cx) ==>
  ce.ce_module = NONE /\ cx_tops cx = tops /\
  get_tenv cx = type_env tops /\ type_memory_size itv = 32 /\
  lo = imm_len tops /\ ~cx_const_name cx (ce.ce_module,id) /\
  off + 32 <= lo /\ off < dimword (:256) /\
  ?pre post vis slot.
    tops = pre ++ VariableDecl vis Immutable id ity slot :: post /\
    off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre
Proof
  strip_tac >>
  `ce.ce_module = NONE /\ cx_tops cx = tops /\
   ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
   ce.ce_module_var_type = build_var_type_map tops /\
   ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    (drule_then strip_assume_tac body_inv_main_code >>
     qpat_assum `body_inv tops ctx _ cx` (assume_tac o assign_main_keys) >>
     drule_then (assume_tac o MATCH_MP contract_inv_singleton_source_modules)
       body_inv_contract >>
     drule_then (strip_assume_tac o REWRITE_RULE [cenv_module_pins_def])
       intcall_args_body_inv_pins >> simp[]) >>
  `get_tenv cx = type_env tops` by
    simp[get_tenv_def,type_env_all_modules_def,type_env_def] >>
  `?pre post vis ty slot.
    tops = pre ++ VariableDecl vis Immutable id ty slot :: post /\
    off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre` by
    (drule body_inv_immutable_section_layout >>
     simp[immutable_section_layout_def] >> metis_tac[]) >>
  `ty = ity` by
    (`MEM (VariableDecl vis Immutable id ty slot) tops` by simp[] >>
     drule_all build_maps_variable >> strip_tac >>
     qpat_x_assum `build_var_type_map tops _ = SOME ty` mp_tac >>
     simp[] >> gvs[build_maps_variable]) >>
  qpat_x_assum `ty = ity` SUBST_ALL_TAC >>
  `type_memory_size itv = 32` by metis_tac[word_tv_memory_size] >>
  `lo = imm_len tops` by metis_tac[dead_lo_ok_def] >>
  `off + 32 <= lo` by
    (`type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ity = 32` by
       metis_tac[imm_frame_size] >>
     mp_tac (Q.INST [`off` |-> `0`, `prefix` |-> `pre`, `suffix` |-> `post`,
       `sft` |-> `get_struct_fields (make_struct_fields_map tops)`,
       `ty` |-> `ity`, `vis` |-> `vis`, `name` |-> `id`, `slot` |-> `slot`]
       immutable_declaration_interval_bound) >>
     simp[GSYM imm_len_def]) >>
  `~cx_const_name cx (NONE,id)` by
    (`MEM (VariableDecl vis Immutable id ity slot) tops` by simp[] >>
     drule_all supportedNameRootTheory.supported_variable_decl_distinct_mem >> strip_tac >>
     spose_not_then assume_tac >> drule_all body_inv_const_name_decl >>
     strip_tac >> gvs[]) >>
  `~cx_const_name cx (ce.ce_module,id)` by metis_tac[] >>
  drule_all immutable_assign_target_layout >> strip_tac >>
  qpat_x_assum `!cfn. _` (qspec_then `ARB` strip_assume_tac) >>
  `off + 32 < dimword (:256)` by
    (qpat_x_assum `FLOOKUP _ _ = SOME (ImmutableLoc off')` mp_tac >>
     asm_rewrite_tac[] >> strip_tac >> gvs[] >> metis_tac[]) >>
  `off < dimword (:256)` by decide_tac >>
  simp[] >> metis_tac[]
QED

Theorem body_assign_immutable_bytes_selected_dead[local]:
  ((?cap. dtv = BaseTV (BytesT (Dynamic cap))) \/
   (?cap. dtv = BaseTV (StringT cap))) /\
  len < dimword(:256) /\
  mem_word_at off sec2 = n2w len /\
  32 + len <= 32*n /\
  (!i. a <= i /\ i < a + 32 + len ==> i NOTIN M1) /\
  (!k. k < 32*n /\ off+k IN M2 ==> a+k IN M1) ==>
  !j. off <= j /\ j < off + type_memory_size dtv /\ j IN M2 ==>
      mem_dead_bytes sec2 off dtv j
Proof
  rpt strip_tac >>
  `off + 32 + len <= j` by
    (CCONTR_TAC >>
     `j - off < 32*n /\ off + (j-off) = j` by decide_tac >>
     `a + (j-off) IN M1` by
       (qpat_x_assum `!k. _ ==> a+k IN M1`
          (qspec_then `j-off` mp_tac) >> simp[]) >>
     qpat_x_assum `!i. _ ==> i NOTIN M1`
       (qspec_then `a+(j-off)` mp_tac) >>
     simp[] >> decide_tac) >>
  gvs[immSectionDeadTheory.mem_dead_bytes_def, w2n_n2w]
QED

Theorem body_assign_immutable_bytes_restore[local]:
  P H0 /\
  (!H. P H ==> stmt_state_rel H ctx func ce cx es s /\
    ghost_inv_at (DF H) lo d ce cx es G tn s /\
    dead_lo_ok H (DF H) lo ce cx) /\
  expr_sim_inv ce cx env es /\ local_ptrs_reserved ce sa /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME dty /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  tops = cx_tops cx /\ get_tenv cx = type_env tops /\ struct_args_unique tops /\
  tops = pre ++ VariableDecl vis Immutable id dty slot :: post /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  type_widens_to (get_tenv cx) sty dty /\ value_has_type stv v /\
  well_formed_type_value dtv /\ immutable_value_admissible dtv v /\
  off + type_memory_size dtv <= lo /\ lo < dimword(:256) /\
  write_place cx (ImmutablePlace ce.ce_module id []) v es = (INL (),es') /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory stv v a mem) /\
  lo <= a /\ a + 32*n < dimword(:256) /\ n = 1 + word_size len /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  (t with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
    vs_prev_bb := s.vs_prev_bb; vs_inst_idx := s.vs_inst_idx|>) =
    immutable_transfers T T (n2w a) (n2w off) n 0 s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x. ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  (!k. k < 32*n /\ off+k IN tnf.t_mem ==> a+k IN tn.t_mem) /\
  (!i. ~(off <= i /\ i < off+32*n) /\ i IN tnf.t_mem ==> i IN tn.t_mem) /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
  return_buf_frame d ce sa s /\ sa.cs_next_var <= sb.cs_next_var /\
  alloca_history func s /\ fn_inst_ids_distinct func /\
  gas_origin_ptr_path (DF H0,lo,explicit,ctx,func,PG)
    (s,G,tn) marks (OK t,Gf,tnf) /\
  ghost_kept_at lo c0 es0 sa0 G0 tn0 s0 G tn /\
  sa0.cs_next_var <= sa.cs_next_var /\
  (!name b cap. local_region c0 es0.scopes s0 name b cap ==> lo <= b) /\
  alloca_frame c0 es0 sa0 s0 ce es s /\ allocas_from lo s0 /\
  (!aid b sz i. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa0.cs_next_id /\
    (!name q cap. local_region c0 es0.scopes s0 name q cap ==>
      b+sz <= q \/ q+cap <= b) /\ b <= i /\ i < b+sz /\ i IN tn.t_mem ==>
    i IN tn0.t_mem) ==>
  (!H. P H ==> stmt_state_rel H ctx func ce cx es' t /\
    ghost_inv_at (DF H) lo d ce cx es' Gf tnf t) /\
  return_buf_frame d ce sb t /\ alloca_history func t /\
  ghost_kept_at lo c0 es0 sa0 G0 tn0 s0 Gf tnf /\
  alloca_frame c0 es0 sa0 s0 ce es' t /\
  (!aid b sz i. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa0.cs_next_id /\
    (!name q cap. local_region c0 es0.scopes s0 name q cap ==>
      b+sz <= q \/ q+cap <= b) /\ b <= i /\ i < b+sz /\ i IN tnf.t_mem ==>
    i IN tn0.t_mem)
Proof
  strip_tac >> (
  `stmt_state_rel H0 ctx func ce cx es s /\
   ghost_inv_at (DF H0) lo d ce cx es G tn s` by metis_tac[] >>
  `local_ptrs_rel func ce es.scopes s /\ alloca_inv s` by
    metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `es'.scopes = es.scopes` by metis_tac[vyperPlaceFramesTheory.write_immutable_place_scopes] >>
  `val_in_memory stv v a s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `mload a s = n2w len /\
   (!i. a <= i /\ i < a + 32 + len ==> i NOTIN tn.t_mem)` by
    (drule_all body_assign_immutable_bytes_source_live_clean >> strip_tac >>
     gvs[]) >>
  `32 + len <= 32*n /\ 32*n <= type_memory_size dtv` by
    suspend "extent" >>
  `off+32*n < dimword(:256) /\ off+32*n <= lo` by decide_tac >>
  `t.vs_memory = (immutable_transfers T T (n2w a) (n2w off) n 0 s).vs_memory /\
   (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
     vs_immutables := s.vs_immutables; vs_current_bb := s.vs_current_bb;
     vs_prev_bb := s.vs_prev_bb; vs_inst_idx := s.vs_inst_idx|>) = s` by
    suspend "physical" >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient` by
    (qpat_x_assum `(_ with <|vs_vars := _; vs_memory := _; vs_immutables := _;
       vs_current_bb := _; vs_prev_bb := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `(!p k. p+k <= off \/ off+32*n <= p ==>
     mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory)` by
    (rpt strip_tac >>
     qpat_assum `t.vs_memory = _` (fn th => rewrite_tac[th]) >>
     irule immutable_transfers_memory_frame >> asm_rewrite_tac[]) >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    metis_tac[immutable_transfers_memory_nondecreasing] >>
  `val_in_memory dtv v off t.vs_memory /\
   immutable_value_bytes_rel dtv v (mem_bytes_at off (type_memory_size dtv) t.vs_memory)` by
    suspend "representation" >>
  `!i. i < lo /\ i IN tnf.t_mem ==>
     imm_section_dead tops (mem_bytes_at 0 lo t.vs_memory) i` by
    suspend "section" >>
  conj_tac >- suspend "family" >>
  conj_tac >- (irule return_buf_frame_frame >> qexistsl [`ce`,`s`,`sa`] >> simp[] >> metis_tac[]) >>
  conj_tac >- metis_tac[body_full_path_alloca_history] >>
  `!i. lo <= i /\ i IN tnf.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >> qpat_assum `!i. ~(_ /\ _) /\ i IN tnf.t_mem ==> _` irule >>
     conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
  conj_asm1_tac >- suspend "kept" >>
  conj_tac >- suspend "frame" >>
  qpat_assum `ghost_kept_at lo c0 es0 sa0 G0 tn0 s0 Gf tnf`
    (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [ghost_kept_at_def]))
QED

Resume body_assign_immutable_bytes_restore[extent]:
  markerLib.RESUME_TAC >> (
  drule_all immutable_assign_bytestring_extent >> strip_tac >>
  drule_all placeStoreStorageTheory.place_store_bytestring_representation >> strip_tac >>
  gvs[loweringPostsTheory.val_footprint_def, value_has_type_def])
QED
Resume body_assign_immutable_bytes_restore[physical]:
  markerLib.RESUME_TAC >> (
  `((immutable_transfers T T (n2w a) (n2w off) n 0 s) with
      <|vs_memory := s.vs_memory; vs_immutables := s.vs_immutables|>) = s` by
    simp[immutable_transfers_record_restore] >>
  qpat_x_assum `(t with <|vs_vars := _; vs_current_bb := _;
    vs_prev_bb := _; vs_inst_idx := _|>) = _` mp_tac >>
  fs[venom_state_component_equality])
QED
Resume body_assign_immutable_bytes_restore[representation]:
  markerLib.RESUME_TAC >> (
  `val_footprint stv v = 32+len /\ value_has_type dtv v` by
    (drule_all placeStoreStorageTheory.place_store_bytestring_representation >>
     strip_tac >> gvs[loweringPostsTheory.val_footprint_def, value_has_type_def]) >>
  `mem_bytes_at off (32+len) t.vs_memory = mem_bytes_at a (32+len) s.vs_memory` by
    (qpat_assum `t.vs_memory = _` (fn th => rewrite_tac[th]) >>
     irule immutable_transfers_memory_prefix >>
     rpt conj_tac >> decide_tac) >>
  irule immutableDeployMeaningfulTransferTheory.immutable_direct_meaningful_transfer >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`dty`,`s.vs_memory`,`32+len`,`a`,`stv`,`sty`,`get_tenv cx`] >>
  gvs[])
QED
Resume body_assign_immutable_bytes_restore[section]:
  markerLib.RESUME_TAC >> (
  `(?cap. dtv = BaseTV (BytesT (Dynamic cap))) \/
   (?cap. dtv = BaseTV (StringT cap))` by metis_tac[bytestring_type_value] >> (
  `mem_word_at off t.vs_memory = n2w len` by
    (gvs[val_in_memory_def] >> metis_tac[]) >>
  `mem_word_at off (mem_bytes_at 0 lo t.vs_memory) = n2w len` by
    (`off + 32 <= lo` by decide_tac >>
     `mem_bytes_at off 32 (mem_bytes_at 0 lo t.vs_memory) =
       mem_bytes_at off 32 t.vs_memory` by
       (mp_tac (Q.SPECL [`0`,`off`,`32`,`lo`,`t.vs_memory`] mem_bytes_at_window) >>
        gvs[mem_bytes_at_bounded]) >>
     metis_tac[mem_word_at_bytes]) >>
  `!j. off <= j /\ j < off + type_memory_size dtv /\ j IN tnf.t_mem ==>
    mem_dead_bytes (mem_bytes_at 0 lo t.vs_memory) off dtv j` by
    (`len < dimword(:256)` by decide_tac >>
     rpt strip_tac >> irule body_assign_immutable_bytes_selected_dead >>
     metis_tac[]) >>
  rpt strip_tac >> irule immutable_section_replace >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexists_tac `tn.t_mem` >> qexists_tac `tnf.t_mem` >> qexists_tac `lo` >>
  qpat_assum `tops = _ ++ _` (irule_at Any) >>
  qexistsl [`dtv`,`mem_bytes_at 0 lo s.vs_memory`,`off`] >>
  simp[NoAsms] >> rpt conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at j 1 t.vs_memory = mem_bytes_at j 1 s.vs_memory` by
        (first_x_assum irule >> decide_tac) >>
      qpat_x_assum `mem_bytes_at j 1 _ = _`
        (mp_tac o Q.AP_TERM `EL 0`) >>
      simp[EL_mem_bytes_at])
  >- (rpt strip_tac >> first_x_assum irule >>
      (conj_tac >- decide_tac) >> first_assum ACCEPT_TAC)
  >- metis_tac[ghost_inv_at_def]
  >> asm_rewrite_tac[] >> gvs[] >>
  qpat_x_assum `_ = cx_tops cx` (mp_tac o GSYM) >>
  simp_tac std_ss [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  disch_then SUBST1_TAC >> asm_rewrite_tac[]))
QED
Resume body_assign_immutable_bytes_restore[family]:
  markerLib.RESUME_TAC >> (
  qx_gen_tac `H` >> strip_tac >>
  `stmt_state_rel H ctx func ce cx es s /\
   ghost_inv_at (DF H) lo d ce cx es G tn s /\
   dead_lo_ok H (DF H) lo ce cx` by metis_tac[] >>
  `!p k. regions_disjoint p k off (type_memory_size dtv) ==>
     mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory` by
    (rpt strip_tac >> qpat_x_assum `!p k. _ \/ _ ==> _` irule >>
     qpat_x_assum `regions_disjoint _ _ _ _` mp_tac >>
     rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `stmt_state_rel H ctx func ce cx es' t` by
    ((irule immutable_store_stmt_state_rel >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`env`,`es`,`id`,`off`,`s`,`sa`,`ce.ce_module`,`dtv`,`dty`,`v`] >>
     (conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[])) >>
     asm_rewrite_tac[venom_state_fupdcanon] >> (gvs[venom_state_fupdcanon, immutable_store_stmt_state_rel]))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `ce.ce_module_var_type (ce.ce_module,id) = SOME dty` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def,exprSimHypsDefsTheory.bare_globals_layout_def]) >>
  `!name b sz. local_region ce es.scopes s name b sz ==>
      regions_disjoint off (type_memory_size dtv) b sz` by
    (rpt strip_tac >>
     irule (cj 3 immutableDeployAssignFactsTheory.immutable_assign_declared_region) >>
     metis_tac[]) >>
  `!im. (DF H).d_imm im = UNIV` by fs[dead_lo_ok_def] >>
  qpat_x_assum `ghost_inv_at (DF H) lo d ce cx es G tn s`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
  rewrite_tac[ghost_inv_at_def] >>
  conj_tac >- suspend "local_ghost" >>
  conj_tac >-
    (Cases_on `d` >> simp[return_buf_ptr_def] >>
     PairCases_on `x` >>
     qpat_x_assum `return_buf_ptr _ _ _ _ _` mp_tac >>
     simp[return_buf_ptr_def,ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- fs[stor_taint_ok_at_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[allocas_from_def] >>
  metis_tac[])
QED
Resume body_assign_immutable_bytes_restore[local_ghost]:
  markerLib.RESUME_TAC >> (
  qx_gen_tac `name` >> qx_gen_tac `entry` >> qx_gen_tac `p` >> qx_gen_tac `sz` >>
  qpat_assum `es'.scopes = es.scopes` (fn th => rewrite_tac[th]) >> strip_tac >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  qpat_assum `!x. not_fresh_at sa x ==> _` drule >> strip_tac >>
  conj_tac >-
    (`ptr_covers G tn p s sz` by metis_tac[] >> fs[ptr_covers_def]) >>
  qx_gen_tac `w` >> qx_gen_tac `mem` >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  `local_region ce es.scopes s name (w2n w) sz` by metis_tac[local_region_def] >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (qpat_assum `local_ptrs_rel func ce es.scopes s`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [local_ptrs_rel_def]) >>
     disch_then (qspecl_then [`name`,`entry`,`p`,`sz`] mp_tac) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= sz` by
    metis_tac[val_footprint_le,arithmeticTheory.LESS_EQ_TRANS] >>
  `regions_disjoint off (type_memory_size dtv) (w2n w) sz` by metis_tac[] >>
  `regions_disjoint (w2n w) sz off (type_memory_size dtv)` by
    (qpat_assum `regions_disjoint off _ _ _` mp_tac >>
     rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at (w2n w) sz t.vs_memory = mem_bytes_at (w2n w) sz s.vs_memory` by metis_tac[] >>
  `!i. w2n w <= i /\ i < w2n w+sz /\ i IN tnf.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >> qpat_assum `!i. ~(_ /\ _) /\ i IN tnf.t_mem ==> _` irule >>
     conj_tac >-
       (qpat_assum `regions_disjoint off _ _ _` mp_tac >>
        rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     first_assum ACCEPT_TAC) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory entry.type entry.value (w2n w) m` by metis_tac[] >>
  drule_all robust_val_in_memory_window_transport >> simp[])
QED
Resume body_assign_immutable_bytes_restore[kept]:
  markerLib.RESUME_TAC >> (
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  rewrite_tac[ghost_kept_at_def] >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac >-
    (map_every qx_gen_tac [`aid`,`b0`,`sz0`,`i`] >> strip_tac >>
     `lo <= b0` by (qpat_assum `allocas_from lo s0` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
                   disch_then irule >> metis_tac[]) >>
     `i IN tn.t_mem` by (qpat_assum `!i. lo <= i /\ i IN tnf.t_mem ==> _` irule >>
                         conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `!aid b sz i. _ ==> i IN tn0.t_mem`
       (qspecl_then [`aid`,`b0`,`sz0`,`i`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  map_every qx_gen_tac [`name`,`b0`,`sz0`,`i`] >> strip_tac >>
  `lo <= b0` by metis_tac[] >>
  `i IN tn.t_mem` by (qpat_assum `!i. lo <= i /\ i IN tnf.t_mem ==> _` irule >>
                      conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!n b sz i. local_region _ _ _ _ _ _ /\ _ ==> i IN tn0.t_mem`
    (qspecl_then [`name`,`b0`,`sz0`,`i`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[])
QED
Resume body_assign_immutable_bytes_restore[frame]:
  markerLib.RESUME_TAC >> (
  qpat_x_assum `alloca_frame _ _ _ _ _ _ _`
    (assume_tac o REWRITE_RULE [alloca_frame_def]) >>
  rewrite_tac[alloca_frame_def] >>
  map_every qx_gen_tac [`aid`,`b0`,`sz0`] >> strip_tac >>
  `lo <= b0` by metis_tac[allocas_from_def] >>
  qpat_assum `!aid off sz. _ ==> _ /\ _`
    (qspecl_then [`aid`,`b0`,`sz0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  conj_tac >-
    (`mem_bytes_at b0 sz0 t.vs_memory = mem_bytes_at b0 sz0 s.vs_memory` by
       (qpat_assum `!p k. _ \/ _ ==> _` irule >> decide_tac) >> metis_tac[]) >>
  map_every qx_gen_tac [`name`,`b1`,`sz1`] >> strip_tac >>
  `local_region ce es.scopes s name b1 sz1` by
     metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame] >>
  metis_tac[])
QED
Finalise body_assign_immutable_bytes_restore[local]

Theorem body_assign_snapshot_memory_alloc_joint[local]:
  !ce cx env e es pv ee v sa vv0 sm buf sn func ctx s DF lo st0 G tn d
   s0 Gi ti explicit PG.
  expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL pv,ee) /\ read_result cx pv ee = (INL v,ee) /\
  ~is_word_type (lowered_value_type ce e) /\
  compile_expr ce (expr_type e) e sa = (vv0,sm) /\
  compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) sm = (buf,sn) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x. vv_operand vv0 = Var x ==> not_fresh_at sm x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func ce cx e es sa sm s0 ee pv vv0 s /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee pv vv0 s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_vv_ok cx (post_value_type ce e) pv vv0 ee G tn s /\
  (!t op0. vv0 = StackValue t op0 /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e op0 G s) /\
  (!t p. vv0 = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv0 = SOME LocCode ==>
    ?val. read_result cx pv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv0) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  return_buf_frame d ce sm s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?a Ga tna xd b.
    buf.buf_operand = Var xd /\ not_fresh_at sn xd /\
    sm.cs_next_id < sn.cs_next_id /\ local_ptrs_reserved ce sn /\ ci_mono sm sn /\
    ~a.vs_halted /\ a.vs_current_bb = sn.cs_current_bb /\
    a.vs_inst_idx = LENGTH sn.cs_current_insts /\
    FLOOKUP a.vs_allocas sm.cs_next_id = SOME (b,type_memory_bytes ce (lowered_value_type ce e)) /\
    lookup_var xd a = SOME (n2w b) /\
    ptr_covers Ga tna xd a (type_memory_bytes ce (lowered_value_type ce e)) /\
    lo <= b /\ b + type_memory_bytes ce (lowered_value_type ce e) < dimword (:256) /\
    b + type_memory_bytes ce (lowered_value_type ce e) <= a.vs_alloca_next /\
    (!name off len. local_region ce ee.scopes a name off len ==>
      regions_disjoint b (type_memory_bytes ce (lowered_value_type ce e)) off len) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,Ga,tna) /\
      vv_post H ctx func ce cx e es sa sm s0 ee pv vv0 a /\
      ghost_inv_at (DF H) lo d ce cx ee Ga tna a) /\
    vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee pv vv0 a /\
    ptr_vv_ok cx (post_value_type ce e) pv vv0 ee Ga tna a /\
    (!t op0. vv0 = StackValue t op0 /\ ~is_word_type (post_value_type ce e) ==>
      ptr_buf_ok ce e op0 Ga a) /\
    (!t p. vv0 = LocatedValue t p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand Ga a) /\
    (ce.ce_is_ctor /\ vv_location vv0 = SOME LocCode ==>
      ?val. read_result cx pv ee = (INL val,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
          eval_operand (vv_operand vv0) a = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tna.t_mem a.vs_memory mem ==>
            val_in_memory rt val (w2n w) mem)) /\
    ghost_kept_at lo ce es sa Gi ti s0 Ga tna /\
    return_buf_frame d ce sn a /\ alloca_history func a /\
    s.vs_alloca_next <= a.vs_alloca_next /\ s0.vs_alloca_next <= a.vs_alloca_next /\
    a.vs_memory = s.vs_memory /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP a.vs_allocas aid = SOME entry) /\
    (!aid off len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
      regions_disjoint b (type_memory_bytes ce (lowered_value_type ce e)) off len) /\
    (!x. not_fresh_at sm x ==> lookup_var x a = lookup_var x s /\
      FLOOKUP Ga x = FLOOKUP G x /\ op_taint tna (Var x) = op_taint tn (Var x)) /\
    ghost_kept_at lo ce ee sm G tn s Ga tna /\
    alloca_frame ce ee sm s ce ee a /\
    (!aid off len i. FLOOKUP s.vs_allocas aid = SOME (off,len) /\
      aid < sm.cs_next_id /\ off <= i /\ i < off+len /\ i IN tna.t_mem ==> i IN tn.t_mem)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by
    fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H0` (fn th => first_assum (strip_assume_tac o MATCH_MP th))) >>
  `stmt_state_rel H0 ctx func ce cx ee s` by fs[vv_post_def] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `(do pv <- eval_expr cx e; read_result cx pv od) es = (INL v,ee)` by
    simp[vyperStateTheory.bind_def] >>
  drule_all immutable_rhs_physical_typed >> strip_tac >>
  `type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e)` by
    (irule immutable_rhs_physical_widens >> qexistsl_tac [`env`,`es`] >>
     simp[vyperTypeSystemTheory.type_widens_to_def]) >>
  `~is_word_type (expr_type e)` by metis_tac[type_widens_to_word] >>
  `type_memory_bytes ce (expr_type e) < 2 ** 64` by
    (drule_then strip_assume_tac expr_body_pre_static_facts >>
     drule_then mp_tac alloc_limits_expr_type_alloc_ok >>
     simp[allocLimitsTheory.type_alloc_ok_def]) >>
  `expr_sim_inv ce cx env es` by
    drule_then (ACCEPT_TAC o cj 1) expr_body_pre_static_facts >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >> strip_tac >>
  `type_memory_bytes ce (lowered_value_type ce e) < dimword (:256)` by
    metis_tac[widening_memory_layout_bound] >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``] alloc_buffer_origin_ptr_path_exact) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choose_then `xd` (qx_choose_then `w` (qx_choose_then `a`
      (qx_choose_then `Ga` (qx_choose_then `tna` strip_assume_tac)))))) >>
  `ci_mono sm sn` by
    (mp_tac (Q.SPEC `type_memory_bytes ce (lowered_value_type ce e)`
       exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >>
     disch_then (qspec_then `sm` mp_tac) >> simp[]) >>
  `sm.cs_next_id < sn.cs_next_id` by
    (drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[]) >>
  `sm.cs_next_var <= sn.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved ce sn` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `~a.vs_halted /\ a.vs_memory = s.vs_memory /\ a.vs_labels = s.vs_labels /\
   a.vs_accounts = s.vs_accounts /\ a.vs_transient = s.vs_transient /\
   a.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `a with <|vs_vars := _; vs_allocas := _;
                           vs_alloca_next := _; vs_inst_idx := _|> = s`
       mp_tac >> simp[venom_state_component_equality] >> strip_tac >> simp[]) >>
  `lo <= w2n w` by
    (qpat_assum `allocas_from lo a` mp_tac >>
     rewrite_tac[ptrDisciplineTheory.allocas_from_def] >>
     disch_then (qspecl_then [`sm.cs_next_id`,`w2n w`,
       `type_memory_bytes ce (lowered_value_type ce e)`] mp_tac) >> simp[]) >>
  `eval_operand (vv_operand vv0) a = eval_operand (vv_operand vv0) s` by
    (Cases_on `vv_operand vv0` >> fs[eval_operand_def]) >>
  `(!x. vv_operand vv0 = Var x ==> FLOOKUP Ga x = FLOOKUP G x) /\
   op_taint tna (vv_operand vv0) = op_taint tn (vv_operand vv0) /\
   op_prov Ga (vv_operand vv0) = op_prov G (vv_operand vv0)` by
    (Cases_on `vv_operand vv0` >> fs[ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def]) >>
  `!x. not_fresh_at sa x ==> lookup_var x a = lookup_var x s /\
        FLOOKUP Ga x = FLOOKUP G x /\ op_taint tna (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `not_fresh_at sm x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     fs[]) >>
  `local_ptrs_rel func ce ee.scopes s /\ alloca_inv s` by
    (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `!aid off len. FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
        off + len <= s.vs_alloca_next` by
    (rpt strip_tac >> drule_all allocaSiteResourceTheory.alloca_site_registered_below >> simp[]) >>
  `!i. i < s.vs_alloca_next /\ i IN tna.t_mem ==> i IN tn.t_mem` by
    (simp[] >> rpt strip_tac >> fs[]) >>
  `!name off len. local_region ce ee.scopes s name off len ==>
        off + len <= s.vs_alloca_next` by
    (rpt strip_tac >> drule_all bodyMemoryDefsTheory.body_local_region_frontier >> simp[]) >>
  qexistsl_tac [`a`,`Ga`,`tna`,`xd`,`w2n w`] >> simp[n2w_w2n] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac >- suspend "horizon" >>
  conj_tac >- (irule exprSimMemDefsTheory.vv_store_bound_frame_mem_src >>
               qexists_tac `s` >> simp[]) >>
  conj_tac >- suspend "pointer" >>
  conj_tac >- suspend "stack_buffer" >>
  conj_tac >- suspend "located_buffer" >>
  conj_tac >- suspend "constructor" >>
  conj_tac >- suspend "entry_kept" >>
  conj_tac
  >- (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
      qexistsl_tac [`ce`,`s`,`sm`] >> simp[]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac >- suspend "rhs_kept" >>
  conj_tac
  >- (qpat_assum `stmt_state_rel H0 _ _ _ _ _ s`
        (mp_then Any irule alloca_frame_of_mem_frame) >> simp[]) >>
  rpt strip_tac >>
  `off + len <= s.vs_alloca_next` by metis_tac[] >> decide_tac
QED

Resume body_assign_snapshot_memory_alloc_joint[horizon]:
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H` (fn th => first_assum (strip_assume_tac o MATCH_MP th))) >>
  conj_tac
  >- (`stmt_state_rel H ctx func ce cx ee s` by fs[vv_post_def] >>
      `stmt_state_rel H ctx func ce cx ee a` by
        (qpat_assum `!H'. stmt_state_rel H' ctx func ce cx ee s ==> _` irule >> simp[]) >>
      irule materialize_vv_post_alloc_storage_frame >> simp[] >>
      qexistsl_tac [`s`,`sm`] >> simp[contract_storage_def, contract_transient_def]) >>
  qpat_assum `ghost_inv_at (DF H) lo d ce cx ee G tn s`
    (mp_then Any irule alloc_buffer_ghost_inv_at_locals) >>
  goal_assum (drule_at Any) >> simp[]
  >> (metis_tac[])
QED

Resume body_assign_snapshot_memory_alloc_joint[entry_kept]:
  irule alloc_buffer_ghost_kept_at >>
  qexistsl_tac [`G`,`w2n w + type_memory_bytes ce (lowered_value_type ce e)`,`s`,`tn`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `local_region ce ee.scopes s name b sz` by
        (irule local_region_frame_fwd >>
         qexistsl_tac [`s0`,`sa`,`es.scopes`] >> fs[vv_post_def]) >>
      metis_tac[]) >>
  fs[vv_post_def] >> rpt strip_tac >>
  `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by simp[] >>
  qpat_assum `!aid off len. FLOOKUP s.vs_allocas aid = SOME (off,len) ==> _`
    (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[] >> decide_tac
QED

Resume body_assign_snapshot_memory_alloc_joint[rhs_kept]:
  irule alloc_buffer_ghost_kept_at >>
  qexistsl_tac [`G`,`w2n w + type_memory_bytes ce (lowered_value_type ce e)`,`s`,`tn`] >>
  simp[ghost_kept_at_def]
  >> (metis_tac[])
QED

Resume body_assign_snapshot_memory_alloc_joint[pointer]:
  `vv_at ce cx (post_value_type ce e) sa sm ee pv vv0 s` by fs[vv_post_def] >>
  `~is_word_type (post_value_type ce e) /\
   (?ptv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv /\ val_wf ptv v)` by
    (`post_value_type ce e = expr_type e \/
      post_value_type ce e = lowered_value_type ce e` by
       (Cases_on `e` >> simp[post_value_type_def] >>
        rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
        simp[post_value_type_def, vyperASTTheory.expr_type_def] >> IF_CASES_TAC >> simp[]) >>
     fs[] >> simp[valueEncodingTypingTheory.value_has_type_val_wf]) >>
  `( !t p. vv0 = LocatedValue t p ==> p.ptr_location = LocMemory) /\
   ptr_mem_ok cx (post_value_type ce e) v (vv_operand vv0) G tn s ==>
   ptr_mem_ok cx (post_value_type ce e) v (vv_operand vv0) Ga tna a` by
    (strip_tac >> irule bop_ptr_mem_ok_frame >>
     qexistsl_tac [`G`,`s`,`tn`,`ptv`] >> simp[] >> rpt strip_tac >>
     drule_all vv_at_memory_footprint >> strip_tac >>
     `i < s.vs_alloca_next` by simp[] >> fs[]) >>
  Cases_on `vv0` >> fs[contextTheory.vv_operand_def]
  >- (gvs[ptr_vv_ok_def, ptr_val_ok_def] >> simp[]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (gvs[ptr_vv_ok_def] >> simp[]) >>
  irule ptr_vv_ok_nonmemory_frame >> simp[] >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]
QED

Resume body_assign_snapshot_memory_alloc_joint[stack_buffer]:
  rpt strip_tac >> fs[contextTheory.vv_operand_def] >>
  irule ptr_buf_ok_frame >> qexistsl_tac [`G`,`s`] >> simp[]
QED

Resume body_assign_snapshot_memory_alloc_joint[located_buffer]:
  rpt strip_tac >> fs[contextTheory.vv_operand_def] >>
  irule ptr_buf_ok_frame >> qexistsl_tac [`G`,`s`] >> simp[]
QED

Resume body_assign_snapshot_memory_alloc_joint[constructor]:
  disch_then (fn guard =>
    qpat_x_assum `ce.ce_is_ctor /\ vv_location vv0 = SOME LocCode ==> _`
      (strip_assume_tac o C MATCH_MP guard)) >>
  gvs[] >> qx_gen_tac `rt` >> qx_gen_tac `src` >> strip_tac >>
  `type_memory_size rt + w2n src <= lo /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory rt v (w2n src) mem)` by
    (qpat_assum `!rt src. evaluate_type _ _ = SOME rt /\ _ ==> _`
       (qspecl_then [`rt`,`src`] mp_tac) >> simp[]) >>
  simp[] >> qx_gen_tac `mem` >> strip_tac >>
  `val_wf rt v` by
    (`post_value_type ce e = expr_type e \/
      post_value_type ce e = lowered_value_type ce e` by
       (Cases_on `e` >> simp[post_value_type_def] >>
        rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
        simp[post_value_type_def, vyperASTTheory.expr_type_def] >> IF_CASES_TAC >> simp[]) >>
     fs[] >> simp[valueEncodingTypingTheory.value_has_type_val_wf]) >>
  irule robust_val_in_memory_footprint_frame >> simp[] >>
  qexistsl_tac [`s.vs_memory`,`s.vs_memory`,`tn.t_mem`,`tna.t_mem`] >> simp[] >>
  `val_footprint rt v <= type_memory_size rt` by simp[exprSimPropsTheory.val_footprint_le] >>
  rpt strip_tac >> `i < s.vs_alloca_next` by decide_tac >> fs[]
QED

Finalise body_assign_snapshot_memory_alloc_joint[local]

Theorem immutable_word_store_endpoint:
  compile_assign_value ce (Lit (n2w off)) LocCode op T loc ity sty bytes su = ((),sb) /\
  fn_has_code su sb func /\ ~block_is_terminated sb /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts /\
  (!x. op = Var x ==> not_fresh_at su x) /\
  eval_operand op s = SOME (typed_val_to_w256 itv v) /\
  (!region. ce.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w) /\
  stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
  ghost_inv_at D lo d ce cx ee G tn s /\ dead_lo_ok H D lo ce cx /\
  return_buf_frame d ce su s /\ alloca_history func s /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x) /\
  expr_sim_inv ce cx env ee /\ local_ptrs_reserved ce su /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ity /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME itv /\ is_word_type ity /\ value_has_type itv v /\
  write_place cx (ImmutablePlace ce.ce_module id []) v ee = (INL (),fin) /\
  off < dimword (:256) /\ off + 32 <= lo /\
  sb.cs_current_bb = su.cs_current_bb /\
  sb.cs_current_insts = su.cs_current_insts ++ emitted_insts su sb /\
  run_inst_seq (emitted_insts su sb) s = OK u /\
  tf.t_mem = tn.t_mem DIFF {j | off <= j /\ j < off + 32} /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
  (!p. not_fresh_at su p ==> FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tf (Var p) = op_taint tn (Var p)) /\
  allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  u.vs_memory = (mstore off (typed_val_to_w256 itv v) s).vs_memory /\
  (!i. i < lo /\ i IN tf.t_mem ==>
    imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo u.vs_memory) i) /\
  (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_immutables := s.vs_immutables|>) = s ==>
  fin.storage_trace = ee.storage_trace /\
  stmt_post H ctx func cx lctx ce ce su sb ee s (INL ()) fin (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ghost_inv_at D lo d ce cx fin Gf tf (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  return_buf_frame d ce sb (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\ alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  (u with vs_inst_idx := LENGTH sb.cs_current_insts).vs_alloca_next = s.vs_alloca_next /\ (u with vs_inst_idx := LENGTH sb.cs_current_insts).vs_allocas = s.vs_allocas /\
  (!x. not_fresh_at su x ==> lookup_var x (u with vs_inst_idx := LENGTH sb.cs_current_insts) = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  alloca_frame ce ee su s ce fin (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\ ghost_kept_at lo ce ee su G tn s Gf tf
Proof
  strip_tac >>
  qpat_x_assum `sb.cs_current_insts = _ ++ _` (mk_asm "word_code") >> simp[] >>
  `type_memory_size itv = 32` by metis_tac[word_tv_memory_size] >>
  `fin.scopes = ee.scopes /\ fin.storage_trace = ee.storage_trace` by
    (drule write_immutable_place_frame >> strip_tac >> simp[]) >>
  `!i. i IN tf.t_mem ==> i IN tn.t_mem` by
    (qpat_assum `tf.t_mem = _` (fn th => simp[th,pred_setTheory.IN_DIFF])) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_call_ctx = s.vs_call_ctx /\
   (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
     vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
     vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s` by
    (qpat_assum `u with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = s`
       mp_tac >> simp[venom_state_component_equality]) >>
  `(!x. not_fresh_at su x ==> lookup_var x u = lookup_var x s) /\
   val_in_memory itv v off u.vs_memory /\
   immutable_value_bytes_rel itv v (mem_bytes_at off (type_memory_size itv) u.vs_memory)` by
    suspend "word" >>
  `!a k. regions_disjoint a k off 32 ==>
      mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory` by
    (rpt strip_tac >> simp[] >> irule mstore_mem_bytes_at_disjoint >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> (gvs[])) >>
  `!i. ~(off <= i /\ i < off + 32) ==>
    mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >> first_x_assum irule >>
     gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `stmt_post H ctx func cx lctx ce ce su sb ee s (INL ()) fin
    (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by suspend "post" >>
  `alloca_frame ce ee su s ce fin (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qpat_assum `stmt_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [stmtSimDefsTheory.stmt_post_def]) >>
     simp[] >> strip_tac >> gvs[]) >>
  simp[lookup_var_def,ptrDisciplineTheory.allocas_below_fmp_def] >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "return" >>
  conj_tac >- suspend "history" >>
  simp[ghost_kept_at_def, GSYM lookup_var_def]
QED

Resume immutable_word_store_endpoint[word]:
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all immutable_assign_word_store >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> gvs[]
QED

Resume immutable_word_store_endpoint[post]:
  `LENGTH s.vs_memory <= LENGTH u.vs_memory` by
    simp[venomMemPropsTheory.LENGTH_mstore_eq] >>
  `immutable_value_admissible itv v` by metis_tac[evaluated_immutable_admissible] >>
  irule immutable_assign_suffix_stmt_post >>
  simp[IgnAsm `u.vs_memory = _`] >>
  qexistsl_tac [`env`,`id`,`itv`,`ity`,`off`,`v`] >>
  simp[IgnAsm `u.vs_memory = _`] >>
  metis_tac[]
QED

Resume immutable_word_store_endpoint[ghost]:
  rewrite_tac[ghostPcTransportPtrTheory.ghost_inv_at_inst_idx] >>
  qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
  `!x. not_fresh_at su x ==> lookup_var x u = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)`
    by simp[] >>
  `!x k. ce.ce_return_buf = SOME (PtrVar (Var x) k) ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  `return_buf_ptr d ce Gf tf u` by
    (Cases_on `d` >- simp[return_buf_ptr_def] >>
     rename1 `return_buf_ptr (SOME p) _ _ _ _` >> PairCases_on `p` >>
     qpat_x_assum `return_buf_ptr _ _ _ _ _` mp_tac >>
     simp[return_buf_ptr_def,ptr_covers_def] >> metis_tac[]) >>
  `stor_taint_ok_at D tf u` by
    (`!im. D.d_imm im = UNIV` by
       (qpat_assum `dead_lo_ok _ _ _ _ _`
          (strip_assume_tac o REWRITE_RULE [dead_lo_ok_def]) >> metis_tac[]) >>
     qpat_assum `stor_taint_ok_at _ _ _`
       (strip_assume_tac o REWRITE_RULE [stor_taint_ok_at_def]) >>
     simp[stor_taint_ok_at_def,pred_setTheory.SUBSET_UNIV]) >>
  `local_ptrs_rel func ce ee.scopes s` by
    metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `!n b k. local_region ce ee.scopes s n b k ==> regions_disjoint off 32 b k` by
    (drule_all_then strip_assume_tac immutable_assign_declared_region >>
     metis_tac[]) >>
  simp[ghost_inv_at_def,ptrDisciplineTheory.allocas_from_def,
       IgnAsm `u.vs_memory = _`, IgnAsm `off = _`, IgnAsm `tops = _`] >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at su p` by metis_tac[local_ptrs_reserved_def] >>
     `lookup_var p u = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)` by simp[] >>
     qpat_assum `fin.scopes = ee.scopes` (fn eq =>
       qpat_assum `lookup_scopes name fin.scopes = SOME entry`
         (assume_tac o REWRITE_RULE [eq])) >>
     qpat_assum `!name entry p sz. _ ==> ptr_covers _ _ _ _ _ /\ _`
       (drule_all_then strip_assume_tac) >>
     conj_tac >-
       (qpat_assum `ptr_covers _ _ _ _ _`
          (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
        simp[ptr_covers_def] >> metis_tac[]) >>
     rpt gen_tac >> strip_tac >>
     `lookup_var p s = SOME w` by metis_tac[] >>
     `local_region ce ee.scopes s name (w2n w) sz` by
       (rewrite_tac[local_region_def] >> qexistsl_tac [`entry`,`p`,`w`] >> simp[]) >>
     `regions_disjoint off 32 (w2n w) sz` by metis_tac[] >>
     qpat_assum `local_ptrs_rel _ _ _ _`
       (drule_all_then strip_assume_tac o CONJUNCT1 o REWRITE_RULE [local_ptrs_rel_def]) >>
     `val_footprint entry.type entry.value <= type_memory_size entry.type` by
       simp[val_footprint_le] >>
     `!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
          ~(off <= i /\ i < off + 32)` by
       (rpt gen_tac >> strip_tac >>
        qpat_assum `regions_disjoint off 32 _ _` mp_tac >>
        rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     irule robust_val_in_memory_exterior_no_new_taint >>
     conj_tac >- simp[] >>
     qexistsl_tac [`{j | off <= j /\ j < off + 32}`,`s.vs_memory`,
                   `u.vs_memory`,`tn.t_mem`,`tf.t_mem`] >>
     simp[IgnAsm `u.vs_memory = _`, IgnAsm `off = _`, IgnAsm `tops = _`] >>
     metis_tac[]) >>
  gvs[local_ptrs_reserved_def]
QED

Resume immutable_word_store_endpoint[return]:
  irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s`,`su`] >> simp[] >>
  `compile_imm_store_word ce.ce_imm_alloca (Lit (n2w off)) op su = ((),sb)` by
    fs[compile_assign_value_def,comp_bind_def,comp_return_def] >>
  `ci_mono su sb` by metis_tac[ci_mono_compile_imm_store_word,pairTheory.SND] >>
  fs[ci_mono_def,lookup_var_def]
QED

Resume immutable_word_store_endpoint[history]:
  `compile_imm_store_word ce.ce_imm_alloca (Lit (n2w off)) op su = ((),sb)` by
    fs[compile_assign_value_def,comp_bind_def,comp_return_def] >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts su sb)` by
    (Cases_on `ce.ce_imm_alloca` >>
     qpat_x_assum `compile_imm_store_word _ _ _ _ = _` mp_tac >>
     simp[compile_imm_store_word_def,emit_op_def,emit_void_def,
          fresh_id_def,fresh_var_def,emit_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
     strip_tac >> gvs[emitted_insts_def,DROP_APPEND,mk_inst_def,arithmeticTheory.SUB_PLUS]) >>
  asm_x "word_code" assume_tac >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s.vs_inst_idx bb.bb_instructions = emitted_insts su sb ++ rest` by
    (fs[fn_has_code_def,rich_listTheory.IS_PREFIX_APPEND] >>
     qexists_tac `l` >>
     `LENGTH su.cs_current_insts - (LENGTH su.cs_current_insts + LENGTH (emitted_insts su sb)) = 0`
       by decide_tac >> simp[DROP_APPEND]) >>
  `alloca_history func (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts su sb))` by
    (irule alloca_history_no_alloca_slice >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `LENGTH sb.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts su sb)` by simp[] >>
  metis_tac[]
QED

Finalise immutable_word_store_endpoint

Theorem body_assign_immutable_word_endpoint_run[local]:
  compile_assign_value ce (Lit (n2w off)) LocCode op T loc ity sty bytes su = ((),sb) /\
  fn_has_code su sb func /\ ~block_is_terminated sb /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts /\
  (!x. op = Var x ==> not_fresh_at su x) /\
  eval_operand op s = SOME (typed_val_to_w256 itv v) /\
  (!region. ce.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w) /\
  stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
  ghost_inv_at D lo d ce cx ee G tn s /\ dead_lo_ok H D lo ce cx /\
  return_buf_frame d ce su s /\ alloca_history func s /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x) /\
  expr_sim_inv ce cx env ee /\ local_ptrs_reserved ce su /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ity /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME itv /\ is_word_type ity /\ value_has_type itv v /\
  write_place cx (ImmutablePlace ce.ce_module id []) v ee = (INL (),fin) /\
  struct_args_unique tops /\ cx_tops cx = tops /\ get_tenv cx = type_env tops /\
  tops = pre ++ VariableDecl vis Immutable id ity slot :: post /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
  off < dimword (:256) /\ off + 32 <= lo /\
  sb.cs_current_bb = su.cs_current_bb /\
  sb.cs_current_insts = su.cs_current_insts ++ emitted_insts su sb /\
  run_inst_seq (emitted_insts su sb) s = OK u /\
  tf.t_mem = tn.t_mem DIFF {j | off <= j /\ j < off + 32} /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
  (!p. not_fresh_at su p ==> FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tf (Var p) = op_taint tn (Var p)) /\
  allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  u.vs_memory = (mstore off (typed_val_to_w256 itv v) s).vs_memory /\
  (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_immutables := s.vs_immutables|>) = s ==>
  fin.storage_trace = ee.storage_trace /\
  stmt_post H ctx func cx lctx ce ce su sb ee s (INL ()) fin (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ghost_inv_at D lo d ce cx fin Gf tf (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  return_buf_frame d ce sb (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\ alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  (u with vs_inst_idx := LENGTH sb.cs_current_insts).vs_alloca_next = s.vs_alloca_next /\ (u with vs_inst_idx := LENGTH sb.cs_current_insts).vs_allocas = s.vs_allocas /\
  (!x. not_fresh_at su x ==> lookup_var x (u with vs_inst_idx := LENGTH sb.cs_current_insts) = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  alloca_frame ce ee su s ce fin (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\ ghost_kept_at lo ce ee su G tn s Gf tf
Proof
  strip_tac >>
  `!i. ~(off <= i /\ i < off + 32) ==>
    mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >> simp[IgnAsm `off = _`, IgnAsm `tops = _`] >>
     irule mstore_mem_bytes_at_disjoint >>
     rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `imm_section_dead tops (mem_bytes_at 0 lo u.vs_memory) =
   imm_section_dead tops (mem_bytes_at 0 lo s.vs_memory)` by
    (`!j. j < lo /\ ~(off <= j /\ j < off + 32) ==>
         EL j (mem_bytes_at 0 lo u.vs_memory) = EL j (mem_bytes_at 0 lo s.vs_memory)` by
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!i. ~(off <= i /\ i < off + 32) ==> _`
          (qspec_then `j` mp_tac) >>
        impl_tac >- (strip_tac >> gvs[]) >>
        disch_then (mp_tac o Q.AP_TERM `EL 0`) >>
        simp[EL_mem_bytes_at, IgnAsm `u.vs_memory = _`]) >>
     irule body_assign_immutable_word_dead_frame >>
     conj_tac >- simp[] >>
     conj_tac >- simp[] >>
     qexistsl_tac [`id`,`off`,`post`,`pre`,`slot`,`itv`,`ity`,`vis`] >>
     pure_rewrite_tac[LENGTH_mem_bytes_at] >>
     qpat_assum `off = _` (fn th =>
       qpat_assum `tops = _` (fn th' =>
         once_rewrite_tac [GSYM th, GSYM th'])) >>
     metis_tac[]) >>
  `!i. i < lo /\ i IN tf.t_mem ==>
     imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo u.vs_memory) i` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     qpat_assum `tf.t_mem = _` (fn th => simp[th,pred_setTheory.IN_DIFF]) >>
     metis_tac[]) >>
  drule_all immutable_word_store_endpoint >> simp[]
QED

Theorem body_assign_snapshot_copy_endpoint_frame[local]:
  compile_store_memory cenv src (Var xd) pty pty sk = ((),sb) /\
  ~is_word_type pty /\ type_memory_bytes cenv pty = type_memory_size tv /\
  not_fresh_at sk xd /\ lookup_var xd s = SOME (n2w b) /\
  ptr_covers G tn xd s (type_memory_size tv) /\
  b + type_memory_size tv < dimword (:256) /\
  b + type_memory_size tv <= s.vs_alloca_next /\
  MEM (mk_inst aid ALLOCA [Lit (n2w (type_memory_size tv))] [p]) (fn_insts func) /\
  FLOOKUP s.vs_allocas aid = SOME (b,type_memory_size tv) /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint b (type_memory_size tv) a len) /\
  stmt_state_rel H0 ctx func cenv cx es s /\
  local_ptrs_reserved cenv sk /\ alloca_history func s /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sk x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sk x) /\
  allocas_from lo s /\ lo <= b /\ lo <= s.vs_alloca_next /\
  fn_has_code sk sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sk.cs_current_bb /\
  s.vs_inst_idx = LENGTH sk.cs_current_insts /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,Gf,tf)) /\
  typed_copy_state_frame sk b (type_memory_size tv) s t /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!i. ~(b <= i /\ i < b+type_memory_size tv) ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  (!x. not_fresh_at sk x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
    val_in_memory tv v b mem) ==>
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    (!H. stmt_state_rel H ctx func cenv cx es s ==>
      stmt_state_rel H ctx func cenv cx es t) /\
    (!D d. ghost_inv_at D lo d cenv cx es G tn s ==>
      ghost_inv_at D lo d cenv cx es Gf tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    lookup_var xd t = SOME (n2w b) /\
    ptr_covers Gf tf xd t (type_memory_size tv) /\
    FLOOKUP t.vs_allocas aid = SOME (b,type_memory_size tv) /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory tv v b mem) /\
    typed_copy_state_frame sk b (type_memory_size tv) s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_history func t /\ allocas_from lo t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!x. not_fresh_at sk x ==>
      not_fresh_at sb x /\ lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!name a len. local_region cenv es.scopes t name a len <=>
      local_region cenv es.scopes s name a len) /\
    (!es0 se s0 G0 tn0.
      se.cs_next_var <= sk.cs_next_var /\
      ghost_kept_at lo cenv es0 se G0 tn0 s0 G tn /\
      alloca_frame cenv es0 se s0 cenv es s /\
      (!old off sz. FLOOKUP s0.vs_allocas old = SOME (off,sz) /\
        old < se.cs_next_id ==> regions_disjoint b (type_memory_size tv) off sz) /\
      (!name off sz. local_region cenv es0.scopes s0 name off sz ==>
        regions_disjoint b (type_memory_size tv) off sz) ==>
      ghost_kept_at lo cenv es0 se G0 tn0 s0 Gf tf /\
      alloca_frame cenv es0 se s0 cenv es t /\
      (!old off sz i. FLOOKUP s0.vs_allocas old = SOME (off,sz) /\
        old < se.cs_next_id /\
        (!name a len. local_region cenv es0.scopes s0 name a len ==>
          off+sz <= a \/ a+len <= off) /\
        off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
   copy_static t = copy_static s` by
    (qpat_assum `typed_copy_state_frame sk b _ _ _`
      (mp_tac o CONJUNCT1 o REWRITE_RULE [typed_copy_state_frame_def]) >>
     simp[venom_state_component_equality,copy_static_def]) >>
  `!a len. a+len <= b \/ b+type_memory_size tv <= a ==>
    mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory` by
    fs[typed_copy_state_frame_def,typed_copy_frame_def] >>
  `!x. not_fresh_at sk x ==> not_fresh_at sb x` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `sk` >> metis_tac[ci_mono_compile_store_memory,ci_mono_def,pairTheory.SND]) >>
  `!name a len. local_region cenv es.scopes t name a len <=>
    local_region cenv es.scopes s name a len` by
    (rw[local_region_def] >> metis_tac[local_ptrs_reserved_def]) >>
  `!i. ~(b <= i /\ i < b+type_memory_size tv) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (conj_tac >- metis_tac[allocas_from_def] >>
     drule typed_copy_state_frame_allocas_below_fmp >> simp[] >>
     drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `lookup_var xd t = SOME (n2w b) /\ ptr_covers Gf tf xd t (type_memory_size tv)` by
    (qpat_assum `!x. not_fresh_at sk x ==> lookup_var x t = _ /\ _`
      (qspec_then `xd` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     strip_tac >> simp[] >>
     irule ptr_covers_lookup_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  simp[] >>
  conj_tac >- suspend "state" >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "history" >>
  suspend "entry"
QED

Resume body_assign_snapshot_copy_endpoint_frame[state]:
  rpt strip_tac >> irule literal_copy_window_stmt_state_rel >>
  qexistsl_tac [`aid`,`b`,`type_memory_size tv`,`p`,`sk`,`sk`,`s`] >>
  simp[] >> fs[typed_copy_state_frame_def,typed_copy_frame_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume body_assign_snapshot_copy_endpoint_frame[ghost]:
  rpt strip_tac >> irule body_full_memory_ghost_frame >> simp[] >>
  qexistsl_tac [`G`,`s`,`sk`,`tn`,`{i | b <= i /\ i < b+type_memory_size tv}`] >>
  simp[] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all literal_ptr_local_footprint_exterior >> simp[])
  >- (rpt strip_tac >>
      `~(b <= i /\ i < b+type_memory_size tv)` by decide_tac >> metis_tac[]) >>
  metis_tac[arithmeticTheory.ADD_CLAUSES]
QED

Resume body_assign_snapshot_copy_endpoint_frame[history]:
  `alloca_inv s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  metis_tac[body_full_path_alloca_history]
QED

Resume body_assign_snapshot_copy_endpoint_frame[entry]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!old off sz i. FLOOKUP s0.vs_allocas old = SOME (off,sz) /\
    old < se.cs_next_id /\ off <= i /\ i < off+sz ==>
    ~(b <= i /\ i < b+type_memory_size tv)` by
    (rpt strip_tac >>
     `regions_disjoint b (type_memory_size tv) off sz` by metis_tac[] >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  conj_tac >- suspend "kept" >>
  conj_tac >- suspend "frame" >> metis_tac[]
QED

Resume body_assign_snapshot_copy_endpoint_frame[kept]:
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  rewrite_tac[ghost_kept_at_def] >>
  conj_tac >- (rpt strip_tac >>
    `not_fresh_at sk x` by metis_tac[not_fresh_at_mono] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    `~(b <= i /\ i < b+type_memory_size tv)` by metis_tac[] >> metis_tac[]) >>
  rpt strip_tac >>
  `regions_disjoint b (type_memory_size tv) b' sz` by metis_tac[] >>
  `~(b <= i /\ i < b+type_memory_size tv)` by (fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  metis_tac[]
QED

Resume body_assign_snapshot_copy_endpoint_frame[frame]:
  qpat_x_assum `alloca_frame _ _ _ _ _ _ _`
    (assume_tac o REWRITE_RULE [alloca_frame_def]) >>
  rewrite_tac[alloca_frame_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `regions_disjoint b (type_memory_size tv) off sz` by metis_tac[] >>
  SUBGOAL_THEN ``off+sz <= b \/ b+type_memory_size tv <= off`` assume_tac
  >- (qpat_x_assum `regions_disjoint b _ off sz` mp_tac >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s.vs_memory` by metis_tac[] >>
  `mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory /\
   (!n a len. local_region cenv es.scopes s n a len ==>
     off+sz <= a \/ a+len <= off)` by
    (qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
       (qspecl_then [`aid'`,`off`,`sz`] mp_tac) >>
     (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> simp[]) >>
  simp[] >> first_assum ACCEPT_TAC
QED

Finalise body_assign_snapshot_copy_endpoint_frame[local]

Theorem body_assign_snapshot_bytes_copy_endpoint[local]:
  !ce xs xd pty sk sb cx tv v s sw dw tn G lo ctx func explicit PG.
  compile_store_memory ce (Var xs) (Var xd) pty pty sk = ((),sb) /\
  is_bytestring_type pty /\ evaluate_type (get_tenv cx) pty = SOME tv /\
  type_memory_bytes ce pty = type_memory_size tv /\ value_has_type tv v /\ val_wf tv v /\
  not_fresh_at sk xs /\ not_fresh_at sk xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size tv) /\ ptr_covers G tn xd s (type_memory_size tv) /\
  w2n sw + type_memory_size tv < dimword(:256) /\ w2n dw + type_memory_size tv < dimword(:256) /\
  w2n sw + type_memory_size tv <= s.vs_alloca_next /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sk sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sk.cs_current_bb /\ s.vs_inst_idx = LENGTH sk.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> val_in_memory tv v (w2n dw) mem) /\
    typed_copy_state_frame sk (w2n dw) (type_memory_size tv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size tv) ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sk x ==> lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_store_bytestring (Var xs) (Var xd) sk = ((),sb)` by
    gvs[compile_store_memory_def,bytestring_type_not_word] >>
  Q.SUBGOAL_THEN
    `?len. 32 + 32 * word_size len <= type_memory_size tv /\
           ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
            (?str. v = StringV str /\ len = LENGTH str))`
    (qx_choose_then `len` (CONJUNCTS_THEN assume_tac))
  >- suspend "extent" >>
  drule_all robust_bytestring_header >> strip_tac >>
  qabbrev_tac `n = 32 + 32 * word_size len` >>
  `len <= 32 * word_size len` by simp[word_size_capacity] >>
  `n <= type_memory_size tv /\ len+31 < dimword(:256) /\ n < dimword(:256)` by
    (simp[Abbr `n`] >> decide_tac) >>
  `ptr_covers G tn xs s n /\ ptr_covers G tn xd s n` by
    (conj_tac >> irule ptr_covers_mono >> metis_tac[]) >>
  `eval_operand (Var xs) s = SOME sw /\ eval_operand (Var xd) s = SOME dw` by
    simp[eval_operand_def] >>
  `!x. Var xs = Var x \/ Var xd = Var x ==> not_fresh_at sk x` by
    (rpt strip_tac >> gvs[]) >>
  `w2n sw + n <= s.vs_alloca_next /\ w2n dw + n <= s.vs_alloca_next` by decide_tac >>
  `run_inst_seq_mem_ok (emitted_insts sk sb) s` by
    (irule compile_store_bytestring_body_mem_ok >>
     qexistsl_tac [`dw`,`Var xd`,`len`,`Var xs`,`sw`] >>
     gnvs[Abbr `n`] >> metis_tac[]) >>
  `n = 32 + 32 * ((len+31) DIV 32)` by simp[Abbr `n`,word_size_def] >>
  drule bytesCopyCodeTheory.compile_store_bytestring_code >> strip_tac >>
  `sb.cs_current_bb = sk.cs_current_bb` by gvs[same_blocks_def] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sk sb) (DROP s.vs_inst_idx bb.bb_instructions)` by suspend "prefix" >>
  drule_all compile_store_bytestring_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `(sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s` by suspend "raw" >>
  drule_all bytestring_copy_effects >> strip_tac >>
  `!mem. mem_agree_outside tnf.t_mem sf.vs_memory mem ==>
         val_in_memory tv v (w2n dw) mem` by suspend "robust" >>
  `sf.vs_current_bb = s.vs_current_bb /\ sf.vs_halted = s.vs_halted` by suspend "fields" >>
  qexistsl_tac [`sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sk sb)`,`Gf`,`tnf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[blockPrefixEquivTheory.lookup_var_set_inst_idx] >>
  suspend "frame"
QED

Resume body_assign_snapshot_bytes_copy_endpoint[extent]:
  drule_all valueCopyBytesTheory.bytestring_type_value >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def,type_memory_size_def] >>
  irule exprSimPropsTheory.word_size_monotone >> simp[]
QED

Resume body_assign_snapshot_bytes_copy_endpoint[prefix]:
  qpat_x_assum `fn_has_code sk sb func` mp_tac >> simp[fn_has_code_def] >>
  strip_tac >> goal_assum drule >>
  gvs[rich_listTheory.IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,DROP_LENGTH_APPEND] >> simp[]
QED

Resume body_assign_snapshot_bytes_copy_endpoint[raw]:
  `32 + 32 * word_size len < dimword(:256)` by gvs[Abbr `n`] >>
  drule_all buffer_store_bytestring_run >> strip_tac >> gvs[]
QED

Resume body_assign_snapshot_bytes_copy_endpoint[robust]:
  rpt strip_tac >> irule bytestring_copy_robust_destination >> metis_tac[]
QED

Resume body_assign_snapshot_bytes_copy_endpoint[fields]:
  qpat_x_assum `(sf with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
  simp[venom_state_component_equality]
QED

Resume body_assign_snapshot_bytes_copy_endpoint[frame]:
  irule typed_copy_state_frame_subinterval >>
  qexistsl_tac [`w2n dw`,`n`] >> simp[] >>
  simp[typed_copy_state_frame_def,blockPrefixEquivTheory.lookup_var_set_inst_idx] >>
  conj_tac >-
    (qpat_x_assum `(sf with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  simp[] >>
  irule (SRULE [] (cj 3 (REWRITE_RULE [typed_copy_state_frame_def]
    typed_copy_mcopy_state_frame)))
QED

Finalise body_assign_snapshot_bytes_copy_endpoint[local]

Theorem body_assign_snapshot_positive_source_ready[local]:
  0 < type_memory_size tv /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  eval_operand op u = SOME w /\
  ptr_buf_ok ce e op Gu u /\
  ptr_val_ok cx (post_value_type ce e) v op Gu tnu u /\
  (type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= u.vs_alloca_next) /\
  stmt_state_rel H ctx func ce cx ee u ==>
  ?xs. op = Var xs /\ lookup_var xs u = SOME w /\
    ptr_covers Gu tnu xs u (type_memory_size tv) /\
    w2n w + type_memory_size tv <= u.vs_alloca_next /\
    w2n w + type_memory_size tv < dimword(:256) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `w2n w + type_memory_size tv <= u.vs_alloca_next` by decide_tac >>
  `w2n w + type_memory_size tv < dimword (:256)` by
    metis_tac[stmt_state_rel_alloca_room, alloca_room_next_lt, LESS_EQ_LESS_TRANS] >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  `op_taint tnu op = {}` by fs[ptr_val_ok_def] >>
  `?xs. op = Var xs /\ ptr_covers Gu tnu xs u (type_memory_size tv)` by
    (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
     simp[] >> qexistsl_tac [`ce`,`e`] >> simp[]) >>
  qexists_tac `xs` >> gvs[eval_operand_def]
QED

Theorem body_assign_observed_storage_write_wf[local]:
  regions_consistent (FST H) /\ storage_well_formed_on cx ee (FST H) /\
  storage_place_observed H (StoragePlace tr slot dtv) /\
  well_formed_type_value dtv /\ value_has_type dtv v /\
  write_place cx (StoragePlace tr slot dtv) v ee = (INL (),ff) ==>
  storage_well_formed_on cx ff (FST H)
Proof
  simp[vyperStoragePlaceObservedTheory.storage_place_observed_def] >>
  strip_tac >>
  rename1 `MEM (tr,root,rtv) (FST H)` >>
  `w2n root + type_slot_size rtv <= dimword(:256)` by
    (fs[regions_consistent_def] >> (metis_tac[regions_consistent_def])) >>
  qpat_assum `write_place _ _ _ _ = _`
    (mp_then Any mp_tac
      vyperFiniteStoragePreservationTheory.write_place_preserves_storage_well_formed_on) >>
  disch_then (qspecl_then [`[StorageRoot tr (w2n root) rtv]`,`dtv`,`H`] mp_tac) >>
  simp[storage_observations_ok_def, storage_trace_regions_def,
       storage_trace_locks_def, storage_roots_fit_def,
       storage_trace_backends_well_formed_def, wordsTheory.n2w_w2n,
       vyperTypeInvariantsTheory.runtime_place_typed_def,
       vyperStateTheory.place_type_value_def, vyperStateTheory.return_def] >>
  metis_tac[]
QED

(* The direct slots arm starts at the landing of the RHS, target and
   unwrap prefix. The prefix's replay marks do not belong to this suffix. *)
Theorem body_assign_other_direct_slots_write_full[local]:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
                                 sz = type_memory_size rt) fields) /\
  evaluate_type (get_tenv cx) dty = SOME tv /\ value_has_type tv v /\
  0 < type_slot_size tv /\
  compile_store_slots cenv op dst dty tr su = ((),sb) /\
  (!x. op = Var x \/ dst = Var x ==> not_fresh_at su x) /\
  eval_operand op z = SOME sw /\ eval_operand dst z = SOME k /\
  op_taint tnz op = {} /\ op_taint tnz dst = {} /\
  (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem) /\
  (?x. op = Var x /\ ptr_covers Gz tnz x z (type_memory_size tv)) /\
  w2n sw + type_memory_size tv <= z.vs_alloca_next /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  ~z.vs_halted /\ z.vs_current_bb = su.cs_current_bb /\
  z.vs_inst_idx = LENGTH su.cs_current_insts /\
  local_ptrs_reserved cenv su /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  return_buf_frame d cenv su z /\ alloca_history func z /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  expr_sim_inv cenv cx env (ee with gas_obs := []) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) z /\
    storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) Gz tnz z /\
    dead_lo_ok H (DF H) lo cenv cx /\
    storage_place_observed H (StoragePlace tr k tv)) /\
  sa.cs_next_var <= su.cs_next_var /\
  s0.vs_alloca_next <= z.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x z = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP Gz x = FLOOKUP G0 x /\ op_taint tnz (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame cenv es sa s0 cenv ee z /\
  (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
    off <= i /\ i < off + sz /\ i IN tnz.t_mem ==> i IN tn0.t_mem) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (write_place cx (StoragePlace tr k tv) v) (ee,z,Gz,tnz)
    (\H res ef G tn t. ?ce.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
      cenv_top_ext cenv ce ef.scopes /\ stmt_state_rel H ctx func ce cx ef t /\
      storage_well_formed_on cx ef (FST H) /\ return_buf_frame d ce sb t /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d ce cx ef G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 ce ef t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem))
    (\H res ef gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ef with gas_obs := tail) res gt r) /\
      halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==>
        !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ?rootk root path delta. MEM (tr,rootk,root) (FST H) /\
      storage_subregion root path delta tv /\ w2n k = w2n rootk + delta /\
      w2n k + type_slot_size tv <= dimword (:256)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     qpat_x_assum `storage_place_observed _ _`
       (qx_choose_then `rootk` (qx_choose_then `root` (qx_choose_then `path`
          (qx_choose_then `delta` strip_assume_tac))) o
        REWRITE_RULE [vyperStoragePlaceObservedTheory.storage_place_observed_def]) >>
     `w2n rootk + type_slot_size root <= dimword (:256)` by
       (fs[valid_horizon_def,regions_consistent_def] >> metis_tac[]) >>
     drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
     `w2n rootk + delta < dimword (:256)` by decide_tac >>
     drule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> strip_tac >>
     qexistsl [`rootk`,`root`,`path`,`delta`] >> simp[] >> decide_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `w2n k + type_slot_size tv <= dimword (:256)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> ?rootk root path delta. _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `w2n sw + type_memory_size tv < dimword (:256)` by
    (drule stmt_state_rel_alloca_room >> simp[alloca_room_def] >> decide_tac) >>
  `alloca_inv z` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `z.vs_call_ctx.cc_static = cx.txn.is_static` by
    (drule_then (mp_then Any mp_tac state_rel_call_ctx_rel) stmt_state_rel_state_rel >>
     simp[call_ctx_rel_def]) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `?writes. encode_value tv v = SOME writes` by
    metis_tac[cj 1 vyperTypingTheory.value_has_type_equiv,optionTheory.IS_SOME_EXISTS] >>
  `ci_mono su sb` by
    (mp_tac (Q.SPECL [`cenv`,`op`,`dst`,`dty`,`tr`,`su`] (cj 1 ci_mono_compile_store_slots)) >> simp[]) >>
  `su.cs_next_var <= sb.cs_next_var` by fs[ci_mono_def] >>
  `~block_is_terminated sb` by
    (drule (cj 1 stmtSimAssignStorageSparseTheory.store_slots_open) >> simp[]) >>
  Cases_on `cx.txn.is_static` >- suspend "static" >> suspend "normal"
QED

Resume body_assign_other_direct_slots_write_full[static]:
  `type_slot_size tv <> 0` by decide_tac >>
  mp_tac (Q.INST [`s` |-> `z`,`sa` |-> `su`,`src` |-> `op`,
    `ty` |-> `dty`,`dw` |-> `k`,`G` |-> `Gz`,`tn` |-> `tnz`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
    `ee` |-> `ee with gas_obs := []`]
    (SPEC_ALL body_assign_slots_full_static_exit)) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[])) >> simp[] >>
  disch_then (qx_choose_then `u` (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac))) >>
  irule gas_outcome_full_intro >>
  qexistsl [`Gf`,`ee`,`[]`,`Abort ExHalt_abort (halt_state (set_returndata [] u))`,
           `INR (Error (RuntimeError "write in static context"))`,`tnf`] >>
  simp[write_place_def,write_storage_slot_eq,stmt_exit_ptr_def,
       exprSimDefsTheory.expr_exit_def,halt_exit_not_halt]
QED

Resume body_assign_other_direct_slots_write_full[normal]:
  mp_tac (Q.INST [`s` |-> `z`,`sa` |-> `su`,`src` |-> `op`,
    `ty` |-> `dty`,`dw` |-> `k`,`G` |-> `Gz`,`tn` |-> `tnz`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (SPEC_ALL body_assign_slots_full_frame_path)) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> fs[local_ptrs_reserved_def])) >>
  disch_then (qx_choose_then `u` (qx_choose_then `ks` (qx_choose_then `Gf`
    (qx_choose_then `tnf` (REPEAT_TCL CONJUNCTS_THEN assume_tac))))) >>
  qabbrev_tac `e0 = ee with gas_obs := []` >>
  qabbrev_tac `ef = set_storage cx e0 tr (apply_writes k writes (get_storage cx e0 tr))` >>
  `write_place cx (StoragePlace tr k tv) v e0 = (INL (),ef)` by
    simp[Abbr `ef`,write_place_def,write_storage_slot_eq] >>
  `ef.gas_obs = [] /\ ef.storage_trace = ee.storage_trace /\ ef.scopes = ee.scopes` by
    (Cases_on `tr` >> simp[Abbr `ef`,Abbr `e0`,set_storage_def]) >>
  irule gas_outcome_full_intro >>
  qexistsl [`Gf`,`ef`,`[]`,`OK u`,`INL ()`,`tnf`] >>
  simp[] >> conj_tac
  >- (gen_tac >> simp[write_place_def] >>
      qpat_assum `write_place _ _ _ e0 = _`
        (mp_tac o REWRITE_RULE [write_place_def]) >>
      simp[Once (GSYM write_storage_slot_gas_obs),Abbr `e0`,write_storage_slot_gas_obs] >>
      disch_then (mp_tac o AP_TERM ``\s:evaluation_state. s with gas_obs := tail`` o CONJUNCT2) >>
      simp[]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?rootk root path delta. _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H e env rootk root path delta. _ ==> _`
    (qspecl_then [`H`,`e0`,`env`,`rootk`,`root`,`path`,`delta`] mp_tac) >>
  (impl_tac >- fs[valid_horizon_def]) >>
  disch_then (qx_choose_then `ef'` strip_assume_tac) >>
  `ef' = ef` by fs[write_place_def] >>
  qpat_x_assum `ef' = ef` SUBST_ALL_TAC >>
  `storage_well_formed_on cx ef (FST H)` by
    (irule body_assign_observed_storage_write_wf >>
     conj_tac >- fs[valid_horizon_def] >>
     qexistsl [`tv`,`e0`,`k`,`tr`,`v`] >>
     simp[] >> metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value]) >>
  `!x. not_fresh_at su x ==> lookup_var x u = lookup_var x z` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at su x ==> _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  drule_all_then assume_tac exprSimCopyTheory.copy_buffer_local_region_frame >>
  `alloca_frame cenv es sa s0 cenv ef u` by
    (qpat_x_assum `alloca_frame _ _ _ _ _ ee z` mp_tac >> simp[alloca_frame_def]) >>
  `(ef with gas_obs := []) = ef` by simp[evaluation_state_component_equality] >>
  disj1_tac >> simp[stmt_lands_def,cenv_top_ext_refl] >>
  `!x. not_fresh_at sa x ==> not_fresh_at su x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  metis_tac[]
QED

Finalise body_assign_other_direct_slots_write_full[local]

(* The bytes loop reads the physical source length, not destination capacity. *)
Theorem body_assign_other_bytes_slots_write_full[local]:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
                                 sz = type_memory_size rt) fields) /\
  sty <> dty /\ is_bytestring_type sty /\ is_bytestring_type dty /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
  compile_store_slots cenv op dst dty tr su = ((),sb) /\
  (!x. op = Var x \/ dst = Var x ==> not_fresh_at su x) /\
  eval_operand op z = SOME sw /\ eval_operand dst z = SOME k /\
  op_taint tnz op = {} /\ op_taint tnz dst = {} /\
  (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==>
         val_in_memory stv v (w2n sw) mem) /\
  (?x. op = Var x /\ ptr_covers Gz tnz x z (type_memory_size stv)) /\
  w2n sw + type_memory_size stv <= z.vs_alloca_next /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  ~z.vs_halted /\ z.vs_current_bb = su.cs_current_bb /\
  z.vs_inst_idx = LENGTH su.cs_current_insts /\
  local_ptrs_reserved cenv su /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  return_buf_frame d cenv su z /\ alloca_history func z /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  expr_sim_inv cenv cx env (ee with gas_obs := []) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) z /\
    storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) Gz tnz z /\
    dead_lo_ok H (DF H) lo cenv cx /\
    storage_place_observed H (StoragePlace tr k dtv)) /\
  sa.cs_next_var <= su.cs_next_var /\
  s0.vs_alloca_next <= z.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x z = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP Gz x = FLOOKUP G0 x /\ op_taint tnz (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame cenv es sa s0 cenv ee z /\
  (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
    off <= i /\ i < off + sz /\ i IN tnz.t_mem ==> i IN tn0.t_mem) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (write_place cx (StoragePlace tr k dtv) v) (ee,z,Gz,tnz)
    (\H res ef G tn t. ?ce.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
      cenv_top_ext cenv ce ef.scopes /\ stmt_state_rel H ctx func ce cx ef t /\
      storage_well_formed_on cx ef (FST H) /\ return_buf_frame d ce sb t /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d ce cx ef G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 ce ef t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem))
    (\H res ef gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ef with gas_obs := tail) res gt r) /\
      halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==>
        !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `compile_store_slots cenv op dst sty tr su = ((),sb)` by
    metis_tac[placeStoreSlotsTheory.store_slots_bytes_compile_eq] >>
  `type_slot_size stv <= type_slot_size dtv /\ encode_value stv v = encode_value dtv v` by
    (irule placeStoreSlotsTheory.store_slots_bytes_encoding >> metis_tac[]) >>
  `0 < type_slot_size stv` by
    (qspecl_then [`get_tenv cx`,`sty`,`stv`] mp_tac valueCopyBytesTheory.bytestring_type_value >>
     simp[] >> strip_tac >> simp[vyperValueTheory.type_slot_size_def]) >>
  `0 < type_slot_size dtv` by decide_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ?rootk root path delta. MEM (tr,rootk,root) (FST H) /\
      storage_subregion root path delta dtv /\ w2n k = w2n rootk + delta /\
      w2n k + type_slot_size dtv <= dimword (:256)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     qpat_x_assum `storage_place_observed _ _`
       (qx_choose_then `rootk` (qx_choose_then `root` (qx_choose_then `root_path`
          (qx_choose_then `delta` strip_assume_tac))) o
        REWRITE_RULE [vyperStoragePlaceObservedTheory.storage_place_observed_def]) >>
     `w2n rootk + type_slot_size root <= dimword (:256)` by
       (fs[valid_horizon_def,regions_consistent_def] >> metis_tac[]) >>
     drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
     `w2n rootk + delta < dimword (:256)` by decide_tac >>
     drule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> strip_tac >>
     qexistsl [`rootk`,`root`,`root_path`,`delta`] >> simp[] >> decide_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `w2n k + type_slot_size dtv <= dimword (:256)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> ?rootk root path delta. _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `w2n k + type_slot_size stv <= dimword (:256)` by decide_tac >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (drule stmt_state_rel_alloca_room >> simp[alloca_room_def] >> decide_tac) >>
  `z.vs_call_ctx.cc_static = cx.txn.is_static` by
    (drule_then (mp_then Any mp_tac state_rel_call_ctx_rel) stmt_state_rel_state_rel >>
     simp[call_ctx_rel_def]) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `?writes. encode_value dtv v = SOME writes` by
    metis_tac[cj 1 vyperTypingTheory.value_has_type_equiv,optionTheory.IS_SOME_EXISTS] >>
  `encode_value stv v = SOME writes` by simp[] >>
  Cases_on `cx.txn.is_static` >- suspend "static" >> suspend "normal"
QED

Resume body_assign_other_bytes_slots_write_full[static]:
  `type_slot_size stv <> 0` by decide_tac >>
  mp_tac (Q.INST [`s` |-> `z`,`sa` |-> `su`,`src` |-> `op`,
    `ty` |-> `sty`,`tv` |-> `stv`,`dw` |-> `k`,`G` |-> `Gz`,`tn` |-> `tnz`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
    `ee` |-> `ee with gas_obs := []`]
    (SPEC_ALL bodyFullAssignTopCopyTailTheory.body_assign_slots_full_static_exit)) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[])) >> simp[] >>
  disch_then (qx_choose_then `u` (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac))) >>
  irule gas_outcome_full_intro >>
  qexistsl [`Gf`,`ee`,`[]`,`Abort ExHalt_abort (halt_state (set_returndata [] u))`,
           `INR (Error (RuntimeError "write in static context"))`,`tnf`] >>
  simp[write_place_def,write_storage_slot_eq,stmt_exit_ptr_def,
       exprSimDefsTheory.expr_exit_def,halt_exit_not_halt]
QED

Resume body_assign_other_bytes_slots_write_full[normal]:
  mp_tac (Q.INST [`s` |-> `z`,`sa` |-> `su`,`src` |-> `op`,
    `tv` |-> `stv`,`dw` |-> `k`,`G` |-> `Gz`,`tn` |-> `tnz`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (SPEC_ALL (Q.SPECL [`cenv`,`get_tenv cx`,`sty`] compile_store_slots_origin_ptr_path))) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[])) >>
  disch_then (qx_choose_then `u` (qx_choose_then `ks` (qx_choose_then `Gf`
    (qx_choose_then `tnf` (REPEAT_TCL CONJUNCTS_THEN assume_tac))))) >>
  suspend "landing"
QED

Resume body_assign_other_bytes_slots_write_full[landing]:
  `!x. not_fresh_at su x ==> lookup_var x u = lookup_var x z` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at su x ==> _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `su.cs_next_var <= sb.cs_next_var` by
    (`ci_mono su sb` by
       (mp_tac (Q.SPECL [`cenv`,`op`,`dst`,`dty`,`tr`,`su`] (cj 1 ci_mono_compile_store_slots)) >> simp[]) >>
     fs[ci_mono_def]) >>
  `~block_is_terminated sb` by
    (drule (cj 1 stmtSimAssignStorageSparseTheory.store_slots_open) >> simp[]) >>
  `return_buf_frame d cenv sb u` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`,`z`,`su`] >> simp[]) >>
  `alloca_history func u` by
    (`alloca_inv z` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
     `gas_origin_ptr_path (ARB,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (z,Gz,tnz) [] (OK u,Gf,tnf)` by simp[] >>
     drule_all body_full_path_alloca_history >> simp[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (drule bodyFullStoreSlotsFrameTheory.store_slots_normalize_allocas_below_fmp >>
     simp[bodyFullStoreSlotsFrameTheory.store_slots_fold_allocas_below_fmp]) >>
  `well_formed_type_value dtv` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==>
     val_in_memory dtv v (w2n sw) mem` by
    (gen_tac >> strip_tac >>
     irule valueCopyBytesTheory.bytestring_val_in_memory_transfer >> metis_tac[]) >>
  qabbrev_tac `e0 = ee with gas_obs := []` >>
  qabbrev_tac `ef = set_storage cx e0 tr (apply_writes k writes (get_storage cx e0 tr))` >>
  `write_place cx (StoragePlace tr k dtv) v e0 = (INL (),ef)` by
    simp[Abbr `ef`,write_place_def,write_storage_slot_eq] >>
  `ef.gas_obs = [] /\ ef.storage_trace = ee.storage_trace /\ ef.scopes = ee.scopes` by
    (Cases_on `tr` >> simp[Abbr `ef`,Abbr `e0`,set_storage_def]) >>
  irule gas_outcome_full_intro >>
  qexistsl [`Gf`,`ef`,`[]`,`OK u`,`INL ()`,`tnf`] >>
  simp[] >> conj_tac
  >- (gen_tac >> simp[write_place_def] >>
      qpat_assum `write_place _ _ _ e0 = _`
        (mp_tac o REWRITE_RULE [write_place_def]) >>
      simp[Once (GSYM write_storage_slot_gas_obs),Abbr `e0`,write_storage_slot_gas_obs] >>
      disch_then (mp_tac o AP_TERM ``\s:evaluation_state. s with gas_obs := tail`` o CONJUNCT2) >>
      simp[]) >>
  suspend "posts"
QED

Resume body_assign_other_bytes_slots_write_full[posts]:
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?rootk root path delta. _`
    (drule_then strip_assume_tac) >>
  qpat_assum `valid_horizon _ _ H _`
    (strip_assume_tac o REWRITE_RULE [valid_horizon_def]) >>
  `!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at su x` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC local_ptrs_reserved_imm_base) >>
  `stmt_state_rel H ctx func cenv cx ef u /\ ghost_inv_at (DF H) lo d cenv cx ef Gf tnf u` by
    (simp[Abbr `ef`] >>
     match_mp_tac (GEN_ALL (SRULE [LET_THM] body_assign_slots_positive_endpoint_post)) >>
     asm_rewrite_tac[] >>
     qexistsl [`v`,`dtv`,`tnz`,`su`,`z`,`rootk`,`root`,`path`,
               `w2n sw`,`ks`,`env`,`delta`,`Gz`] >>
     asm_rewrite_tac[] >>
     qpat_assum `w2n k = _` (once_rewrite_tac o single o SYM) >>
     qpat_assum `w2n k + type_slot_size dtv <= _` ACCEPT_TAC) >>
  `storage_well_formed_on cx ef (FST H)` by
    (irule body_assign_observed_storage_write_wf >>
     conj_tac >- fs[valid_horizon_def] >>
     qexistsl [`dtv`,`e0`,`k`,`tr`,`v`] >> simp[]) >>
  drule_all_then assume_tac exprSimCopyTheory.copy_buffer_local_region_frame >>
  `alloca_frame cenv es sa s0 cenv ef u` by
    (qpat_x_assum `alloca_frame _ _ _ _ _ ee z` mp_tac >> simp[alloca_frame_def]) >>
  `(ef with gas_obs := []) = ef` by simp[evaluation_state_component_equality] >>
  disj1_tac >> simp[stmt_lands_def,cenv_top_ext_refl] >>
  `!x. not_fresh_at sa x ==> not_fresh_at su x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  metis_tac[]
QED

Finalise body_assign_other_bytes_slots_write_full[local]

Theorem body_assign_empty_backend_ghost[local]:
  ghost_inv_at D lo d cenv cx ee G tn s /\ dead_lo_ok H D lo cenv cx /\
  ff.scopes = ee.scopes /\ s.vs_call_ctx.cc_address = cx.txn.target ==>
  ghost_inv_at D lo d cenv cx ff G
    (if tr then tn with t_trans := key_update tn.t_trans slot {}
     else tn with t_stor := key_update tn.t_stor slot {})
    ((if tr then tstore slot 0w s else sstore slot 0w s) with vs_inst_idx := pc)
Proof
  strip_tac >>
  `stor_taint_ok_at D tn s` by fs[ghost_inv_at_def] >>
  `stor_taint_ok_at D
     (if tr then tn with t_trans := key_update tn.t_trans slot {}
      else tn with t_stor := key_update tn.t_stor slot {})
     ((if tr then tstore slot 0w s else sstore slot 0w s) with vs_inst_idx := pc)` by
    (qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` kall_tac >>
     Cases_on `tr` >>
     gvs[dead_lo_ok_def, stor_taint_ok_at_def, sourceUnitExecutionTheory.cx_dead_def,
         sstore_def, tstore_def, vfmStateTheory.lookup_account_def,
         combinTheory.APPLY_UPDATE_THM, ptrDisciplineTheory.key_update_def,
         pred_setTheory.SUBSET_DEF, pairTheory.FORALL_PROD] >>
     metis_tac[accountsRelPropsTheory.storage_dead_update_zero]) >>
  Cases_on `d`
  >- (Cases_on `tr` >>
      gvs[ghost_inv_at_def, return_buf_ptr_def, ptr_covers_def,
          ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.allocas_from_def,
          sstore_def, tstore_def, lookup_var_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  PairCases_on `x` >> Cases_on `tr` >>
  gvs[ghost_inv_at_def, return_buf_ptr_def, ptr_covers_def,
      ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.allocas_from_def,
          sstore_def, tstore_def, lookup_var_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem body_assign_ghost_imm_decrease[local]:
  ghost_inv_at D lo d cenv cx es G tn s ==>
  !m. m SUBSET tn.t_imm ==> ghost_inv_at D lo d cenv cx es G (tn with t_imm := m) s
Proof
  rpt strip_tac >>
  `!p sz. ptr_covers G (tn with t_imm := m) p s sz <=> ptr_covers G tn p s sz` by
    simp[ptr_covers_def, ptrDisciplineTheory.op_taint_def] >>
  `return_buf_ptr d cenv G (tn with t_imm := m) s <=> return_buf_ptr d cenv G tn s` by
    (Cases_on `d` >- simp[return_buf_ptr_def] >>
     rename1 `return_buf_ptr (SOME pair) _ _ _ _` >> PairCases_on `pair` >>
     simp[return_buf_ptr_def]) >>
  fs[ghost_inv_at_def, ptrDisciplineTheory.op_taint_def, stor_taint_ok_at_def] >>
  metis_tac[pred_setTheory.SUBSET_TRANS]
QED

(* The scalar suffix chooses one concrete endpoint before the horizon split. *)

Theorem body_assign_empty_place_joint[local]:
  compile_store_at_loc imm dst (Lit 0w) (SOME loc) sa = ((),sb) /\
  eval_operand dst s = SOME w /\ op_taint tn dst = {} /\
  has_length_word dty /\ evaluate_type (get_tenv cx) dty = SOME dtv /\
  write_place cx p (default_value dtv) ee = (INL (),ff) /\
  body_inv tops ctx cenv cx /\ struct_args_unique tops /\
  expr_sim_inv cenv cx env ee /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  loc <> LocCalldata /\
  (loc <> LocCode ==> place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty)) /\
  (loc = LocCode ==>
     ?id. p = ImmutablePlace cenv.ce_module id [] /\ cenv.ce_is_ctor /\
       FLOOKUP env.bare_globals (cenv.ce_module,id) = SOME dty /\
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc (w2n w)) /\
       cenv.ce_module_var_type (cenv.ce_module,id) = SOME dty) /\
  (loc = LocMemory ==> lo <= w2n w /\ ?x. dst = Var x /\
      ptr_covers G tn x s 32 /\ w2n w + 32 <= s.vs_alloca_next) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  ((loc = LocStorage \/ loc = LocTransient) ==> ~s.vs_call_ctx.cc_static) /\
  (loc = LocCode ==> fresh_vars_wrt sa s /\ op_prov G dst = NONE /\
     w2n w + 32 <= lo /\
     (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
       op_taint tn region = {} /\ op_prov G region = NONE)) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  return_buf_frame d cenv sa s /\
  sa0.cs_next_id <= sa.cs_next_id /\ sa0.cs_next_var <= sa.cs_next_var /\
  (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP s.vs_allocas aid = SOME ent) /\
  (!x v. not_fresh_at sa0 x /\ lookup_var x s0 = SOME v ==> lookup_var x s = SOME v) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  alloca_frame cenv es0 sa0 s0 cenv ee s /\
  ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G tn /\
  (?H : (bool # bytes32 # type_value) list # num list.
     valid_horizon cx st0 H ee.storage_trace) /\
  (!H : (bool # bytes32 # type_value) list # num list.
    valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\ dead_lo_ok H (DF H) lo cenv cx /\
    storage_place_observed H p) ==>
  ?t Gf tf.
    (!H : (bool # bytes32 # type_value) list # num list.
      valid_horizon cx st0 H ff.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf) /\
      stmt_state_rel H ctx func cenv cx ff t /\ storage_well_formed_on cx ff (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ff Gf tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    return_buf_frame d cenv sb t /\ alloca_history func t /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!x v. not_fresh_at sa0 x /\ lookup_var x s0 = SOME v ==> lookup_var x t = SOME v) /\
    alloca_frame cenv es0 sa0 s0 cenv ff t /\
    ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 Gf tf /\
    (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
       (!name b len. local_region cenv es0.scopes s0 name b len ==>
          off+sz <= b \/ b+len <= off) /\
       off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn0.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`explicit` |-> `explicit`, `PG` |-> `PG`]
            (SPEC_ALL body_assign_empty_scalar_suffix)) >>
  impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS)) >>
  `ff.storage_trace = ee.storage_trace` by
    (drule write_place_storage_trace >> simp[]) >>
  `!x. not_fresh_at sa0 x ==> not_fresh_at sa x` by
    metis_tac[not_fresh_at_mono] >>
  `ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 Gf tf` by
    (irule ghost_kept_at_clean_suffix >> qexistsl_tac [`G`,`tn`] >>
     simp[] >> metis_tac[]) >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s`,`sa`] >> simp[] >>
     `ci_mono sa sb` by metis_tac[cj 2 ci_mono_stmt_helpers,pairTheory.SND] >>
     fs[ci_mono_def] >> metis_tac[]) >>
  `!H : (bool # bytes32 # type_value) list # num list.
    valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ff t /\ storage_well_formed_on cx ff (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ff Gf tf t /\
    alloca_frame cenv ee sa s cenv ff t` by suspend "restore" >>
  qpat_x_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H0` assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _ /\ _ /\ alloca_frame _ _ _ _ _ _ _`
    (qspec_then `H0` mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[] >>
  conj_tac >-
    (irule alloca_frame_trans >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ Gf tf`
    (ACCEPT_TAC o cj 2 o REWRITE_RULE [ghost_kept_at_def])
QED

Resume body_assign_empty_place_joint[restore]:
  qx_gen_tac `H` >> strip_tac >>
  Cases_on `loc` >> gvs[] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==>
      stmt_state_rel H _ _ _ _ ee s /\ _ /\ _ /\ _ /\ storage_place_observed H p`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS)
  >- suspend "memory"
  >- suspend "backend"
  >- suspend "backend"
  >> suspend "immutable"
QED

Resume body_assign_empty_place_joint[memory]:
  qmatch_goalsub_abbrev_tac `stmt_state_rel H ctx func cenv cx ff u` >>
  `32 <= type_memory_size dtv` by
    (qpat_assum `evaluate_type _ _ = _` (mp_then Any mp_tac place_store_empty_representation) >>
     disch_then (qspecl_then [`w2n w`,`u.vs_memory`] mp_tac) >>
     simp[Abbr `u`]) >>
  `gas_marked_path F ctx func s 0 (OK u)` by
    (`gas_origin_path T explicit ctx func s [] (OK u)` by
       (qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
          (qspec_then `DF H` (mp_tac o cj 1 o MATCH_MP gas_origin_ptr_path_projections)) >> simp[]) >>
     drule gas_origin_path_erase >>
     simp[fragGasModeTheory.gas_marked_path_def] >>
     metis_tac[fragGasPathMemTheory.gas_path_mem_exec]) >>
  `typed_copy_effect ctx func sa sb s u (w2n w) (type_memory_size dtv)` by
    (simp[typed_copy_effect_def, Abbr `u`, lookup_var_def,
          venomMemPropsTheory.mstore_memory_nondecreasing] >>
     conj_tac >- simp[mstore_def, venom_state_component_equality] >>
     rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tf.t_mem` by simp[] >>
  `!mem. mem_agree_outside tf.t_mem u.vs_memory mem ==>
      val_in_memory dtv (default_value dtv) (w2n w) mem` by
    (rpt strip_tac >>
     `mem_word_at (w2n w) mem = 0w` by
       (qpat_assum `mem_agree_outside _ _ _`
          (mp_then Any mp_tac bodyPtrPrecompileBuiltinsArithmeticValueTheory.clean_word_mem_agree) >>
        disch_then (qspec_then `w2n w` mp_tac) >> simp[Abbr `u`]) >>
     qpat_assum `evaluate_type _ _ = _` (mp_then Any mp_tac place_store_empty_representation) >>
     disch_then (qspecl_then [`w2n w`,`mem`] mp_tac) >> simp[]) >>
  `value_has_type dtv (default_value dtv)` by
    (drule vyperTypeDefaultsTheory.default_value_has_type_thm >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx ff u /\
   ghost_inv_at (DF H) lo d cenv cx ff G tf u /\
   alloca_frame cenv ee sa s cenv ff u` by
    (mp_tac (Q.INST [`dw` |-> `w`,`v` |-> `default_value dtv`,`t` |-> `u`,
                    `D` |-> `DF H`, `Gf` |-> `G`]
      (horizonTypeLib.at_horizon_named "H"
         (SPEC_ALL body_assign_memory_place_store_post))) >>
     (impl_tac >- simp[]) >>
     strip_tac >> simp[]) >>
  simp[] >>
  Cases_on `p` >> gvs[place_ptr_rel_def, slot_loc_def, AllCaseEqs()] >>
  drule write_memory_place_frame >> strip_tac >>
  `(ee with scopes := sc).accounts = ee.accounts /\
   (ee with scopes := sc).tStorage = ee.tStorage` by simp[] >>
  metis_tac[storage_well_formed_on_backends]
QED
Resume body_assign_empty_place_joint[backend]:
  markerLib.RESUME_TAC >>
  Cases_on `p` >> gvs[place_ptr_rel_def, slot_loc_def, AllCaseEqs()] >>
  drule_then assume_tac write_storage_place_scopes >>
  (conj_tac >-
    (simp[stmt_state_rel_inst_idx] >>
     drule_all place_store_empty_backend_state >> simp[])) >>
  (conj_tac >- suspend "backend_wf") >>
  (reverse conj_tac >-
    (irule alloca_frame_same >> simp[sstore_def,tstore_def])) >>
  suspend "backend_ghost"
QED

Resume body_assign_empty_place_joint[backend_wf]:
  markerLib.RESUME_TAC >>
  `regions_consistent (FST H)` by fs[valid_horizon_def] >>
  `well_formed_type_value dtv` by metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `value_has_type dtv (default_value dtv)` by
    (drule vyperTypeDefaultsTheory.default_value_has_type_thm >> simp[]) >>
  drule_all body_assign_observed_storage_write_wf >> simp[]
QED

Resume body_assign_empty_place_joint[backend_ghost]:
  markerLib.RESUME_TAC >>
  `s.vs_call_ctx.cc_address = cx.txn.target` by
    (drule stateRelProjTheory.stmt_state_rel_state_rel >> strip_tac >>
     drule stateRelProjTheory.state_rel_call_ctx_rel >>
     simp[loweringStateRelDefsTheory.call_ctx_rel_def]) >>
  qpat_assum `dead_lo_ok H _ _ _ _` (mp_then Any mp_tac body_assign_empty_backend_ghost) >>
  metis_tac[]
QED
Resume body_assign_empty_place_joint[immutable]:
  `ff.scopes = ee.scopes /\ ff.accounts = ee.accounts /\ ff.tStorage = ee.tStorage` by
    (drule write_immutable_place_frame >> strip_tac >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by simp[] >>
  `(t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s` by
    (qpat_assum `(t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _;
       vs_immutables := _|>) = s`
       (mp_tac o AP_TERM ``\u:venom_state.
          u with <|vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb|>``) >>
     simp[]) >>
  (conj_tac >- (drule_all immutable_assign_empty_store_restore >> simp[])) >>
  (conj_tac >- (simp[storage_well_formed_on_backends] >> (metis_tac[storage_well_formed_on_backends]))) >>
  (reverse conj_tac >-
    (`32 <= type_memory_size dtv` by
       (qpat_assum `evaluate_type _ _ = _` (mp_then Any mp_tac place_store_empty_representation) >>
        disch_then (qspecl_then [`w2n w`,`t.vs_memory`] mp_tac) >> simp[]) >>
     drule_all immutable_assign_header_alloca_frame >> simp[])) >>
  (* Restore with the old immutable taint, then use the actual cleared set. *)
  `ghost_inv_at (DF H) lo d cenv cx ff Gf (tf with t_imm := tn.t_imm) t` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx ee s`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _`) mp_tac body_assign_empty_immutable_ghost) >>
     disch_then irule >>
     simp[ptrDisciplineTheory.op_taint_def, pred_setTheory.DIFF_SUBSET, SF SFY_ss] >>
     (conj_tac >- (qexistsl_tac [`env`,`id`,`w2n w`,`dtv`,`dty`] >> simp[])) >>
     qexistsl_tac [`G`,`sa`,`tn`] >> fs[ptrDisciplineTheory.op_taint_def]) >>
  `tf.t_imm SUBSET tn.t_imm` by
    simp[ptrDisciplineTheory.key_update_def, pred_setTheory.SUBSET_DEF,
         pairTheory.FORALL_PROD] >>
  qpat_x_assum `tf.t_imm = key_update _ _ _` kall_tac >>
  drule body_assign_ghost_imm_decrease >>
  disch_then (qspec_then `tf.t_imm` mp_tac) >> simp[]
QED
Finalise body_assign_empty_place_joint[local]

Theorem body_assign_empty_target_typing[local]:
  type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' ==>
  well_typed_expr env e /\ assignable_type env.type_defs (expr_type e) /\
  ?dty. type_place_target env t = SOME (Type dty) /\
        type_widens_to env.type_defs (expr_type e) dty
Proof
  simp[Once type_stmt_def, atarget_accepts_def] >>
  Cases_on `type_place_target env t` >> simp[] >>
  rename1 `type_place_target env t = SOME vt` >> Cases_on `vt` >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[]
QED

Theorem body_assign_empty_target_widths[local]:
  !t. alloc_limits_target cenv t /\
      ~supported_target_exists
        (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ (array_slot_base cenv e \/ alloc_limits_expr cenv e))) t ==>
      byte_widths_target t
Proof
  recInduct base_assignment_target_induct >>
  simp[byte_widths_expr_def, alloc_limits_expr_def, supported_expr_exists_def] >>
  rpt strip_tac >> CCONTR_TAC >>
  qpat_x_assum `~supported_expr_exists _ e` mp_tac >> simp[] >>
  irule supported_expr_exists_root >>
  metis_tac[allocLimitsPropsTheory.alloc_limits_expr_not_extcode]
QED

Theorem body_assign_empty_target_no_const[local]:
  body_inv tops ctx cenv cx /\ stmt_exprs_ok cenv (Assign (BaseTarget t) e) ==>
  ~supported_target_exists (const_name_root cx) t
Proof
  strip_tac >> drule_all body_inv_stmt_const_name_free >>
  simp[supported_stmt_expr_exists_def, supported_assignment_exists_def]
QED

Theorem body_assign_target_indices_pre[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget t) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (BaseTarget t) e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\ type_place_target env t = SOME (Type dty) /\
  stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) ==>
  target_indices_pre cenv cx env t
Proof
  strip_tac >>
  `supported_target tops bindings t` by
    fs[Once supported_stmt_def, supported_assignment_def] >>
  `~supported_target_exists expr_evm_run_root t /\
   EVERY (\c. FST c = NONE /\
              IS_SOME (supported_function_decl tops c Internal)) (int_calls_target t)` by
    (mp_tac (Q.SPECL [`tops`, `bindings`, `t`]
        bodyStorageCasesTheory.supported_target_info_main_calls) >>
     `IS_SOME (type_place_target env t)` by simp[] >>
     drule_all_then assume_tac body_inv_typed_target_calls_main >>
     Cases_on `t` >>
     gvs[supported_target_def, supported_expr_exists_def, int_calls_expr_def,
         EVERY_MEM] >> metis_tac[]) >>
  drule_all body_assign_empty_target_no_const >> strip_tac >>
  `cx_tops cx = tops` by drule_then (ACCEPT_TAC o cj 2) body_inv_main_code >>
  drule_then strip_assume_tac body_inv_main_support >>
  drule_then assume_tac body_assign_main_type_env >>
  irule popTargetPreTheory.target_indices_pre_of_body >>
  gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, alloc_limits_stmt_def, alloc_limits_assignment_def,
      int_calls_stmt_def, int_calls_atarget_def] >>
  rpt conj_tac
  >- (irule body_assign_empty_target_widths >> qexists_tac `cenv` >> simp[])
  >- metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem body_assign_empty_target_pre[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget t) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (BaseTarget t) e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\ type_place_target env t = SOME (Type dty) /\
  stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
  ~immutable_root cx t ==>
  target_pre cenv cx env t es
Proof
  strip_tac >> simp[target_pre_def] >>
  drule_all_then ACCEPT_TAC body_assign_target_indices_pre
QED

(* The empty read changes neither state; its certificate prefix has no marks. *)
Theorem body_assign_empty_target_source[local]:
  expr_body_pre cenv cx env e es /\ is_empty_value_expr e /\
  has_length_word (expr_type e) /\
  type_widens_to env.type_defs (expr_type e) dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ ~s.vs_halted /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (eval_target_place cx t) (\p. write_place cx p (default_value dtv)))
    (es,s,G,tn) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_stmt cx (Assign (BaseTarget t) e)) (es,s,G,tn) Q R
Proof
  strip_tac >>
  drule_all assignPlaceEmptyTheory.assign_place_empty_source_action >>
  disch_then (qspec_then `t` assume_tac) >>
  irule (Q.INST_TYPE [`:'a` |-> `:unit`]
    gasOutcomeFullStmtsTheory.gas_outcome_full_handler_transport) >>
  qexistsl [`Q`,`R`,`es`,
            `bind (eval_target_place cx t) (\p. write_place cx p (default_value dtv))`] >>
  simp[] >> rpt conj_tac
  >~ [`gas_bad_storage_at _ _ _ _ _ _`]
  >- simp[gas_bad_storage_at_def]
  >~ [`gas_origin_ptr_path _ _ _ _`]
  >- (rpt gen_tac >> strip_tac >> qexistsl [`marks`,`res`,`ee`,`r`,`G'`,`tn'`] >> simp[]) >>
  rpt strip_tac >> qexistsl [`err`,`ee`] >>
  `gas_marked_exec T (ctx,func) (vyperState$bind (eval_expr cx e) (read_result cx))
     (es,s) [] (INL (default_value dtv)) es (OK s)` by
    (drule_all immutable_assign_empty_read >>
     simp[gasSummaryTheory.gas_marked_exec_def, gasSummaryTheory.gas_explicit_def,
          gas_marked_path_def, fragGasPathMemTheory.gas_path_mem_rules] >>
     metis_tac[]) >>
  `ignore_bind (eval_stmt cx (Assign (BaseTarget t) e)) (return ()) =
   vyperState$bind (vyperState$bind (eval_expr cx e) (read_result cx))
     (\v. ignore_bind (vyperState$bind (eval_target_place cx t) (\p. write_place cx p v))
                        (return ()))` by
    simp[Once evaluate_def, ignore_bind_def, bind_assoc] >>
  pop_assum SUBST1_TAC >>
  drule gas_exempt_cert_bind_value >> simp[] >> disch_then irule >>
  drule gas_exempt_cert_start_gas_obs >> simp[]
QED

(* Switch from the actual target endpoint to the default-value write. *)
Theorem body_assign_empty_target_bind[local]:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_target_place cx target) (es,s,G,tn) P X /\
  (!H res mid G1 tn1 t. P H res mid G1 tn1 t ==> ?p. res = INL p) /\
  (!H res mid gt r. X H res mid gt r ==>
    ?ex. res = INR ex /\ R H (INR ex) mid gt r) /\
  (!marks p mid G1 tn1 t.
    (!tail. eval_target_place cx target
       (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL p,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    ~t.vs_halted /\ mid.gas_obs = [] /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> P H (INL p) mid G1 tn1 t) ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
      (write_place cx p v) (mid,t,G1,tn1) Q R) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_target_place cx target) (\p. write_place cx p v)) (es,s,G,tn) Q R
Proof
  strip_tac >> irule gas_outcome_full_bind_all >> BETA_TAC >> rpt conj_tac
  >- simp[storage_trace_frame_write_place]
  >~ [`storage_trace_frame (eval_target_place _ _)`]
  >- simp[cj 8 evaluate_storage_trace_frame]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_place >>
      qexistsl_tac [`mid`,`t`,`v'`] >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_place >> simp[]) >>
  qexists_tac `\H res mid G1 tn1 t. P H res mid G1 tn1 t /\ ~t.vs_halted /\ mid.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  `?p. res = INL p` by metis_tac[] >>
  disj1_tac >> qexists_tac `p` >> gvs[] >>
  first_x_assum irule >> conj_tac >- (qexists_tac `marks` >> simp[]) >>
  first_assum (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]
QED

Theorem body_assign_other_empty_target_full[local]:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    struct_args_unique tops /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              is_word_type ty) /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              ~is_word_type ty /\
              (expr_type e = ty \/ lowered_value_type cenv e = ty \/
               is_bytestring_type ty \/
               has_length_word (expr_type e) /\ is_empty_value_expr e)) /\
    ~(?nsid dty. t = TopLevelNameTarget nsid /\
          supported_scalar_target tops nsid /\
          type_place_target env t = SOME (Type dty) /\ is_word_type dty) /\
    ~(?nsid mut ty slot.
        t = TopLevelNameTarget nsid /\
        supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
        (mut = Storage \/ mut = Transient) /\
        ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
        ~is_bytestring_type ty /\
        0 < type_memory_bytes cenv ty /\ expr_type e = ty /\
        lowered_value_type cenv e = expr_type e) /\
    ~(?id fld sid fty.
        t = AttributeTarget (NameTarget id) fld /\
        FLOOKUP env.var_types id = SOME (StructT sid) /\
        attribute_type env.type_defs (StructT sid) fld = SOME fty /\
        is_word_type fty) /\
    ~(?nsid fld fty.
        t = AttributeTarget (TopLevelNameTarget nsid) fld /\
        supported_storage_field_write tops nsid fld /\
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) /\
    has_length_word (expr_type e) /\ is_empty_value_expr e /\ ~immutable_root cx t ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e)))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule body_assign_empty_target_typing >> strip_tac >>
  drule_all body_assign_empty_target_rhs_pre >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv` by
    (drule expr_body_pre_type_evaluates >> simp[IS_SOME_EXISTS]) >>
  `?dtv. evaluate_type (get_tenv cx) dty = SOME dtv` by
    (fs[type_widens_to_def, well_formed_type_def] >> metis_tac[IS_SOME_EXISTS]) >>
  `body_base_target_full_ok cx t` by
    (drule_all immutable_assign_empty_read >>
     disch_then (qspec_then `es.gas_obs` mp_tac) >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all body_assign_empty_target_pre >> strip_tac >>
  simp[stmt_frag_full_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all assignPlacePureCodeTheory.assign_place_pure_empty_code >> strip_tac >>
  `stmt_env (gas_shadow_env T cenv) lctx ret_ty
      (Assign (BaseTarget (gas_shadow_target t)) (gas_shadow_expr e)) shadow_sa =
      (gas_shadow_env T cenv',shadow_sb)` by
    fs[gas_shadow_stmt_def, gas_shadow_assignment_def] >>
  `?shadow_sp. compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
      (gas_shadow_target t) shadow_sa = (tr,shadow_sp) /\
      gas_shadow_state st shadow_sp` by
    (`FST (compile_get_target_ptr compile_expr cenv t sa) =
       FST (compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
         (gas_shadow_target t) shadow_sa) /\
       gas_shadow_state (SND (compile_get_target_ptr compile_expr cenv t sa))
         (SND (compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
           (gas_shadow_target t) shadow_sa))` by
       (irule (REWRITE_RULE [gas_shadow_compiles_def]
          (Q.INST [`sd` |-> `T`] gas_shadow_stmt_get_target_ptr_env)) >> simp[]) >>
     Cases_on `compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
       (gas_shadow_target t) shadow_sa` >> gvs[]) >>
  `compile_store_at_loc cenv.ce_imm_alloca (FST tr) (Lit 0w) (FST (SND tr))
      shadow_sp = ((),shadow_sb)` by
    (qpat_assum `stmt_env _ _ _ (Assign (BaseTarget (gas_shadow_target _)) _) _ = _`
       (mp_then Any mp_tac assignPlacePureCodeTheory.assign_place_pure_empty_code) >>
     simp[]) >>
  gvs[] >>
  `ci_mono sa st /\ ci_mono shadow_sa shadow_sp` by
     metis_tac[ci_mono_compile_get_target_ptr, pairTheory.SND] >>
  `ci_mono st sb /\ ci_mono shadow_sp shadow_sb` by
     metis_tac[cj 2 ci_mono_stmt_helpers, pairTheory.SND] >>
  `fn_has_code sa st func /\ fn_has_code st sb func /\
   fn_has_code shadow_sa shadow_sp shadow_func` by
     metis_tac[ci_mono_def, fn_has_code_split] >>
  `gas_admissible (eval_target_place cx t) target_place_res_ok es` by
     metis_tac[assignPlaceEmptyComposeTheory.assign_place_empty_target_admissible] >>
  drule_all bodyFullTargetTheory.body_target_place_sim_full >>
  disch_then (qspecl_then [`DF`,`lo`,`d`,`PG`,`func`,`shadow_func`]
    (mp_tac o REWRITE_RULE [target_place_sim_full_def])) >>
  disch_then (qspecl_then [`st0`,`dty`,`sa`,`st`,`shadow_sa`,`shadow_sp`,`tr`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> fs[ret_pc_ok_def] >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  irule assign_return_buf_sep >> asm_rewrite_tac[] >>
  irule body_assign_empty_target_source >>
  simp[] >> qexistsl [`cenv`,`dtv`,`dty`,`env`] >> simp[] >>
  irule body_assign_empty_target_bind >>
  qpat_assum `gas_outcome_full _ _ _ _ (eval_target_place _ _) _ _ _` (irule_at Any) >>
  BETA_TAC >> reverse (rpt conj_tac)
  >- (rpt gen_tac >> Cases_on `res` >> simp[] >> strip_tac >>
      conj_tac >- (simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]) >>
      conj_tac >- metis_tac[halt_exit_INR_type] >>
      rpt strip_tac >> gvs[] >> fs[expr_exit_def])
  >- (rpt strip_tac >> qexists_tac `p` >> simp[]) >>
  suspend "write"
QED

Resume body_assign_other_empty_target_full[write]:
  qx_genl_tac [`marks`,`p`,`mid`,`G1`,`tn1`,`u`] >> simp[] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace`
      (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `eval_target_place cx t (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL p,mid)` by
    (qpat_assum `!tail. eval_target_place _ _ _ = _` (qspec_then `[]` mp_tac) >>
     `mid with gas_obs := [] = mid` by gvs[vyperStateTheory.evaluation_state_component_equality] >>
     qpat_assum `mid with gas_obs := [] = mid`
       (fn th => rewrite_tac[APPEND_NIL,th])) >>
  `expr_sim_inv cenv cx env mid` by
    (irule bodySimAugPlaceLoadTheory.aug_place_target_inv >>
     goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
     simp[expr_sim_inv_gas_obs] >>
     qpat_assum `target_pre _ _ _ _ _`
       (ACCEPT_TAC o cj 3 o REWRITE_RULE [target_pre_def])) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_target_place_preserves_scopes_dom >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H (es with gas_obs := gas_explicit marks s0.vs_gas_readings).storage_trace`
       suffices_by simp[] >>
     qpat_assum `eval_target_place _ _ _ = _`
       (mp_then (Pos (el 2)) mp_tac valid_horizon_frame) >>
     simp[cj 8 evaluate_storage_trace_frame]) >>
  `alloca_frame cenv es sa s0 cenv mid u` by
    (qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then (Pos (el 1)) mp_tac target_post_alloca_frame) >>
     simp[] >> metis_tac[]) >>
  `!src id path. p <> ImmutablePlace src id path` by
    (rpt strip_tac >> gvs[] >>
     drule tuplePlaceSourceHeadTheory.tuple_place_target_base_inversion >>
     metis_tac[aug_place_base_immutable_origin]) >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [target_post_def]) >>
  pop_assum kall_tac >>
  qpat_x_assum `?w. eval_operand _ u = SOME w /\ _`
    (qx_choose_then `w` strip_assume_tac) >>
  `?dst loc. tr = (dst,SOME loc,SOME (ValPT dty)) /\
             loc <> LocCode /\ loc <> LocCalldata` by
    (qpat_assum `place_ptr_rel _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `SND (SND tr) = _` mp_tac >>
     qpat_assum `!src id path. p <> _` mp_tac >>
     rpt (pop_assum kall_tac) >> PairCases_on `tr` >>
     Cases_on `p` >> simp[place_ptr_rel_def,value_type_place_def]
     >- (rename1 `slot_loc transient` >> Cases_on `transient` >> simp[slot_loc_def]) >>
     rpt strip_tac >> qexists_tac `LocMemory` >> simp[]) >>
  qpat_x_assum `tr = (_,SOME _,SOME _)` SUBST_ALL_TAC >>
  gs[] >>
  `sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv st` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x` by
    metis_tac[not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x` by
    (fs[ret_pc_ok_def] >> metis_tac[not_fresh_at_mono]) >>
  `return_buf_frame d cenv st u` by
    (irule return_buf_frame_frame >>
     goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >> simp[]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace`
         (drule_then (map_every assume_tac o CONJUNCTS o
                      REWRITE_RULE [ghost_inv_at_def] o CONJUNCT2))) >>
     simp[]) >>
  `u.vs_call_ctx.cc_static = cx.txn.is_static` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ mid u`
       (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_state_rel) >>
     disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >> simp[call_ctx_rel_def]) >>
  `has_length_word dty` by metis_tac[type_widens_to_has_length_word] >>
  `op_taint tn1 dst = {}` by fs[target_ptr_ok_def] >>
  `~block_is_terminated st` by
    metis_tac[placeRelayoutOpenTheory.compile_get_target_ptr_endpoint_open] >>
  `~block_is_terminated sb` by
    (qpat_assum `compile_store_at_loc _ _ _ _ st = ((),sb)` mp_tac >>
     qpat_assum `loc <> LocCode` mp_tac >> qpat_assum `loc <> LocCalldata` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `loc` >> simp[compile_store_at_loc_def] >>
     disch_then (mp_tac o MATCH_MP exprOpenPrimitivesTheory.emit_void_terminated) >>
     simp[is_terminator_def]) >>
  Cases_on `write_place cx p (default_value dtv) mid` >>
  rename1 `write_place cx p (default_value dtv) mid = (wr,ff)` >>
  `!tail. write_place cx p (default_value dtv) (mid with gas_obs := tail) =
      (wr,ff with gas_obs := tail)` by
    metis_tac[placeRelayoutFragTheory.place_pointer_write_gas_obs] >>
  Cases_on `loc <> LocMemory /\ cx.txn.is_static`
  >- suspend "static" >>
  `stmt_res_ok lctx wr` by
    (`eval_stmt cx (Assign (BaseTarget t) e)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (wr,ff)` by
       (`eval_stmt cx (Assign (BaseTarget t) e)
           (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
         bind (eval_target_place cx t) (\p. write_place cx p (default_value dtv))
           (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
          (irule assignPlaceEmptyTheory.assign_place_empty_source_action >> simp[] >>
           qexistsl_tac [`cenv`,`dty`,`env`] >> simp[]) >>
        simp[bind_def]) >>
     metis_tac[gas_admissible_result]) >>
  `wr = INL ()` by
    (Cases_on `p`
     >- (qpat_x_assum `place_ptr_rel _ _ _ _ _ _ _` mp_tac >>
         simp[place_ptr_rel_def] >> strip_tac >> gvs[] >>
         `~cx.txn.is_static` by (Cases_on `b` >> gvs[slot_loc_def]) >>
         qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
         simp[write_place_def] >> strip_tac >>
         metis_tac[vyperStorageFrameTheory.write_storage_slot_succeeds,
                   vyperTypingTheory.default_value_well_typed, pairTheory.FST])
     >- metis_tac[placeRelayoutOutcomeTheory.memory_write_admissible_success] >>
     metis_tac[]) >>
  qpat_x_assum `wr = INL ()` SUBST_ALL_TAC >>
  suspend "normal"
QED

Resume body_assign_other_empty_target_full[static]:
  Cases_on `p` >> gvs[place_ptr_rel_def] >>
  rename1 `StoragePlace tr slot dtv` >>
  `emit_void (if tr then TSTORE else SSTORE) [dst; Lit 0w] st = ((),sb)` by
    (Cases_on `tr` >> gvs[slot_loc_def, compile_store_at_loc_def]) >>
  `wr = INR (Error (RuntimeError "write in static context")) /\ ff = mid` by
    (qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
     simp[write_place_def, vyperStorageBackendTheory.write_storage_slot_eq]) >>
  irule gas_outcome_full_exit >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G1`,`mid`,`Abort ExHalt_abort (halt_state (set_returndata [] u))`,
                `wr`,`tn1`] >>
  simp[exit_result_def] >> qx_gen_tac `H` >> strip_tac >>
  conj_tac
  >- (irule augAssignFullStoreTheory.storage_emit_static_origin_ptr >> simp[] >>
      goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >>
      simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def]) >>
  simp[stmt_exit_ptr_def, expr_exit_def, halt_exit_not_halt]
QED

Resume body_assign_other_empty_target_full[normal]:
  `ff.storage_trace = mid.storage_trace` by
    (drule write_place_storage_trace >> simp[]) >>
  `ff with gas_obs := [] = ff` by
    (`mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. write_place _ _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_x_assum `mid with gas_obs := [] = mid` (rewrite_tac o single) >>
     qpat_assum `write_place _ _ _ mid = _` (rewrite_tac o single) >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid u /\
       storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 u /\
       dead_lo_ok H (DF H) lo cenv cx /\ storage_place_observed H p` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> target_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then (CONJUNCTS_THEN2
          (map_every assume_tac o CONJUNCTS o REWRITE_RULE [target_post_def])
          assume_tac))) >> simp[] >>
     Cases_on `p` >> simp[storage_place_observed_def] >>
     irule (REWRITE_RULE [storage_place_observed_def]
       stmtSimAugAssignPlaceStorageTheory.aug_place_target_observed) >>
     simp[] >>
     qexistsl_tac [`cx`,`es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                   `mid`,`st0`,`t`] >> simp[]) >>
  `!id path entry t0. p = MemoryPlace id path /\
       lookup_scopes id mid.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (drule_then (qspec_then `p` assume_tac)
       (GEN_ALL stmtSimAugAssignPlaceMemoryTheory.aug_place_store_entry_types) >>
     simp[]) >>
  `loc = LocMemory ==> lo <= w2n w /\ ?x. dst = Var x /\
      ptr_covers G1 tn1 x u 32 /\ w2n w + 32 <= u.vs_alloca_next` by
    suspend "memory_header" >>
  suspend "normal_tail"
QED

Resume body_assign_other_empty_target_full[memory_header]:
  disch_then SUBST_ALL_TAC >>
  `32 <= type_memory_size dtv` by
    (`mem_word_at 0 (REPLICATE 32 (0w:word8)) = 0w` by
       (EVAL_TAC >> simp[]) >>
     qpat_assum `evaluate_type _ dty = SOME dtv`
       (mp_then Any mp_tac place_store_empty_representation) >>
     disch_then (qspecl_then [`0`,`REPLICATE 32 (0w:word8)`] mp_tac) >> simp[]) >>
  drule_all placeMemoryLiveRegionTheory.memory_place_live_region >> strip_tac >>
  `0 < len` by decide_tac >>
  `lo <= b` by
    (irule (INST_TYPE [Type.alpha |-> ``:256``] body_full_local_region_lower_bound) >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >> simp[] >>
     qexistsl_tac [`DF (storage_trace_horizon mid.storage_trace)`,
       `storage_trace_horizon mid.storage_trace`,`ctx`,`cx`,`env`,`mid`,`func`,`tops`] >> simp[]) >>
  `b + len <= u.vs_alloca_next` by
    (irule (INST_TYPE [Type.alpha |-> ``:256``] body_local_region_frontier) >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >> metis_tac[]) >>
  conj_tac >- decide_tac >>
  `w2n w + 32 <= u.vs_alloca_next` by decide_tac >> simp[] >>
  suspend "memory_coverage"
QED

Resume body_assign_other_empty_target_full[memory_coverage]:
  qpat_x_assum `place_ptr_rel _ _ u (PlaceR p) _ _ _` mp_tac >>
  namedCases_on `p` ["tr slot tv", "id path", "src name0 path0"] >> simp[place_ptr_rel_def]
  >- (Cases_on `tr` >> simp[slot_loc_def])
  >- (disch_then (qx_choosel_then [`memroot`,`memcap`,`memaddr`,`memty`,`memtv`,`memoff`]
                    (map_every assume_tac o CONJUNCTS)) >>
      qpat_assum `!id' path'. MemoryPlace id path = _ ==> _`
        (qspecl_then [`id`,`path`] mp_tac) >>
      rewrite_tac[] >>
      disch_then (qx_choosel_then [`mementry`,`memval`] strip_assume_tac) >>
      `mementry.type = memtv` by
        (qpat_assum `!id' path' entry t0. MemoryPlace id path = _ /\ _ /\ _ ==> _`
           (qspecl_then [`id`,`path`,`mementry`,`memty`] mp_tac) >> gvs[]) >>
      `w2n memaddr + memcap <= u.vs_alloca_next /\ type_memory_size memtv <= memcap` by
        (qpat_assum `stmt_state_rel _ _ _ _ _ mid u`
          (mp_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
         disch_then (mp_tac o CONJUNCT1 o REWRITE_RULE [local_ptrs_rel_def] o CONJUNCT1) >>
         disch_then (qspecl_then [`id`,`mementry`,`memroot`,`memcap`] mp_tac) >> simp[] >> metis_tac[SOME_11]) >>
      `memoff + type_memory_size dtv <= type_memory_size memtv` by metis_tac[mem_path_offset_sound] >>
      `u.vs_alloca_next < dimword (:256)` by
        metis_tac[stateRelProjTheory.stmt_state_rel_alloca_room,alloca_room_next_lt] >>
      `w2n w = w2n memaddr + memoff` by
        (pure_asm_rewrite_tac[] >> irule buffer_offset_no_wrap >>
         qexists_tac `memcap` >> decide_tac) >>
      `ptr_covers G1 tn1 memroot u memcap` by
        (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _ /\ ghost_inv_at _ _ _ _ _ _ _ _ _ /\ _`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         disch_then (mp_tac o CONJUNCT1 o REWRITE_RULE [ghost_inv_at_def] o cj 3) >>
         disch_then (qspecl_then [`id`,`mementry`,`memroot`,`memcap`] mp_tac) >> simp[]) >>
      `op_prov G1 dst = FLOOKUP G1 memroot` by
        (qpat_assum `target_ptr_ok _ _ _ _ _ _`
           (qspecl_then [`id`,`path`,`memroot`,`memcap`] mp_tac o
            cj 2 o REWRITE_RULE [target_ptr_ok_def]) >> simp[]) >>
      qpat_x_assum `ptr_covers _ _ _ _ _`
        (mp_tac o CONJUNCT2 o REWRITE_RULE [ptr_covers_def]) >>
      disch_then (qx_choosel_then [`memword`,`provbase`,`provsize`] strip_assume_tac) >>
      Cases_on `dst` >> gvs[op_prov_def,venomStateTheory.eval_operand_def,ptr_covers_def] >>
      qexistsl_tac [`provbase`,`provsize`] >> simp[] >> decide_tac) >>
  metis_tac[]
QED

Resume body_assign_other_empty_target_full[normal_tail]:
  `((loc = LocStorage \/ loc = LocTransient) ==> ~cx.txn.is_static)` by
    (Cases_on `loc` >> gvs[]) >>
  mp_tac (Q.INST [`sa` |-> `st`, `sa0` |-> `sa`, `s` |-> `u`,
      `ee` |-> `mid`, `es0` |-> `es`, `G` |-> `G1`, `tn` |-> `tn1`,
      `imm` |-> `cenv.ce_imm_alloca`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (SPEC_ALL body_assign_empty_place_joint)) >>
  (impl_tac >- (simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
                qexists_tac `storage_trace_horizon mid.storage_trace` >> simp[])) >>
  disch_then (qx_choosel_then [`sf`,`Gf`,`tnf`] (map_every assume_tac o CONJUNCTS)) >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`,`ff`,`INL ()`,`sf`,`tnf`] >> simp[] >>
  qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H ff.storage_trace` by simp[] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ Gf tnf`
    (assume_tac o CONJUNCT1 o REWRITE_RULE [ghost_kept_at_def]) >>
  simp[stmt_lands_def,cenv_top_ext_refl] >>
  first_assum ACCEPT_TAC
QED

Finalise body_assign_other_empty_target_full[local]

Theorem body_assign_other_empty_immutable_full[local]:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    struct_args_unique tops /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              is_word_type ty) /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              ~is_word_type ty /\
              (expr_type e = ty \/ lowered_value_type cenv e = ty \/
               is_bytestring_type ty \/
               has_length_word (expr_type e) /\ is_empty_value_expr e)) /\
    ~(?nsid dty. t = TopLevelNameTarget nsid /\
          supported_scalar_target tops nsid /\
          type_place_target env t = SOME (Type dty) /\ is_word_type dty) /\
    ~(?nsid mut ty slot.
        t = TopLevelNameTarget nsid /\
        supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
        (mut = Storage \/ mut = Transient) /\
        ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
        ~is_bytestring_type ty /\
        0 < type_memory_bytes cenv ty /\ expr_type e = ty /\
        lowered_value_type cenv e = expr_type e) /\
    ~(?id fld sid fty.
        t = AttributeTarget (NameTarget id) fld /\
        FLOOKUP env.var_types id = SOME (StructT sid) /\
        attribute_type env.type_defs (StructT sid) fld = SOME fty /\
        is_word_type fty) /\
    ~(?nsid fld fty.
        t = AttributeTarget (TopLevelNameTarget nsid) fld /\
        supported_storage_field_write tops nsid fld /\
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) /\
    has_length_word (expr_type e) /\ is_empty_value_expr e /\ immutable_root cx t /\
    (?nsid. t = TopLevelNameTarget nsid) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e)))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac body_assign_immutable_supported >>
  qpat_x_assum `t = TopLevelNameTarget _` SUBST_ALL_TAC >>
  rename1 `supported_immutable_type tops nsid = SOME ity` >> PairCases_on `nsid` >>
  rename1 `supported_immutable_type tops (src,id) = SOME ity` >>
  drule_all_then strip_assume_tac body_assign_immutable_typed >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    qpat_assum `body_inv tops ctx cenv cx` (ACCEPT_TAC o assign_main_keys) >>
  `get_module_code cx NONE = SOME tops /\
   env_context_consistent env cx` by
    (drule_then (assume_tac o cj 1) body_inv_main_code >>
     fs[expr_sim_inv_def, env_consistent_def]) >>
  `env.type_defs = get_tenv cx` by fs[env_context_consistent_def] >>
  `supported_expr tops e` by
    fs[Once supported_stmt_def, supported_assignment_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule bodyMemAssignTopCopyFactsTheory.topcopy_rhs_pre_supported >> metis_tac[]) >>
  `assignable_type (get_tenv cx) ity` by
    metis_tac[vyperTypeArgFitsTheory.type_widens_to_assignable_type] >>
  `?tv. evaluate_type (get_tenv cx) ity = SOME tv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def,
              optionTheory.IS_SOME_EXISTS] >>
  `has_length_word ity` by
    metis_tac[memoryLocalRhsPropsTheory.type_widens_to_has_length_word] >>
  drule_all immutableAssignMetadataTheory.immutable_assign_bare_global >> strip_tac >>
  qpat_x_assum `src = NONE` SUBST_ALL_TAC >>
  drule_all immutable_assign_target_layout >>
  disch_then (qspec_then `compile_expr` strip_assume_tac) >>
  `type_widens_to env.type_defs (expr_type e) ity` by simp[] >>
  drule_all immutable_assign_empty_source >> strip_tac >>
  simp[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_initial_domain >>
  simp[cj 1 vyperStorageTraceTheory.evaluate_storage_trace_frame] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `compile_get_target_ptr compile_expr cenv (TopLevelNameTarget (cenv.ce_module,id)) =
    comp_return (Lit (n2w off),SOME LocCode,SOME (ValPT ity))` by metis_tac[] >>
  drule_all immutableAssignCodeTheory.immutable_assign_empty_code >> strip_tac >>
  irule assign_return_buf_sep >> asm_rewrite_tac[] >>
  `cx_tops cx = tops` by metis_tac[gasContextTheory.cx_tops_module] >>
  `get_tenv cx = type_env tops /\ cenv.ce_module_var_type = build_var_type_map tops` by
    (drule_then assume_tac body_assign_main_type_env >>
     drule_then (strip_assume_tac o REWRITE_RULE [cenv_module_pins_def])
       intcall_args_body_inv_pins >> simp[]) >>
  `?pre post vis ty slot.
    tops = pre ++ VariableDecl vis Immutable id ty slot :: post /\
    off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre` by
    (drule body_inv_immutable_section_layout >>
     simp[immutableRelationTheory.immutable_section_layout_def] >> metis_tac[]) >>
  `ty = ity` by
    (`MEM (VariableDecl vis Immutable id ty slot) tops` by simp[] >>
     drule_all bodyStorageMetadataTheory.build_maps_variable >> strip_tac >>
     qpat_assum `cenv.ce_module_var_type = _` (fn th =>
       qpat_assum `cenv.ce_module_var_type (NONE,id) = SOME _`
         (mp_tac o REWRITE_RULE [th])) >>
     qpat_assum `build_var_type_map tops (NONE,id) = SOME ty`
       (fn th => simp[NoAsms, th])) >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ity = type_memory_size tv` by
    (irule ctorDeployDeadSectionFrameTheory.imm_frame_size >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `get_tenv cx = _` (fn th =>
       qpat_assum `evaluate_type (get_tenv cx) ity = SOME tv`
         (ACCEPT_TAC o REWRITE_RULE [th]))) >>
  `off + type_memory_size tv <= imm_len tops` by
    (rewrite_tac[immSectionDeadTheory.imm_len_def] >>
     qpat_assum `tops = _`
       (fn th => CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV th)))) >>
     qpat_assum `off = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `ty = ity` (fn th => rewrite_tac[th]) >>
     qpat_assum `type_mem_bytes _ ity = _` (fn th =>
       simp[NoAsms,th,compileVyperTheory.compute_immutables_len_append,
            compileVyperTheory.compute_immutables_len_def])) >>
  `32 <= type_memory_size tv` by
    (qspec_then `get_tenv cx` mp_tac stmtSimDeclMemTheory.memory_length_word_layout >>
     disch_then (qspecl_then [`ity`,`tv`,`off`,`(mstore off 0w s0).vs_memory`] mp_tac) >>
     simp[valueEncodingPropsTheory.mstore_mem_word_at_same]) >>
  `lo = imm_len tops` by fs[bodyPtrDefsTheory.dead_lo_ok_def] >>
  `off + type_memory_size tv < dimword (:256)` by simp[] >>
  `off + 32 <= lo /\ off < dimword (:256) /\ lo <> 0` by decide_tac >>
  `w2n (n2w off : bytes32) = off` by simp[wordsTheory.w2n_n2w_compute] >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >> simp[]) >>
  `!reg. cenv.ce_imm_alloca = SOME reg ==>
      eval_operand reg s0 = SOME 0w /\ op_taint tn0 reg = {} /\ op_prov G0 reg = NONE` by
    (gen_tac >> disch_tac >>
     conj_tac
     >- (qpat_assum `stmt_state_rel _ _ _ _ _ _ s0`
         (mp_tac o MATCH_MP stmt_state_rel_immutable_base_zero) >>
         simp[loweringStateRelDefsTheory.immutable_base_zero_def]) >>
     Cases_on `reg` >> simp[ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def] >>
     qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
       (mp_tac o cj 6 o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
     simp[ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `compile_imm_store_word cenv.ce_imm_alloca (Lit (n2w off)) (Lit 0w) sa = ((),sb)` by
    (qpat_x_assum `compile_store_at_loc _ _ _ _ _ = _` mp_tac >>
     simp[stmtLoweringTheory.compile_store_at_loc_def]) >>
  qabbrev_tac `D0 = <| d_stor := K (K {}); d_trans := K (K {});
                        d_imm := K {}; d_ret := K {} |> ` >>
  `?Gf tf u.
     run_inst_seq (emitted_insts sa sb) s0 = OK u /\
     (!k. inst_seq_ptr D0 lo ctx func PG G0 tn0 (emitted_insts sa sb)
            (s0 with vs_inst_idx := k) Gf tf) /\
     tf.t_mem = tn0.t_mem DIFF {i | off <= i /\ i < off + 32} /\
     tf.t_imm = key_update tn0.t_imm off {} /\
     tf.t_stor = tn0.t_stor /\ tf.t_trans = tn0.t_trans /\
     (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G0 p /\
            op_taint tf (Var p) = op_taint tn0 (Var p)) /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
     sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
     EVERY (\i. MEM i.inst_opcode [ADD;ISTORE]) (emitted_insts sa sb)` by
    (qpat_x_assum `off = compute_immutables_len _ _` kall_tac >>
     qpat_x_assum `lo = imm_len _` kall_tac >>
     Cases_on `cenv.ce_imm_alloca`
     >- (qpat_assum `compile_imm_store_word _ _ _ _ = _`
           (mp_tac o REWRITE_RULE [compile_imm_store_word_no_base]) >>
         disch_tac >>
         drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
         mp_tac (Q.INST [`arg` |-> `Lit (n2w off)`, `v` |-> `Lit 0w`,
                          `a` |-> `n2w off`, `value` |-> `0w`,
                          `s` |-> `s0`, `tn` |-> `tn0`, `G` |-> `G0`,
                          `id` |-> `sa.cs_next_id`, `D` |-> `D0`,
                          `fn` |-> `func`] exprPtrCtorImmStoreTheory.ctor_istore_segment) >>
         simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def,
              ptrDisciplineTheory.op_prov_def] >>
         strip_tac >>
         qexistsl [`Gf`, `tnf`, `istore off 0w s0`] >>
         simp[] >> simp[venomInstTheory.mk_inst_def] >>
         metis_tac[]) >>
     rename1 `cenv.ce_imm_alloca = SOME region` >>
     drule compile_imm_store_word_result >> strip_tac >>
     qmatch_asmsub_abbrev_tac `mk_inst _ ADD _ [tmp]` >>
     `~not_fresh_at sa tmp` by
       simp[Abbr `tmp`, loweringStateRelDefsTheory.not_fresh_at_def] >>
     `emitted_insts sa sb = [mk_inst sa.cs_next_id ADD [region; Lit (n2w off)] [tmp];
         mk_inst (sa.cs_next_id + 1) ISTORE [Var tmp; Lit 0w] []]` by
       simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
     `eval_operand region s0 = SOME 0w /\ op_taint tn0 region = {} /\
      op_prov G0 region = NONE` by simp[] >>
     mp_tac (Q.INST [`region` |-> `region`, `dst` |-> `Lit (n2w off)`,
                     `v` |-> `Lit 0w`, `a` |-> `n2w off`, `value` |-> `0w`,
                     `s` |-> `s0`, `tn` |-> `tn0`, `G` |-> `G0`,
                     `id` |-> `sa.cs_next_id`, `D` |-> `D0`, `fn` |-> `func`,
                     `P` |-> `not_fresh_at sa`, `tmp` |-> `tmp`] exprPtrCtorImmStoreTheory.ctor_word_store_seq) >>
     simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def,
          ptrDisciplineTheory.op_prov_def] >> strip_tac >>
     qexistsl [`Gf`, `tnf`, `istore off 0w (update_var tmp (n2w off) s0)`] >>
     simp[] >> simp[venomInstTheory.mk_inst_def]) >>
  `(!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s0) /\
   (u with <|vs_vars := s0.vs_vars; vs_memory := s0.vs_memory;
              vs_immutables := s0.vs_immutables|>) = s0 /\
   u.vs_memory = (mstore off 0w s0).vs_memory /\
   u.vs_immutables = s0.vs_immutables |+ (off,0w)` by
    (drule immutableDeployOperandTransferTheory.immutable_store_word_old_execution >>
     disch_then (qspecl_then [`0w`,`s0`,`n2w off`] mp_tac) >>
     simp[venomStateTheory.eval_operand_def, IgnAsm `off = compute_immutables_len _ _`] >>
     metis_tac[]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\ ~block_is_terminated sb` by
    (qpat_assum `compile_imm_store_word _ _ _ _ = _` mp_tac >>
     Cases_on `cenv.ce_imm_alloca` >>
     simp[NoAsms, compile_imm_store_word_def, emitHelperTheory.emit_void_def,
          emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def, emit_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     disch_then (SUBST1_TAC o SYM) >>
     simp[block_is_terminated_def] >> Cases_on `sa.cs_current_insts` >>
     simp[listTheory.LAST_CONS_cond, listTheory.LAST_APPEND_CONS,
          arithmeticTheory.SUB_PLUS, venomInstTheory.mk_inst_def,
          venomInstTheory.is_terminator_def]) >>
  `?bb. lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s0.vs_inst_idx bb.bb_instructions)` by
    (drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
         (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[listTheory.EVERY_MEM, listTheory.FILTER_EQ_NIL] >>
     conj_tac >> gen_tac >> disch_tac >>
     qpat_assum `EVERY (\i. MEM i.inst_opcode _) _`
       (drule_then (strip_assume_tac o BETA_RULE) o REWRITE_RULE[listTheory.EVERY_MEM,listTheory.MEM]) >>
     simp[venomInstTheory.is_terminator_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s0` by
    (irule body_assign_immutable_word_mem_ok >>
     qexistsl [`cenv.ce_imm_alloca`,`off`,`Lit 0w`] >>
     simp[IgnAsm `off = compute_immutables_len _ _`] >> decide_tac) >>
  `ctx_has_dalloca ctx ==> !pre i post u'.
     emitted_insts sa sb = pre ++ i::post /\ run_inst_seq pre s0 = OK u' ==>
     dalloca_no_wrap i u'` by
    (rpt strip_tac >>
     qpat_assum `EVERY (\i. MEM i.inst_opcode [ADD; ISTORE]) _` mp_tac >>
     qpat_assum `emitted_insts _ _ = _ ++ _` (fn th => pure_rewrite_tac [th]) >>
     simp[EVERY_APPEND] >> strip_tac >>
     irule dalloca_no_wrap_non_dalloca >> simp[]) >>
  qabbrev_tac `q = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) [] (OK q,Gf,tf)` by
    (`inst_seq_ptr D0 lo ctx func PG G0 tn0 (emitted_insts sa sb) s0 Gf tf` by
       (qpat_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
          (qspec_then `s0.vs_inst_idx` mp_tac) >> simp[NoAsms]) >>
     drule_all fragGasSeqPtrTheory.run_inst_seq_gas_origin_ptr_path >>
     disch_then (qspec_then `gas_explicit_sites ctx shadow_ctx` mp_tac) >>
     simp[Abbr `q`, Abbr `D0`, listTheory.LENGTH_APPEND] >>
     metis_tac[fragGasOriginPtrDeadTheory.gas_origin_ptr_path_from_no_dead]) >>
  `ee.scopes = es.scopes /\ ee.storage_trace = es.storage_trace /\
   ee.accounts = es.accounts /\ ee.tStorage = es.tStorage` by
    (drule vyperPlaceFramesTheory.write_immutable_place_frame >> strip_tac >> simp[]) >>
  `q.vs_memory = (mstore off 0w s0).vs_memory` by
    simp[Abbr `q`, IgnAsm `off = compute_immutables_len _ _`] >>
  `(!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s0) /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp q)` by
    (conj_tac
     >- (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _` mp_tac >>
         simp[NoAsms, Abbr `q`, venomStateTheory.lookup_var_def]) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u` mp_tac >>
     simp[NoAsms, Abbr `q`, ptrDisciplineTheory.allocas_below_fmp_def] >> metis_tac[]) >>
  `q.vs_allocas = s0.vs_allocas /\ q.vs_alloca_next = s0.vs_alloca_next /\
   q.vs_current_bb = s0.vs_current_bb /\ ~q.vs_halted /\
   (q with <|vs_vars := s0.vs_vars; vs_memory := s0.vs_memory;
      vs_immutables := s0.vs_immutables; vs_prev_bb := s0.vs_prev_bb;
      vs_current_bb := s0.vs_current_bb; vs_inst_idx := s0.vs_inst_idx|>) = s0` by
    (qpat_assum `u with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = s0` mp_tac >>
     simp[Abbr `q`, venomStateTheory.venom_state_component_equality]) >>
  `alloca_history func q` by
    (`?rest. DROP s0.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
       metis_tac[rich_listTheory.IS_PREFIX_APPEND] >>
     `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
       (simp[listTheory.EVERY_MEM] >> gen_tac >> disch_tac >>
        qpat_assum `EVERY (\i. MEM i.inst_opcode _) _`
          (drule_then (strip_assume_tac o BETA_RULE) o REWRITE_RULE[listTheory.EVERY_MEM,listTheory.MEM]) >>
        simp[]) >>
     drule_all bodyBinopFragMemoryTheory.alloca_history_no_alloca_slice >>
     simp[Abbr `q`, listTheory.LENGTH_APPEND]) >>
  `return_buf_frame d cenv sb q` by
    (`ci_mono sa sb` by
       (qpat_assum `compile_imm_store_word _ _ _ sa = ((),sb)` (fn th =>
         qspecl_then [`cenv.ce_imm_alloca`,`Lit (n2w off)`,`Lit 0w`,`sa`] mp_tac
           exprLoweringPropsTheory.ci_mono_compile_imm_store_word >> simp[NoAsms, th])) >>
     qpat_assum `return_buf_frame d cenv sa s0`
       (mp_then Any irule bodyMemoryDefsTheory.return_buf_frame_frame) >>
     qpat_assum `ci_mono sa sb` (strip_assume_tac o REWRITE_RULE [exprLoweringPropsTheory.ci_mono_def]) >>
     simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[loweringPostsTheory.ret_pc_ok_def] >>
  `tf.t_mem SUBSET tn0.t_mem /\
   (!i. off <= i /\ i < off+32 ==> i NOTIN tf.t_mem)` by
    (qpat_assum `tf.t_mem = _ DIFF _` (fn th =>
       simp[NoAsms, th, pred_setTheory.DIFF_SUBSET, pred_setTheory.IN_DIFF])) >>
  rewrite_tac[gasOutcomeFullTheory.gas_outcome_full_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INL ()`,`ee`,`OK q`,`Gf`,`tf`] >>
  conj_tac
  >- (simp[gasSummaryTheory.gas_explicit_def] >> metis_tac[]) >>
  conj_tac >- simp[] >>
  qx_gen_tac `H` >> strip_tac >>
  conj_tac >- simp[] >>
  disj1_tac >> qexists_tac `q` >> BETA_TAC >>
  `valid_horizon cx st0 H es.storage_trace` by metis_tac[] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee q` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _`) irule
          immutableAssignEmptyTheory.immutable_assign_empty_store_restore) >>
     metis_tac[]) >>
  `alloca_frame cenv es sa s0 cenv ee q` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _`) irule
          immutableAssignEmptyTheory.immutable_assign_header_alloca_frame) >>
     metis_tac[]) >>
  `ghost_inv_at (DF H) lo d cenv cx ee Gf (tf with t_imm := tn0.t_imm) q` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _`) mp_tac body_assign_empty_immutable_ghost) >>
     disch_then irule >>
     simp[ptrDisciplineTheory.op_taint_def,
          IgnAsm `off = compute_immutables_len _ _`, IgnAsm `tops = _`,
          IgnAsm `lo = imm_len _`, IgnAsm `tf.t_mem = _ DIFF _`] >>
     conj_tac >- (qexists_tac `tops` >> simp[]) >>
     conj_tac >-
       (qexistsl_tac [`env`,`id`,`off`,`tv`,`ity`] >>
        simp[IgnAsm `off = compute_immutables_len _ _`, IgnAsm `tops = _`] >>
        metis_tac[]) >>
     qexistsl_tac [`G0`,`sa`,`tn0`] >>
     simp[IgnAsm `tf.t_mem = _ DIFF _`, IgnAsm `lo = imm_len _`] >>
     fs[ptrDisciplineTheory.op_taint_def]) >>
  `tf.t_imm SUBSET tn0.t_imm` by
    simp[ptrDisciplineTheory.key_update_def, pred_setTheory.SUBSET_DEF,
         pairTheory.FORALL_PROD] >>
  `ghost_inv_at (DF H) lo d cenv cx ee Gf tf q` by
    (qpat_x_assum `tf.t_imm = key_update _ _ _` kall_tac >>
     drule body_assign_ghost_imm_decrease >>
     disch_then (qspec_then `tf.t_imm` mp_tac) >> simp[IgnAsm `lo = imm_len _`]) >>
  `ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) Gf tf q` by
    (qpat_assum `ghost_inv_at (DF H) lo d cenv cx ee Gf tf q` mp_tac >>
     rewrite_tac[bodyPtrDefsTheory.ghost_inv_at_def,
                 vyperStateTheory.evaluation_state_accfupds]) >>
  `stmt_lands lctx sb (INL ()) q` by
    simp[loweringPostsTheory.stmt_lands_def, Abbr `q`] >>
  `storage_well_formed_on cx (ee with gas_obs := []) (FST H)` by
    (irule (iffRL vyperStorageFootprintTheory.storage_well_formed_on_backends) >>
     qexists_tac `es` >> simp[]) >>
  simp[stmtSimPropsTheory.cenv_top_ext_refl,
       exprLoweringPropsTheory.stmt_state_rel_start_gas_obs,
       stmtSimDefsTheory.alloca_frame_gas_obs,
       IgnAsm `lo = imm_len _`] >>
  metis_tac[pred_setTheory.SUBSET_DEF]
QED

Theorem body_assign_immutable_supported_rhs[local]:
  supported_stmt tops bindings (Assign (BaseTarget t) e) ==>
  supported_expr tops e
Proof
  simp[Once supported_stmt_def, supported_assignment_def]
QED

(* Keep the ordinary expression post and the lowered allocation capacity
   at the same RHS endpoint, across the source-only immutable lookup. *)
Theorem body_assign_other_immutable_frontier_bind[local]:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    struct_args_unique tops /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              is_word_type ty) /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              ~is_word_type ty /\
              (expr_type e = ty \/ lowered_value_type cenv e = ty \/
               is_bytestring_type ty \/
               has_length_word (expr_type e) /\ is_empty_value_expr e)) /\
    ~(?nsid dty. t = TopLevelNameTarget nsid /\
          supported_scalar_target tops nsid /\
          type_place_target env t = SOME (Type dty) /\ is_word_type dty) /\
    ~(?nsid mut ty slot.
        t = TopLevelNameTarget nsid /\
        supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
        (mut = Storage \/ mut = Transient) /\
        ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
        ~is_bytestring_type ty /\
        0 < type_memory_bytes cenv ty /\ expr_type e = ty /\
        lowered_value_type cenv e = expr_type e) /\
    ~(?id fld sid fty.
        t = AttributeTarget (NameTarget id) fld /\
        FLOOKUP env.var_types id = SOME (StructT sid) /\
        attribute_type env.type_defs (StructT sid) fld = SOME fty /\
        is_word_type fty) /\
    ~(?nsid fld fty.
        t = AttributeTarget (TopLevelNameTarget nsid) fld /\
        supported_storage_field_write tops nsid fld /\
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    immutable_root cx t /\ (?nsid. t = TopLevelNameTarget nsid) /\
    (!src id ity off vv op st0 sa sm su sb shadow_sa shadow_su shadow_sb
        s0 G0 tn0 marks v ee z G tn.
      t = TopLevelNameTarget (src,id) /\ src = NONE /\ src = cenv.ce_module /\
      cx.in_deploy /\ cenv.ce_is_ctor /\
      supported_immutable_type tops (src,id) = SOME ity /\
      ~cx_const_name cx (src,id) /\
      assignable_type env.type_defs (expr_type e) /\
      type_widens_to env.type_defs (expr_type e) ity /\
      FLOOKUP env.bare_globals (src,id) = SOME ity /\
      cenv.ce_module_var_type (src,id) = SOME ity /\
      FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
      (!tv. evaluate_type (get_tenv cx) ity = SOME tv ==>
            off + type_memory_size tv < dimword (:256)) /\
      stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e) sa = (cenv,sb) /\
      stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e))
        shadow_sa = (gas_shadow_env T cenv,shadow_sb) /\
      compile_get_target_ptr compile_expr cenv t =
        comp_return (Lit (n2w off), SOME LocCode, SOME (ValPT ity)) /\
      compile_expr cenv (expr_type e) e sa = (vv,sm) /\
      unwrap_value cenv vv sm = (op,su) /\
      lower_value compile_expr cenv (expr_type e) e sa = (op,su) /\
      lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa =
        (op,shadow_su) /\
      compile_assign_value cenv (Lit (n2w off)) LocCode op (is_word_type ity)
        (vv_location vv) ity (lowered_value_type cenv e)
        (type_memory_bytes cenv ity) su = ((),sb) /\
      cs_extends sa sm /\ cs_extends sm su /\ cs_extends su sb /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state su shadow_su /\
      gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa su func /\ fn_has_code su sb func /\
      fn_has_code shadow_sa shadow_su shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\ ret_pc_ok cenv sa s0 /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      ~block_is_terminated sa /\
      gas_admissible (eval_stmt cx (Assign (BaseTarget t) e)) (stmt_res_ok lctx) es /\
      expr_body_pre cenv cx env e es /\
      return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
           stmt_state_rel H ctx func cenv cx es s0 /\
           storage_well_formed_on cx es (FST H) /\
           ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!tail. bind (eval_expr cx e) (read_result cx)
         (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
         (INL v,ee with gas_obs := tail)) /\
      storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
      ~z.vs_halted /\
      (!tail. expr_sim_inv cenv cx env (ee with gas_obs := tail) /\
        eval_target_place cx t (ee with gas_obs := tail) =
          (INL (ImmutablePlace src id []),ee with gas_obs := tail)) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
         expr_post H ctx func cenv cx e es sa su s0 ee v op z /\
         expr_store_bound cx (post_value_type cenv e) v op z /\
         z.vs_current_bb = su.cs_current_bb /\ z.vs_inst_idx = LENGTH su.cs_current_insts /\
         alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
         s0.vs_alloca_next <= z.vs_alloca_next /\
         ghost_inv_at (DF H) lo d cenv cx ee G tn z /\
         ptr_val_ok cx (post_value_type cenv e) v op G tn z /\
         (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G z) /\
         ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) /\
      (~is_word_type (post_value_type cenv e) ==>
         !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
                eval_operand op z = SOME w ==>
                type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) ==>
      gas_outcome_full
        (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
        (write_place cx (ImmutablePlace src id []) v) (ee,z,G,tn)
        (\H res ff Gf tf u. ?ce.
          stmt_lands lctx sb res u /\ ~u.vs_halted /\
          (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
          cenv_top_ext cenv ce ff.scopes /\
          stmt_state_rel H ctx func ce cx ff u /\
          storage_well_formed_on cx ff (FST H) /\
          return_buf_frame d ce sb u /\ alloca_history func u /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
          s0.vs_alloca_next <= u.vs_alloca_next /\
          ghost_inv_at (DF H) lo d ce cx ff Gf tf u /\
          (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                 lookup_var x u = SOME w) /\
          (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                   FLOOKUP u.vs_allocas aid = SOME b) /\
          (!x. not_fresh_at sa x ==>
               FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
          alloca_frame cenv es sa s0 ce ff u /\
          (!aid off sz i.
             FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
             (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                        off + sz <= b \/ b + sz' <= off) /\
             off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tn0.t_mem))
        (\H res ff gt r.
           (!tail. stmt_exit_ptr (RetQ H) (ff with gas_obs := tail) res gt r) /\
           halt_exit H cx ff res r /\
           (ctx_has_dalloca ctx ==>
            !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e)))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac body_assign_immutable_supported >>
  qpat_x_assum `t = TopLevelNameTarget _` SUBST_ALL_TAC >>
  rename1 `supported_immutable_type tops nsid = SOME ity` >>
  PairCases_on `nsid` >>
  drule_all_then strip_assume_tac body_assign_immutable_typed >>
  drule_all_then strip_assume_tac immutable_assign_bare_global >>
  drule_all_then strip_assume_tac immutable_assign_target_layout >>
  qpat_x_assum `!cfn. _` (qspec_then `compile_expr` strip_assume_tac) >>
  drule_then assume_tac body_assign_immutable_supported_rhs >>
  `body_stmt_safe tops (Assign (BaseTarget (TopLevelNameTarget (nsid0,nsid1))) e)` by
    metis_tac[supported_stmt_body_safe] >>
  `expr_body_pre cenv cx env e es` by metis_tac[topcopy_rhs_pre] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by metis_tac[body_expr_full_ok_def] >>
  drule_then (qx_choose_then `rty` assume_tac) post_type_evaluates >>
  `!gs tv ee v. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
       read_result cx tv ee = (INL v,ee) ==> value_has_type rty v` by
    (rpt gen_tac >> strip_tac >>
     `env.type_defs = get_tenv cx` by
       fs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
     `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
     `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
       simp[bind_def] >>
     drule_all (SIMP_RULE (srw_ss() ++ ETA_ss) [] memory_rhs_read_post_typed) >>
     simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def]) >>
  drule_then assume_tac body_post_type_allocation_bound >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  drule_all body_assign_immutable_value_code >> strip_tac >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by fs[ret_pc_ok_def] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  drule_all_then assume_tac body_assign_local_memory_rhs_frontier >>
  irule assign_return_buf_sep >> asm_rewrite_tac[] >>
  irule body_assign_immutable_bind >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`\H v ee G tn z.
    expr_post H ctx func cenv cx e es sa su s0 ee v op z /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    z.vs_current_bb = su.cs_current_bb /\ z.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn z /\
    ptr_val_ok cx (post_value_type cenv e) v op G tn z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G z) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    (~is_word_type (post_value_type cenv e) ==>
      !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
             eval_operand op z = SOME w ==>
             type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next)`,
    `cenv`, `env`, `ity`, `tops`] >>
  simp[] >> reverse conj_tac
  >- (conj_tac
      >- (qpat_assum `nsid0 = cenv.ce_module` (fn eq => pure_rewrite_tac[GSYM eq]) >>
          first_assum ACCEPT_TAC) >>
      irule gas_outcome_full_post_mono >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      BETA_TAC >> conj_tac
      >- (rpt gen_tac >> strip_tac >> qexists `v` >> gvs[arithmeticTheory.ADD_COMM]) >>
      rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def] >> strip_tac >>
      conj_tac >- (simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]) >>
      conj_tac >- (qpat_assum `halt_exit _ _ _ (INR _) _`
        (MATCH_ACCEPT_TAC o MATCH_MP (iffLR halt_exit_INR_type))) >>
      rpt strip_tac
      >- (qpat_assum `ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u`
            (fn frame => qpat_assum `ctx_has_dalloca ctx` (fn active =>
               qpat_assum `r = Halt _`
                 (ACCEPT_TAC o MATCH_MP (SPEC_ALL (MP frame active)))))) >>
      qpat_assum `r = IntRet _ _` (fn ret =>
        qpat_assum `expr_exit _ r` (mp_tac o REWRITE_RULE [ret])) >>
      simp[expr_exit_def]) >>
  rpt strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (assume_tac o last o CONJUNCTS) >>
  qpat_x_assum `!src id ity off vv op st0 sa sm su sb sha shu shb s0 G0 tn0 marks v ee z G tn. _`
    irule >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexists `marks` >> first_assum ACCEPT_TAC) >>
  conj_tac >- gvs[] >>
  conj_tac >- gvs[] >>
  qexistsl_tac [`ity`,`off`,`shadow_sa`,`shadow_sb`,`shadow_su`] >>
  qpat_assum `nsid0 = cenv.ce_module` (fn th => pure_rewrite_tac[GSYM th]) >>
  simp[] >> gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` drule >> simp[]
QED

Theorem body_assign_saved_slot_dead[local]:
  storage_agree (storage_dead H tr src) src dst /\
  storage_range_agree src dst w rt /\ storage_read_live H tr src w rt /\
  storage_dead H tr dst j b /\
  w2n w <= j /\ j < w2n w + type_slot_size rt ==>
  dead_bytes dst (w2n w) rt j b
Proof
  strip_tac >>
  drule storage_agree_storage_dead >> strip_tac >>
  `dead_bytes src (w2n w) rt j b` by fs[storage_read_live_def] >>
  drule storage_range_agree_dead_bytes >> simp[]
QED

Theorem body_assign_saved_rhs_nonmemory_ptr[local]:
  stmt_state_rel H ctx func cenv cx ee u /\
  vv_holds cenv cx t tv (LocatedValue ann p) ee u /\
  vv_storage_live H cx (LocatedValue ann p) ee u /\
  tnu.t_stor SUBSET (cx_dead H cx).d_stor u.vs_call_ctx.cc_address
                    (u.vs_accounts u.vs_call_ctx.cc_address).storage /\
  tnu.t_trans SUBSET (cx_dead H cx).d_trans u.vs_call_ctx.cc_address
                     (u.vs_transient u.vs_call_ctx.cc_address) /\
  p.ptr_location <> LocMemory /\
  op_taint tnu p.ptr_operand = {} /\
  (p.ptr_location = LocCode ==> op_prov Gu p.ptr_operand = NONE) ==>
  ptr_vv_ok cx t tv (LocatedValue ann p) ee Gu tnu u
Proof
  strip_tac >>
  `ann = t` by fs[vv_holds_def] >>
  drule stmt_state_rel_state_rel >> strip_tac >>
  `u.vs_call_ctx.cc_address = cx.txn.target` by
    (drule state_rel_call_ctx_rel >> simp[call_ctx_rel_def]) >>
  simp[ptr_vv_ok_def] >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (strip_tac >>
      drule state_rel_storage_rel >>
      simp[storage_rel_def, GSYM (cj 2 get_storage_def),
           vfmStateTheory.lookup_account_def] >> strip_tac >>
      `storage_holds cx F t tv w ee u` by fs[vv_holds_def] >>
      `storage_range_agree (get_storage cx ee F) (contract_storage u) w ty` by
        gvs[storage_holds_def] >>
      `storage_read_live H F (get_storage cx ee F) w ty` by
        fs[vv_storage_live_def] >>
      `storage_dead H F (contract_storage u) (w2n k) b` by
        (qpat_x_assum `tnu.t_stor SUBSET _` mp_tac >>
         simp[cx_dead_def, contract_storage_def,
              vfmStateTheory.lookup_account_def, SUBSET_DEF] >>
         disch_then (qspec_then `(k,b)` mp_tac) >> simp[]) >>
      `dead_bytes (contract_storage u) (w2n w) ty (w2n k) b` by
        metis_tac[body_assign_saved_slot_dead, arithmeticTheory.ADD_COMM] >>
      gvs[contract_storage_def, vfmStateTheory.lookup_account_def]) >>
  strip_tac >>
  drule state_rel_transient_rel >>
  simp[transient_rel_def, GSYM (cj 1 get_storage_def)] >> strip_tac >>
  `storage_holds cx T t tv w ee u` by fs[vv_holds_def] >>
  `storage_range_agree (get_storage cx ee T) (contract_transient u) w ty` by
    gvs[storage_holds_def] >>
  `storage_read_live H T (get_storage cx ee T) w ty` by
    fs[vv_storage_live_def] >>
  `storage_dead H T (contract_transient u) (w2n k) b` by
    (qpat_x_assum `tnu.t_trans SUBSET _` mp_tac >>
     simp[cx_dead_def, contract_transient_def, SUBSET_DEF] >>
     disch_then (qspec_then `(k,b)` mp_tac) >> simp[]) >>
  `dead_bytes (contract_transient u) (w2n w) ty (w2n k) b` by
    metis_tac[body_assign_saved_slot_dead, arithmeticTheory.ADD_COMM] >>
  gvs[contract_transient_def]
QED

(* Work on the whole declared immutable, before projecting its subvalue. *)

Theorem body_assign_saved_rhs_ctor_read_mods[local]:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  expr_sim_inv_mods mods cenv cx env ee /\ cenv.ce_is_ctor /\
  stmt_state_rel H ctx func cenv cx ee u /\
  dead_lo_ok_mods H D lo cenv cx /\ ghost_inv_at_mods D lo d cenv cx ee Gu tnu u /\
  vv_holds cenv cx t tv (LocatedValue ann p) ee u /\ p.ptr_location = LocCode ==>
  ?val. read_result cx tv ee = (INL val,ee) /\
        !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
               eval_operand p.ptr_operand u = SOME w ==>
               w2n w + type_memory_size rt <= lo /\
               (!mem. mem_agree_outside tnu.t_mem u.vs_memory mem ==>
                      val_in_memory rt val (w2n w) mem)
Proof
  strip_tac >>
  qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
  simp[vv_holds_def, immutable_holds_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `w` (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`name`,`off`,`itv`,`iv`,`k`,`tvt`,`v`] strip_assume_tac)))) >>
  Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[] >>
  rename1 `ALOOKUP ee.immutables cx.txn.target = SOME imms` >>
  mp_tac (Q.INST [`entry` |-> `ee`, `es` |-> `ee`, `id` |-> `name`,
                  `s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tnu`,
                  `rt` |-> `itv`, `v` |-> `iv`] immutable_ctor_frame_mods) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `k + type_memory_size tvt <= type_memory_size itv` by fs[sub_layout_def] >>
  `k + off < dimword(:256)` by decide_tac >>
  `(k + off) MOD dimword(:256) = off + k` by
    (qpat_assum `k + off < dimword(:256)` (fn th =>
       simp[NoAsms, arithmeticTheory.LESS_MOD, th, Once arithmeticTheory.ADD_COMM])) >>
  pop_assum SUBST1_TAC >>
  conj_tac >- decide_tac >>
  rpt strip_tac >>
  qpat_x_assum `sub_layout _ _ _ _ _` mp_tac >>
  simp[NoAsms, sub_layout_def] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem body_assign_saved_rhs_ctor_read[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env ee /\ cenv.ce_is_ctor /\
  stmt_state_rel H ctx func cenv cx ee u /\
  dead_lo_ok H D lo cenv cx /\ ghost_inv_at D lo d cenv cx ee Gu tnu u /\
  vv_holds cenv cx t tv (LocatedValue ann p) ee u /\ p.ptr_location = LocCode ==>
  ?val. read_result cx tv ee = (INL val,ee) /\
        !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
               eval_operand p.ptr_operand u = SOME w ==>
               w2n w + type_memory_size rt <= lo /\
               (!mem. mem_agree_outside tnu.t_mem u.vs_memory mem ==>
                      val_in_memory rt val (w2n w) mem)
Proof
  strip_tac >>
  drule_then assume_tac body_inv_contract >>
  drule_then assume_tac body_inv_module >>
  drule_then (assume_tac o cj 2) body_inv_main_code >>
  drule_then assume_tac contract_inv_cenv_modules >>
  `expr_sim_inv_mods [(NONE,tops)] cenv cx env ee` by
    fs[expr_sim_inv_split_def] >>
  `dead_lo_ok_mods H D lo cenv cx /\ ghost_inv_at_mods D lo d cenv cx ee Gu tnu u` by
    metis_tac[dead_lo_ok_mods_singleton, ghost_inv_at_mods_singleton] >>
  drule_all body_assign_saved_rhs_ctor_read_mods >> simp[]
QED

(* The saved operand still belongs to sm, but its representation and dead-byte
   tests are those of the actual target endpoint. *)

Theorem body_assign_saved_rhs_nonmemory_frame[local]:
  body_inv tops ctx cenv cx /\ struct_args_unique tops /\
  target_indices_pre cenv cx env bt /\ expr_sim_inv cenv cx env es1 /\ eval_base_place cx bt es1 = (INL pv,ee) /\
  vv_post H ctx func cenv cx e ee sa sm u ee tv (LocatedValue ann p) u /\
  vv_storage_live H cx (LocatedValue ann p) ee u /\
  dead_lo_ok H D lo cenv cx /\ ghost_inv_at D lo d cenv cx ee Gu tnu u /\
  ghost_kept_at lo cenv es1 sm G tn s Gu tnu /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  ptr_vv_ok cx (post_value_type cenv e) tv (LocatedValue ann p) es1 G tn s /\
  p.ptr_location <> LocMemory ==>
  ptr_vv_ok cx (post_value_type cenv e) tv (LocatedValue ann p) ee Gu tnu u /\
  (cenv.ce_is_ctor /\ p.ptr_location = LocCode ==>
   ?val. read_result cx tv ee = (INL val,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand p.ptr_operand u = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tnu.t_mem u.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem))
Proof
  strip_tac >>
  qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[vv_post_def]) >>
  conj_tac
  >- (`tnu.t_stor SUBSET (cx_dead H cx).d_stor u.vs_call_ctx.cc_address
                         (u.vs_accounts u.vs_call_ctx.cc_address).storage /\
       tnu.t_trans SUBSET (cx_dead H cx).d_trans u.vs_call_ctx.cc_address
                          (u.vs_transient u.vs_call_ctx.cc_address)` by
        (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
           (mp_tac o cj 4 o REWRITE_RULE[ghost_inv_at_def]) >>
         fs[dead_lo_ok_def, stor_taint_ok_at_def]) >>
      `op_taint tnu p.ptr_operand = op_taint tn p.ptr_operand /\
       op_prov Gu p.ptr_operand = op_prov G p.ptr_operand` by
        (Cases_on `p.ptr_operand` >>
         gvs[ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def,
             ghost_kept_at_def]) >>
      qpat_x_assum `ptr_vv_ok _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE[ptr_vv_ok_def]) >>
      irule body_assign_saved_rhs_nonmemory_ptr >>
      metis_tac[]) >>
  strip_tac >>
  drule_all_then assume_tac bodySimAugPlaceLoadTheory.aug_place_base_inv >>
  drule_all body_assign_saved_rhs_ctor_read >> simp[]
QED

Theorem body_assign_snapshot_positive_copy_guard[local]:
  compile_store_memory cenv (Var xs) (Var xd) (lowered_value_type cenv e)
    (lowered_value_type cenv e) sk = ((),sb) /\
  ~is_word_type (lowered_value_type cenv e) /\
  type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv /\
  not_fresh_at sk xd /\ lookup_var xd s = SOME (n2w b) /\
  ptr_covers G tn xd s (type_memory_size tv) /\
  b + type_memory_bytes cenv (lowered_value_type cenv e) < dimword (:256) /\
  b + type_memory_size tv <= s.vs_alloca_next /\
  MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size tv))] [xd])
    (fn_insts func) /\
  FLOOKUP s.vs_allocas sm.cs_next_id = SOME (b,type_memory_size tv) /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint b (type_memory_size tv) a len) /\
  stmt_state_rel H0 ctx func cenv cx es s /\
  local_ptrs_reserved cenv sk /\ alloca_history func s /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sk x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sk x) /\
  allocas_from lo s /\ lo <= b /\ lo <= s.vs_alloca_next /\
  fn_has_code sk sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sk.cs_current_bb /\
  s.vs_inst_idx = LENGTH sk.cs_current_insts /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,Gf,tf)) /\
  typed_copy_state_frame sk b (type_memory_size tv) s t /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!i. ~(b <= i /\ i < b+type_memory_size tv) ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  (!x. not_fresh_at sk x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
    val_in_memory tv v b mem) ==>
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    (!H. stmt_state_rel H ctx func cenv cx es s ==>
      stmt_state_rel H ctx func cenv cx es t) /\
    (!D d. ghost_inv_at D lo d cenv cx es G tn s ==>
      ghost_inv_at D lo d cenv cx es Gf tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    lookup_var xd t = SOME (n2w b) /\
    ptr_covers Gf tf xd t (type_memory_size tv) /\
    FLOOKUP t.vs_allocas sm.cs_next_id = SOME (b,type_memory_size tv) /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory tv v b mem) /\
    t.vs_alloca_next = s.vs_alloca_next /\ alloca_history func t /\
    (!x. not_fresh_at sk x ==>
      not_fresh_at sb x /\ lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!name a len. local_region cenv es.scopes t name a len <=>
      local_region cenv es.scopes s name a len) /\
    (!es0 se s0 G0 tn0.
      se.cs_next_var <= sk.cs_next_var /\
      ghost_kept_at lo cenv es0 se G0 tn0 s0 G tn /\
      alloca_frame cenv es0 se s0 cenv es s /\
      (!old off sz. FLOOKUP s0.vs_allocas old = SOME (off,sz) /\
        old < se.cs_next_id ==> regions_disjoint b (type_memory_size tv) off sz) /\
      (!name off sz. local_region cenv es0.scopes s0 name off sz ==>
        regions_disjoint b (type_memory_size tv) off sz) ==>
      ghost_kept_at lo cenv es0 se G0 tn0 s0 Gf tf /\
      alloca_frame cenv es0 se s0 cenv es t /\
      (!old off sz i. FLOOKUP s0.vs_allocas old = SOME (off,sz) /\
        old < se.cs_next_id /\
        (!name a len. local_region cenv es0.scopes s0 name a len ==>
          off+sz <= a \/ a+len <= off) /\
        off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `b + type_memory_size tv < dimword (:256)` by simp[] >>
  mp_tac (Q.INST [`src` |-> `Var xs`, `p` |-> `xd`, `aid` |-> `sm.cs_next_id`,
                  `pty` |-> `lowered_value_type cenv e`]
          body_assign_snapshot_copy_endpoint_frame) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem body_assign_snapshot_positive_entry_join[local]:
  (!es0 se r G0 tn0.
    se.cs_next_var <= sk.cs_next_var /\
    ghost_kept_at lo ce es0 se G0 tn0 r (Gq : (string, num # num) fmap) tnq /\
    alloca_frame ce es0 se r ce ee q /\
    (!aid off len. FLOOKUP r.vs_allocas aid = SOME (off,len) /\
      aid < se.cs_next_id ==> regions_disjoint b N off len) /\
    (!name off len. local_region ce es0.scopes r name off len ==>
      regions_disjoint b N off len) ==>
    ghost_kept_at lo ce es0 se G0 tn0 r Gf tf /\
    alloca_frame ce es0 se r ce ee u /\
    (!aid off sz i. FLOOKUP r.vs_allocas aid = SOME (off,sz) /\
      aid < se.cs_next_id /\
      (!name a len. local_region ce es0.scopes r name a len ==>
        off+sz <= a \/ a+len <= off) /\
      off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tnq.t_mem)) /\
  (!x. not_fresh_at sk x ==>
    lookup_var x u = lookup_var x q /\ FLOOKUP Gf x = FLOOKUP Gq x /\
    op_taint tf (Var x) = op_taint tnq (Var x)) /\
  u.vs_alloca_next = q.vs_alloca_next /\
  sm.cs_next_var <= sk.cs_next_var /\ sk.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  ghost_kept_at lo ce ee sm G tn s Gq tnq /\
  alloca_frame ce ee sm s ce ee q /\
  (!aid off len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
    regions_disjoint b N off len) /\
  (!name off len. local_region ce ee.scopes q name off len ==>
    regions_disjoint b N off len) /\
  (!name off len. local_region ce ee.scopes q name off len <=>
    local_region ce ee.scopes s name off len) /\
  (!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sm.cs_next_id /\
    (!name base len. local_region ce ee.scopes s name base len ==>
      off+sz <= base \/ base+len <= off) /\
    off <= i /\ i < off+sz /\ i IN tnq.t_mem ==> i IN tn.t_mem) /\
  (!x. not_fresh_at sm x ==>
    lookup_var x q = lookup_var x s /\ FLOOKUP Gq x = FLOOKUP G x /\
    op_taint tnq (Var x) = op_taint tn (Var x)) /\
  return_buf_frame d ce sk q /\
  ghost_kept_at lo ce es sa Gi ti s0 Gq tnq /\
  vv_post (H : (bool # bytes32 # type_value) list # num list)
    ctx func ce cx e es sa sm s0 ee pv vv0 s /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!i. ~(b <= i /\ i < b+N) ==> (i IN tf.t_mem <=> i IN tnq.t_mem)) ==>
  ghost_kept_at lo ce es sa Gi ti s0 Gf tf /\
  ghost_kept_at lo ce ee sm G tn s Gf tf /\
  alloca_frame ce ee sm s ce ee u /\
  (!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sm.cs_next_id /\
    (!name base len. local_region ce ee.scopes s name base len ==>
      off+sz <= base \/ base+len <= off) /\
    off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn.t_mem) /\
  return_buf_frame d ce sb u /\
  (!x. not_fresh_at sm x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!name off len. local_region ce ee.scopes s name off len ==>
    regions_disjoint b N off len` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!name off len. local_region ce ee.scopes q name off len ==> _`
       (qspecl_then [`name`,`off`,`len`] mp_tac) >> simp[]) >>
  qpat_x_assum `!es0 se r G0 tn0. _ ==> ghost_kept_at _ _ es0 se _ _ r _ _ /\ _`
    (qspecl_then [`ee`,`sm`,`s`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (map_every assume_tac o CONJUNCTS o REWRITE_RULE[loweringPostsTheory.vv_post_def]) >>
      `!name off len. local_region ce es.scopes s0 name off len ==>
        local_region ce ee.scopes s name off len` by
        (rpt gen_tac >> disch_tac >>
         irule exprSimPropsTheory.local_region_frame_fwd >>
         qexistsl [`s0`,`sa`,`es.scopes`] >> simp[]) >>
      qpat_x_assum `ghost_kept_at lo ce es sa Gi ti s0 Gq tnq`
        (map_every assume_tac o CONJUNCTS o REWRITE_RULE[bodyPtrDefsTheory.ghost_kept_at_def]) >>
      rewrite_tac[bodyPtrDefsTheory.ghost_kept_at_def] >> conj_tac
      >- (qx_gen_tac `x` >> disch_tac >>
          `not_fresh_at sk x` by
            (irule stmtFragPtrTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[] >> decide_tac) >>
          simp[]) >>
      conj_tac
      >- (map_every qx_gen_tac [`aid`,`off`,`sz`,`i`] >>
          disch_then (map_every assume_tac o CONJUNCTS) >>
          `aid < sm.cs_next_id` by decide_tac >>
          `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by simp[] >>
          `regions_disjoint b N off sz` by
            (qpat_assum `!aid off len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = _ ==> _`
               (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[]) >>
          `~(b <= i /\ i < b+N)` by
            (qpat_assum `regions_disjoint b N off sz` mp_tac >>
             qpat_assum `off <= i` mp_tac >> qpat_assum `i < off+sz` mp_tac >>
             POP_ASSUM_LIST (K ALL_TAC) >>
             rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
          `i IN tnq.t_mem` by
        (qpat_assum `!j. ~(b <= j /\ j < b+N) ==> (j IN tf.t_mem <=> j IN tnq.t_mem)`
           (qspec_then `i` mp_tac) >> simp[]) >>
          qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
            (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
          (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
          disch_then ACCEPT_TAC) >>
      map_every qx_gen_tac [`name`,`off`,`sz`,`i`] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      `regions_disjoint b N off sz` by
        (qpat_assum `!name off len. local_region ce ee.scopes s name off len ==> _`
           (qspecl_then [`name`,`off`,`sz`] mp_tac) >> simp[]) >>
      `~(b <= i /\ i < b+N)` by
            (qpat_assum `regions_disjoint b N off sz` mp_tac >>
             qpat_assum `off <= i` mp_tac >> qpat_assum `i < off+sz` mp_tac >>
             POP_ASSUM_LIST (K ALL_TAC) >>
             rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
      `i IN tnq.t_mem` by
        (qpat_assum `!j. ~(b <= j /\ j < b+N) ==> (j IN tf.t_mem <=> j IN tnq.t_mem)`
           (qspec_then `i` mp_tac) >> simp[]) >>
      qpat_assum `!name off sz i. local_region ce es.scopes s0 name off sz /\ _ ==> _`
        (qspecl_then [`name`,`off`,`sz`,`i`] mp_tac) >> simp[]) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >> conj_tac
  >- (map_every qx_gen_tac [`aid`,`off`,`sz`,`i`] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      `i IN tnq.t_mem` by
        (qpat_assum `!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ _ /\ _ /\ _ /\ _ /\ i IN tf.t_mem ==> _`
           (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
          (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
          disch_then ACCEPT_TAC) >>
      qpat_assum `!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ _ /\ _ /\ _ /\ _ /\ i IN tnq.t_mem ==> _`
        (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
          (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
          disch_then ACCEPT_TAC) >>
  conj_tac
  >- (irule bodyMemoryDefsTheory.return_buf_frame_frame >> qexistsl [`ce`,`q`,`sk`] >> simp[]) >>
  qx_gen_tac `x` >> disch_tac >>
  `not_fresh_at sk x` by (irule stmtFragPtrTheory.not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  simp[]
QED

Theorem body_assign_snapshot_memory_joint[local]:
  expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL pv,ee) /\ read_result cx pv ee = (INL v,ee) /\
  ~is_word_type (lowered_value_type ce e) /\
  compile_expr ce (expr_type e) e sa = (vv0,sm) /\
  compile_snapshot_vv ce T (vv_with_type (lowered_value_type ce e) vv0) sm = (snap,sb) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x. vv_operand vv0 = Var x ==> not_fresh_at sm x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func ce cx e es sa sm s0 ee pv vv0 s /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee pv vv0 s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_vv_ok cx (post_value_type ce e) pv vv0 ee G tn s /\
  (!t op0. vv0 = StackValue t op0 /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e op0 G s) /\
  (!t p. vv0 = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv0 = SOME LocCode ==>
    ?val. read_result cx pv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv0) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  return_buf_frame d ce sm s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?u Gf tnf stv xd b.
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    value_has_type stv v /\ val_wf stv v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK u,Gf,tnf) /\
      stmt_state_rel H ctx func ce cx ee u /\
      ghost_inv_at (DF H) lo d ce cx ee Gf tnf u) /\
    vv_location snap = SOME LocMemory /\ vv_type snap = lowered_value_type ce e /\
    vv_operand snap = Var xd /\ not_fresh_at sb xd /\
    lookup_var xd u = SOME (n2w b) /\
    ptr_covers Gf tnf xd u (type_memory_size stv) /\
    (!mem. mem_agree_outside tnf.t_mem u.vs_memory mem ==>
      val_in_memory stv v b mem) /\
    sm.cs_next_id < sb.cs_next_id /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (b,type_memory_size stv) /\
    lo <= b /\ b + type_memory_size stv < dimword (:256) /\
    b + type_memory_size stv <= u.vs_alloca_next /\
    (!name off len. local_region ce ee.scopes u name off len ==>
      regions_disjoint b (type_memory_size stv) off len) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    s0.vs_alloca_next <= u.vs_alloca_next /\ return_buf_frame d ce sb u /\
    ghost_kept_at lo ce es sa Gi ti s0 Gf tnf /\
    ghost_kept_at lo ce ee sm G tn s Gf tnf /\
    (!x. not_fresh_at sm x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    alloca_frame ce ee sm s ce ee u /\
    (!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sm.cs_next_id /\
      (!name base len. local_region ce ee.scopes s name base len ==>
        off+sz <= base \/ base+len <= off) /\
      off <= i /\ i < off+sz /\ i IN tnf.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >>
  `vv_type (vv_with_type (lowered_value_type ce e) vv0) = lowered_value_type ce e` by
    (Cases_on `vv0` >> simp[vv_with_type_def,vv_type_def]) >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) sm` >>
  rename1 `compile_alloc_buffer _ sm = (buf,sn)` >>
  Cases_on `unwrap_value ce (vv_with_type (lowered_value_type ce e) vv0) sn` >>
  rename1 `unwrap_value ce _ sn = (op,sk)` >>
  Cases_on `compile_store_memory ce op buf.buf_operand
              (lowered_value_type ce e) (lowered_value_type ce e) sk` >>
  qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
  simp[compile_snapshot_vv_def,compile_materialize_vv_def,
       comp_bind_def,comp_ignore_bind_def,comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `compile_store_memory ce op buf.buf_operand _ _ sk = ((),sb)` >>
  `(ce.ce_is_ctor /\ vv_location vv0 = SOME LocCode ==>
    ?val. read_result cx pv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv0) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem))` by simp[] >>
  `ci_mono sm sn` by
    (qspecl_then [`type_memory_bytes ce (lowered_value_type ce e)`,`sm`] mp_tac
      ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono sn sk` by
    (qspecl_then [`ce`,`vv_with_type (lowered_value_type ce e) vv0`,`sn`] mp_tac
      ci_mono_unwrap_value >> simp[]) >>
  `ci_mono sk sb` by
    (qspecl_then [`ce`,`op`,`buf.buf_operand`,`lowered_value_type ce e`,
                  `lowered_value_type ce e`,`sk`] mp_tac
       ci_mono_compile_store_memory >> simp[]) >>
  `fn_has_code sm sn func /\ fn_has_code sn sk func /\ fn_has_code sk sb func` by
    (fs[ci_mono_def] >>
     `cs_extends sm sk` by metis_tac[cs_extends_trans] >>
     `fn_has_code sm sk func /\ fn_has_code sk sb func` by
       metis_tac[fn_has_code_split] >>
     metis_tac[fn_has_code_split]) >>
  drule_all body_assign_snapshot_memory_alloc_joint >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `a` (qx_choose_then `Ga` (qx_choose_then `tna`
      (qx_choose_then `xd` (qx_choose_then `b`
        (map_every assume_tac o CONJUNCTS))))))) >>
  `(do pv <- eval_expr cx e; read_result cx pv od) es = (INL v,ee)` by
    simp[vyperStateTheory.bind_def] >>
  `env.type_defs = get_tenv cx` by
    drule_then ACCEPT_TAC expr_body_pre_env_type_defs >>
  drule_all exprSimHypsTheory.memory_rhs_read_post_typed >>
  simp[value_runtime_typed_def] >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty` >>
  `!w. read_result cx pv ee = (INL w,ee) ==> value_has_type rty w` by simp[] >>
  `sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id` by
    fs[ci_mono_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post H ctx func ce cx e es sa sm s0 ee pv vv0 a /\
       ghost_inv_at (DF H) lo d ce cx ee Ga tna a` by simp[] >>
  qpat_assum `ptr_vv_ok _ _ _ _ _ Ga tna a`
    (mp_then Any mp_tac body_assign_snapshot_memory_unwrap_joint) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `q` (qx_choose_then `Gq` (qx_choose_then `tnq`
      (qx_choose_then `stv` (qx_choose_then `w`
        (map_every assume_tac o CONJUNCTS))))))) >>
  `!name off len. local_region ce ee.scopes q name off len <=>
                 local_region ce ee.scopes a name off len` by
    (rpt gen_tac >> irule loweringStateRelDefsTheory.local_region_lookup_cong >>
     qx_gen_tac `nm` >> qx_gen_tac `entry` >> qx_gen_tac `p` >>
     qx_gen_tac `caplen` >> strip_tac >>
     `not_fresh_at sn p` by (fs[local_ptrs_reserved_def] >> (metis_tac[local_ptrs_reserved_def])) >> simp[]) >>
  `FLOOKUP q.vs_allocas sm.cs_next_id = SOME (b,type_memory_size stv)` by
    (qpat_assum `!aid b n. FLOOKUP a.vs_allocas aid = SOME (b,n) /\ _ ==> _`
       (qspecl_then [`sm.cs_next_id`,`b`,`type_memory_size stv`] mp_tac) >>
     impl_tac >- (simp[] >> qx_gen_tac `nm` >> qx_gen_tac `lbase` >>
       qx_gen_tac `llen` >> strip_tac >>
       qpat_assum `!name off len. local_region ce ee.scopes a name off len ==> regions_disjoint _ _ off len`
         (qspecl_then [`nm`,`lbase`,`llen`] mp_tac) >>
       simp[loweringStateRelDefsTheory.regions_disjoint_def]) >> simp[]) >>
  `lookup_var xd q = SOME (n2w b) /\ ptr_covers Gq tnq xd q (type_memory_size stv)` by
    ((qpat_assum `!x. not_fresh_at sn x ==> lookup_var x q = _ /\ _`
       (qspec_then `xd` mp_tac) >>
     rewrite_tac[boolTheory.AND_IMP_INTRO] >>
     impl_tac >- simp[] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     simp[exprPtrUnwrapFramesTheory.copy_ptr_covers_transport] >> (metis_tac[boolTheory.AND_IMP_INTRO, exprPtrUnwrapFramesTheory.copy_ptr_covers_transport]))) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (a,Ga,tna) _ (OK q,Gq,tnq) /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~q.vs_halted` by
    (qpat_assum `gas_origin_ptr_path _ (a,Ga,tna) _ (OK q,Gq,tnq)`
       (mp_then Any mp_tac fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec) >>
     simp[exit_result_def]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee q` by
    fs[expr_post_def] >>
  `sn.cs_next_var <= sk.cs_next_var /\ sn.cs_next_id <= sk.cs_next_id /\
   sk.cs_next_var <= sb.cs_next_var /\ sk.cs_next_id <= sb.cs_next_id` by
    fs[ci_mono_def] >>
  `not_fresh_at sk xd /\ not_fresh_at sb xd` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!x. not_fresh_at sm x ==>
      lookup_var x q = lookup_var x s /\ FLOOKUP Gq x = FLOOKUP G x /\
      op_taint tnq (Var x) = op_taint tn (Var x)` by
    (qx_gen_tac `x` >> strip_tac >>
     `not_fresh_at sn x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
     simp[]) >>
  `!nm off len. local_region ce ee.scopes a nm off len <=>
                local_region ce ee.scopes s nm off len` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     qx_gen_tac `nm1` >> qx_gen_tac `entry` >> qx_gen_tac `p` >>
     qx_gen_tac `caplen` >> strip_tac >>
     `not_fresh_at sm p` by
       (qpat_assum `local_ptrs_reserved ce sm`
          (qspecl_then [`nm1`,`nm1`,`p`,`caplen`,`caplen`] mp_tac o
           CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[local_ptrs_reserved_def]) >>
        simp[]) >> simp[]) >>
  `ghost_kept_at lo ce ee sm G tn s Gq tnq` by
    (irule wordArgsPtrTheory.ghost_kept_at_trans >>
     qexistsl [`Ga`,`ee`,`a`,`sn`,`tna`] >> simp[]) >>
  `alloca_frame ce ee sm s ce ee q` by
    (irule stmtSimDefsTheory.alloca_frame_trans >>
     qexistsl [`ce`,`ee`,`a`,`sn`] >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q,Gq,tnq) /\
      stmt_state_rel H ctx func ce cx ee q /\ ghost_inv_at (DF H) lo d ce cx ee Gq tnq q` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (s,G,tn) _ (OK a,Ga,tna) /\ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (assume_tac o CONJUNCT1) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (a,Ga,tna) _ (OK q,Gq,tnq) /\ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     conj_tac >- (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
                  qexistsl [`Ga`,`a`,`tna`] >> simp[]) >>
     fs[expr_post_def]) >>
  `!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sm.cs_next_id /\
      (!name base len. local_region ce ee.scopes s name base len ==>
        off+sz <= base \/ base+len <= off) /\
      off <= i /\ i < off+sz /\ i IN tnq.t_mem ==> i IN tn.t_mem` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     `FLOOKUP a.vs_allocas aid = SOME (off,sz)` by simp[] >>
     qpat_assum `!aid b n. FLOOKUP a.vs_allocas aid = SOME (b,n) /\ _ ==> _`
       (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
     (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >>
     disch_then (qspec_then `i` mp_tac o last o CONJUNCTS) >>
     simp[] >> disch_tac >>
     qpat_assum `!aid off len i. FLOOKUP s.vs_allocas aid = SOME (off,len) /\ _ /\ _ /\ _ /\ i IN tna.t_mem ==> _`
       (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
          (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
          disch_then ACCEPT_TAC) >>
  `sm.cs_next_id < sb.cs_next_id /\ b + type_memory_size stv <= q.vs_alloca_next /\
   s.vs_alloca_next <= q.vs_alloca_next` by decide_tac >>
  `!name off len. local_region ce ee.scopes q name off len ==>
      regions_disjoint b (type_memory_size stv) off len` by (simp[] >> (gvs[])) >>
  Cases_on `type_memory_size stv = 0`
  >- (`type_memory_bytes ce (lowered_value_type ce e) = 0` by simp[] >>
      drule_all_then assume_tac exprSimAbiEncodeArgsMaterializePathTheory.materialize_zero_store >>
      `sk = sb` by fs[comp_return_def] >> qpat_x_assum `sk = sb` SUBST_ALL_TAC >>
      qexistsl [`q`,`Gq`,`tnq`,`stv`,`xd`,`b`] >>
      simp[vv_location_def,vv_type_def,vv_operand_def,mk_ptr_def,
           valueEncodingProofsTheory.return_zero_wf_memory] >>
      conj_tac
      >- (qx_gen_tac `nm` >> qx_gen_tac `off` >> qx_gen_tac `len` >> strip_tac >>
          qpat_assum `!name off len. local_region ce ee.scopes q name off len ==> _`
            (qspecl_then [`nm`,`off`,`len`] mp_tac) >> simp[]) >>
      map_every qx_gen_tac [`aid`,`off`,`sz`,`i`] >> strip_tac >>
      qpat_assum `!j a n k. FLOOKUP s.vs_allocas j = SOME (a,n) /\ _ /\ _ /\ _ /\ _ /\ k IN tnq.t_mem ==> _`
        (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >> simp[] >>
      impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `0 < type_memory_size stv` by decide_tac >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ q`
    (mp_then Any mp_tac body_assign_snapshot_positive_source_ready) >>
  disch_then drule_all >>
  disch_then (qx_choose_then `xs` (map_every assume_tac o CONJUNCTS)) >>
  `not_fresh_at sk xs` by
    (qpat_assum `unwrap_value _ _ sn = _`
      (mp_then Any (qspec_then `xs` mp_tac) exprOperandVarTheory.compiler_unwrap_value_var) >>
     rewrite_tac[boolTheory.AND_IMP_INTRO] >>
     (impl_tac >- (Cases_on `vv0` >> simp[vv_with_type_def] >>
       rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
       qexists_tac `sm` >> simp[] >>
       qpat_assum `!y. vv_operand _ = Var y ==> not_fresh_at sm y`
         (qspec_then `x` mp_tac) >> simp[vv_operand_def])) >> simp[]) >>
  `allocas_from lo q /\ lo <= q.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ lo d ce cx ee Gq tnq q`
      (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >> simp[]) >>
  `local_ptrs_reserved ce sk` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sk x` by
    (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >> decide_tac) >>
  `!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sk x` by
    (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >> decide_tac) >>
  `w2n (n2w b : bytes32) = b` by simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `compile_store_memory ce (Var xs) (Var xd) (lowered_value_type ce e)
    (lowered_value_type ce e) sk = ((),sb)` by fs[] >>
  Q.SUBGOAL_THEN
    `?u Gf tf.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q,Gq,tnq) [] (OK u,Gf,tf)) /\
      (!mem. mem_agree_outside tf.t_mem u.vs_memory mem ==> val_in_memory stv v b mem) /\
      typed_copy_state_frame sk b (type_memory_size stv) q u /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      tf.t_stor = tnq.t_stor /\ tf.t_trans = tnq.t_trans /\ tf.t_imm = tnq.t_imm /\
      (!i. ~(b <= i /\ i < b+type_memory_size stv) ==> (i IN tf.t_mem <=> i IN tnq.t_mem)) /\
      (!x. not_fresh_at sk x ==> lookup_var x u = lookup_var x q /\
        FLOOKUP Gf x = FLOOKUP Gq x /\ op_taint tf (Var x) = op_taint tnq (Var x))`
    (qx_choose_then `u` (qx_choose_then `Gf` (qx_choose_then `tf`
      (map_every assume_tac o CONJUNCTS))))
  >- (Cases_on `is_bytestring_type (lowered_value_type ce e)`
      >- (qspecl_then [`ce`,`xs`,`xd`,`lowered_value_type ce e`,`sk`,`sb`,`cx`,
                      `stv`,`v`,`q`,`w`,`n2w b`,`tnq`,`Gq`,`lo`,`ctx`,`func`,`explicit`,`PG`]
            mp_tac body_assign_snapshot_bytes_copy_endpoint >> simp[]) >>
      `compile_copy_memory (Var xd) (Var xs) (type_memory_size stv) sk = ((),sb)` by
        (qpat_assum `compile_store_memory ce (Var xs) (Var xd) _ _ sk = _`
           (mp_tac o REWRITE_RULE[compile_store_memory_def]) >>
         asm_rewrite_tac[]) >>
      mp_tac (Q.INST [`xd` |-> `xd`,`xs` |-> `xs`,`n` |-> `type_memory_size stv`,
                     `tv` |-> `stv`,`sa` |-> `sk`,`s` |-> `q`,`sw` |-> `w`,`dw` |-> `n2w b`,
                     `tn` |-> `tnq`,`G` |-> `Gq`] bodyFullMemoryCopyTheory.body_full_memory_copy_frame_path) >>
      simp[] >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      strip_tac >> metis_tac[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee s` by
    ((qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ s /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o CONJUNCT1) >> simp[vv_post_def] >> (metis_tac[vv_post_def]))) >>
  `type_memory_bytes ce (lowered_value_type ce e) < dimword (:256)` by
    (simp[] >> decide_tac) >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size stv))] [xd]) (fn_insts func)` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ s`
       (mp_then Any mp_tac bodyPtrIfExpAllocCompilerTheory.compile_alloc_buffer_raw_step) >>
     disch_then drule_all >> strip_tac >> gvs[]) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  mp_tac (Q.INST [`cenv` |-> `ce`, `tv` |-> `stv`, `s` |-> `q`,
                  `G` |-> `Gq`, `tn` |-> `tnq`, `t` |-> `u`, `es` |-> `ee`]
          (horizonTypeLib.at_horizon_named "H"
             (Q.INST_TYPE [`:'a` |-> `:256`] body_assign_snapshot_positive_copy_guard))) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ s /\ _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (assume_tac o CONJUNCT1) >>
  `sm.cs_next_var <= sk.cs_next_var` by
    (irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `sn.cs_next_var` >> simp[]) >>
  `!aid off len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
      regions_disjoint b (type_memory_size stv) off len` by
    (qpat_assum `!aid off len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
       regions_disjoint b (type_memory_bytes ce (lowered_value_type ce e)) off len` mp_tac >> simp[]) >>
  `!name off len. local_region ce ee.scopes q name off len <=>
      local_region ce ee.scopes s name off len` by simp[] >>
  mp_tac (Q.INST [`N` |-> `type_memory_size stv`, `H` |-> `H0`]
          body_assign_snapshot_positive_entry_join) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf) /\
    stmt_state_rel H ctx func ce cx ee u /\ ghost_inv_at (DF H) lo d ce cx ee Gf tf u` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (s,G,tn) [] (OK q,Gq,tnq) /\ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     conj_tac
     >- (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
         qexistsl [`Gq`,`q`,`tnq`] >> simp[]) >>
     conj_tac
     >- (qpat_assum `!H. stmt_state_rel H _ _ _ _ _ q ==> _` (qspec_then `H` mp_tac) >> simp[]) >>
     qpat_assum `!D d. ghost_inv_at D lo d ce cx ee Gq tnq q ==> _`
       (qspecl_then [`DF H`,`d`] mp_tac) >> simp[]) >>
  `!name off len. local_region ce ee.scopes u name off len ==>
      regions_disjoint b (type_memory_size stv) off len` by
    (map_every qx_gen_tac [`name`,`off`,`len`] >> disch_tac >>
     `local_region ce ee.scopes q name off len` by
       (qpat_assum `!name off len. local_region ce ee.scopes u name off len <=> _`
         (qspecl_then [`name`,`off`,`len`] (irule o iffLR)) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!name off len. local_region ce ee.scopes q name off len ==>
       regions_disjoint b (type_memory_size stv) off len`
       (qspecl_then [`name`,`off`,`len`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  qexistsl [`u`,`Gf`,`tf`,`stv`,`xd`,`b`] >>
  asm_rewrite_tac[vv_location_def,vv_type_def,vv_operand_def,mk_ptr_def] >> simp[]
QED

Theorem body_assign_snapshot_target_memory[local]:
  wb_frame ce mid ee ss u z /\
  ghost_kept_at lo ce mid ss Gf tnf u Gz tnz /\
  FLOOKUP u.vs_allocas aid = SOME (b,type_memory_size tv) /\
  aid < ss.cs_next_id /\
  (!n off sz. local_region ce mid.scopes u n off sz ==>
     loweringStateRelDefs$regions_disjoint b (type_memory_size tv) off sz) /\
  not_fresh_at ss xd /\ lookup_var xd u = SOME (n2w b) /\
  ptr_covers Gf tnf xd u (type_memory_size tv) /\ val_wf tv v /\
  (!mem. mem_agree_outside tnf.t_mem u.vs_memory mem ==> val_in_memory tv v b mem) ==>
  FLOOKUP z.vs_allocas aid = SOME (b,type_memory_size tv) /\
  lookup_var xd z = SOME (n2w b) /\ ptr_covers Gz tnz xd z (type_memory_size tv) /\
  (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==> val_in_memory tv v b mem)
Proof
  strip_tac >>
  `!n off sz. local_region ce mid.scopes u n off sz ==>
    b + type_memory_size tv <= off \/ off + sz <= b` by
    fs[loweringStateRelDefsTheory.regions_disjoint_def] >>
  fs[wb_frame_def,ghost_kept_at_def] >>
  `lookup_var xd z = lookup_var xd u /\ FLOOKUP Gz xd = FLOOKUP Gf xd /\
   op_taint tnz (Var xd) = op_taint tnf (Var xd)` by simp[] >>
  `ptr_covers Gz tnz xd z (type_memory_size tv)` by
    metis_tac[exprPtrUnwrapFramesTheory.copy_ptr_covers_transport] >>
  simp[] >>
  rpt strip_tac >> irule robust_val_in_memory_window_transport >>
  conj_tac >- simp[] >>
  qexistsl_tac [`tnf.t_mem`,`tnz.t_mem`,`type_memory_size tv`,`u.vs_memory`,`z.vs_memory`] >>
  simp[val_footprint_le] >>
  conj_tac >-
    (rpt strip_tac >> qpat_assum `!aid off sz i. FLOOKUP _ _ = SOME _ /\ _ ==> _`
       (qspecl_then [`aid`,`b`,`type_memory_size tv`,`i`] mp_tac) >>
     impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  qpat_assum `!aid off sz. FLOOKUP _ _ = SOME _ /\ _ ==> _`
    (qspecl_then [`aid`,`b`,`type_memory_size tv`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> simp[]
QED

(* Bind the actual target outcome.  The store sees the same target landing at
   every horizon, plus the snapshot that was already present on target entry. *)
Theorem body_assign_snapshot_bind_at_target[local]:
  assign_target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx env t mid /\
  type_place_target env t = SOME (Type ty) /\
  compile_get_target_ptr compile_expr ce t ss = (r,st) /\
  compile_get_target_ptr compile_expr (gas_shadow_env T ce) (gas_shadow_target t) shss = (r,shst) /\
  gas_shadow_state ss shss /\ gas_shadow_state st shst /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code ss st func /\ fn_has_code shss shst shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce ss /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x) /\
  gas_admissible (eval_target_place cx t) target_place_res_ok mid /\
  return_buf_frame d ce ss u /\ alloca_history func u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!fn inst s. frag_reachable ctx func u fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func ce cx mid u /\ storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d ce cx mid Gf tnf u) /\
  ~u.vs_halted /\ u.vs_current_bb = ss.cs_current_bb /\
  u.vs_inst_idx = LENGTH ss.cs_current_insts /\
  sa.cs_next_id <= ss.cs_next_id /\ sa.cs_next_var <= ss.cs_next_var /\
  ss.cs_next_var <= st.cs_next_var /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 Gf tnf /\ alloca_frame ce es sa s0 ce mid u /\
  evaluate_type (get_tenv cx) sty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  (!x. op = Var x ==> not_fresh_at ss x) /\
  ((is_word_type sty /\ eval_operand op u = SOME (typed_val_to_w256 tv v) /\
    op_taint tnf op = {} /\ (!lbl. op <> Label lbl)) \/
   (~is_word_type sty /\ ?aid xd b.
      type_memory_bytes ce sty = type_memory_size tv /\
      op = Var xd /\ lookup_var xd u = SOME (n2w b) /\
      FLOOKUP u.vs_allocas aid = SOME (b,type_memory_size tv) /\ aid < ss.cs_next_id /\
      lo <= b /\ b + type_memory_size tv < dimword (:256) /\
      b + type_memory_size tv <= u.vs_alloca_next /\
      (!n off len. local_region ce mid.scopes u n off len ==>
                   loweringStateRelDefs$regions_disjoint b (type_memory_size tv) off len) /\
      ptr_covers Gf tnf xd u (type_memory_size tv) /\
      (!mem. mem_agree_outside tnf.t_mem u.vs_memory mem ==> val_in_memory tv v b mem))) /\
  (!marks p ee z Gz tnz.
     (!tail. eval_target_place cx t
        (mid with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail) =
        (INL p,ee with gas_obs := tail)) /\
     storage_trace_domain cx st0 ee.storage_trace /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==>
       assign_target_post (immutable_root cx t) H ctx func ce cx mid ss st u ee p ty r Gz z /\
       ghost_inv_at (DF H) lo d ce cx ee Gz tnz z) /\
     target_ptr_ok ce (PlaceR p) r Gz tnz z /\
     (!id path. p = MemoryPlace id path ==>
       ?entry w. lookup_scopes id ee.scopes = SOME entry /\
                 evaluate_subscripts entry.type entry.value path = INL w) /\
     ee.gas_obs = [] /\ ~z.vs_halted /\ z.vs_current_bb = st.cs_current_bb /\
     z.vs_inst_idx = LENGTH st.cs_current_insts /\
     return_buf_frame d ce st z /\ alloca_history func z /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ s0.vs_alloca_next <= z.vs_alloca_next /\
     (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x z = SOME w) /\
     (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
     (!x. not_fresh_at sa x ==> FLOOKUP Gz x = FLOOKUP G0 x /\
                                op_taint tnz (Var x) = op_taint tn0 (Var x)) /\
     alloca_frame ce es sa s0 ce ee z /\
     (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
       (!n b len. local_region ce es.scopes s0 n b len ==> off + sz <= b \/ b + len <= off) /\
       off <= i /\ i < off + sz /\ i IN tnz.t_mem ==> i IN tn0.t_mem) /\
     (!x. op = Var x ==> not_fresh_at st x) /\
     ((is_word_type sty /\ eval_operand op z = SOME (typed_val_to_w256 tv v) /\
       op_taint tnz op = {} /\ (!lbl. op <> Label lbl)) \/
      (~is_word_type sty /\ ?aid xd b.
         type_memory_bytes ce sty = type_memory_size tv /\ op = Var xd /\
         lookup_var xd z = SOME (n2w b) /\
         FLOOKUP z.vs_allocas aid = SOME (b,type_memory_size tv) /\ aid < st.cs_next_id /\
         lo <= b /\ b + type_memory_size tv < dimword (:256) /\
         b + type_memory_size tv <= z.vs_alloca_next /\
         (!n off len. local_region ce ee.scopes z n off len ==>
                      loweringStateRelDefs$regions_disjoint b (type_memory_size tv) off len) /\
         ptr_covers Gz tnz xd z (type_memory_size tv) /\
         (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==> val_in_memory tv v b mem))) ==>
     gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (cx_tops cx) cx st0 (write_place cx p v) (ee,z,Gz,tnz) P
       (\H res ee gt q.
         (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt q) /\
         halt_exit H cx ee res q /\
         (ctx_has_dalloca ctx ==>
           !s. (q = Halt s \/ ?ir. q = IntRet ir s) ==> allocas_below_fmp s))) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_target_place cx t) (\p. write_place cx p v))
    (mid,u,Gf,tnf) P
    (\H res ee gt q.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt q) /\
      halt_exit H cx ee res q /\
      (ctx_has_dalloca ctx ==>
        !s. (q = Halt s \/ ?ir. q = IntRet ir s) ==> allocas_below_fmp s))
Proof
  rpt (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >> disch_tac >>
  qpat_x_assum `assign_target_place_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[bodyFullTargetDefsTheory.assign_target_place_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`ty`,`ss`,`st`,`shss`,`shst`,`r`,`u`,`Gf`,`tnf`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ (eval_target_place cx t) _ targetQ targetR` >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all >> BETA_TAC >>
  conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_write_place] >>
  conj_tac >-
    (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_place >>
     goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_place >> simp[]) >>
  conj_tac >- simp[cj 8 vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  qexists_tac `\H res ee G tn z. targetQ H res ee G tn z /\ ~z.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ targetQ targetR` (irule_at Any) >>
      simp[Abbr `targetR`] >> rpt gen_tac >> strip_tac >> Cases_on `res`
      >- fs[exprSimDefsTheory.expr_exit_def] >>
      simp[] >> rename1 `expr_exit (INR exc) q` >>
      conj_tac >- (simp[stmt_exit_ptr_def] >> metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
      conj_tac >- metis_tac[haltExitProjTheory.halt_exit_INR_type] >>
      rpt strip_tac >> gvs[] >> fs[exprSimDefsTheory.expr_exit_def]) >>
  qx_genl_tac [`marks`,`res`,`ee`,`Gz`,`tnz`,`z`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (targetQ = _)` (fn th =>
    CONV_TAC (LAND_CONV (REWRITE_CONV [REWRITE_RULE [markerTheory.Abbrev_def] th]))) >>
  BETA_TAC >>
  disch_then (CONJUNCTS_THEN2
    (qx_choose_then `p` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))
    STRIP_ASSUME_TAC) >>
  disj1_tac >> qexists_tac `p` >> simp[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       assign_target_post (immutable_root cx t) H ctx func ce cx mid ss st u ee p ty r Gz z /\
       ghost_inv_at (DF H) lo d ce cx ee Gz tnz z` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!K. valid_horizon _ _ K ee.storage_trace ==> _` (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `Abbrev (targetQ = _)` (fn th =>
       CONV_TAC (LAND_CONV (REWRITE_CONV [REWRITE_RULE [markerTheory.Abbrev_def] th]))) >>
     BETA_TAC >> disch_then (CONJUNCTS_THEN2 (strip_assume_tac o SRULE []) kall_tac) >> simp[]) >>
  `MAP FDOM ee.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `!tail. eval_target_place _ _ _ = _` (qspec_then `[]` mp_tac) >>
     disch_then (mp_tac o MATCH_MP vyperEvalExprPreservesScopesDomTheory.eval_target_place_preserves_scopes_dom) >>
     simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) mid.storage_trace` by
    (qpat_assum `!tail. eval_target_place _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule_at (Pos (el 2)) vyperStorageFootprintTheory.valid_horizon_frame >>
     simp[cj 8 vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  qmatch_asmsub_abbrev_tac `valid_horizon cx st0 H0 mid.storage_trace` >>
  `stmt_state_rel H0 ctx func ce cx mid u` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` (qspec_then `H0` mp_tac) >> simp[]) >>
  `alloca_frame ce mid ss u ce ee z` by
    (drule_all assign_target_post_alloca_frame >> simp[]) >>
  `alloca_frame ce es sa s0 ce ee z` by
    (irule stmtSimDefsTheory.alloca_frame_trans >> qexistsl_tac [`ce`,`mid`,`u`,`ss`] >> simp[]) >>
  `ss.cs_next_id <= st.cs_next_id` by
    (mp_tac (Q.SPECL [`t`,`ce`,`ss`] stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  qpat_assum `assign_target_post _ H0 _ _ _ _ _ _ _ _ _ _ _ _ _ z`
    (strip_assume_tac o REWRITE_RULE[wb_frame_def] o MATCH_MP assign_target_post_frame) >>
  `return_buf_frame d ce st z` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >> qexistsl_tac [`ce`,`u`,`ss`] >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at ss x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_assum `!marks p ee z Gz tnz. _ ==> _`
    (qspecl_then [`marks`,`p`,`ee`,`z`,`Gz`,`tnz`] irule) >>
  simp[] >> rpt conj_tac
  >- (qexists_tac `marks` >> first_assum ACCEPT_TAC)
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `ss` >> gvs[])
  >- (fs[ghost_kept_at_def] >> rpt strip_tac >> simp[])
  >- (rpt strip_tac >>
      qpat_assum `alloca_frame ce es sa s0 ce mid u`
        (mp_tac o REWRITE_RULE[stmtSimDefsTheory.alloca_frame_def]) >>
      disch_then (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
      (impl_tac >- (simp[] >> (gvs[]))) >> strip_tac >>
      fs[ghost_kept_at_def] >>
      `i IN tnf.t_mem` by
        (qpat_assum `!aid off sz i. FLOOKUP u.vs_allocas _ = _ /\ _ ==> _`
           (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
         (impl_tac >- (simp[] >> gvs[] >> decide_tac)) >> simp[]) >>
      qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas _ = _ /\ _ ==> _`
        (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
      (impl_tac >- (simp[] >> gvs[])) >> simp[]) >>
  qpat_x_assum `(is_word_type sty /\ _) \/ _` strip_assume_tac
  >- (disj1_tac >> simp[] >>
      `eval_operand op z = SOME (typed_val_to_w256 tv v)` by
        (irule exprBopSimPropsTheory.eval_operand_frame >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl_tac [`ss`,`u`] >> simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `op_taint tnz op = op_taint tnf op` by
        (Cases_on `op` >> simp[] >> fs[ghost_kept_at_def,ptrDisciplineTheory.op_taint_def]) >> simp[]) >>
  disj2_tac >> simp[] >>
  `not_fresh_at ss xd` by simp[] >>
  `wb_frame ce mid ee ss u z` by
    (qpat_assum `assign_target_post _ H0 _ _ _ _ _ _ _ _ _ _ _ _ _ z`
       (strip_assume_tac o MATCH_MP assign_target_post_frame) >> simp[]) >>
  drule_all body_assign_snapshot_target_memory >> strip_tac >>
  qexistsl_tac [`aid`,`b`] >> simp[] >>
  `aid < st.cs_next_id /\ b + type_memory_size tv <= z.vs_alloca_next` by decide_tac >> simp[] >>
  qpat_assum `alloca_frame ce mid ss u ce ee z`
    (mp_tac o REWRITE_RULE[stmtSimDefsTheory.alloca_frame_def]) >>
  disch_then (qspecl_then [`aid`,`b`,`type_memory_size tv`] mp_tac) >>
  (impl_tac >-
    (simp[] >> rpt strip_tac >>
     qpat_assum `!n off len. local_region ce mid.scopes u n off len ==> _`
       (drule_then mp_tac) >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)) >>
  disch_then (assume_tac o CONJUNCT2) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> rpt strip_tac >>
  qpat_assum `!n off len. local_region ce ee.scopes z n off len ==> _`
    (drule_then mp_tac) >> decide_tac
QED

Theorem body_assign_other_snapshot_target_bind[local]:
  expr_body_pre ce cx env e es /\
  (!tail. eval_expr cx e
    (es with gas_obs := gas_explicit rhsmarks s0.vs_gas_readings ++ tail) =
    (INL pv,mid with gas_obs := tail)) /\
  read_result cx pv mid = (INL v,mid) /\ mid.gas_obs = [] /\
  compile_expr ce (expr_type e) e sa = (vv0,sm) /\
  compile_snapshot_vv ce T (vv_with_type (lowered_value_type ce e) vv0) sm = (snap,ss) /\
  compile_get_target_ptr compile_expr ce t ss = (r,st) /\
  compile_get_target_ptr compile_expr (gas_shadow_env T ce) (gas_shadow_target t) shss = (r,shst) /\
  unwrap_value ce snap st = (op,su) /\
  fn_has_code sm ss func /\ fn_has_code ss st func /\ fn_has_code shss shst shadow_func /\
  gas_shadow_state ss shss /\ gas_shadow_state st shst /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  body_inv tops ctx ce cx /\
  assign_target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx env t mid /\
  type_place_target env t = SOME (Type ty) /\
  gas_admissible (eval_target_place cx t) target_place_res_ok mid /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\
    vv_post H ctx func ce cx e es sa sm s0 mid pv vv0 s /\
    ghost_inv_at (DF H) lo d ce cx mid G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) mid pv vv0 s /\
  ptr_vv_ok cx (post_value_type ce e) pv vv0 mid G tn s /\
  (!t0 op0. vv0 = StackValue t0 op0 /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e op0 G s) /\
  (!t0 p. vv0 = LocatedValue t0 p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv0 = SOME LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
      eval_operand (vv_operand vv0) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  return_buf_frame d ce sm s /\ alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!tv marks p ee z Gz tnz u.
     (!tail. eval_target_place cx t
        (mid with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail) =
        (INL p,ee with gas_obs := tail)) /\
     storage_trace_domain cx st0 ee.storage_trace /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==>
       assign_target_post (immutable_root cx t) H ctx func ce cx mid ss st u ee p ty r Gz z /\
       ghost_inv_at (DF H) lo d ce cx ee Gz tnz z) /\
     target_ptr_ok ce (PlaceR p) r Gz tnz z /\
     (!id path. p = MemoryPlace id path ==>
       ?entry w. lookup_scopes id ee.scopes = SOME entry /\
                 evaluate_subscripts entry.type entry.value path = INL w) /\
     ee.gas_obs = [] /\ ~z.vs_halted /\ z.vs_current_bb = su.cs_current_bb /\
     z.vs_inst_idx = LENGTH su.cs_current_insts /\
     return_buf_frame d ce su z /\ alloca_history func z /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ s0.vs_alloca_next <= z.vs_alloca_next /\
     (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x z = SOME w) /\
     (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
     (!x. not_fresh_at sa x ==> FLOOKUP Gz x = FLOOKUP G0 x /\
                                op_taint tnz (Var x) = op_taint tn0 (Var x)) /\
     alloca_frame ce es sa s0 ce ee z /\
     (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
       (!n b len. local_region ce es.scopes s0 n b len ==> off + sz <= b \/ b + len <= off) /\
       off <= i /\ i < off + sz /\ i IN tnz.t_mem ==> i IN tn0.t_mem) /\
     evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
     value_has_type tv v /\ val_wf tv v /\
     (!x. op = Var x ==> not_fresh_at su x) /\
     ((is_word_type (lowered_value_type ce e) /\
       eval_operand op z = SOME (typed_val_to_w256 tv v) /\
       op_taint tnz op = {} /\ (!lbl. op <> Label lbl)) \/
      (~is_word_type (lowered_value_type ce e) /\ ?aid xd b.
         type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\ op = Var xd /\
         lookup_var xd z = SOME (n2w b) /\
         FLOOKUP z.vs_allocas aid = SOME (b,type_memory_size tv) /\ aid < su.cs_next_id /\
         lo <= b /\ b + type_memory_size tv < dimword (:256) /\
         b + type_memory_size tv <= z.vs_alloca_next /\
         (!n off len. local_region ce ee.scopes z n off len ==>
                      loweringStateRelDefs$regions_disjoint b (type_memory_size tv) off len) /\
         ptr_covers Gz tnz xd z (type_memory_size tv) /\
         (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==> val_in_memory tv v b mem))) ==>
     gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (cx_tops cx) cx st0 (write_place cx p v) (ee,z,Gz,tnz) P
       (\H res ee gt q.
         (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt q) /\
         halt_exit H cx ee res q /\
         (ctx_has_dalloca ctx ==>
           !s. (q = Halt s \/ ?ir. q = IntRet ir s) ==> allocas_below_fmp s))) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_target_place cx t) (\p. write_place cx p v))
    (mid,s,G,tn) P
    (\H res ee gt q.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt q) /\
      halt_exit H cx ee res q /\
      (ctx_has_dalloca ctx ==>
        !s. (q = Halt s \/ ?ir. q = IntRet ir s) ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule bodyMemSnapshotSourceLocationTheory.snapshot_saved_representation >> strip_tac >>
  `op = vv_operand snap /\ su = st` by gvs[] >>
  qpat_x_assum `op = vv_operand snap` SUBST_ALL_TAC >>
  qpat_x_assum `su = st` SUBST_ALL_TAC >>
  `ci_mono sa sm` by metis_tac[exprLoweringPropsTheory.compile_expr_ci_mono,pairTheory.SND] >>
  `ci_mono sm ss` by metis_tac[exprLoweringPropsTheory.ci_mono_compile_snapshot_vv,pairTheory.SND] >>
  `ci_mono ss st` by metis_tac[stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr,pairTheory.SND] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= ss.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= ss.cs_next_id /\
   ss.cs_next_var <= st.cs_next_var` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  `local_ptrs_reserved ce sm /\ local_ptrs_reserved ce ss` by
    (conj_tac >> irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x /\ not_fresh_at ss x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono,arithmeticTheory.LESS_EQ_TRANS] >>
  `!x. vv_operand vv0 = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var] >>
  qabbrev_tac `started = es with gas_obs := gas_explicit rhsmarks s0.vs_gas_readings` >>
  `mid with gas_obs := [] = mid` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `eval_expr cx e started = (INL pv,mid)` by
    (unabbrev_all_tac >>
     qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE[listTheory.APPEND_NIL])) >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => rewrite_tac[th])) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >>
     simp[Abbr `started`]) >>
  `expr_body_pre ce cx env e started /\ MAP FDOM started.scopes = MAP FDOM mid.scopes` by
    simp[Abbr `started`,exprSimSourceTheory.expr_body_pre_gas_obs] >>
  `ghost_kept_at lo ce started sa G0 tn0 s0 G tn` by
    (fs[Abbr `started`,ghost_kept_at_def] >> (metis_tac[])) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       vv_post H ctx func ce cx e started sa sm s0 mid pv vv0 s /\
       ghost_inv_at (DF H) lo d ce cx mid G tn s` by
    (simp[Abbr `started`,vv_post_initial_gas] >> rpt strip_tac >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qmatch_asmsub_abbrev_tac `valid_horizon cx st0 Hr mid.storage_trace` >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (qspec_then `Hr` (drule_then strip_assume_tac)) >>
  `alloca_frame ce es sa s0 ce mid s` by
    metis_tac[stmtSimDefsTheory.vv_post_alloca_frame] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (fs[vv_post_def,bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >> (metis_tac[vv_post_def, bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp])) >>
  `ce.ce_is_ctor /\ vv_location vv0 = SOME LocCode ==>
    ?val. read_result cx pv mid = (INL val,mid) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv0) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)` by simp[] >>
  Q.SUBGOAL_THEN
    `?u Gf tnf tv.
       (!H. valid_horizon cx st0 H mid.storage_trace ==>
         gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
           (s,G,tn) [] (OK u,Gf,tnf) /\
         stmt_state_rel H ctx func ce cx mid u /\
         ghost_inv_at (DF H) lo d ce cx mid Gf tnf u) /\
       ~u.vs_halted /\ u.vs_current_bb = ss.cs_current_bb /\
       u.vs_inst_idx = LENGTH ss.cs_current_insts /\ alloca_history func u /\
       s0.vs_alloca_next <= u.vs_alloca_next /\ return_buf_frame d ce ss u /\
       ghost_kept_at lo ce started sa G0 tn0 s0 Gf tnf /\
       (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
       alloca_frame ce mid sm s ce mid u /\
       evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
       value_has_type tv v /\ val_wf tv v /\
       (!x. vv_operand snap = Var x ==> not_fresh_at ss x) /\
       ((is_word_type (lowered_value_type ce e) /\
         eval_operand (vv_operand snap) u = SOME (typed_val_to_w256 tv v) /\
         op_taint tnf (vv_operand snap) = {} /\ (!lbl. vv_operand snap <> Label lbl)) \/
        (~is_word_type (lowered_value_type ce e) /\ ?aid xd b.
          type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
          vv_operand snap = Var xd /\ lookup_var xd u = SOME (n2w b) /\
          FLOOKUP u.vs_allocas aid = SOME (b,type_memory_size tv) /\ aid < ss.cs_next_id /\
          lo <= b /\ b + type_memory_size tv < dimword (:256) /\
          b + type_memory_size tv <= u.vs_alloca_next /\
          (!n off len. local_region ce mid.scopes u n off len ==>
                       loweringStateRelDefs$regions_disjoint b (type_memory_size tv) off len) /\
          ptr_covers Gf tnf xd u (type_memory_size tv) /\
          (!mem. mem_agree_outside tnf.t_mem u.vs_memory mem ==> val_in_memory tv v b mem)))`
    (qx_choosel_then [`u`,`Gf`,`tnf`,`tv`] (map_every assume_tac o CONJUNCTS))
  >- ((Cases_on `is_word_type (lowered_value_type ce e)`
      >- (mp_tac (Q.INST [`es` |-> `started`, `ee` |-> `mid`, `sb` |-> `ss`,
                          `Gi` |-> `G0`, `ti` |-> `tn0`,
                          `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
                  body_assign_snapshot_word_joint) >>
          (impl_tac >- simp[]) >>
          disch_then (qx_choosel_then [`u`,`Gf`,`tnf`,`tv`] (map_every assume_tac o CONJUNCTS)) >>
          qexistsl [`u`,`Gf`,`tnf`,`tv`] >> simp[])
      >> mp_tac (Q.INST [`es` |-> `started`, `ee` |-> `mid`, `sb` |-> `ss`,
                         `Gi` |-> `G0`, `ti` |-> `tn0`,
                         `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
                 body_assign_snapshot_memory_joint) >>
      (impl_tac >- simp[]) >>
      disch_then (qx_choosel_then [`u`,`Gf`,`tnf`,`tv`,`xd`,`b`]
        (map_every assume_tac o CONJUNCTS)) >>
      qexistsl [`u`,`Gf`,`tnf`,`tv`] >> simp[] >> qexists_tac `sm.cs_next_id` >> simp[] >> (gvs[Q.INST [`es` |-> `started`, `ee` |-> `mid`, `sb` |-> `ss`,
                          `Gi` |-> `G0`, `ti` |-> `tn0`,
                          `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
                  body_assign_snapshot_word_joint, Q.INST [`es` |-> `started`, `ee` |-> `mid`, `sb` |-> `ss`,
                         `Gi` |-> `G0`, `ti` |-> `tn0`,
                         `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
                 body_assign_snapshot_memory_joint]))) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
    (qspec_then `Hr` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b` by
    (qpat_assum `gas_origin_ptr_path _ (s,_,_) [] (OK u,_,_)`
       (mp_tac o CONJUNCT2 o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
     disch_then (mp_tac o MATCH_MP forPtrAllocationFrameTheory.gas_path_ptr_old_allocations) >>
     simp[]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b` by
    (qpat_assum `vv_post Hr _ _ _ _ _ es _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE[vv_post_def]) >> simp[]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b` by
    metis_tac[] >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w` by
    (qpat_assum `vv_post Hr _ _ _ _ _ es _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[vv_post_def]) >> metis_tac[]) >>
  `alloca_frame ce es sa s0 ce mid u` by
    (irule stmtSimDefsTheory.alloca_frame_trans >> qexistsl_tac [`ce`,`mid`,`s`,`sm`] >> simp[]) >>
  `ghost_kept_at lo ce es sa G0 tn0 s0 Gf tnf` by
    (qpat_assum `ghost_kept_at lo ce started sa _ _ _ Gf tnf`
       (mp_tac o REWRITE_RULE[ghost_kept_at_def]) >>
     simp[Abbr `started`,ghost_kept_at_def] >> strip_tac >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `stmt_state_rel Hr _ _ _ _ mid u`
       (mp_then (Pos hd) mp_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >> simp[]) >>
  `!fn inst s. frag_reachable ctx func u fn inst s ==> dalloca_fmp_headroom inst s` by
    (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
     qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK u,Gf,tnf)` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` (fn phi =>
         qpat_assum `!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z`
           (fn nowrap => ACCEPT_TAC (MATCH_MP
             bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom
             (LIST_CONJ [path,phi,nowrap])))))) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func ce cx mid u /\ storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d ce cx mid Gf tnf u` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
        (qspec_then `H` (drule_then strip_assume_tac)) >> simp[] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ es s0 /\ _`
        (qspec_then `H` (drule_then (strip_assume_tac o REWRITE_RULE[vv_post_def]))) >>
     first_assum ACCEPT_TAC) >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x` by
    (rpt strip_tac >> `not_fresh_at sa x` by simp[] >> simp[]) >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x` by
    (rpt strip_tac >> `not_fresh_at sa x` by simp[] >> simp[]) >>
  `sa.cs_next_id <= ss.cs_next_id /\ sa.cs_next_var <= ss.cs_next_var` by decide_tac >>
  irule gasOutcomeFullGuardedTheory.gas_outcome_full_zero_prefix_guarded >>
  conj_tac >-
    (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
     simp[cj 8 vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_write_place]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`,`u`,`tnf`] >> conj_tac >-
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> first_assum ACCEPT_TAC) >>
  irule (Q.INST [`sty` |-> `lowered_value_type ce e`, `op` |-> `vv_operand snap`]
    body_assign_snapshot_bind_at_target) >>
  qpat_assum `assign_target_place_sim_full _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_get_target_ptr _ _ t ss = _` (irule_at Any) >>
  qpat_assum `compile_get_target_ptr _ _ (gas_shadow_target t) shss = _` (irule_at Any) >>
  qpat_assum `type_place_target env t = SOME (Type ty)` (irule_at Any) >>
  qpat_assum `evaluate_type _ (lowered_value_type ce e) = SOME tv` (irule_at Any) >>
  qpat_assum `ghost_kept_at lo ce es sa G0 tn0 s0 Gf tnf` (irule_at Any) >>
  qexists_tac `snap` >>
  rpt conj_tac >> rpt (first_assum ACCEPT_TAC) >>
  qx_genl_tac [`marks`,`p`,`ee`,`z`,`Gz`,`tnz`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!tv marks p ee z Gz tnz u. _ ==> gas_outcome_full _ _ _ _ (write_place _ _ _) _ _ _`
    (qspecl_then [`tv`,`marks`,`p`,`ee`,`z`,`Gz`,`tnz`,`u`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Theorem body_assign_saved_footprint_window[local]:
  wb_frame cenv es es sm s u /\
  ghost_kept_at lo cenv es sm (G : string |-> num # num) tn s Gu tnu /\
  ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < sm.cs_next_id /\
      b <= p /\ p + len <= b + sz /\
      (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
        b + sz <= lb \/ lb + lsz <= b)) \/
   (?n b sz. local_region cenv es.scopes s n b sz /\ b <= p /\ p + len <= b + sz) \/
   len = 0) ==>
  mem_bytes_at p len u.vs_memory = mem_bytes_at p len s.vs_memory /\
  (!i. p <= i /\ i < p + len /\ i IN tnu.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac
  >- (fs[wb_frame_def, ghost_kept_at_def] >>
      `mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (qpat_assum `!aid off sz. _ ==> mem_bytes_at _ _ _ = _`
           (qspecl_then [`aid`,`b`,`sz`] mp_tac) >> metis_tac[]) >>
      conj_tac >- (drule mem_bytes_at_agree_window >> metis_tac[arithmeticTheory.ADD_COMM]) >>
      rpt strip_tac >>
      `b <= i /\ i < b + sz` by decide_tac >>
      qpat_assum `!aid off sz i. _ ==> i IN tn.t_mem`
        (qspecl_then [`aid`,`b`,`sz`,`i`] mp_tac) >> metis_tac[])
  >- (fs[wb_frame_def, locals_kept_def, ghost_kept_at_def] >>
      `mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (qpat_assum `!n b sz. _ ==> mem_bytes_at _ _ _ = _`
           (qspecl_then [`n`,`b`,`sz`] mp_tac) >> simp[]) >>
      conj_tac >- (drule mem_bytes_at_agree_window >> metis_tac[arithmeticTheory.ADD_COMM]) >>
      rpt strip_tac >>
      `b <= i /\ i < b + sz` by decide_tac >>
      qpat_assum `!n b sz i. _ ==> i IN tn.t_mem`
        (qspecl_then [`n`,`b`,`sz`,`i`] mp_tac) >> simp[]) >>
  fs[mem_bytes_at_def] >> decide_tac
QED

(* Saved RHS without an intermediate copy. *)

Theorem body_assign_saved_rhs_memory_frame[local]:
  vv_at cenv cx (post_value_type cenv e) sa sm es tv vv s /\
  vv_holds cenv cx (post_value_type cenv e) tv vv es s /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  read_result cx tv es = (INL v,es) /\ read_result cx tv ee = (INL v,ee) /\
  wb_frame cenv es es sm s u /\ ghost_kept_at lo cenv es sm G tn s Gu tnu /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!l. vv_operand vv <> Label l) /\ s.vs_alloca_next <= u.vs_alloca_next /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv es G tn s /\
  ((vv_location vv = NONE /\ ~is_word_type (post_value_type cenv e) \/
    vv_location vv = SOME LocMemory) ==> ptr_buf_ok cenv e (vv_operand vv) G s) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) es tv vv s ==>
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee Gu tnu u /\
  ((vv_location vv = NONE /\ ~is_word_type (post_value_type cenv e) \/
    vv_location vv = SOME LocMemory) ==> ptr_buf_ok cenv e (vv_operand vv) Gu u) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv u
Proof
  qabbrev_tac `ty = post_value_type cenv e` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s` by
    (`?w. eval_operand (vv_operand vv) s = SOME w` by
       (Cases_on `vv` >> fs[vv_holds_def, contextTheory.vv_operand_def, expr_val_rel_def] >>
        metis_tac[]) >>
     simp[] >> irule exprBopSimPropsTheory.eval_operand_frame >>
     simp[] >> qexistsl_tac [`sm`,`s`] >> fs[wb_frame_def]) >>
  `!x. vv_operand vv = Var x ==> FLOOKUP Gu x = FLOOKUP G x` by
    (fs[ghost_kept_at_def] >> metis_tac[]) >>
  `op_taint tnu (vv_operand vv) = op_taint tn (vv_operand vv)` by
    (Cases_on `vv_operand vv` >> gvs[op_taint_def, ghost_kept_at_def]) >>
  `vv_store_bound cx ty (lowered_value_type cenv e) ee tv vv u` by
    (irule vv_store_bound_frame_mem_src >> qexists_tac `s` >> simp[] >>
     fs[vv_store_bound_def] >> metis_tac[]) >>
  simp[] >> reverse conj_tac
  >- (disch_tac >> irule ptr_buf_ok_frame >> qexistsl_tac [`G`,`s`] >> simp[] >> metis_tac[]) >>
  `!vt w. (vv_location vv = SOME LocMemory \/ ~is_word_type ty) /\
      evaluate_type (get_tenv cx) ty = SOME vt /\ eval_operand (vv_operand vv) s = SOME w ==>
      val_wf vt v /\
      mem_bytes_at (w2n w) (val_footprint vt v) u.vs_memory =
        mem_bytes_at (w2n w) (val_footprint vt v) s.vs_memory /\
      (!i. w2n w <= i /\ i < w2n w + val_footprint vt v /\ i IN tnu.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >>
     Cases_on `vv` >>
     (gvs[contextTheory.vv_operand_def, vv_location_def, vv_at_def, expr_val_at_def]
      >>~- ([`mem_bytes_at _ 0 _ = _ /\ _`], simp[mem_bytes_at_def] >> decide_tac)) >>
     MATCH_MP_TAC body_assign_saved_footprint_window >>
     simp[SF SFY_ss] >>
     disj1_tac >> HINT_EXISTS_TAC >> simp[] >>
     qpat_assum `!n lb lsz. local_region _ _ _ n lb lsz ==> _` ACCEPT_TAC) >>
  Cases_on `vv` >> gvs[contextTheory.vv_operand_def, vv_location_def, ptr_vv_ok_def]
  >- (irule ptr_val_ok_footprint_frame >> metis_tac[]) >>
  simp[ptr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
  simp[ptr_mem_ok_def] >> strip_tac >>
  reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >> irule robust_val_in_memory_footprint_frame >> metis_tac[]
QED


Theorem body_assign_immutable_direct_prefix[local]:
  compile_assign_value ce (Lit (n2w off)) LocCode op F loc ity sty bytes su = ((),sb) /\
  fn_has_code su sb func /\ ~block_is_terminated sb /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce su /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ity /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME itv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  ity = sty /\ ~is_bytestring_type ity /\
  copy_size = (if is_bytestring_type ity then type_memory_bytes ce sty else bytes) /\
  n = (if copy_size <= 32 then 1 else (copy_size+31) DIV 32) /\
  32*n <= type_memory_size itv /\
  value_has_type itv v /\ value_has_type stv v /\
  val_in_memory stv v a s.vs_memory /\ val_footprint stv v <= k /\
  k <= 32*n /\ a+k < dimword (:256) /\ off+32*n < dimword (:256) /\
  (a+k <= off \/ off+32*n <= a) /\
  write_place cx (ImmutablePlace ce.ce_module id []) v ee = (INL (),fin) /\
  (!x. op = Var x ==> not_fresh_at su x) /\
  (!region x. ce.ce_imm_alloca = SOME region /\ region = Var x ==> not_fresh_at su x) /\
  eval_operand op s = SOME (n2w a) /\
  body_inv tops ctx ce cx /\ struct_args_unique tops /\
  tops = pre ++ VariableDecl vis Immutable id ity slot :: post /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  fn_inst_ids_distinct func /\
  ~is_word_type ity /\ val_wf stv v /\
  ptr_val_ok cx ity v op G tn s /\
  lo <= a /\ a+32*n <= s.vs_alloca_next /\ off+32*n <= lo /\
  return_buf_frame d ce su s /\ alloca_history func s ==>
  ?q Gs ts.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK q,Gs,ts)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_post H ctx func cx lctx ce ce su sb ee s (INL ()) fin q) /\
    itv = stv /\ k = 32*n /\ 32*n = type_memory_size itv /\
    mem_bytes_at off k q.vs_memory = mem_bytes_at a k s.vs_memory /\
    val_in_memory itv v off q.vs_memory /\
    immutable_value_bytes_rel itv v (mem_bytes_at off k q.vs_memory) /\
    immutable_value_admissible itv v /\ LENGTH s.vs_memory <= LENGTH q.vs_memory /\
    (!p len. regions_disjoint p len off k ==>
      mem_bytes_at p len q.vs_memory = mem_bytes_at p len s.vs_memory) /\
    q.vs_immutables = (immutable_transfers T T (n2w a) (n2w off) n 0 s).vs_immutables /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_immutables := s.vs_immutables; vs_inst_idx := s.vs_inst_idx|>) = s /\
    q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
    q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
    q.vs_requests = s.vs_requests /\ q.vs_call_ctx = s.vs_call_ctx /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    su.cs_next_var <= sb.cs_next_var /\
    (!x. not_fresh_at su x ==>
      lookup_var x q = lookup_var x s /\ FLOOKUP Gs x = FLOOKUP G x /\
      op_taint ts (Var x) = op_taint tn (Var x)) /\
    (!i. i IN ts.t_mem <=>
      if off <= i /\ i < off + 32*n then a+(i-off) IN tn.t_mem else i IN tn.t_mem) /\
    ts.t_stor = tn.t_stor /\ ts.t_trans = tn.t_trans /\
    EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts su sb) /\
    sb.cs_current_bb = su.cs_current_bb /\
    sb.cs_current_insts = su.cs_current_insts ++ emitted_insts su sb
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `itv = stv` by metis_tac[SOME_11] >>
  `val_footprint stv v = type_memory_size itv` by
    metis_tac[nonbytes_evaluated_val_footprint] >>
  `k = 32*n /\ 32*n = type_memory_size itv` by decide_tac >>
  `compile_imm_store_words ce.ce_imm_alloca op (Lit (n2w off)) n 0 su = ((),sb)` by
    (qpat_x_assum `n = _` (fn th => rewrite_tac[th]) >>
     irule immutable_store_suffix_words >>
     fs[compile_assign_value_def, comp_bind_def, comp_return_def] >>
     gvs[comp_return_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `alloca_inv s /\ fmp_room ctx func s /\ immutable_base_zero ce s` by
    (qpat_assum `stmt_state_rel _ ctx func ce cx ee s` (fn th =>
       map_every (fn proj => assume_tac (MATCH_MP proj th))
         [stmt_state_rel_local_ptrs_alloca, stmt_state_rel_fmp_room,
          stmt_state_rel_immutable_base_zero]) >>
     fs[]) >>
  `!region. ce.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w` by
    fs[immutable_base_zero_def] >>
  `!x. Lit (n2w off) = Var x ==> not_fresh_at su x` by simp[] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all immutable_words_old_prefix_path >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  `0 < 32*n` by
    (qpat_assum `n = _` (fn th => pure_rewrite_tac[th]) >>
     Cases_on `copy_size <= 32` >- simp[] >>
     `~(copy_size + 31 < 32)` by decide_tac >>
     qpat_assum `~(copy_size <= 32)` (fn th => pure_rewrite_tac[th, COND_CLAUSES]) >>
     simp[NoAsms, GSYM NOT_ZERO_LT_ZERO, DIV_EQ_0] >> first_assum ACCEPT_TAC) >>
  `a < dimword (:256) /\ off < dimword (:256) /\ lo <> 0` by decide_tac >>
  `val_store_size itv v = type_memory_size itv` by
    metis_tac[bodyDeclMemoryCoreTheory.val_store_size_non_bytestring] >>
  `op_taint tn op = {} /\ ptr_mem_ok cx ity v op G tn s` by
    fs[ptr_val_ok_def] >>
  qpat_assum `ptr_mem_ok _ _ _ _ _ _ _`
    (qspecl_then [`itv`, `n2w a`] mp_tac o REWRITE_RULE[ptr_mem_ok_def]) >>
  simp[w2n_n2w, LESS_MOD] >> strip_tac >>
  `?root. op = Var root /\ ptr_covers G tn root s (32*n) /\
          lookup_var root s = SOME (n2w a)` by
    (`type_memory_size stv <> 0` by metis_tac[NOT_ZERO_LT_ZERO] >>
     qpat_assum `type_memory_size stv <> 0 ==> _` drule >>
     strip_tac >> rename1 `op = Var p` >> qexists `p` >>
     fs[ptr_covers_def, eval_operand_def, w2n_n2w, LESS_MOD] >> metis_tac[]) >>
  `allocas_from lo s` by fs[ghost_inv_at_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    (strip_tac >>
     qpat_x_assum `alloca_inv s` mp_tac >>
     qpat_x_assum `fmp_room ctx func s` mp_tac >>
     simp[allocas_below_fmp_def, exprLoweringPropsTheory.fmp_room_def,
          venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     rpt strip_tac >> res_tac >> decide_tac) >>
  qabbrev_tac `q = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `not_fresh_at su root` by metis_tac[] >>
  `lookup_var root (drop_fresh su s) = SOME (n2w a) /\
   ptr_covers G tn root (drop_fresh su s) (32*n)` by
    (qpat_x_assum `ptr_covers G tn root s (32*n)` mp_tac >>
     simp[varsExtTheory.lookup_var_drop_fresh, ptr_covers_def]) >>
  `!x. ce.ce_imm_alloca = SOME (Var x) ==>
       FLOOKUP G x = NONE /\ op_taint tn (Var x) = {}` by
    (qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_once_rewrite_tac[ghost_inv_at_def] >> strip_tac >> metis_tac[]) >>
  `!region. ce.ce_imm_alloca = SOME region ==>
     eval_operand region (drop_fresh su s) = SOME 0w /\
     copy_old_operand su region /\ op_taint tn region = {} /\ op_prov G region = NONE` by
    (rpt strip_tac
     >- (irule EQ_TRANS >> qexists `eval_operand region s` >>
         conj_tac >- (irule freshWritesTheory.eval_operand_drop_fresh >> metis_tac[]) >>
         metis_tac[])
     >- (simp[exprSimCopyTheory.copy_old_operand_def] >> metis_tac[])
     >- (Cases_on `region` >> simp[op_taint_def] >>
         qpat_assum `!x. ce.ce_imm_alloca = SOME (Var x) ==> _` drule >>
         simp[op_taint_def])
     >> Cases_on `region` >> simp[op_prov_def] >>
     qpat_assum `!x. ce.ce_imm_alloca = SOME (Var x) ==> _` drule >> simp[]) >>
  `allocas_from lo (drop_fresh su s) /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp (drop_fresh su s))` by
    ((qpat_x_assum `allocas_from lo s` mp_tac >>
     qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[varsExtTheory.drop_fresh_def, allocas_from_def, allocas_below_fmp_def] >> (metis_tac[varsExtTheory.drop_fresh_def, allocas_from_def, allocas_below_fmp_def]))) >>
  `!D. ?Gs ts r.
     immutable_execution_frame su (drop_fresh su s) sb r /\
     (!pc. inst_seq_ptr D lo ctx func PG G tn (emitted_insts su sb)
          (drop_fresh su s with vs_inst_idx := pc) Gs ts) /\
     EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts su sb) /\
     (!x. x IN ts.t_mem <=>
        if off <= x /\ x < off + 32*n then a + (x-off) IN tn.t_mem
        else x IN tn.t_mem) /\
     ts.t_stor = tn.t_stor /\ ts.t_trans = tn.t_trans /\
     (!p. not_fresh_at su p ==> FLOOKUP Gs p = FLOOKUP G p /\
          op_taint ts (Var p) = op_taint tn (Var p))` by
    (gen_tac >>
     `compile_imm_store_words ce.ce_imm_alloca (Var root) (Lit (n2w off)) n 0 su = ((),sb)` by
       metis_tac[] >>
     `fresh_vars_wrt su (drop_fresh su s)` by simp[varsExtTheory.fresh_vars_wrt_drop_fresh] >>
     `copy_old_operand su (Lit (n2w off)) /\
      eval_operand (Lit (n2w off)) (drop_fresh su s) = SOME (n2w off) /\
      op_taint tn (Lit (n2w off)) = {} /\ op_prov G (Lit (n2w off)) = NONE` by
       simp[exprSimCopyTheory.copy_old_operand_def, eval_operand_def, op_taint_def, op_prov_def] >>
     `w2n (n2w off:bytes32) + 0 + 32*n <= lo /\ lo <= w2n (n2w a:bytes32) /\
      0 + 32*n <= 32*n /\ w2n (n2w a:bytes32) + 32*n < dimword (:256)` by
       (`w2n (n2w off:bytes32) = off /\ w2n (n2w a:bytes32) = a` by
          simp[w2n_n2w, LESS_MOD] >>
        qpat_x_assum `w2n (n2w off:bytes32) = off` SUBST1_TAC >>
        qpat_x_assum `w2n (n2w a:bytes32) = a` SUBST1_TAC >> decide_tac) >>
     drule_all code_ctor_store_range_ptr >>
     disch_then (strip_assume_tac o Q.INST [`fn` |-> `func`] o SPEC_ALL) >>
     rename1 `immutable_execution_frame su (drop_fresh su s) sb clean` >>
     qexistsl [`Gf`, `tnf`, `clean`] >>
     simp[w2n_n2w, LESS_MOD]) >>
  `EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts su sb) /\
   !D. ?Gs ts.
     inst_seq_ptr D lo ctx func PG G tn (emitted_insts su sb) s Gs ts /\
     (!x. x IN ts.t_mem <=>
        if off <= x /\ x < off + 32*n then a + (x-off) IN tn.t_mem
        else x IN tn.t_mem) /\
     ts.t_stor = tn.t_stor /\ ts.t_trans = tn.t_trans /\
     (!p. not_fresh_at su p ==> FLOOKUP Gs p = FLOOKUP G p /\
          op_taint ts (Var p) = op_taint tn (Var p))` by
    (conj_tac
     >- (qpat_assum `!D. ?Gs ts r. _` (qspec_then `DF (storage_trace_horizon ee.storage_trace)` strip_assume_tac) >>
         first_assum ACCEPT_TAC) >>
     gen_tac >> qpat_assum `!D. ?Gs ts r. _` (qspec_then `D` strip_assume_tac) >>
     qexistsl [`Gs`, `ts`] >>
     conj_tac >-
       (irule immutable_direct_sequence_ptr >> simp[] >>
        qexists `drop_fresh su s` >> simp[varsExtTheory.vars_ext_drop_fresh] >>
        conj_tac >- fs[immutable_execution_frame_def] >>
        qpat_x_assum `!pc. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
          (qspec_then `(drop_fresh su s).vs_inst_idx` mp_tac) >> simp[]) >>
     asm_rewrite_tac[]) >>
  qpat_assum `!D. ?Gs ts. _` (qspec_then `DF (storage_trace_horizon ee.storage_trace)` strip_assume_tac) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts su sb) s Gs ts` by
    ((gen_tac >> qpat_assum `!D. ?Gs ts. _` (qspec_then `D` strip_assume_tac) >>
     drule_all inst_seq_ptr_ghost_unique >> simp[] >> (metis_tac[inst_seq_ptr_ghost_unique]))) >>
  `run_inst_seq_mem_ok (emitted_insts su sb) s` by
    (irule immutable_direct_words_mem_ok >>
     qexistsl [`n2w a`, `n2w off`, `Lit (n2w off)`, `ce.ce_imm_alloca`,
              `n`, `0`, `op`] >>
     simp[w2n_n2w, LESS_MOD, IgnAsm `off = _`, IgnAsm `32*n = _`,
          IgnAsm `n = _`] >> decide_tac) >>
  `sb.cs_current_bb = su.cs_current_bb` by fs[same_blocks_def] >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
       (emitted_insts su sb)` by
    (simp[EVERY_MEM] >> gen_tac >> disch_tac >>
     qpat_assum `EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) _`
       (drule_then (strip_assume_tac o BETA_RULE) o REWRITE_RULE[EVERY_MEM, MEM]) >>
     simp[is_terminator_def]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts su sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> gen_tac >> disch_tac >>
     qpat_assum `EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) _`
       (drule_then (strip_assume_tac o BETA_RULE) o REWRITE_RULE[EVERY_MEM, MEM]) >>
     simp[]) >>
  `ctx_has_dalloca ctx ==> !pre i post u'.
     emitted_insts su sb = pre ++ i::post /\ run_inst_seq pre s = OK u' ==>
     dalloca_no_wrap i u'` by
    (rpt strip_tac >>
     qpat_assum `EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) _` mp_tac >>
     qpat_assum `emitted_insts _ _ = _ ++ _` (fn th => pure_rewrite_tac [th]) >>
     simp[EVERY_APPEND] >> strip_tac >>
     irule dalloca_no_wrap_non_dalloca >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK q,Gs,ts)` by
    (gen_tac >> qpat_assum `!D. inst_seq_ptr D lo ctx func PG G tn _ _ _ _`
       (qspec_then `D` assume_tac) >>
     `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      isPREFIX (emitted_insts su sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
     drule_all run_inst_seq_gas_origin_ptr_path >>
     disch_then (mp_tac o SPEC_ALL) >> simp[Abbr `q`]) >>
  `val_in_memory itv v off u.vs_memory /\
   immutable_value_bytes_rel itv v (mem_bytes_at off (type_memory_size itv) u.vs_memory)` by
    (irule immutableDeployMeaningfulTransferTheory.immutable_direct_meaningful_transfer >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`ity`,`s.vs_memory`,`k`,`a`,`stv`,`sty`,`get_tenv cx`] >>
     simp[IgnAsm `off = _`]) >>
  `LENGTH s.vs_memory <= LENGTH u.vs_memory` by
    (drule_all immutableAssignStoreLengthTheory.immutable_assign_store_words_memory_length >> simp[]) >>
  `immutable_value_admissible itv v` by
    (drule_all immutableDeployAssignAdmissibleTheory.evaluated_immutable_admissible >> simp[]) >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_requests = s.vs_requests /\ u.vs_call_ctx = s.vs_call_ctx /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
   (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
     vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
     vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s` by
    (qpat_assum `u with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = s`
       mp_tac >> simp[venom_state_component_equality]) >>
  `!p len. regions_disjoint p len off (type_memory_size itv) ==>
     mem_bytes_at p len u.vs_memory = mem_bytes_at p len s.vs_memory` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!p len. _ ==> mem_bytes_at p len u.vs_memory = _` irule >>
     qpat_x_assum `regions_disjoint _ _ _ _` mp_tac >>
     pure_rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_post H ctx func cx lctx ce ce su sb ee s (INL ()) fin q` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `Abbrev (q = _)` (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     irule immutable_assign_suffix_stmt_post >>
     simp[IgnAsm `off = _`] >>
     qexistsl [`env`,`id`,`itv`,`ity`,`off`,`v`] >> simp[IgnAsm `off = _`]) >>
  `k = type_memory_size itv` by decide_tac >>
  `q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
             vs_immutables := s.vs_immutables; vs_inst_idx := s.vs_inst_idx|> = s` by
    (qpat_assum `u with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = s`
       (mp_tac o Q.AP_TERM `\st. st with vs_inst_idx := s.vs_inst_idx`) >>
     simp[NoAsms, Abbr `q`]) >>
  `!x. not_fresh_at su x ==> lookup_var x q = lookup_var x s /\
       FLOOKUP Gs x = FLOOKUP G x /\ op_taint ts (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (qpat_assum `!x. not_fresh_at su x ==> lookup_var x u = _` drule >>
         simp[NoAsms, Abbr `q`, lookup_var_def]) >>
     qpat_assum `!p. not_fresh_at su p ==> FLOOKUP Gs p = _ /\ _` drule >> simp[]) >>
  `!p len. regions_disjoint p len off k ==>
      mem_bytes_at p len q.vs_memory = mem_bytes_at p len s.vs_memory` by
    (qpat_assum `k = type_memory_size itv` SUBST1_TAC >>
     simp[NoAsms, Abbr `q`] >> first_assum ACCEPT_TAC) >>
  `immutable_value_bytes_rel itv v (mem_bytes_at off k q.vs_memory)` by
    (qpat_assum `k = type_memory_size itv` SUBST1_TAC >>
     simp[NoAsms, Abbr `q`] >> first_assum ACCEPT_TAC) >>
  `mem_bytes_at off k q.vs_memory = mem_bytes_at a k s.vs_memory /\
   val_in_memory itv v off q.vs_memory /\
   LENGTH s.vs_memory <= LENGTH q.vs_memory /\
   q.vs_immutables = (immutable_transfers T T (n2w a) (n2w off) n 0 s).vs_immutables /\
   q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
   q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
   q.vs_requests = s.vs_requests /\ q.vs_call_ctx = s.vs_call_ctx /\
   ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
   q.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (simp[NoAsms, Abbr `q`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl [`q`,`Gs`,`ts`] >>
  qpat_x_assum `k = type_memory_size itv` SUBST_ALL_TAC >>
  qpat_x_assum `itv = stv` SUBST_ALL_TAC >>
  qpat_x_assum `off = compute_immutables_len _ _` SUBST_ALL_TAC >>
  qpat_x_assum `tops = _` SUBST_ALL_TAC >>
  qpat_x_assum `ity = sty` SUBST_ALL_TAC >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  `copy_size = bytes` by
    (qpat_assum `copy_size = _` (fn th => pure_once_rewrite_tac[th]) >>
     qpat_assum `~is_bytestring_type sty` (fn th => rewrite_tac[th])) >>
  `n = (if bytes <= 32 then 1 else (bytes+31) DIV 32)` by
    (qpat_assum `n = (if copy_size <= _ then _ else _)` mp_tac >>
     qpat_assum `copy_size = bytes` (fn th => rewrite_tac[th])) >>
  qpat_assum `n = (if bytes <= _ then _ else _)` (SUBST1_TAC o SYM) >>
  rpt conj_tac >> every_assum CHECK_ASSUME_TAC
  >- (qpat_assum `s.vs_inst_idx = LENGTH su.cs_current_insts` (SUBST1_TAC o SYM) >>
      qpat_assum `q with <|vs_vars := _; vs_memory := _; vs_immutables := _; vs_inst_idx := _|> = s`
        mp_tac >> simp[NoAsms, venom_state_component_equality])
  >- (qpat_assum `sb.cs_current_insts = _ ++ _` (fn th =>
        qpat_assum `q.vs_inst_idx = LENGTH sb.cs_current_insts`
          (ACCEPT_TAC o REWRITE_RULE[th, LENGTH_APPEND])))
  >- (qpat_assum `32*n = type_memory_size stv` (fn th =>
        qpat_assum `!i. i IN ts.t_mem <=> _` (mp_tac o REWRITE_RULE[th])) >>
      simp[NoAsms]) >>
  qpat_assum `EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) _`
    (ACCEPT_TAC o REWRITE_RULE[MEM])
QED

Theorem body_assign_immutable_direct_joint[local]:
  compile_assign_value ce (Lit (n2w off)) LocCode op F loc ity sty bytes su = ((),sb) /\
  fn_has_code su sb func /\ ~block_is_terminated sb /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce su /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ity /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME itv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  ity = sty /\ ~is_bytestring_type ity /\
  copy_size = (if is_bytestring_type ity then type_memory_bytes ce sty else bytes) /\
  n = (if copy_size <= 32 then 1 else (copy_size+31) DIV 32) /\
  32*n <= type_memory_size itv /\
  value_has_type itv v /\ value_has_type stv v /\
  val_in_memory stv v a s.vs_memory /\ val_footprint stv v <= k /\
  k <= 32*n /\ a+k < dimword (:256) /\ off+32*n < dimword (:256) /\
  (a+k <= off \/ off+32*n <= a) /\
  write_place cx (ImmutablePlace ce.ce_module id []) v ee = (INL (),fin) /\
  (!x. op = Var x ==> not_fresh_at su x) /\
  (!region x. ce.ce_imm_alloca = SOME region /\ region = Var x ==> not_fresh_at su x) /\
  eval_operand op s = SOME (n2w a) /\
  body_inv tops ctx ce cx /\ struct_args_unique tops /\
  tops = pre ++ VariableDecl vis Immutable id ity slot :: post /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  fn_inst_ids_distinct func /\
  ~is_word_type ity /\ val_wf stv v /\
  ptr_val_ok cx ity v op G tn s /\
  lo <= a /\ a+32*n <= s.vs_alloca_next /\ off+32*n <= lo /\
  return_buf_frame d ce su s /\ alloca_history func s /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) ==>
  ?q Gf tnf.
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK q,Gf,tnf) /\
      stmt_post H ctx func cx lctx ce ce su sb ee s (INL ()) fin q /\
      ghost_inv_at (DF H) lo d ce cx fin Gf tnf q) /\
    return_buf_frame d ce sb q /\ alloca_history func q /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
    ghost_kept_at lo ce ee su G tn s Gf tnf /\
    alloca_frame ce ee su s ce fin q /\
    (!x. not_fresh_at su x ==>
      lookup_var x q = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!aid b sz i. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      aid < su.cs_next_id /\ b <= i /\ i < b+sz /\ i IN tnf.t_mem ==>
      i IN tn.t_mem) /\
    q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
    q.vs_requests = s.vs_requests /\ q.vs_call_ctx = s.vs_call_ctx /\
    q.vs_alloca_next = s.vs_alloca_next /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all body_assign_immutable_direct_prefix >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) _ [] (OK q,Gs,ts)` >>
  `off+k <= lo` by decide_tac >>
  `a < dimword (:256)` by decide_tac >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory itv v a m` by
    (`ptr_mem_ok cx ity v op G tn s` by fs[ptr_val_ok_def] >>
     qpat_assum `ptr_mem_ok _ _ _ _ _ _ _`
       (qspecl_then [`itv`,`n2w a`] mp_tac o REWRITE_RULE[ptr_mem_ok_def]) >>
     simp[w2n_n2w, LESS_MOD]) >>
  `mem_bytes_at off k (mem_bytes_at 0 lo q.vs_memory) = mem_bytes_at off k q.vs_memory` by
    (irule listTheory.LIST_EQ >> simp[NoAsms, valueEncodingProofsTheory.EL_mem_bytes_at] >>
     rpt strip_tac >> `off+x < lo` by decide_tac >>
     qpat_assum `off+x < lo` (fn th =>
       simp[NoAsms, th, valueEncodingProofsTheory.EL_mem_bytes_at])
     >> qpat_assum `x < k` (fn th =>
       simp[NoAsms, th, valueEncodingProofsTheory.EL_mem_bytes_at])) >>
  `!m. mem_agree_outside ts.t_mem (mem_bytes_at 0 lo q.vs_memory) m ==>
       val_in_memory itv v off m` by
    (gen_tac >> strip_tac >> irule robust_val_in_memory_copy_transport >>
     conj_tac >- fs[] >>
     qexistsl [`s.vs_memory`,`mem_bytes_at 0 lo q.vs_memory`,`k`,`a`,`tn.t_mem`,`ts.t_mem`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (gen_tac >> disch_tac >>
         `off <= off+i /\ off+i < off+32*n` by decide_tac >>
         qpat_assum `!j. j IN ts.t_mem <=> _` (qspec_then `off+i` mp_tac) >>
         simp[IgnAsm `off = _`, IgnAsm `k = _`, IgnAsm `32*n = _`]) >>
     rpt conj_tac
     >- (qpat_assum `itv = stv` SUBST1_TAC >> first_assum ACCEPT_TAC)
     >- (irule EQ_TRANS >> qexists `mem_bytes_at off k q.vs_memory` >>
         conj_tac >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `!i. off <= i /\ i < off+k /\ i IN ts.t_mem ==>
       mem_dead_bytes (mem_bytes_at 0 lo q.vs_memory) off itv i` by
    (`well_formed_type_value itv` by
       (drule vyperTypeValuesTheory.evaluate_type_well_formed_type_value >> simp[]) >>
     `val_wf itv v` by metis_tac[] >>
     qspecl_then [`itv`,`v`,`off`,`mem_bytes_at 0 lo q.vs_memory`,`ts.t_mem`]
       mp_tac immutableRepSensitivityTheory.body_assign_immutable_rep_sensitivity >>
     (impl_tac >- (rpt conj_tac >> every_assum CHECK_ASSUME_TAC >> simp[])) >>
     rpt strip_tac >>
     `off + (i-off) = i /\ i-off < type_memory_size itv` by decide_tac >>
     qpat_assum `!j. _ ==> mem_dead_bytes _ _ _ _` (qspec_then `i-off` mp_tac) >>
     qpat_assum `off+(i-off) = i` (fn th => pure_rewrite_tac[th]) >>
     every_assum CHECK_ASSUME_TAC >>
     qpat_assum `i-off < type_memory_size itv` (fn th =>
       qpat_assum `i IN ts.t_mem` (fn th' => simp[NoAsms, th, th']))) >>
  `!i. ~(off <= i /\ i < off+k) ==> (i IN ts.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >>
     qpat_assum `!j. j IN ts.t_mem <=> _` (qspec_then `i` mp_tac) >>
     qpat_assum `k = 32*n` (fn th => pure_rewrite_tac[GSYM th]) >>
     simp[IgnAsm `k = _`, IgnAsm `off = _`]) >>
  `!i. i < lo /\ ~(off <= i /\ i < off+k) ==>
       EL i (mem_bytes_at 0 lo q.vs_memory) = EL i (mem_bytes_at 0 lo s.vs_memory)` by
    (rpt strip_tac >>
     `regions_disjoint i 1 off k` by
       (pure_rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     qpat_assum `!p len. _ ==> mem_bytes_at p len q.vs_memory = _`
       (drule_then (mp_tac o Q.AP_TERM `EL 0`)) >>
     qpat_assum `i < lo` (fn th =>
       simp[NoAsms, th, valueEncodingProofsTheory.EL_mem_bytes_at])) >>
  `ce.ce_module = NONE /\ get_module_code cx NONE = SOME tops /\
   ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
    (drule_then strip_assume_tac body_inv_module_locations >>
     drule_then strip_assume_tac body_inv_main_code >>
     drule_then (assume_tac o MATCH_MP contract_inv_singleton_source_modules)
       body_inv_contract >> simp[]) >>
  `cx_tops cx = tops` by metis_tac[gasContextTheory.cx_tops_module] >>
  `get_tenv cx = type_env tops` by
    simp[get_tenv_def, type_env_all_modules_def, GSYM type_env_def] >>
  `evaluate_type (type_env tops) ity = SOME itv` by metis_tac[] >>
  `k = type_memory_size itv` by decide_tac >>
  `!D. ghost_inv_at D lo d ce cx ee G tn s ==>
       !i. i < lo /\ i IN ts.t_mem ==>
         imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo q.vs_memory) i` by
    (gen_tac >> disch_then
       (assume_tac o el 5 o CONJUNCTS o REWRITE_RULE[ghost_inv_at_def]) >>
     qpat_assum `cx_tops cx = tops` SUBST_ALL_TAC >>
     gen_tac >> strip_tac >>
     irule immutable_section_replace >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`tn.t_mem`,`ts.t_mem`,`lo`,`id`,`off`,`post`,`pre`,
               `mem_bytes_at 0 lo s.vs_memory`,`slot`,`itv`,`ity`,`vis`] >>
     qpat_assum `k = type_memory_size itv` (fn th => pure_rewrite_tac[GSYM th]) >>
     rpt conj_tac >> every_assum CHECK_ASSUME_TAC
     >- (rpt strip_tac >>
         qpat_assum `!i. ~(off <= i /\ i < off+k) ==> _`
           (qspec_then `j` (drule_then (fn th => pure_rewrite_tac[GSYM th]))) >>
         first_assum ACCEPT_TAC)
     >> simp[NoAsms] >> every_assum CHECK_ASSUME_TAC) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qabbrev_tac `hc = storage_trace_horizon ee.storage_trace` >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (qspec_then `hc` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_post H ctx func cx lctx ce ce su sb ee s (INL ()) fin q`
    (qspec_then `hc` (drule_then assume_tac)) >>
  `stmt_state_rel hc ctx func ce cx fin q /\ alloca_frame ce ee su s ce fin q` by
    (qpat_assum `stmt_post hc ctx func cx lctx ce ce su sb ee s (INL ()) fin q` mp_tac >>
     simp[NoAsms, stmt_post_def]) >>
  `local_ptrs_rel func ce ee.scopes s` by
    (qpat_assum `stmt_state_rel hc ctx func ce cx ee s`
       (ACCEPT_TAC o CONJUNCT1 o MATCH_MP stmt_state_rel_local_ptrs_alloca)) >>
  `fin.scopes = ee.scopes` by metis_tac[vyperPlaceFramesTheory.write_immutable_place_scopes] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (qpat_assum `ghost_inv_at (DF hc) _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[ghost_inv_at_def]) >> simp[]) >>
  `allocas_from lo q /\ lo <= q.vs_alloca_next` by
    (qpat_assum `q.vs_allocas = s.vs_allocas` (fn h =>
       qpat_assum `q.vs_alloca_next = s.vs_alloca_next` (fn h' =>
         pure_rewrite_tac[allocas_from_def, h, h'])) >>
     conj_tac
     >- qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def]) >>
     first_assum ACCEPT_TAC) >>
  `!i. lo <= i /\ i IN ts.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >> `~(off <= i /\ i < off+k)` by decide_tac >>
     qpat_assum `!i. ~(off <= i /\ i < off+k) ==> _`
       (qspec_then `i` (drule_then (fn th => pure_rewrite_tac[GSYM th]))) >>
     first_assum ACCEPT_TAC) >>
  `!name b len. local_region ce ee.scopes s name b len /\ 0 < len ==> lo <= b` by
    (rpt strip_tac >>
     `dead_lo_ok hc (DF hc) lo ce cx` by simp[] >>
     drule_all bodyFullMemoryFramesTheory.body_full_local_region_lower_bound >> simp[]) >>
  `!name b len. local_region ce ee.scopes s name b len ==>
     mem_bytes_at b len q.vs_memory = mem_bytes_at b len s.vs_memory /\
     (!i. b <= i /\ i < b+len /\ i IN ts.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >> Cases_on `len = 0`
     >- (qpat_assum `len = 0` SUBST1_TAC >>
         simp[NoAsms, valueEncodingDefsTheory.mem_bytes_at_def] >> decide_tac) >>
     `0 < len` by decide_tac >>
     `lo <= b` by
       (qpat_assum `!name b len. local_region _ _ _ name b len /\ _ ==> _`
          (qspecl_then [`name`,`b`,`len`] mp_tac) >> simp[]) >>
     `regions_disjoint b len off k` by
       (pure_rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     conj_tac >- (qpat_assum `!p len. _ ==> mem_bytes_at p len q.vs_memory = _` irule >>
                  first_assum ACCEPT_TAC) >>
     rpt strip_tac >> `lo <= i` by decide_tac >>
     qpat_assum `!i. lo <= i /\ i IN ts.t_mem ==> _` irule >> simp[]) >>
  `!x sz. not_fresh_at su x /\ ptr_covers G tn x s sz ==>
     ptr_covers Gs ts x q sz` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at su x ==> lookup_var x q = _ /\ _`
       (qspec_then `x` (drule_then (fn h => pure_rewrite_tac[ptr_covers_def,h]))) >>
     qpat_assum `ptr_covers G tn x s sz` (ACCEPT_TAC o REWRITE_RULE[ptr_covers_def])) >>
  `!aid b sz i. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
     aid < su.cs_next_id /\ b <= i /\ i < b+sz /\ i IN ts.t_mem ==>
     i IN tn.t_mem` by
    (rpt strip_tac >>
     qpat_assum `allocas_from lo s` (drule_then assume_tac o REWRITE_RULE[allocas_from_def]) >>
     `lo <= i` by decide_tac >>
     qpat_assum `!i. lo <= i /\ i IN ts.t_mem ==> _` irule >> simp[]) >>
  qexistsl [`q`,`Gs`,`ts`] >>
  rpt conj_tac >> every_assum CHECK_ASSUME_TAC
  >- suspend "horizon"
  >- suspend "return"
  >- suspend "history"
  >- suspend "fmp"
  >> suspend "kept"
QED

Resume body_assign_immutable_direct_joint[horizon]:
  gen_tac >> disch_tac >>
  conj_tac >- (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` MATCH_ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_post H ctx func cx lctx ce ce su sb ee s (INL ()) fin q`
                  (drule_then ACCEPT_TAC)) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `!im. (DF H).d_imm im = UNIV` by
    (qpat_assum `!H. dead_lo_ok H _ _ _ _`
       (qspec_then `H` (mp_tac o el 4 o CONJUNCTS o
                        PURE_REWRITE_RULE[dead_lo_ok_def])) >>
     qpat_assum `ce.ce_is_ctor` (fn th => simp[NoAsms, th])) >>
  simp[NoAsms, ghost_inv_at_def] >>
  qpat_assum `fin.scopes = ee.scopes` SUBST1_TAC >>
  qpat_assum `ghost_inv_at (DF H) _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[ghost_inv_at_def]) >>
  rpt conj_tac >> every_assum CHECK_ASSUME_TAC
  >- suspend "locals"
  >- suspend "bufghost"
  >- suspend "pcghost"
  >- suspend "storg"
  >- (qpat_assum `!D. ghost_inv_at D _ _ _ _ _ _ _ _ ==> _`
        (qspec_then `DF H` (drule_then ACCEPT_TAC)))
  >> suspend "immghost"
QED

Resume body_assign_immutable_direct_joint[return]:
  irule bodyMemoryDefsTheory.return_buf_frame_frame >>
  qexistsl [`ce`,`s`,`su`] >>
  simp[IgnAsm `off = _`] >> metis_tac[]
QED

Resume body_assign_immutable_direct_joint[history]:
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts su sb)` by
    (simp[NoAsms, EVERY_MEM] >> gen_tac >> disch_tac >>
     qpat_assum `EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) _`
       (drule_then (mp_tac o BETA_RULE) o REWRITE_RULE[EVERY_MEM]) >>
     simp[NoAsms] >> strip_tac >> pop_assum SUBST1_TAC >> simp[NoAsms]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `q.vs_current_bb = s.vs_current_bb` by simp[] >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = emitted_insts su sb ++ rest` by
    (qpat_assum `s.vs_inst_idx = LENGTH su.cs_current_insts` SUBST1_TAC >>
     qpat_assum `isPREFIX (emitted_insts su sb) _`
       (ACCEPT_TAC o PURE_REWRITE_RULE[rich_listTheory.IS_PREFIX_APPEND])) >>
  `alloca_history func (q with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts su sb))` by
    (irule bodyBinopFragMemoryTheory.alloca_history_no_alloca_slice >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `q.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts su sb)` by
    (qpat_assum `sb.cs_current_insts = _ ++ _` SUBST1_TAC >> simp[]) >>
  qpat_assum `alloca_history func (q with vs_inst_idx := _)` mp_tac >>
  qpat_assum `q.vs_inst_idx = s.vs_inst_idx + _` (fn h => simp[NoAsms, GSYM h])
QED

Resume body_assign_immutable_direct_joint[fmp]:
  drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  simp[]
QED

Resume body_assign_immutable_direct_joint[kept]:
  simp[NoAsms, ghost_kept_at_def] >> rpt conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!x. not_fresh_at su x ==> lookup_var x q = _ /\ _`
        (drule_then strip_assume_tac) >> simp[])
  >- (rpt strip_tac >>
      qpat_assum `!aid b sz i. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ _ ==> _`
        (qspecl_then [`aid`,`off'`,`sz`,`i`] mp_tac) >> simp[])
  >> rpt strip_tac >>
  qpat_assum `!name b len. local_region ce ee.scopes s name b len ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!j. b <= j /\ j < b+sz /\ j IN ts.t_mem ==> j IN tn.t_mem`
    (drule_all_then ACCEPT_TAC)
QED

Resume body_assign_immutable_direct_joint[locals]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at su p` by
    (qpat_assum `local_ptrs_reserved ce su` mp_tac >>
     simp[NoAsms, local_ptrs_reserved_def] >> metis_tac[]) >>
  qpat_assum `!name entry p sz. lookup_scopes name ee.scopes = SOME entry /\ _ ==> ptr_covers G tn p s sz /\ _`
    (drule_all_then strip_assume_tac) >>
  conj_tac >- (qpat_assum `!x sz. not_fresh_at su x /\ ptr_covers G tn x s sz ==> _` irule >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by
    (qpat_assum `!x. not_fresh_at su x ==> lookup_var x q = _ /\ _`
       (drule_then strip_assume_tac) >> metis_tac[]) >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (qpat_assum `local_ptrs_rel func ce ee.scopes s`
       (drule_all_then strip_assume_tac o el 1 o CONJUNCTS o REWRITE_RULE[local_ptrs_rel_def]) >>
     simp[]) >>
  `val_footprint entry.type entry.value <= sz` by
    (qpat_assum `val_wf entry.type entry.value`
       (mp_tac o MATCH_MP exprSimPropsTheory.val_footprint_le) >> decide_tac) >>
  `local_region ce ee.scopes s name (w2n w) sz` by
    (simp[NoAsms, local_region_def] >> metis_tac[]) >>
  qpat_assum `!name b len. local_region ce ee.scopes s name b len ==> _`
    (drule_then strip_assume_tac) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory entry.type entry.value (w2n w) m` by
    (gen_tac >> disch_tac >> first_assum (drule_all_then ACCEPT_TAC)) >>
  drule_all bodyPtrBytestringBuiltinsWindowGhostTheory.robust_val_in_memory_window_transport >> simp[]
QED

Resume body_assign_immutable_direct_joint[bufghost]:
  Cases_on `d` >- fs[return_buf_ptr_def] >>
  rename1 `return_buf_ptr (SOME bc)` >> PairCases_on `bc` >>
  qpat_assum `return_buf_frame _ ce su s` (strip_assume_tac o REWRITE_RULE[return_buf_frame_def]) >>
  qpat_assum `return_buf_ptr _ ce G tn s` (strip_assume_tac o REWRITE_RULE[return_buf_ptr_def]) >>
  `not_fresh_at su x'` by
    (qpat_assum `ce.ce_return_buf = SOME (PtrVar (Var x) slot_size)` mp_tac >>
     qpat_assum `ce.ce_return_buf = SOME (PtrVar (Var x') slot_size')` (fn th => simp[NoAsms, th]) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!x. not_fresh_at su x ==> lookup_var x q = _ /\ _`
    (qspec_then `x'` (drule_then strip_assume_tac)) >>
  qpat_assum `!x sz. not_fresh_at su x /\ ptr_covers G tn x s sz ==> _`
    (drule_all_then assume_tac) >>
  simp[return_buf_ptr_def]
QED

Resume body_assign_immutable_direct_joint[pcghost]:
  rpt gen_tac >> disch_tac >>
  `not_fresh_at su x` by
    (qpat_assum `!x sz. ce.ce_return_pc = _ ==> not_fresh_at su x` (drule_then ACCEPT_TAC)) >>
  qpat_assum `!x. not_fresh_at su x ==> lookup_var x q = _ /\ _`
    (drule_then strip_assume_tac) >>
  simp[] >> qpat_assum `!x sz. ce.ce_return_pc = _ ==> op_taint tn (Var x) = {}`
    (drule_then ACCEPT_TAC)
QED

Resume body_assign_immutable_direct_joint[storg]:
  qpat_assum `ts.t_stor = tn.t_stor` (fn h =>
    qpat_assum `ts.t_trans = tn.t_trans` (fn h' =>
      qpat_assum `q.vs_accounts = s.vs_accounts` (fn ha =>
        qpat_assum `q.vs_transient = s.vs_transient` (fn ht =>
          qpat_assum `q.vs_call_ctx = s.vs_call_ctx` (fn hc =>
            pure_rewrite_tac[stor_taint_ok_at_def, h, h', ha, ht, hc]))))) >>
  qpat_assum `!im. (DF H).d_imm im = UNIV` (fn h =>
    simp[NoAsms, h, pred_setTheory.SUBSET_UNIV]) >>
  qpat_assum `stor_taint_ok_at (DF H) tn s`
    (mp_tac o PURE_REWRITE_RULE[stor_taint_ok_at_def]) >>
  simp[NoAsms]
QED

Resume body_assign_immutable_direct_joint[immghost]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at su x` by metis_tac[] >>
  qpat_assum `!x. not_fresh_at su x ==> lookup_var x q = _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!x. lo <> 0 /\ ce.ce_imm_alloca = _ ==> FLOOKUP G x = _ /\ _`
    (drule_all_then strip_assume_tac) >> simp[]
QED

Finalise body_assign_immutable_direct_joint[local]

Theorem body_assign_nonmutating_rhs_rebase[local]:
  body_inv tops ctx cenv cx /\
  runtime_consistent env cx es /\ well_typed_expr env e /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e) /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  eval_expr cx e es = (INL tv,es1) /\ read_result cx tv es1 = (INL v,es1) /\
  ~expr_can_mutate cenv (target_to_expr bt) /\
  cenv.ce_func_mutability = build_func_mutability (cx_tops cx) /\
  (!vis mut nr rr fn args dflts ret body.
    MEM (FunctionDecl vis mut nr rr fn args dflts ret body) (cx_tops cx) ==>
    function_mutability_ok [(NONE,cx_tops cx)] vis mut nr dflts body) /\
  get_module_code cx NONE = SOME (cx_tops cx) /\
  EVERY (\c. FST c = NONE /\ supported_program (cx_tops cx) /\
             IS_SOME (supported_function_decl (cx_tops cx) c Internal))
    (int_calls_target bt) /\
  eval_base_place cx bt es1 = (INL (PlaceR p),ee) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    storage_well_formed_on cx es (FST H) /\ stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    vv_post H ctx func cenv cx e es sa sm s0 es1 tv vv s) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    assign_target_post (immutable_root cx bt) H ctx func cenv cx es1 sm sb s ee p ty r Gu u) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!l. vv_operand vv <> Label l) /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_id <= sb.cs_next_id /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm ==>
  !H. valid_horizon cx st0 H ee.storage_trace ==>
    read_result cx tv ee = (INL v,ee) /\
    vv_post H ctx func cenv cx e ee sa sm u ee tv vv u /\
    wb_frame cenv es ee sa s0 u /\
    wb_frame cenv es1 es1 sm s u /\
    MAP FDOM ee.scopes = MAP FDOM es1.scopes /\
    vv_storage_live H cx vv ee u /\
    vv_post H ctx func cenv cx e es sa sm s0 es1 tv vv s /\
    assign_target_post (immutable_root cx bt) H ctx func cenv cx es1 sm sb s ee p ty r Gu u /\
    stmt_state_rel H ctx func cenv cx es s0
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `valid_horizon cx st0 H es1.storage_trace` by
    (irule (INST_TYPE [alpha |-> ``:eval_result``] valid_horizon_frame) >>
     qexistsl [`eval_base_place cx bt`, `INL (PlaceR p)`, `ee`] >>
     simp[cj 7 evaluate_storage_trace_frame]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (irule (INST_TYPE [alpha |-> ``:eval_result``] valid_horizon_frame) >>
     qexistsl [`eval_expr cx e`, `INL tv`, `es1`] >>
     simp[cj 5 evaluate_storage_trace_frame]) >>
  `vv_post H ctx func cenv cx e es sa sm s0 es1 tv vv s /\
   assign_target_post (immutable_root cx bt) H ctx func cenv cx es1 sm sb s ee p ty r Gu u /\
   storage_well_formed_on cx es (FST H) /\
   stmt_state_rel H ctx func cenv cx es s0` by metis_tac[] >>
  drule_then strip_assume_tac assign_target_post_frame >>
  drule_all body_assign_saved_rhs_rebased >> strip_tac >>
  `ee.scopes = es1.scopes` by
    (qpat_assum `ee = _` (fn th => simp[Once th])) >>
  `wb_frame cenv es1 es1 sm s u` by
    (qpat_assum `wb_frame cenv es1 ee sm s u` mp_tac >>
     qpat_assum `ee.scopes = es1.scopes` (fn eq =>
       simp[NoAsms,wb_frame_def,locals_kept_def,popped_kept_def,eq]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >> rpt conj_tac >>
     first_assum ACCEPT_TAC) >>
  simp[]
QED

Theorem body_assign_nonmutating_rhs_physical[local]:
  body_inv tops ctx cenv cx /\ struct_args_unique tops /\
  target_indices_pre cenv cx env bt /\ expr_sim_inv cenv cx env es1 /\ eval_base_place cx bt es1 = (INL pv,ee) /\
  vv_post H ctx func cenv cx e es sa sm s0 es1 tv vv s /\
  vv_post H ctx func cenv cx e ee sa sm u ee tv vv u /\
  vv_storage_live H cx vv ee u /\
  dead_lo_ok H D lo cenv cx /\ ghost_inv_at D lo d cenv cx ee Gu tnu u /\
  read_result cx tv es1 = (INL v,es1) /\ read_result cx tv ee = (INL v,ee) /\
  wb_frame cenv es1 es1 sm s u /\ ghost_kept_at lo cenv es1 sm G tn s Gu tnu /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!l. vv_operand vv <> Label l) /\ s.vs_alloca_next <= u.vs_alloca_next /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv es1 G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) es1 tv vv s ==>
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee Gu tnu u /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv u /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 Gu u) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand Gu u) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) u = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tnu.t_mem u.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `vv_location vv = NONE \/ vv_location vv = SOME LocMemory`
  >- (`vv_at cenv cx (post_value_type cenv e) sa sm es1 tv vv s /\
       vv_holds cenv cx (post_value_type cenv e) tv vv es1 s` by fs[vv_post_def] >>
      `((vv_location vv = NONE /\ ~is_word_type (post_value_type cenv e) \/
         vv_location vv = SOME LocMemory) ==> ptr_buf_ok cenv e (vv_operand vv) G s)` by
        (Cases_on `vv` >> gvs[vv_location_def,vv_operand_def]) >>
      drule_all body_assign_saved_rhs_memory_frame >> strip_tac >>
      Cases_on `vv` >> gvs[vv_location_def,vv_operand_def]) >>
  Cases_on `vv` >> fs[vv_location_def,vv_operand_def,vv_store_bound_def,
                       Excl "vv_storage_live_def"] >>
  drule_all body_assign_saved_rhs_nonmemory_frame >> simp[vv_operand_def]
QED

(* The target has already run at u; unwrap the original compiled value,
   not a snapshot or a retyped value, while retaining the target operand. *)

Theorem body_assign_nonmutating_target_rhs[local]:
  body_inv tops ctx cenv cx /\ struct_args_unique tops /\
  expr_body_pre cenv cx env e es /\ runtime_consistent env cx es /\
  functions_well_typed cx /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  eval_expr cx e es = (INL tv,es1) /\ read_result cx tv es1 = (INL v,es1) /\
  ~expr_can_mutate cenv (target_to_expr bt) /\
  cenv.ce_func_mutability = build_func_mutability (cx_tops cx) /\
  (!vis mut nr rr fn args dflts ret body.
    MEM (FunctionDecl vis mut nr rr fn args dflts ret body) (cx_tops cx) ==>
    function_mutability_ok [(NONE,cx_tops cx)] vis mut nr dflts body) /\
  get_module_code cx NONE = SOME (cx_tops cx) /\
  EVERY (\c. FST c = NONE /\ supported_program (cx_tops cx) /\
             IS_SOME (supported_function_decl (cx_tops cx) c Internal))
    (int_calls_target bt) /\
  target_indices_pre cenv cx env bt /\ expr_sim_inv cenv cx env es1 /\ eval_base_place cx bt es1 = (INL (PlaceR p),ee) /\
  compile_get_target_ptr compile_expr cenv bt sm = (r,sb) /\
  unwrap_value cenv vv sb = (op,sc) /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    storage_well_formed_on cx es (FST H) /\ stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    vv_post H ctx func cenv cx e es sa sm s0 es1 tv vv s) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    assign_target_post (immutable_root cx bt) H ctx func cenv cx es1 sm sb s ee p ty r Gu u /\
    ghost_inv_at (DF H) lo d cenv cx ee Gu tnu u) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!l. vv_operand vv <> Label l) /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv es1 G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) es1 tv vv s /\
  alloca_history func u /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\ target_ptr_ok cenv (PlaceR p) r Gu tnu u /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  ghost_kept_at lo cenv es1 sm G tn s Gu tnu /\
  return_buf_frame d cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?z Gz tnz.
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Gu,tnu) [] (OK z,Gz,tnz) /\
       expr_post H ctx func cenv cx e ee sa sc u ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee Gz tnz z) /\
    (!ann p. vv = LocatedValue ann p /\ ~is_word_type ann /\
      (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
       p.ptr_location = LocCode) ==>
      vv_own cenv cx (post_value_type cenv e) sb sc ee (Value v)
        (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sa sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sa sm ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z \/
     vv_at cenv cx (post_value_type cenv e) sb sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    ptr_val_ok cx (post_value_type cenv e) v op Gz tnz z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op Gz z) /\
    (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\ return_buf_frame d cenv sc z /\
    eval_operand (FST r) z = eval_operand (FST r) u /\
    op_prov Gz (FST r) = op_prov Gu (FST r) /\
    op_taint tnz (FST r) = op_taint tnu (FST r) /\
    target_ptr_ok cenv (PlaceR p) r Gz tnz z /\
    wb_frame cenv ee ee sb u z /\ ghost_kept_at lo cenv ee sb Gu tnu u Gz tnz /\
    wb_frame cenv es ee sa s0 z /\ ghost_kept_at lo cenv es sa Gi ti s0 Gz tnz /\
    alloca_frame cenv es sa s0 cenv ee z /\
    (!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa.cs_next_id /\
      (!name b cap. local_region cenv es.scopes s0 name b cap ==>
        a+n <= b \/ b+cap <= a) /\ a <= i /\ i < a+n /\ i IN tnz.t_mem ==>
      i IN ti.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono sa sm` by
    (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac
      (cj 1 ci_mono_compile_expr_sa) >> simp[]) >>
  `ci_mono sm sb` by
    (qspecl_then [`bt`,`cenv`,`sm`] mp_tac ci_mono_compile_get_target_ptr >> simp[]) >>
  `ci_mono sb sc` by
    (qspecl_then [`cenv`,`vv`,`sb`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sb` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var]) >>
  fs[ci_mono_def] >>
  `well_typed_expr env e /\ call_evaluation_safe cx (int_calls_expr e)` by
    (drule_then strip_assume_tac expr_body_pre_static_facts >>
     drule_then assume_tac expr_body_pre_call_evaluation_safe >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     assign_target_post (immutable_root cx bt) H ctx func cenv cx es1 sm sb s ee p ty r Gu u` by metis_tac[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     read_result cx tv ee = (INL v,ee) /\
     vv_post H ctx func cenv cx e ee sa sm u ee tv vv u /\
     wb_frame cenv es ee sa s0 u /\ wb_frame cenv es1 es1 sm s u /\
     MAP FDOM ee.scopes = MAP FDOM es1.scopes /\ vv_storage_live H cx vv ee u /\
     vv_post H ctx func cenv cx e es sa sm s0 es1 tv vv s /\
     assign_target_post (immutable_root cx bt) H ctx func cenv cx es1 sm sb s ee p ty r Gu u /\
     stmt_state_rel H ctx func cenv cx es s0` by
    (mp_tac body_assign_nonmutating_rhs_rebase >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[storage_trace_domain_def, Abbr `H0`] >>
  qpat_assum `!H. _ ==> (read_result _ _ _ = _) /\ _` (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e ee sa sm u ee tv vv u /\
     ghost_inv_at (DF H) lo d cenv cx ee Gu tnu u` by metis_tac[] >>
  `dead_lo_ok H0 (DF H0) lo cenv cx /\ ghost_inv_at (DF H0) lo d cenv cx ee Gu tnu u` by
    metis_tac[] >>
  drule_all body_assign_nonmutating_rhs_physical >> strip_tac >>
  `!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    ~is_word_type (post_value_type cenv e) ==>
    type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64` by metis_tac[body_post_type_allocation_bound] >>
  `(do p <- eval_expr cx e; read_result cx p od) es = (INL v,es1)` by
    simp[vyperStateTheory.bind_def] >>
  drule_all memory_rhs_read_post_typed >> simp[value_runtime_typed_def] >> strip_tac >>
  `!w. read_result cx tv ee = (INL w,ee) ==> value_has_type tv' w` by simp[] >>
  `ghost_kept_at lo cenv ee sa Gu tnu u Gu tnu` by simp[ghost_kept_at_refl] >>
  `env.type_defs = get_tenv cx` by
    drule_then ACCEPT_TAC expr_body_pre_env_type_defs >>
  `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tv'` by
    metis_tac[] >>
  (* Rebase only the source/machine starts and ghosts, not the compilation. *)
  mp_tac (Q.INST [`ty` |-> `expr_type e`, `rty` |-> `tv'`,
    `es` |-> `ee`, `s0` |-> `u`, `s` |-> `u`,
    `Gi` |-> `Gu`, `ti` |-> `tnu`, `G` |-> `Gu`, `tn` |-> `tnu`]
    unwrap_value_origin_ptr) >>
  (impl_tac >- (rpt conj_tac >> simp[])) >>
  strip_tac >>
  `v' = v` by
    (qpat_assum `read_result cx tv ee = (INL v',ee)` mp_tac >>
     qpat_assum `read_result cx tv ee = (INL v,ee)` (fn th => rewrite_tac[th]) >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `~z.vs_halted` by
    (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[fragExecTheory.exit_result_def]) >>
  `z.vs_labels = u.vs_labels` by
    (drule gas_origin_ptr_path_preserves_labels >> simp[]) >>
  `!x. FST r = Var x ==> not_fresh_at sb x` by
    (qpat_assum `assign_target_post _ H0 _ _ _ _ _ _ _ _ _ _ _ _ _ u`
       (mp_tac o MATCH_MP assign_target_post_frame) >> simp[]) >>
  `eval_operand (FST r) z = eval_operand (FST r) u /\
   op_prov G' (FST r) = op_prov Gu (FST r) /\
   op_taint tn' (FST r) = op_taint tnu (FST r)` by
    (Cases_on `FST r` >> simp[eval_operand_def, op_prov_def, op_taint_def] >>
     metis_tac[op_taint_def]) >>
  `target_ptr_ok cenv (PlaceR p) r G' tn' z` by
    (qpat_assum `target_ptr_ok cenv (PlaceR p) r Gu tnu u`
       (STRIP_ASSUME_TAC o REWRITE_RULE [target_ptr_ok_def]) >>
     qpat_assum `local_ptrs_reserved cenv sb`
       (STRIP_ASSUME_TAC o REWRITE_RULE [local_ptrs_reserved_def]) >>
     simp[target_ptr_ok_def] >> rpt strip_tac >> metis_tac[]) >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (qpat_assum `wb_frame cenv es ee sa s0 u` mp_tac >>
     rewrite_tac[wb_frame_def, locals_kept_def] >> simp[]) >>
  `wb_frame cenv es ee sa s0 z` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es s0`
       (mp_then Any irule wb_frame_trans) >> simp[] >>
     qexistsl [`ee`,`sb`,`u`] >> simp[]) >>
  `stmt_state_rel H0 ctx func cenv cx es1 s /\ wb_frame cenv es es1 sa s0 s` by
    (qpat_assum `vv_post H0 ctx func cenv cx e es sa sm s0 es1 tv vv s`
       (STRIP_ASSUME_TAC o REWRITE_RULE [vv_post_def]) >>
     rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `MAP FDOM es1.scopes = MAP FDOM es.scopes` by metis_tac[] >>
  `ghost_kept_at lo cenv es1 sm G tn s G' tn'` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es1 s`
       (mp_then Any irule ghost_kept_at_wb_trans) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa Gi ti s0 G' tn'` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es s0`
       (mp_then Any irule ghost_kept_at_wb_trans) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `s0.vs_alloca_next <= z.vs_alloca_next /\ sa.cs_next_var <= sc.cs_next_var` by decide_tac >>
  `return_buf_frame d cenv sc z` by
    (qpat_assum `return_buf_frame d cenv sa s0`
       (mp_then Any irule return_buf_frame_frame) >> simp[] >>
     qpat_assum `wb_frame cenv es ee sa s0 z`
       (STRIP_ASSUME_TAC o REWRITE_RULE [wb_frame_def]) >>
     first_assum ACCEPT_TAC) >>
  `alloca_frame cenv es sa s0 cenv ee z` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es s0`
       (mp_then Any irule log_wb_alloca_frame) >> simp[] >>
     qexists `ee` >> simp[]) >>
  qpat_assum `ghost_kept_at lo cenv es sa Gi ti s0 G' tn'`
    (STRIP_ASSUME_TAC o REWRITE_RULE [ghost_kept_at_def]) >>
  qexistsl [`z`,`G'`,`tn'`] >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >> simp[] >>
  once_rewrite_tac [arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC
QED

Theorem body_assign_word_store_segment[local]:
  compile_imm_store_word imm (Lit (n2w off)) op su = ((),sb) /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
    op_taint tn region = {} /\ op_prov G region = NONE) /\
  (!x. op = Var x ==> not_fresh_at su x) /\
  eval_operand op s = SOME value /\ op_taint tn op = {} /\
  off < dimword (:256) /\ off + 32 <= lo /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  sb.cs_current_bb = su.cs_current_bb /\ ~block_is_terminated sb /\
  sb.cs_current_insts = su.cs_current_insts ++ emitted_insts su sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
    ~is_terminator i.inst_opcode) (emitted_insts su sb) /\
  ?Gf tf u. run_inst_seq (emitted_insts su sb) s = OK u /\
    (!k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts su sb)
      (s with vs_inst_idx := k) Gf tf) /\
    tf.t_mem = tn.t_mem DIFF {j | off <= j /\ j < off + 32} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at su p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u)
Proof
  strip_tac >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   op_taint tn (Lit (n2w off)) = {} /\ op_prov G (Lit (n2w off)) = NONE` by
    simp[eval_operand_def,op_taint_def,op_prov_def] >>
  `w2n (n2w off : bytes32) = off` by simp[w2n_n2w] >>
  `w2n (n2w off : bytes32) + 32 <= lo` by simp[] >>
  Cases_on `imm` >>
  qpat_x_assum `compile_imm_store_word _ _ _ _ = _` mp_tac >>
  simp[compile_imm_store_word_def,emit_op_def,emit_void_def,
       fresh_id_def,fresh_var_def,emit_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def] >>
  strip_tac >> gvs[Excl "APPEND_ASSOC", GSYM listTheory.APPEND_ASSOC,
    emitted_insts_def,DROP_APPEND2] >>
  (conj_tac >- (Cases_on `su.cs_current_insts` >>
    simp[block_is_terminated_def,LAST_CONS_cond,mk_inst_def,is_terminator_def])) >>
  simp[is_terminator_def] >>
  `op_prov G (Lit (n2w off)) = NONE /\ w2n (n2w off : bytes32) + 32 <= lo` by
    simp[op_prov_def,w2n_n2w]
  >- (qpat_assum `eval_operand op s = SOME value`
       (mp_then (Pos (el 5)) mp_tac ctor_istore_segment) >>
      disch_then (drule_all o Q.INST [`arg` |-> `Lit (n2w off)`]) >>
      disch_then (qspecl_then [`su.cs_next_id`,`func`,`PG`,`D`] strip_assume_tac) >>
      qexistsl [`Gf`,`tnf`,`t`] >> gvs[w2n_n2w]) >>
  `!p. not_fresh_at su p ==> p <> STRING #"%" (toString su.cs_next_var)` by
    simp[not_fresh_at_def] >>
  `!x. op = Var x ==> x <> STRING #"%" (toString su.cs_next_var)` by metis_tac[] >>
  qpat_assum `eval_operand op s = SOME value`
    (mp_then (Pos (el 8)) mp_tac (Q.INST [`P` |-> `not_fresh_at su`,
      `tmp` |-> `STRING #"%" (toString su.cs_next_var)`, `dst` |-> `Lit (n2w off)`]
      ctor_word_store_seq)) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`su.cs_next_id`,`func`,`PG`,`D`] strip_assume_tac) >>
  qexistsl [`Gf`,`tnf`,`t`] >> gvs[w2n_n2w]
QED

Theorem body_assign_word_store_path:
  compile_imm_store_word imm (Lit (n2w off)) op su = ((),sb) /\
  fn_has_code su sb func /\ ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
    op_taint tn region = {} /\ op_prov G region = NONE) /\
  (!x. op = Var x ==> not_fresh_at su x) /\
  eval_operand op s = SOME value /\ op_taint tn op = {} /\
  off < dimword (:256) /\ off + 32 <= lo /\ lo <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  sb.cs_current_bb = su.cs_current_bb /\ ~block_is_terminated sb /\
  sb.cs_current_insts = su.cs_current_insts ++ emitted_insts su sb /\
  ?u Gf tf. run_inst_seq (emitted_insts su sb) s = OK u /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf)) /\
    tf.t_mem = tn.t_mem DIFF {j | off <= j /\ j < off + 32} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at su p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u)
Proof
  strip_tac >>
  drule_all body_assign_word_store_segment >>
  disch_then (mk_asm "segment") >>
  asm "segment" (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts su sb) s = OK u` >>
  (rpt conj_tac) >- simp[] >- simp[] >- simp[] >>
  qexistsl [`u`,`Gf`,`tf`] >> simp[IgnAsm `sb.cs_current_insts = _`] >>
  qx_gen_tac `D'` >>
  asm "segment" (qspecl_then [`func`,`PG`,`D'`] strip_assume_tac) >>
  `Gf' = Gf /\ tf' = tf` by
    (qpat_assum `!k. inst_seq_ptr D' _ _ _ _ _ _ _ _ Gf' tf'` (qspec_then `0` mp_tac) >>
     qpat_assum `!k. inst_seq_ptr D _ _ _ _ _ _ _ _ Gf tf` (qspec_then `0` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[inst_seq_ptr_ghost_unique]) >>
  `u' = u` by metis_tac[exec_result_11] >>
  `run_inst_seq_mem_ok (emitted_insts su sb) s` by
    (`off + 32 <= s.vs_alloca_next` by decide_tac >>
     `!region. imm = SOME region ==> eval_operand region s = SOME 0w` by metis_tac[] >>
     drule_all body_assign_immutable_word_mem_ok >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts su sb)` by
    (Cases_on `imm` >>
     qpat_x_assum `compile_imm_store_word _ _ _ _ = _` mp_tac >>
     simp[compile_imm_store_word_def,emit_op_def,emit_void_def,
          fresh_id_def,fresh_var_def,emit_def,comp_bind_def,
          comp_ignore_bind_def,comp_return_def] >>
     strip_tac >> gvs[Excl "APPEND_ASSOC", GSYM listTheory.APPEND_ASSOC,
       emitted_insts_def,DROP_APPEND2,mk_inst_def]) >>
  irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
  simp[] >> qexistsl [`emitted_insts su sb`,`su`] >> simp[] >>
  conj_tac >-
    (rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >>
     qpat_assum `EVERY (\i. i.inst_opcode <> DALLOCA) _` mp_tac >>
     qpat_assum `emitted_insts _ _ = _ ++ _` (fn th => pure_rewrite_tac [th]) >>
     simp[EVERY_APPEND]) >>
  qpat_x_assum `Gf' = Gf` SUBST_ALL_TAC >>
  qpat_x_assum `tf' = tf` SUBST_ALL_TAC >>
  qpat_assum `!k. inst_seq_ptr D' _ _ _ _ _ _ _ _ Gf tf`
    (qspec_then `s.vs_inst_idx`
      (ACCEPT_TAC o REWRITE_RULE [venomStateTheory.venom_state_fupdselfid]))
QED

Theorem body_assign_other_immutable_word_write_full[local]:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    struct_args_unique tops /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              is_word_type ty) /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              ~is_word_type ty /\
              (expr_type e = ty \/ lowered_value_type cenv e = ty \/
               is_bytestring_type ty \/
               has_length_word (expr_type e) /\ is_empty_value_expr e)) /\
    ~(?nsid dty. t = TopLevelNameTarget nsid /\
          supported_scalar_target tops nsid /\
          type_place_target env t = SOME (Type dty) /\ is_word_type dty) /\
    ~(?nsid mut ty slot.
        t = TopLevelNameTarget nsid /\
        supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
        (mut = Storage \/ mut = Transient) /\
        ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
        ~is_bytestring_type ty /\
        0 < type_memory_bytes cenv ty /\ expr_type e = ty /\
        lowered_value_type cenv e = expr_type e) /\
    ~(?id fld sid fty.
        t = AttributeTarget (NameTarget id) fld /\
        FLOOKUP env.var_types id = SOME (StructT sid) /\
        attribute_type env.type_defs (StructT sid) fld = SOME fty /\
        is_word_type fty) /\
    ~(?nsid fld fty.
        t = AttributeTarget (TopLevelNameTarget nsid) fld /\
        supported_storage_field_write tops nsid fld /\
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    immutable_root cx t ==>
    !src id ity off vv op st0 sa sm su sb shadow_sa shadow_su shadow_sb
        s0 G0 tn0 marks v ee z G tn.
      is_word_type ity /\
      t = TopLevelNameTarget (src,id) /\ src = NONE /\ src = cenv.ce_module /\
      cx.in_deploy /\ cenv.ce_is_ctor /\
      supported_immutable_type tops (src,id) = SOME ity /\
      ~cx_const_name cx (src,id) /\
      assignable_type env.type_defs (expr_type e) /\
      type_widens_to env.type_defs (expr_type e) ity /\
      FLOOKUP env.bare_globals (src,id) = SOME ity /\
      cenv.ce_module_var_type (src,id) = SOME ity /\
      FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
      (!tv. evaluate_type (get_tenv cx) ity = SOME tv ==>
            off + type_memory_size tv < dimword (:256)) /\
      stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e) sa = (cenv,sb) /\
      stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e))
        shadow_sa = (gas_shadow_env T cenv,shadow_sb) /\
      compile_get_target_ptr compile_expr cenv t =
        comp_return (Lit (n2w off), SOME LocCode, SOME (ValPT ity)) /\
      compile_expr cenv (expr_type e) e sa = (vv,sm) /\
      unwrap_value cenv vv sm = (op,su) /\
      lower_value compile_expr cenv (expr_type e) e sa = (op,su) /\
      lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa =
        (op,shadow_su) /\
      compile_assign_value cenv (Lit (n2w off)) LocCode op (is_word_type ity)
        (vv_location vv) ity (lowered_value_type cenv e)
        (type_memory_bytes cenv ity) su = ((),sb) /\
      cs_extends sa sm /\ cs_extends sm su /\ cs_extends su sb /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state su shadow_su /\
      gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa su func /\ fn_has_code su sb func /\
      fn_has_code shadow_sa shadow_su shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\ ret_pc_ok cenv sa s0 /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      ~block_is_terminated sa /\
      gas_admissible (eval_stmt cx (Assign (BaseTarget t) e)) (stmt_res_ok lctx) es /\
      expr_body_pre cenv cx env e es /\
      return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
           stmt_state_rel H ctx func cenv cx es s0 /\
           storage_well_formed_on cx es (FST H) /\
           ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!tail. bind (eval_expr cx e) (read_result cx)
         (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
         (INL v,ee with gas_obs := tail)) /\
      storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
      ~z.vs_halted /\
      (!tail. expr_sim_inv cenv cx env (ee with gas_obs := tail) /\
        eval_target_place cx t (ee with gas_obs := tail) =
          (INL (ImmutablePlace src id []),ee with gas_obs := tail)) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
         expr_post H ctx func cenv cx e es sa su s0 ee v op z /\
         expr_store_bound cx (post_value_type cenv e) v op z /\
         z.vs_current_bb = su.cs_current_bb /\ z.vs_inst_idx = LENGTH su.cs_current_insts /\
         alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
         s0.vs_alloca_next <= z.vs_alloca_next /\
         ghost_inv_at (DF H) lo d cenv cx ee G tn z /\
         ptr_val_ok cx (post_value_type cenv e) v op G tn z /\
         (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G z) /\
         ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
      gas_outcome_full
        (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
        (write_place cx (ImmutablePlace src id []) v) (ee,z,G,tn)
        (\H res ff Gf tf u. ?ce.
          stmt_lands lctx sb res u /\ ~u.vs_halted /\
          (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
          cenv_top_ext cenv ce ff.scopes /\
          stmt_state_rel H ctx func ce cx ff u /\
          storage_well_formed_on cx ff (FST H) /\
          return_buf_frame d ce sb u /\ alloca_history func u /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
          s0.vs_alloca_next <= u.vs_alloca_next /\
          ghost_inv_at (DF H) lo d ce cx ff Gf tf u /\
          (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                 lookup_var x u = SOME w) /\
          (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                   FLOOKUP u.vs_allocas aid = SOME b) /\
          (!x. not_fresh_at sa x ==>
               FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
          alloca_frame cenv es sa s0 ce ff u /\
          (!aid off sz i.
             FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
             (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                        off + sz <= b \/ b + sz' <= off) /\
             off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tn0.t_mem))
        (\H res ff gt r.
           (!tail. stmt_exit_ptr (RetQ H) (ff with gas_obs := tail) res gt r) /\
           halt_exit H cx ff res r /\
           (ctx_has_dalloca ctx ==>
            !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_type e = ity` by metis_tac[type_widens_to_word] >>
  `post_value_type cenv e = ity` by simp[] >>
  `is_word_type (expr_type e)` by simp[] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at su x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `local_ptrs_reserved cenv su` by metis_tac[local_ptrs_reserved_next_var] >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. expr_sim_inv _ _ _ _ /\ _`
    (qspec_then `[]` (strip_assume_tac o REWRITE_RULE [expr_sim_inv_gas_obs])) >>
  qpat_assum `!tail. bind _ _ _ = _`
    (qspec_then `[]` (mk_asm "rhs" o SRULE [APPEND_NIL])) >>
  `env.type_defs = get_tenv cx` by
    (qpat_assum `expr_sim_inv cenv cx env ee` mp_tac >>
     simp[NoAsms,expr_sim_inv_def,env_consistent_def,env_context_consistent_def]) >>
  `?itv. evaluate_type (get_tenv cx) ity = SOME itv /\ value_has_type itv v` by
    (`expr_body_pre cenv cx env e
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     asm "rhs" assume_tac >>
     drule_all (SIMP_RULE (srw_ss() ++ ETA_ss) [] memory_rhs_read_post_typed) >>
     simp[value_runtime_typed_def]) >>
  suspend "landing"
QED

Resume body_assign_other_immutable_word_write_full[landing]:
  qpat_x_assum `src = cenv.ce_module` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac body_assign_immutable_word_layout >>
  drule_all_then strip_assume_tac immutable_assign_source_lookup >>
  drule_all immutable_augassign_write_source >>
  disch_then (qspec_then `v` (mk_asm "source_write")) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by
    fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `eval_operand op z = SOME (typed_val_to_w256 itv v)` by
    (qpat_assum `expr_post H0 ctx func cenv cx e es sa su s0 ee v op z` mp_tac >>
     simp_tac bool_ss [expr_post_def] >> strip_tac >>
     qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) ity = SOME itv` mp_tac >>
     simp[expr_val_rel_def] >> metis_tac[]) >>
  `op_taint tn op = {}` by
    (qpat_assum `ptr_val_ok _ _ _ _ _ _ _`
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [ptr_val_ok_def])) >>
  `stmt_state_rel H0 ctx func cenv cx ee z` by
    (drule expr_post_state >> simp[]) >>
  `!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region z = SOME 0w` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx ee z`
       (mp_tac o MATCH_MP stmt_state_rel_immutable_base_zero) >>
     simp[NoAsms,immutable_base_zero_def]) >>
  `lo <> 0` by decide_tac >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next /\
   (!region. cenv.ce_imm_alloca = SOME region ==>
       op_taint tn region = {} /\ op_prov G region = NONE)` by
    (qpat_assum `ghost_inv_at (DF H0) lo d cenv cx ee G tn z`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     simp[] >> Cases >> simp[op_taint_def,op_prov_def]) >>
  `compile_imm_store_word cenv.ce_imm_alloca (Lit (n2w off)) op su = ((),sb)` by
    (qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_assign_value_def,comp_bind_def,comp_return_def] >>
     gvs[compile_assign_value_def,comp_bind_def,comp_return_def]) >>
  `!region. cenv.ce_imm_alloca = SOME region ==>
     eval_operand region z = SOME 0w /\ op_taint tn region = {} /\ op_prov G region = NONE` by
    simp[] >>
  drule_all body_assign_word_store_path >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  `eval_operand (Lit (n2w off)) z = SOME (n2w off)` by simp[eval_operand_def] >>
  qpat_assum `is_word_type ity` (fn hw =>
    qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`
      (assume_tac o REWRITE_RULE [hw])) >>
  drule_all immutable_assign_word_store >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `u' = u` by metis_tac[exec_result_11] >>
  qpat_x_assum `u' = u` SUBST_ALL_TAC >>
  suspend "write_outcome"
QED

Resume body_assign_other_immutable_word_write_full[write_outcome]:
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x z = SOME w` by
    (qpat_assum `expr_post H0 _ _ _ _ _ _ _ _ _ _ _ _ z` mp_tac >>
     simp_tac bool_ss [expr_post_def] >> strip_tac >> simp[]) >>
  `return_buf_frame d cenv su z` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`,`s0`,`sa`] >> simp[]) >>
  `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x` by simp[] >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x` by
    (rpt strip_tac >>
     `not_fresh_at sa x` by
       (qpat_assum `ret_pc_ok cenv sa s0` (drule o REWRITE_RULE [ret_pc_ok_def]) >> simp[]) >>
     simp[]) >>
  asm_x "source_write" assume_tac >>
  qmatch_asmsub_abbrev_tac `write_place cx _ v ee = (INL (),fin)` >>
  `fin.storage_trace = ee.storage_trace /\ fin.gas_obs = []` by
    (drule write_immutable_place_frame >> strip_tac >> simp[]) >>
  drule_then assume_tac immutable_write_place_gas_obs >>
  qabbrev_tac `q = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl [`Gf`,`fin`,`INL ()`,`q`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H ee.storage_trace` by
    (qpat_assum `valid_horizon cx st0 H fin.storage_trace` mp_tac >>
     qpat_assum `fin.storage_trace = ee.storage_trace` (fn th => rewrite_tac[th])) >>
  conj_tac >- simp[] >>
  `fin with gas_obs := [] = fin` by
    (qpat_assum `fin.gas_obs = []` (fn th => simp[NoAsms,GSYM th])) >>
  qpat_assum `fin with gas_obs := [] = fin` (fn th => simp_tac bool_ss [th]) >>
  qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `ghost_inv_at (DF H0) _ _ _ _ _ _ _ _` kall_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ z`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  qpat_assum `!H. dead_lo_ok H _ _ _ _` (qspec_then `H` assume_tac) >>
  drule_all body_assign_immutable_word_endpoint_run >>
  disch_then (qspec_then `lctx` mp_tac) >>
  qpat_assum `Abbrev (q = _)`
    (fn th => simp_tac bool_ss [LET_THM,GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  strip_tac >>
  suspend "entry_post"
QED

Resume body_assign_other_immutable_word_write_full[entry_post]:
  `valid_horizon cx st0 H es.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       simp[storage_trace_frame_bind_all,cj 5 evaluate_storage_trace_frame,
            storage_trace_frame_read_result] >>
     asm "rhs" assume_tac >>
     drule valid_horizon_frame >> disch_then drule >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (asm "rhs" (mp_tac o MATCH_MP eval_read_preserves_scopes_dom) >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv ee z` by
    (drule_all_then ACCEPT_TAC expr_post_alloca_frame) >>
  `alloca_frame cenv es sa s0 cenv fin q` by
    (irule alloca_frame_trans >> qexistsl [`cenv`,`ee`,`z`,`su`] >> simp[]) >>
  qpat_assum `stmt_post H ctx func cx lctx cenv cenv su sb ee z (INL ()) fin q`
    (mp_tac o REWRITE_RULE [stmt_post_def]) >>
  simp_tac bool_ss [] >> strip_tac >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x q = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at su x` by simp[] >>
     `lookup_var x z = SOME w` by simp[] >>
     qpat_assum `!x w. not_fresh_at su x /\ lookup_var x z = SOME w ==> _`
       (irule o SPEC_ALL) >> simp[]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP q.vs_allocas aid = SOME b` by
    simp[] >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
     op_taint tf (Var x) = op_taint tn0 (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at su x` by simp[] >>
     qpat_assum `!p. not_fresh_at su p ==> FLOOKUP Gf p = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `!i. i IN tf.t_mem ==> i IN tn.t_mem` by
    (qpat_assum `tf.t_mem = _` (fn th => simp[NoAsms,th,pred_setTheory.IN_DIFF])) >>
  rpt conj_tac >> simp[IgnAsm `tf.t_mem = _`] >>
  rpt strip_tac >>
  qpat_assum `!i. i IN tf.t_mem ==> _` (drule_then assume_tac) >>
  qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN tn0.t_mem`
    (drule_all_then ACCEPT_TAC)
QED

Finalise body_assign_other_immutable_word_write_full[local]

Theorem body_assign_saved_target_admissible[local]:
  gas_admissible (eval_stmt cx (Assign (BaseTarget t) e)) (stmt_res_ok lctx) es /\
  (!tail. eval_expr cx e (es with gas_obs := prefix ++ tail) =
    (INL tv, mid with gas_obs := tail)) /\
  read_result cx tv mid = (INL v,mid) ==>
  gas_admissible (eval_target_place cx t) target_place_res_ok mid
Proof
  strip_tac >>
  drule read_result_gas_obs >> strip_tac >>
  rw[gas_admissible_def] >> Cases_on `res`
  >- simp[target_place_res_ok_def] >>
  rename1 `INR ex` >>
  `no_control_exc ex` by metis_tac[eval_target_place_no_control] >>
  `stmt_res_ok lctx (INR ex)` by
    (drule gas_admissible_result >> disch_then irule >>
     qexistsl [`ee`, `prefix ++ gs`] >>
     simp[Once evaluate_def, bind_def]) >>
  gvs[stmt_res_ok_def, target_place_res_ok_def, no_control_exc_def]
QED

Theorem body_assign_saved_target_type[local]:
  type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' ==>
  ?ty. type_place_target env t = SOME (Type ty)
Proof
  simp[Once type_stmt_def, atarget_accepts_def] >>
  Cases_on `type_place_target env t` >> simp[] >>
  rename1 `_ = SOME vt` >> Cases_on `vt` >> simp[] >> strip_tac >> gvs[]
QED

Theorem body_assign_saved_target_pre[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget t) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (BaseTarget t) e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env mid /\
  type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
  ~immutable_root cx t ==>
  target_pre cenv cx env t mid
Proof
  strip_tac >>
  drule body_assign_saved_target_type >> strip_tac >>
  metis_tac[body_assign_empty_target_pre]
QED

Theorem body_assign_saved_target_outcome[local]:
  assign_target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx env t mid /\
  type_place_target env t = SOME (Type ty) /\
  compile_get_target_ptr compile_expr cenv t sr = (r,st) /\
  compile_get_target_ptr compile_expr (gas_shadow_env T cenv) (gas_shadow_target t) shadow_sr = (r,shadow_st) /\
  gas_shadow_state sr shadow_sr /\ gas_shadow_state st shadow_st /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sr st func /\ fn_has_code shadow_sr shadow_st shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sr /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sr x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sr x) /\
  gas_admissible (eval_target_place cx t) target_place_res_ok mid /\
  return_buf_frame d cenv sr s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid s /\
       storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sr.cs_current_bb /\
  s.vs_inst_idx = LENGTH sr.cs_current_insts /\
  (!marks p ee Gu tnu u.
    (!tail. eval_target_place cx t
       (mid with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL p,ee with gas_obs := tail)) /\
    storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\ ~u.vs_halted /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       assign_target_post (immutable_root cx t) H ctx func cenv cx mid sr st s ee p ty r Gu u /\
       ghost_inv_at (DF H) lo d cenv cx ee Gu tnu u) /\
    (!id path. p = MemoryPlace id path ==>
       ?entry w. lookup_scopes id ee.scopes = SOME entry /\
                 evaluate_subscripts entry.type entry.value path = INL w) /\
    u.vs_current_bb = st.cs_current_bb /\ u.vs_inst_idx = LENGTH st.cs_current_insts /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s.vs_alloca_next <= u.vs_alloca_next /\ target_ptr_ok cenv (PlaceR p) r Gu tnu u /\
    ghost_kept_at lo cenv mid sr G tn s Gu tnu ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (write_place cx p v) (ee,u,Gu,tnu) Q
      (\H res ee gt r.
        (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
        halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==>
           !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_target_place cx t) (\p. write_place cx p v))
    (mid,s,G,tn) Q
    (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==>
         !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >>
  qpat_x_assum `assign_target_place_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [bodyFullTargetDefsTheory.assign_target_place_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`ty`,`sr`,`st`,`shadow_sr`,`shadow_st`,`r`,`s`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`storage_trace_frame (eval_target_place _ _)`]
  >- simp[cj 8 evaluate_storage_trace_frame]
  >~ [`!p. storage_trace_frame (write_place _ p _)`]
  >- simp[storage_trace_frame_write_place]
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule gas_exempt_cert_bind_place >> simp[] >>
      disch_then irule >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_place >> first_assum ACCEPT_TAC) >>
  qexists `\H res ee G tn u. childQ H res ee G tn u /\ ee.gas_obs = [] /\ ~u.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >> first_assum (irule_at Any) >>
      simp[Abbr `childR`] >> rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def] >>
      rewrite_tac[stmt_exit_ptr_def] >>
      ONCE_REWRITE_TAC [
        INST_TYPE [alpha |-> ``:unit``, beta |-> ``:place``]
          stmtSimPropsTheory.expr_exit_INR_type,
        INST_TYPE [alpha |-> ``:unit``, beta |-> ``:place``]
          halt_exit_INR_type] >>
      rpt strip_tac >> gvs[expr_exit_def]) >>
  suspend "normal"
QED

Resume body_assign_saved_target_outcome[normal]:
  qx_genl_tac [`marks`,`res`,`ee`,`Gu`,`tnu`,`u`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  fs[Abbr `childQ`] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[] >>
  qpat_x_assum `!marks p ee Gu tnu u. _` irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists `marks` >> first_assum ACCEPT_TAC
QED
Finalise body_assign_saved_target_outcome[local]

Theorem body_assign_saved_resources_gas[local]:
  (runtime_consistent env cx (es with gas_obs := gs) <=> runtime_consistent env cx es) /\
  (target_pre cenv cx env bt (es with gas_obs := gs) <=> target_pre cenv cx env bt es) /\
  (storage_well_formed_on cx (es with gas_obs := gs) regions <=>
   storage_well_formed_on cx es regions) /\
  (ptr_vv_ok cx ty tv vv (es with gas_obs := gs) G tn s <=>
   ptr_vv_ok cx ty tv vv es G tn s) /\
  (vv_store_bound cx ty lt (es with gas_obs := gs) tv vv s <=>
   vv_store_bound cx ty lt es tv vv s) /\
  (ghost_kept_at lo cenv (es with gas_obs := gs) sa Gi ti s0 G tn <=>
   ghost_kept_at lo cenv es sa Gi ti s0 G tn)
Proof
  Cases_on `vv` >>
  simp[runtime_consistent_def, env_consistent_def, env_scopes_consistent_def,
       env_immutables_consistent_def, state_well_typed_def, target_pre_def,
       ghost_kept_at_def, ptr_vv_ok_def, vv_store_bound_def, exprSimSubscriptArrayComposeTheory.read_result_success_gas_iff] >>
  irule storage_well_formed_on_backends >> simp[]
QED

Theorem body_assign_function_mutability_mods[local]:
  contract_inv mods exps ctx cenv cx ==>
  !src tops vis mut nr rr fn args dflts ret body.
    ALOOKUP mods src = SOME tops /\
    MEM (FunctionDecl vis mut nr rr fn args dflts ret body) tops /\
    (src = NONE \/ MEM (src,fn) (linked_live_functions mods exps)) ==>
    function_mutability_ok mods vis mut nr dflts body
Proof
  simp[contract_inv_def] >> rpt strip_tac >> res_tac
QED

(* Run the target before unwrapping the original, unsnapshotted RHS.
   The only open outcome is the actual destination write. *)
Theorem body_assign_other_saved_target_bind[local]:
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\ struct_args_unique tops /\
  supported_stmt tops bindings (Assign (BaseTarget bt) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (BaseTarget bt) e) ==> occurs_abi_decode_target target tops) /\
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget bt) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget bt) e)) /\
  ~expr_can_mutate cenv (target_to_expr bt) /\
  target_indices_pre cenv cx env bt /\
  assign_target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env bt mid /\
  body_base_target_full_ok cx bt /\ expr_sim_inv cenv cx env mid /\
  body_const_cells_agree [(NONE,tops)] cx env mid /\
  expr_body_pre cenv cx env e es /\ runtime_consistent env cx es /\
  functions_well_typed cx /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e)) (stmt_res_ok lctx) es /\
  (!tail. eval_expr cx e (es with gas_obs := prefix ++ tail) =
    (INL tv,mid with gas_obs := tail)) /\
  read_result cx tv mid = (INL v,mid) /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  compile_get_target_ptr compile_expr cenv bt sm = (r,sb) /\
  compile_get_target_ptr compile_expr (gas_shadow_env T cenv) (gas_shadow_target bt) shadow_sr =
    (r,shadow_st) /\
  unwrap_value cenv vv sb = (op,sc) /\
  (case FST (SND r) of
     SOME loc => compile_assign_value cenv (FST r) loc op
       (is_word_type (case SND (SND r) of SOME (ValPT t) => t
          | _ => lowered_value_type cenv e))
                   (vv_location vv)
       (case SND (SND r) of SOME (ValPT t) => t
          | _ => lowered_value_type cenv e) (lowered_value_type cenv e)
       (type_memory_bytes cenv (case SND (SND r) of SOME (ValPT t) => t
          | _ => lowered_value_type cenv e))
   | NONE => emit_void INVALID []) sc = ((),sf) /\
  gas_shadow_state sm shadow_sr /\ gas_shadow_state sb shadow_st /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sm sb func /\ fn_has_code shadow_sr shadow_st shadow_func /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ret_pc_ok cenv sa s0 /\ return_buf_frame d cenv sa s0 /\
  return_buf_frame d cenv sm s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       storage_well_formed_on cx es (FST H) /\ stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       vv_post H ctx func cenv cx e es sa sm s0 mid tv vv s /\
       ghost_inv_at (DF H) lo d cenv cx mid G tn s) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!l. vv_operand vv <> Label l) /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv mid G tn s /\
  (!ann op0. vv = StackValue ann op0 /\ ~is_word_type (post_value_type cenv e) ==>
     ptr_buf_ok cenv e op0 G s) /\
  (!ann p. vv = LocatedValue ann p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G s) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) mid tv vv s /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!marks p ee Gu tnu u z Gz tnz ty.
    type_place_target env bt = SOME (Type ty) /\
    (!tail. eval_target_place cx bt
       (mid with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL p,ee with gas_obs := tail)) /\
    storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       assign_target_post (immutable_root cx bt) H ctx func cenv cx mid sm sb s ee p ty r Gu u /\
       expr_post H ctx func cenv cx e ee sa sc u ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee Gz tnz z) /\
    (!id path. p = MemoryPlace id path ==>
       ?entry w. lookup_scopes id ee.scopes = SOME entry /\
                 evaluate_subscripts entry.type entry.value path = INL w) /\
    (!ann pp. vv = LocatedValue ann pp /\ ~is_word_type ann /\
      (pp.ptr_location = LocStorage \/ pp.ptr_location = LocTransient \/
       pp.ptr_location = LocCode) ==>
      vv_own cenv cx (post_value_type cenv e) sb sc ee (Value v)
        (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sa sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sa sm ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z \/
     vv_at cenv cx (post_value_type cenv e) sb sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    ptr_val_ok cx (post_value_type cenv e) v op Gz tnz z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op Gz z) /\
    (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\ return_buf_frame d cenv sc z /\
    eval_operand (FST r) z = eval_operand (FST r) u /\
    op_prov Gz (FST r) = op_prov Gu (FST r) /\
    op_taint tnz (FST r) = op_taint tnu (FST r) /\
    target_ptr_ok cenv (PlaceR p) r Gz tnz z /\
    wb_frame cenv ee ee sb u z /\ ghost_kept_at lo cenv ee sb Gu tnu u Gz tnz /\
    wb_frame cenv es ee sa s0 z /\ ghost_kept_at lo cenv es sa Gi ti s0 Gz tnz /\
    alloca_frame cenv es sa s0 cenv ee z /\
    (!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa.cs_next_id /\
      (!name b cap. local_region cenv es.scopes s0 name b cap ==>
        a+n <= b \/ b+cap <= a) /\ a <= i /\ i < a+n /\ i IN tnz.t_mem ==>
      i IN ti.t_mem) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (write_place cx p v) (ee,z,Gz,tnz) Q
      (\H res ee gt r.
        (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
        halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==>
           !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_target_place cx bt) (\p. write_place cx p v))
    (mid,s,G,tn) Q
    (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==>
         !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule body_assign_saved_target_type >> strip_tac >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok mid` by
    (mp_tac (Q.INST [`t` |-> `bt`] body_assign_saved_target_admissible) >> simp[]) >>
  `ci_mono sa sm` by
    (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac
      (cj 1 ci_mono_compile_expr_sa) >> simp[]) >>
  `local_ptrs_reserved cenv sm /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    (fs[ci_mono_def, ret_pc_ok_def, not_fresh_at_def] >>
     metis_tac[local_ptrs_reserved_next_var, LESS_LESS_EQ_TRANS]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid s /\
       storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid G tn s` by
    (rpt strip_tac >> fs[vv_post_def]) >>
  mp_tac (Q.INST [`t` |-> `bt`, `sr` |-> `sm`, `st` |-> `sb`]
    body_assign_saved_target_outcome) >>
  (impl_tac >-
    (reverse (rpt conj_tac) >- suspend "normal" >> first_assum ACCEPT_TAC)) >>
  simp[]
QED

Resume body_assign_other_saved_target_bind[normal]:
  qx_genl_tac [`marks`,`p`,`ee`,`Gu`,`tnu`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `gs = gas_explicit marks s.vs_gas_readings` >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL])) >>
  `eval_base_place cx bt (mid with gas_obs := gs) = (INL (PlaceR p),ee)` by
    (irule tuplePlaceSourceHeadTheory.tuple_place_target_base_inversion >> simp[Abbr `gs`] >>
     metis_tac[]) >>
  drule_then strip_assume_tac body_inv_main_support >>
  drule_then (assume_tac o cj 2) body_inv_main_code >>
  drule_then (strip_assume_tac o REWRITE_RULE [cenv_module_pins_def])
    intcall_args_body_inv_pins >>
  drule_then
    (assume_tac o SIMP_RULE (srw_ss()) [optionTheory.FORALL_OPTION, ALOOKUP_def] o
     MATCH_MP body_assign_function_mutability_mods) body_inv_contract >>
  `IS_SOME (type_place_target env bt)` by
    (drule_then strip_assume_tac body_assign_saved_target_type >> simp[]) >>
  drule_all_then assume_tac body_inv_typed_target_calls_main >>
  `EVERY (\c. FST c = NONE /\ supported_program (cx_tops cx) /\
          IS_SOME (supported_function_decl (cx_tops cx) c Internal))
    (int_calls_target bt)` by
    (drule supported_stmt_body_safe >>
     simp[body_stmt_safe_def, int_calls_stmt_def, int_calls_atarget_def, EVERY_APPEND] >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  mp_tac (Q.INST [`es` |-> `es with gas_obs := prefix ++ gs`,
                  `es1` |-> `mid with gas_obs := gs`,
                  `p` |-> `p`, `ty` |-> `ty`,
                  `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
            body_assign_nonmutating_target_rhs) >>
  (impl_tac >-
    (simp[body_assign_saved_resources_gas, exprSimSubscriptArrayComposeTheory.read_result_success_gas_iff,
          vv_post_initial_gas, exprSimSubscriptArrayComposeTheory.vv_post_final_gas,
          assign_target_post_gas_obs] >>
     rpt conj_tac >> rpt strip_tac >> fs[ret_pc_ok_def] >>
     qpat_assum `!vis mut nr rr fn args dflts ret body. _ ==> function_mutability_ok _ _ _ _ _ _`
       drule >> simp[])) >>
  disch_then (qx_choose_then `z` (qx_choose_then `Gz` (qx_choose_then `tnz`
    (map_every assume_tac o CONJUNCTS)))) >>
  irule gas_outcome_full_zero_prefix_guarded >>
  simp[storage_trace_frame_write_place] >>
  qexistsl [`Gz`,`z`,`tnz`] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ [] _ /\ _` drule >> simp[]) >>
  `wb_frame cenv es ee sa s0 z` by
    (qpat_assum `wb_frame cenv (es with gas_obs := _) ee sa s0 z` mp_tac >>
     simp[NoAsms, wb_frame_def, locals_kept_def, popped_kept_def] >>
     gvs[NoAsms, wb_frame_def, locals_kept_def, popped_kept_def]) >>
  qpat_x_assum `!ms pl et g t w z gz tz ty'. (type_place_target _ _ = SOME (Type ty')) /\ _ ==> _`
    (qspecl_then [`marks`,`p`,`ee`,`Gu`,`tnu`,`u`,`z`,`Gz`,`tnz`,`ty`] mp_tac) >>
  (impl_tac >-
    (gvs[Abbr `gs`, body_assign_saved_resources_gas] >>
     conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[]
QED
Finalise body_assign_other_saved_target_bind[local]

Theorem body_assign_value_code_slice[local]:
  compile_expr cenv (expr_type e) e sa = (vv0,sr) /\
  ((expr_can_mutate cenv (target_to_expr t) /\
    compile_snapshot_vv cenv T (vv_with_type (lowered_value_type cenv e) vv0)
      sr = (vv,ss)) \/
   (~expr_can_mutate cenv (target_to_expr t) /\ vv = vv0 /\ ss = sr)) /\
  compile_get_target_ptr compile_expr cenv t ss = (r,st) /\
  unwrap_value cenv vv st = (op,su) /\
  (case FST (SND r) of
     SOME loc => compile_assign_value cenv (FST r) loc op
       (is_word_type (case SND (SND r) of SOME (ValPT ty) => ty
          | _ => lowered_value_type cenv e))
       (vv_location vv)
       (case SND (SND r) of SOME (ValPT ty) => ty
          | _ => lowered_value_type cenv e) (lowered_value_type cenv e)

       (type_memory_bytes cenv (case SND (SND r) of SOME (ValPT ty) => ty
          | _ => lowered_value_type cenv e)) su = ((),sb)
   | NONE => emit_void INVALID [] su = ((),sb)) /\
  fn_has_code sa sb func ==>
  ci_mono sa sr /\ ci_mono sr ss /\ ci_mono ss st /\
  ci_mono st su /\ ci_mono su sb /\
  fn_has_code sa sr func /\ fn_has_code sr ss func /\
  fn_has_code ss st func /\ fn_has_code st su func /\ fn_has_code su sb func
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono sa sr` by metis_tac[compile_expr_ci_mono,SND] >>
  `ci_mono sr ss` by metis_tac[ci_mono_compile_snapshot_vv,ci_mono_refl,SND] >>
  `ci_mono ss st` by metis_tac[ci_mono_compile_get_target_ptr,SND] >>
  `ci_mono st su` by metis_tac[ci_mono_unwrap_value,SND] >>
  `ci_mono su sb` by
    (qpat_x_assum `case FST (SND r) of SOME loc => _ | NONE => _` mp_tac >>
     Cases_on `FST (SND r)` >> simp[] >> strip_tac >>
     metis_tac[cj 1 ci_mono_stmt_helpers,ci_mono_emit_void,SND]) >>
  simp[] >>
  fs[ci_mono_def] >> imp_res_tac cs_extends_trans >>
  rpt conj_tac >> metis_tac[fn_has_code_split,cs_extends_refl]
QED

Theorem body_assign_value_paired_code[local]:
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  stmt_env cenv lctx ty (Assign (BaseTarget t) e) sa = (cenv',sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (Assign (BaseTarget t) e)) ta = (gas_shadow_env T cenv',tb) /\
  gas_shadow_state sa ta /\ fn_has_code sa sb func /\ fn_has_code ta tb tf ==>
  ?vv0 sr vv ss r st op su tr ts tt tu.
    cenv' = cenv /\
    compile_expr cenv (expr_type e) e sa = (vv0,sr) /\
    compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) ta = (vv0,tr) /\
    ((expr_can_mutate cenv (target_to_expr t) /\
      compile_snapshot_vv cenv T (vv_with_type (lowered_value_type cenv e) vv0)
        sr = (vv,ss) /\
      compile_snapshot_vv cenv T (vv_with_type (lowered_value_type cenv e) vv0)
        tr = (vv,ts)) \/
     (~expr_can_mutate cenv (target_to_expr t) /\ vv = vv0 /\ ss = sr /\ ts = tr)) /\
    compile_get_target_ptr compile_expr cenv t ss = (r,st) /\
    compile_get_target_ptr compile_expr (gas_shadow_env T cenv) (gas_shadow_target t) ts = (r,tt) /\
    unwrap_value cenv vv st = (op,su) /\ unwrap_value cenv vv tt = (op,tu) /\
    (case FST (SND r) of
       SOME loc => compile_assign_value cenv (FST r) loc op
         (is_word_type (case SND (SND r) of SOME (ValPT ty) => ty
            | _ => lowered_value_type cenv e))
         (vv_location vv)
         (case SND (SND r) of SOME (ValPT ty) => ty
            | _ => lowered_value_type cenv e) (lowered_value_type cenv e)

         (type_memory_bytes cenv (case SND (SND r) of SOME (ValPT ty) => ty
            | _ => lowered_value_type cenv e)) su = ((),sb) /\
         compile_assign_value cenv (FST r) loc op
         (is_word_type (case SND (SND r) of SOME (ValPT ty) => ty
            | _ => lowered_value_type cenv e))
         (vv_location vv)
         (case SND (SND r) of SOME (ValPT ty) => ty
            | _ => lowered_value_type cenv e) (lowered_value_type cenv e)

         (type_memory_bytes cenv (case SND (SND r) of SOME (ValPT ty) => ty
            | _ => lowered_value_type cenv e)) tu = ((),tb)
     | NONE => emit_void INVALID [] su = ((),sb) /\
               emit_void INVALID [] tu = ((),tb)) /\
    gas_shadow_state sr tr /\ gas_shadow_state ss ts /\
    gas_shadow_state st tt /\ gas_shadow_state su tu /\
    ci_mono sa sr /\ ci_mono sr ss /\ ci_mono ss st /\ ci_mono st su /\
    ci_mono su sb /\
    fn_has_code sa sr func /\ fn_has_code sr ss func /\ fn_has_code ss st func /\
    fn_has_code st su func /\ fn_has_code su sb func /\
    fn_has_code ta tr tf /\ fn_has_code tr ts tf /\ fn_has_code ts tt tf /\
    fn_has_code tt tu tf /\ fn_has_code tu tb tf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
  simp[Once gas_shadow_stmt_def,gas_shadow_assignment_def,Once gas_shadow_expr_def] >>
  disch_then (mp_tac o MATCH_MP stmt_env_assign) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (mk_asm "shadow")) >>
  qpat_x_assum `stmt_env _ _ _ (Assign _ _) _ = _`
    (mp_tac o MATCH_MP stmt_env_assign) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (mk_asm "real")) >>
  asm_x "real" mp_tac >>
  qpat_assum `~(has_length_word (expr_type e) /\ _)`
    (fn th => PURE_REWRITE_TAC [BETA_RULE (REWRITE_RULE [LET_THM]
      (MATCH_MP assignEffectfulIndexCodeTheory.assign_effectful_value_code th))]) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  `~(has_length_word (expr_type (gas_shadow_expr e)) /\
      is_empty_value_expr (gas_shadow_expr e))` by
    (rewrite_tac[gas_shadow_expr_type,gasShadowCompileStmtBaseTheory.gas_shadow_is_empty_value_expr] >>
     first_assum ACCEPT_TAC) >>
  asm_x "shadow" mp_tac >>
  qpat_x_assum `~(has_length_word (expr_type (gas_shadow_expr e)) /\ _)`
    (fn th => PURE_REWRITE_TAC [BETA_RULE (REWRITE_RULE [LET_THM]
      (MATCH_MP assignEffectfulIndexCodeTheory.assign_effectful_value_code th))]) >>
  pure_rewrite_tac[gas_shadow_expr_type,gasShadowCompileStmtBaseTheory.gas_shadow_target_to_expr,
       gasShadowCompileHelpersTheory.gas_shadow_expr_can_mutate,
       gasShadowCompilePureTheory.gas_shadow_lowered_value_type] >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  drule_all body_assign_value_code_slice >> strip_tac >>
  drule_all (PURE_REWRITE_RULE
    [gas_shadow_expr_type,gasShadowCompileStmtBaseTheory.gas_shadow_target_to_expr,
     gasShadowCompileHelpersTheory.gas_shadow_expr_can_mutate,
     gasShadowCompilePureTheory.gas_shadow_lowered_value_type]
    (Q.INST [`e` |-> `gas_shadow_expr e`,`t` |-> `gas_shadow_target t`]
      body_assign_value_code_slice)) >> strip_tac >>
  `vv0 = vv0' /\ gas_shadow_state sr sr'` by
    (`FST (compile_expr cenv (expr_type e) e sa) =
       FST (compile_expr (gas_shadow_env T cenv) (expr_type e)
         (gas_shadow_expr e) ta) /\
       gas_shadow_state (SND (compile_expr cenv (expr_type e) e sa))
         (SND (compile_expr (gas_shadow_env T cenv) (expr_type e)
           (gas_shadow_expr e) ta))` by
       (irule (REWRITE_RULE [gas_shadow_compiles_def]
          (Q.INST [`sd` |-> `T`] gas_shadow_stmt_compile_expr_env)) >> simp[]) >>
     gvs[]) >>
  Cases_on `expr_can_mutate cenv (target_to_expr t)` >> fs[] >>
  `vv = vv' /\ gas_shadow_state ss ss'` by
    (mp_tac (Q.INST [`copy_flag` |-> `T`,
                      `vv` |-> `vv_with_type (lowered_value_type cenv e) vv0`]
       gasShadowCompileConvertTheory.gas_shadow_compiles_snapshot_vv) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sr`,`sr'`] mp_tac) >> simp[]) >>
  rename1 `compile_get_target_ptr compile_expr _ (gas_shadow_target t) ss' = (trg,st')` >>
  `r = trg /\ gas_shadow_state st st'` by
    (`FST (compile_get_target_ptr compile_expr cenv t ss) =
       FST (compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
         (gas_shadow_target t) ss') /\
       gas_shadow_state (SND (compile_get_target_ptr compile_expr cenv t ss))
         (SND (compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
           (gas_shadow_target t) ss'))` by
       (irule (REWRITE_RULE [gas_shadow_compiles_def]
          (Q.INST [`sd` |-> `T`] gas_shadow_stmt_get_target_ptr_env)) >> simp[]) >>
     gvs[]) >>
  `op = op' /\ gas_shadow_state su su'` by
    (qpat_assum `vv = vv'` (fn eq =>
       qpat_assum `unwrap_value cenv vv' st' = _`
         (assume_tac o REWRITE_RULE [GSYM eq])) >>
     mp_tac gasShadowCompileConvertTheory.gas_shadow_compiles_unwrap_value >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`st`,`st'`] mp_tac) >>
     qpat_assum `unwrap_value cenv vv st = _` (fn real =>
       qpat_assum `unwrap_value cenv vv st' = _` (fn shadow =>
         qpat_assum `gas_shadow_state st st'` (fn states =>
           simp[NoAsms,real,shadow,states])))) >>
  gvs[] >>
  rename1 `compile_get_target_ptr compile_expr _ t _ = (z,_)` >>
  Cases_on `FST (SND z)` >> gvs[]
QED

(* Reading a materialised value is a source-only prefix at the raw RHS
   landing; the same target endpoint and marks witness the whole bind. *)
Theorem body_assign_read_prefix[local]:
  (!gs. read_result cx tv (mid with gas_obs := gs) =
          (INL v,mid with gas_obs := gs)) /\
  mid.gas_obs = [] /\ ~s.vs_halted /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (next v) (mid,s,G,tn) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (read_result cx tv) next) (mid,s,G,tn) Q R
Proof
  strip_tac >>
  `!gs. bind (read_result cx tv) next (mid with gas_obs := gs) =
         next v (mid with gas_obs := gs)` by simp[bind_def] >>
  irule gasOutcomeFullStmtsTheory.gas_outcome_full_handler_transport >>
  first_assum (irule_at Any) >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> qexistsl_tac [`err`,`ee`] >>
      simp[ignore_bind_def,bind_assoc] >>
      irule gasExemptPurePrefixTheory.gas_exempt_cert_pure_prefix >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexists `v` >>
      `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
      qpat_x_assum `gas_exempt_cert _ _ _ _ _ _ _ _` mp_tac >>
      simp[ignore_bind_def]) >>
  reverse conj_tac >- simp[gasStorageTheory.gas_bad_storage_at_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl_tac [`marks`,`res`,`ee`,`r`,`G'`,`tn'`] >> simp[]
QED

Theorem body_assign_raw_read_bind[local]:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_expr cx e) (es,s0,G0,tn0) A B /\
  (!H res ee G tn s. A H res ee G tn s ==>
    ?tv. res = INL tv /\ vv_post H ctx func cenv cx e es sa sr s0 ee tv vv0 s) /\
  (!H res ee gt r. B H res ee gt r ==>
    ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!marks tv v mid G tn s.
     (!tail. eval_expr cx e
          (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
          (INL tv,mid with gas_obs := tail)) /\
     (!tail. read_result cx tv (mid with gas_obs := tail) =
          (INL v,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     mid.gas_obs = [] /\ ~s.vs_halted /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          A H (INL tv) mid G tn s /\
          gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
            (s0,G0,tn0) marks (OK s,G,tn)) ==>
     gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
       (bind (eval_target_place cx t) (\p. write_place cx p v)) (mid,s,G,tn) Q R) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (eval_expr cx e) (\tv. bind (read_result cx tv)
      (\v. bind (eval_target_place cx t) (\p. write_place cx p v))))
    (es,s0,G0,tn0) Q R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule gas_outcome_full_bind_all_path >> BETA_TAC >> rpt conj_tac
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[cj 5 evaluate_storage_trace_frame]
  >- simp[storage_trace_frame_bind_all,storage_trace_frame_read_result,
          cj 8 evaluate_storage_trace_frame,storage_trace_frame_write_place]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule gas_exempt_cert_bind_result >> simp[] >>
      disch_then irule >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> first_assum ACCEPT_TAC) >>
  qexists `\H res ee G tn s. A H res ee G tn s /\ ee.gas_obs = [] /\ ~s.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >> first_assum (irule_at Any) >> simp[]) >>
  qx_genl_tac [`marks`,`res`,`mid`,`G`,`tn`,`s`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> A H res mid G tn s /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H res ee G tn s. A H res ee G tn s ==> _`
    (drule_then strip_assume_tac) >>
  gvs[] >>
  drule_then strip_assume_tac exprSimAggregateSourceTheory.vv_post_materialises >>
  `!tail. read_result cx tv (mid with gas_obs := tail) =
          (INL v,mid with gas_obs := tail)` by
    metis_tac[exprSimMemorySourceTheory.read_result_gas_obs] >>
  irule body_assign_read_prefix >> simp[] >>
  qpat_assum `!marks tv v mid G tn s. _ ==> gas_outcome_full _ _ _ _ _ _ _ _`
    (qspecl_then [`marks`,`tv`] irule) >> simp[] >>
  qexistsl_tac [`marks`,`tv`] >> simp[]
QED

Theorem body_assign_value_rhs_pre[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget t) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Assign (BaseTarget t) e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) ==>
  expr_body_pre cenv cx env e es
Proof
  strip_tac >>
  `well_typed_expr env e` by
    (qpat_x_assum `type_stmt _ _ _ = _` mp_tac >> simp[Once type_stmt_def]) >>
  drule_all_then ACCEPT_TAC body_assign_empty_target_rhs_pre
QED

Theorem body_assign_value_rhs_exit[local]:
  expr_exit (res : eval_result + exception) r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z) ==>
  ?exc. res = INR exc /\
    (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR exc) gt r) /\
    halt_exit H cx ee (INR exc : unit + exception) r /\
    (ctx_has_dalloca ctx ==>
      !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z)
Proof
  strip_tac >> Cases_on `res` >> fs[expr_exit_def] >>
  fs[stmt_exit_ptr_def,
     INST_TYPE [alpha |-> ``:unit``, beta |-> ``:eval_result``]
       stmtSimPropsTheory.expr_exit_INR_type,
     INST_TYPE [alpha |-> ``:unit``, beta |-> ``:eval_result``]
       haltExitProjTheory.halt_exit_INR_type] >>
  rpt strip_tac >> fs[expr_exit_def]
QED

(* Common prefix of the snapshot and nonmutating-target value assignments.
   The suffix starts at sr, before any snapshot, with the original stmt post. *)
Theorem body_assign_other_value_rhs_bind[local]:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    struct_args_unique tops /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (!st0 sa sb shadow_sa shadow_sb s0 G0 tn0 cenv'
      vv0 sr vv ss r st op su tr ts tt tu marks tv v mid G tn s.
      stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e) sa = (cenv',sb) /\
      stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e))
        shadow_sa = (gas_shadow_env T cenv',shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ret_pc_ok cenv sa s0 /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      ~block_is_terminated sa /\
      gas_admissible (eval_stmt cx (Assign (BaseTarget t) e)) (stmt_res_ok lctx) es /\
      return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\ ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      storage_trace_domain cx st0 es.storage_trace /\
      cenv' = cenv /\
      compile_expr cenv (expr_type e) e sa = (vv0,sr) /\
      compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa = (vv0,tr) /\
      ((expr_can_mutate cenv (target_to_expr t) /\
        compile_snapshot_vv cenv T (vv_with_type (lowered_value_type cenv e) vv0)
          sr = (vv,ss) /\
        compile_snapshot_vv cenv T (vv_with_type (lowered_value_type cenv e) vv0)
          tr = (vv,ts)) \/
       (~expr_can_mutate cenv (target_to_expr t) /\ vv = vv0 /\ ss = sr /\ ts = tr)) /\
      compile_get_target_ptr compile_expr cenv t ss = (r,st) /\
      compile_get_target_ptr compile_expr (gas_shadow_env T cenv) (gas_shadow_target t) ts = (r,tt) /\
      unwrap_value cenv vv st = (op,su) /\ unwrap_value cenv vv tt = (op,tu) /\
      (case FST (SND r) of
         SOME loc => compile_assign_value cenv (FST r) loc op
           (is_word_type (case SND (SND r) of SOME (ValPT ty) => ty
              | _ => lowered_value_type cenv e))
           (vv_location vv)
           (case SND (SND r) of SOME (ValPT ty) => ty
              | _ => lowered_value_type cenv e) (lowered_value_type cenv e)

           (type_memory_bytes cenv (case SND (SND r) of SOME (ValPT ty) => ty
              | _ => lowered_value_type cenv e)) su = ((),sb) /\
           compile_assign_value cenv (FST r) loc op
           (is_word_type (case SND (SND r) of SOME (ValPT ty) => ty
              | _ => lowered_value_type cenv e))
           (vv_location vv)
           (case SND (SND r) of SOME (ValPT ty) => ty
              | _ => lowered_value_type cenv e) (lowered_value_type cenv e)

           (type_memory_bytes cenv (case SND (SND r) of SOME (ValPT ty) => ty
              | _ => lowered_value_type cenv e)) tu = ((),shadow_sb)
       | NONE => emit_void INVALID [] su = ((),sb) /\
                 emit_void INVALID [] tu = ((),shadow_sb)) /\
      gas_shadow_state sr tr /\ gas_shadow_state ss ts /\
      gas_shadow_state st tt /\ gas_shadow_state su tu /\
      ci_mono sa sr /\ ci_mono sr ss /\ ci_mono ss st /\ ci_mono st su /\
      ci_mono su sb /\
      fn_has_code sa sr func /\ fn_has_code sr ss func /\ fn_has_code ss st func /\
      fn_has_code st su func /\ fn_has_code su sb func /\
      fn_has_code shadow_sa tr shadow_func /\ fn_has_code tr ts shadow_func /\
      fn_has_code ts tt shadow_func /\ fn_has_code tt tu shadow_func /\
      fn_has_code tu shadow_sb shadow_func /\
      (!tail. eval_expr cx e
          (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
          (INL tv,mid with gas_obs := tail)) /\
      (!tail. read_result cx tv (mid with gas_obs := tail) =
          (INL v,mid with gas_obs := tail)) /\
      storage_trace_domain cx st0 mid.storage_trace /\
      mid.gas_obs = [] /\ ~s.vs_halted /\
      (!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z) /\
      expr_body_pre cenv cx env e es /\ expr_sim_inv cenv cx env mid /\
      body_base_target_full_ok cx t /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        vv_post H ctx func cenv cx e es sa sr s0 mid tv vv0 s /\
        vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
          mid tv vv0 s /\
        s.vs_current_bb = sr.cs_current_bb /\ s.vs_inst_idx = LENGTH sr.cs_current_insts /\
        alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
        s0.vs_alloca_next <= s.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx mid G tn s /\
        ptr_vv_ok cx (post_value_type cenv e) tv vv0 mid G tn s /\
        (!v'. tv = Value v' /\ ~is_word_type (post_value_type cenv e) /\
             ~is_bytestring_type (post_value_type cenv e) ==>
             vv_own cenv cx (post_value_type cenv e) sa sr mid tv vv0 s /\
             (!ty p. vv0 = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
        (cenv.ce_is_ctor /\ vv_location vv0 = SOME LocCode ==>
           ?val. read_result cx tv mid = (INL val,mid) /\
                 !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                        eval_operand (vv_operand vv0) s = SOME w ==>
                        w2n w + type_memory_size rt <= lo /\
                        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                               val_in_memory rt val (w2n w) mem)) /\
        (!ty x. vv0 = StackValue ty x /\ ~is_word_type (post_value_type cenv e) ==>
                ptr_buf_ok cenv e x G s) /\
        (!ty p. vv0 = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
                ptr_buf_ok cenv e p.ptr_operand G s) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0 (bind (eval_target_place cx t) (\p. write_place cx p v))
        (mid,s,G,tn)
        (\H res ee G' tn' z. ?cenv''.
          stmt_lands lctx sb res z /\ ~z.vs_halted /\
          (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
          cenv_top_ext cenv cenv'' ee.scopes /\
          stmt_state_rel H ctx func cenv'' cx ee z /\
          storage_well_formed_on cx ee (FST H) /\
          return_buf_frame d cenv'' sb z /\ alloca_history func z /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
          s0.vs_alloca_next <= z.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv'' cx ee G' tn' z /\
          (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                 lookup_var x z = SOME w) /\
          (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                   FLOOKUP z.vs_allocas aid = SOME b) /\
          (!x. not_fresh_at sa x ==>
               FLOOKUP G' x = FLOOKUP G0 x /\
               op_taint tn' (Var x) = op_taint tn0 (Var x)) /\
          alloca_frame cenv es sa s0 cenv'' ee z /\
          (!aid off sz i.
             FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
             (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                        off + sz <= b \/ b + sz' <= off) /\
             off <= i /\ i < off + sz /\ i IN tn'.t_mem ==>
             i IN tn0.t_mem))
        (\H res ee gt r.
          (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
          halt_exit H cx ee res r /\
          (ctx_has_dalloca ctx ==>
           !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z))) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e)))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all body_assign_value_rhs_pre >> strip_tac >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by metis_tac[body_expr_full_ok_def] >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule gas_outcome_full_initial_domain >>
  simp[cj 1 evaluate_storage_trace_frame] >> strip_tac >>
  drule_all body_assign_value_paired_code >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    (drule expr_body_pre_vv_gas_admissible >> simp[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sr`,`shadow_sa`,`tr`,`vv0`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  irule assign_return_buf_sep >> asm_rewrite_tac[] >>
  once_rewrite_tac[evaluate_def] >>
  irule body_assign_raw_read_bind >> first_assum (irule_at Any) >> BETA_TAC >>
  qexistsl [`vv0`,`sr`,`sa`,`cenv`] >>
  reverse conj_tac
  >- (conj_tac >- (rpt gen_tac >> strip_tac >> simp[] >> metis_tac[]) >>
      rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      irule body_assign_value_rhs_exit >> simp[]) >>
  qx_genl_tac [`marks`,`tv`,`v`,`mid`,`G`,`tn`,`s`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z` by
    (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
     `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
       fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\
        gas_origin_ptr_path _ (s0,G0,tn0) marks (OK s,G,tn)`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (fn post =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` (fn phi =>
         qpat_assum `!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z`
           (fn nowrap => ACCEPT_TAC (MATCH_MP
             bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom
             (LIST_CONJ [CONJUNCT2 post,phi,nowrap])))))) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,mid)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => simp[NoAsms, listTheory.APPEND_NIL, th])) >>
  `read_result cx tv mid = (INL v,mid)` by
    (qpat_assum `!tail. read_result _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => simp[NoAsms, th])) >>
  `body_base_target_full_ok cx t` by
    (qpat_assum `!a b c d e f. _ ==> body_base_target_full_ok _ _` irule >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `expr_sim_inv cenv cx env mid` by
    (irule bodySimStmtFactsTheory.expr_body_pre_eval_result >>
     qexistsl [`e`,`es with gas_obs := gas_explicit marks s0.vs_gas_readings`,`INL tv`] >>
     simp[exprSimSourceTheory.expr_body_pre_gas_obs]) >>
  first_assum irule >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`marks`,`op`,`r`,`shadow_sa`,`shadow_sb`,`ss`,`st`,`su`,
            `tr`,`ts`,`tt`,`tu`,`tv`,`vv`] >>
  simp[] >> qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
    (?tv'. _) /\ gas_origin_ptr_path _ _ _ _`
    (qspec_then `H` (drule_then (strip_assume_tac o CONJUNCT1))) >>
  qpat_x_assum `INL tv = INL tv'` (SUBST_ALL_TAC o SYM o SRULE []) >>
  simp[] >> conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_assum `!v. tv = Value v /\ _ ==> vv_own _ _ _ _ _ _ _ _ _ /\ _`
        (qspec_then `v'` mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      strip_tac >>
      qpat_assum `tv = Value v'` (SUBST1_TAC o SYM) >>
      first_assum ACCEPT_TAC) >>
  strip_tac >>
  qpat_assum `cenv.ce_is_ctor /\ vv_location vv0 = SOME LocCode ==> ?val. _` mp_tac >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `val` strip_assume_tac) >>
  `val = v` by
    (qpat_assum `read_result cx tv mid = (INL val,mid)` mp_tac >>
     qpat_assum `read_result cx tv mid = (INL v,mid)` (fn th => simp[NoAsms, th])) >>
  qpat_x_assum `val = v` SUBST_ALL_TAC >>
  qpat_assum `!rt w. evaluate_type _ _ = SOME rt /\ _ ==> _`
    (ACCEPT_TAC o ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM])
QED


Theorem body_assign_immutable_bytes_joint_frame[local]:
  compile_store_immutable_bytestring ce.ce_imm_alloca (Var src) (Lit (n2w off)) sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  not_fresh_at sa src /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  P H0 /\
  (!H. P H ==> stmt_state_rel H ctx func ce cx es s /\
    ghost_inv_at (DF H) lo d ce cx es G tn s /\
    dead_lo_ok H (DF H) lo ce cx) /\
  expr_sim_inv ce cx env es /\ local_ptrs_reserved ce sa /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME dty /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  tops = cx_tops cx /\ get_tenv cx = type_env tops /\ struct_args_unique tops /\
  tops = pre ++ VariableDecl vis Immutable id dty slot :: post /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  type_widens_to (get_tenv cx) sty dty /\ value_has_type stv v /\
  well_formed_type_value dtv /\ immutable_value_admissible dtv v /\
  off + type_memory_size dtv <= lo /\ lo < dimword(:256) /\
  write_place cx (ImmutablePlace ce.ce_module id []) v es = (INL (),es') /\
  eval_operand (Var src) s = SOME (n2w a) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory stv v a mem) /\
  ptr_covers G tn src s (type_memory_size stv) /\
  lo <= a /\ a + type_memory_size stv < dimword(:256) /\
  (type_memory_size stv = 0 \/ a + type_memory_size stv <= s.vs_alloca_next) /\
  (!region. ce.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ op_taint tn region = {} /\
    op_prov G region = NONE) /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x. ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ghost_kept_at lo c0 es0 sa0 G0 tn0 s0 G tn /\
  sa0.cs_next_var <= sa.cs_next_var /\
  (!name b cap. local_region c0 es0.scopes s0 name b cap ==> lo <= b) /\
  alloca_frame c0 es0 sa0 s0 ce es s /\ allocas_from lo s0 /\
  (!aid b sz i. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa0.cs_next_id /\
    (!name q cap. local_region c0 es0.scopes s0 name q cap ==>
      b+sz <= q \/ q+cap <= b) /\ b <= i /\ i < b+sz /\ i IN tn.t_mem ==>
    i IN tn0.t_mem) ==>
  ?t Gf tnf.
    (!H. P H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf) /\ stmt_state_rel H ctx func ce cx es' t /\
      ghost_inv_at (DF H) lo d ce cx es' Gf tnf t) /\
    return_buf_frame d ce sb t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    ghost_kept_at lo c0 es0 sa0 G0 tn0 s0 Gf tnf /\
    alloca_frame c0 es0 sa0 s0 ce es' t /\
    (!aid b sz i. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa0.cs_next_id /\
      (!name q cap. local_region c0 es0.scopes s0 name q cap ==>
        b+sz <= q \/ q+cap <= b) /\ b <= i /\ i < b+sz /\ i IN tnf.t_mem ==>
      i IN tn0.t_mem) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `allocas_from lo s` by
    (qpat_assum `!H. P H ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `H0` (drule_then strip_assume_tac)) >>
     qpat_assum `ghost_inv_at (DF H0) lo d ce cx es G tn s`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     first_assum ACCEPT_TAC) >>
  `copy_old_operand sa (Lit (n2w off)) /\
   eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   op_taint tn (Lit (n2w off)) = {} /\ op_prov G (Lit (n2w off)) = NONE` by
    simp[copy_old_operand_def, eval_operand_def, op_taint_def, op_prov_def] >>
  mp_tac (Q.INST [`imm` |-> `ce.ce_imm_alloca`, `dst` |-> `Lit (n2w off)`,
                  `explicit` |-> `explicit`, `PG` |-> `PG`]
    body_assign_immutable_bytes_path_copy) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`len`,`t_exit`,`G_exit`,`tn_exit`]
    (map_every assume_tac o CONJUNCTS)) >>
  Q.SUBGOAL_THEN
    `((?bs. v = BytesV bs /\ len = LENGTH bs) \/
      (?str. v = StringV str /\ len = LENGTH str)) /\
     val_store_size stv v = 32 * (1 + word_size len)`
    (map_every assume_tac o CONJUNCTS)
  >- (`(?n. stv = BaseTV (BytesT (Dynamic n))) \/ (?n. stv = BaseTV (StringT n))` by
       (match_mp_tac (Q.SPECL [`get_tenv cx`,`sty`,`stv`] bytestring_type_value) >>
        asm_rewrite_tac[]) >>
     qpat_assum `value_has_type stv v` mp_tac >>
     qpat_assum `val_footprint stv v = 32 + len` mp_tac >>
     pop_assum mp_tac >>
     POP_ASSUM_LIST kall_tac >>
     disch_then strip_assume_tac >> disch_tac >> disch_tac >>
     Cases_on `v` >>
     gvs[value_has_type_def, val_footprint_def, val_store_size_def,
         LEFT_ADD_DISTRIB]) >>
  `a + 32 * (1 + word_size len) < dimword(:256)` by
    (`val_store_size stv v <= type_memory_size stv` by
       simp[val_store_size_le, valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
     decide_tac) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qspecl_then [`ce.ce_imm_alloca`,`Var src`,`Lit (n2w off)`,`sa`]
       mp_tac ci_mono_store_immutable_bytestring >>
     simp[ci_mono_def]) >>
  `gas_origin_ptr_path (DF H0,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK t_exit,G_exit,tn_exit)` by
    first_assum MATCH_ACCEPT_TAC >>
  `!k. k < 32 * (1 + word_size len) /\ off+k IN tn_exit.t_mem ==>
      a+k IN tn.t_mem` by
    (rpt strip_tac >>
     qpat_assum `!k. k < _ ==> (off+k IN tn_exit.t_mem <=> _)`
       (qspec_then `k` (drule_then mp_tac)) >> simp[]) >>
  `!i. ~(off <= i /\ i < off+32 * (1 + word_size len)) /\ i IN tn_exit.t_mem ==>
      i IN tn.t_mem` by
    (rpt strip_tac >>
     qpat_assum `!i. ~(_ /\ _) ==> (i IN tn_exit.t_mem <=> _)`
       (qspec_then `i` (drule_then mp_tac)) >> simp[]) >>
  mp_tac (Q.INST [`n` |-> `1 + word_size len`, `t` |-> `t_exit`,
    `Gf` |-> `G_exit`, `tnf` |-> `tn_exit`, `marks` |-> `[]`]
    body_assign_immutable_bytes_restore) >>
  impl_tac >-
    (pure_rewrite_tac[REFL_CLAUSE, boolTheory.AND_CLAUSES] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  `t_exit.vs_allocas = s.vs_allocas /\ t_exit.vs_alloca_next = s.vs_alloca_next /\
   t_exit.vs_fmp = s.vs_fmp /\ t_exit.vs_initial_fmp = s.vs_initial_fmp` by
    (`((immutable_transfers T T (n2w a) (n2w off) (1 + word_size len) 0 s) with
       <|vs_memory := s.vs_memory; vs_immutables := s.vs_immutables|>) = s` by
       simp[immutable_transfers_record_restore] >>
     pop_assum mp_tac >>
     qpat_assum `(t_exit with <|vs_vars := _; vs_current_bb := _;
       vs_prev_bb := _; vs_inst_idx := _|>) = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t_exit` by
    (disch_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
       (drule_then (strip_assume_tac o REWRITE_RULE [allocas_below_fmp_def])) >>
     rewrite_tac[allocas_below_fmp_def] >> asm_rewrite_tac[]) >>
  qexistsl_tac [`t_exit`,`G_exit`,`tn_exit`] >>
  conj_tac
  >- (gen_tac >> disch_tac >> conj_tac
      >- first_assum MATCH_ACCEPT_TAC >>
      qpat_assum `!H. P H ==> stmt_state_rel H _ _ _ _ es' t_exit /\ _`
        (drule_then ACCEPT_TAC)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem body_assign_immutable_memory_dispatch[local]:
  compile_assign_value ce dst LocCode src F loc dty sty bytes sa = ((),sb) /\
  type_widens_to tenv sty dty ==>
  (is_bytestring_type dty /\ is_bytestring_type sty /\
   compile_store_immutable_bytestring ce.ce_imm_alloca src dst sa = ((),sb)) \/
  (~is_bytestring_type dty /\ sty = dty) \/
  (~is_bytestring_type dty /\ ~is_bytestring_type sty /\ sty <> dty /\
   ?buf sm sn. compile_alloc_buffer bytes sa = (buf,sm) /\
     compile_store_memory_typed ce buf.buf_operand dty src sty sm = ((),sn) /\
     compile_assign_value ce dst LocCode buf.buf_operand F loc dty dty bytes sn = ((),sb))
Proof
  strip_tac >> Cases_on `is_bytestring_type dty`
  >- (`is_bytestring_type sty` by metis_tac[typed_copy_bytestring_source] >>
      fs[compile_assign_value_def, comp_bind_def, comp_return_def]) >>
  Cases_on `sty = dty` >- simp[] >>
  `~is_bytestring_type sty` by metis_tac[type_widens_from_bytestring] >>
  `dty <> sty` by metis_tac[] >>
  drule_all immutable_assign_normalized_compile >> strip_tac >> simp[] >>
  fs[compile_assign_value_def, comp_bind_def, comp_return_def, comp_ignore_bind_def]
QED

Theorem body_assign_other_immutable_nonword_entry[local]:
  ~is_word_type ity /\
  assignable_type env.type_defs (expr_type e) /\
  type_widens_to env.type_defs (expr_type e) ity /\
  FLOOKUP env.bare_globals (src,id) = SOME ity /\
  expr_body_pre ce cx env e es /\ ee.gas_obs = [] /\
  expr_sim_inv ce cx env ee /\
  (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gs ++ tail) = (INL v,ee with gas_obs := tail)) /\
  expr_post (H:(bool # bytes32 # type_value) list # num list)
    ctx func ce cx e es sa su s0 ee v op z /\
  ptr_val_ok cx (post_value_type ce e) v op G tn z /\
  (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G z) ==>
  ?itv stv p (w:bytes32) fin.
    evaluate_type (get_tenv cx) ity = SOME itv /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    type_widens_to (get_tenv cx) (lowered_value_type ce e) ity /\
    ~is_word_type (lowered_value_type ce e) /\
    value_has_type stv v /\ val_wf stv v /\
    type_memory_bytes ce ity = type_memory_size itv /\
    0 < type_memory_size itv /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
    0 < type_memory_size stv /\
    op = Var p /\ lookup_var p z = SOME w /\
    ptr_covers G tn p z (type_memory_size stv) /\
    (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
           val_in_memory stv v (w2n w) mem) /\
    expr_val_at ce cx (lowered_value_type ce e) sa su ee v op z /\
    write_place cx (ImmutablePlace src id []) v ee = (INL (),fin) /\
    (!tail. write_place cx (ImmutablePlace src id []) v (ee with gas_obs := tail) =
       (INL (),fin with gas_obs := tail)) /\
    fin.gas_obs = [] /\ fin.storage_trace = ee.storage_trace
Proof
  strip_tac >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
    (qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
       (qspec_then `[]` mp_tac) >>
     qpat_assum `ee with gas_obs := [] = ee`
       (fn th => rewrite_tac[listTheory.APPEND_NIL,th])) >>
  `expr_body_pre ce cx env e (es with gas_obs := gs)` by
    simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
  drule_all_then strip_assume_tac
    (SIMP_RULE (srw_ss() ++ ETA_ss) [] immutableDeployPhysicalSourceTheory.immutable_rhs_physical_typed) >>
  drule_all_then assume_tac immutableDeployPhysicalSourceTheory.immutable_rhs_physical_widens >>
  drule_all_then (qx_choose_then `itv` strip_assume_tac)
    vyperTypeArgFitsTheory.type_widens_to_value_has_type >>
  `~is_word_type (lowered_value_type ce e)` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq] >>
  `0 < type_memory_size stv` by
    (drule_all immutableAssignRepresentationTheory.immutable_assign_rhs_memory_positive >> simp[]) >>
  `type_memory_bytes ce ity = type_memory_size itv` by
    (drule_all exprSimHypsTheory.expr_sim_inv_memory_size >> simp[]) >>
  `0 < type_memory_size itv` by
    (`env.type_defs = get_tenv cx` by
       (drule exprSimAbiDecodeEntryTypingTheory.abi_decode_inv_type_env >> simp[]) >>
     `?etv. evaluate_type env.type_defs (expr_type e) = SOME etv` by
       metis_tac[exprSimHypsTheory.expr_body_pre_type_evaluates, optionTheory.IS_SOME_EXISTS] >>
     pop_assum strip_assume_tac >>
     `evaluate_type env.type_defs ity = SOME itv` by simp[] >>
     drule_all immutableAssignRepresentationTheory.immutable_assign_widened_memory_positive >> simp[]) >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[immutableDeployPhysicalSourceTheory.immutable_rhs_post_physical_classify,
              valueCopyBytesTheory.is_bytestring_word_type] >>
  `expr_val_at ce cx (lowered_value_type ce e) sa su ee v op z` by
    (irule abiEncodeArgsSimTheory.abi_args_expr_post_lowered_at >>
     conj_tac >- (strip_tac >> qexists `stv` >> simp[]) >>
     conj_tac >- (qexistsl [`env`,`es`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  `expr_post H ctx func ce cx e (es with gas_obs := gs) sa su s0 ee v op z` by
    simp[exprSimExtract32PostTheory.extract32_expr_post_start_gas_obs] >>
  drule_all_then (qx_choose_then `w` strip_assume_tac)
    (SIMP_RULE (srw_ss() ++ ETA_ss) [] bodyFullStructLitPhysicalTheory.structlit_child_physical_robust) >>
  `op_taint tn op = {}` by fs[ptr_val_ok_def] >>
  `ptr_buf_ok ce e op G z` by simp[] >>
  `?p. op = Var p /\ ptr_covers G tn p z (type_memory_size stv)` by
    (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
     simp[] >> qexistsl [`ce`,`e`] >> simp[]) >>
  pop_assum strip_assume_tac >>
  `lookup_var p z = SOME w` by fs[eval_operand_def] >>
  drule_all_then (qx_choose_then `mods` (qx_choose_then `old` strip_assume_tac))
    immutableDeployAssignSourceFrameTheory.immutable_assign_source_lookup >>
  qabbrev_tac `fin = ee with immutables :=
    (cx.txn.target, update_immutable src id itv v mods) ::
    ADELKEY cx.txn.target ee.immutables` >>
  `write_place cx (ImmutablePlace src id []) v ee = (INL (),fin)` by
    simp[Abbr `fin`, bodyImmutableAugAssignStoreTheory.immutable_augassign_write_source] >>
  drule_then assume_tac bodyImmutableAugAssignExecTheory.immutable_write_place_gas_obs >>
  qexistsl [`itv`,`stv`,`p`,`w`,`fin`] >> simp[Abbr `fin`]
QED

(* The physical RHS is already materialised at the literal constructor
   destination's write entry.  Normalisation, when required, is part of
   the write suffix, so preservation of allocations is monotone. *)
Theorem body_assign_immutable_memory_joint[local]:
  compile_assign_value ce (Lit (n2w off)) LocCode (Var src) F loc ity sty
    (type_memory_bytes ce ity) sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~block_is_terminated sb /\
  body_inv tops ctx ce cx /\ struct_args_unique tops /\ expr_sim_inv ce cx env ee /\
  ce.ce_is_ctor /\ local_ptrs_reserved ce sa /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ity /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\
  tops = cx_tops cx /\ get_tenv cx = type_env tops /\
  tops = pre ++ VariableDecl vis Immutable id ity slot :: post /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
  evaluate_type (get_tenv cx) ity = SOME itv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  ~is_word_type ity /\ ~is_word_type sty /\ type_widens_to (get_tenv cx) sty ity /\
  type_memory_bytes ce ity = type_memory_size itv /\ 0 < type_memory_size itv /\
  value_has_type stv v /\ val_wf stv v /\
  off + type_memory_size itv <= lo /\ lo < dimword (:256) /\
  write_place cx (ImmutablePlace ce.ce_module id []) v ee = (INL (),fin) /\
  not_fresh_at sa src /\ lookup_var src s = SOME (n2w a) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory stv v a mem) /\
  ptr_covers G tn src s (type_memory_size stv) /\
  lo <= a /\ a + type_memory_size stv < dimword (:256) /\
  a + type_memory_size stv <= s.vs_alloca_next /\
  (~is_bytestring_type sty ==> expr_val_at ce cx sty start sa ee v (Var src) s) /\
  (!region. ce.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ op_taint tn region = {} /\ op_prov G region = NONE) /\
  (!x. ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) ==>
  ?q Gf tf.
    fin.storage_trace = ee.storage_trace /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q,Gf,tf) /\
      stmt_post H ctx func cx lctx ce ce sa sb ee s (INL ()) fin q /\
      ghost_inv_at (DF H) lo d ce cx fin Gf tf q) /\
    return_buf_frame d ce sb q /\ alloca_history func q /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
    s.vs_alloca_next <= q.vs_alloca_next /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP q.vs_allocas aid = SOME ent) /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    ghost_kept_at lo ce ee sa G tn s Gf tf /\ alloca_frame ce ee sa s ce fin q /\
    (!aid b sz i. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
      (!name a len. local_region ce ee.scopes s name a len ==>
        b+sz <= a \/ a+len <= b) /\ b <= i /\ i < b+sz /\ i IN tf.t_mem ==>
      i IN tn.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `fin.storage_trace = ee.storage_trace /\ fin.accounts = ee.accounts /\
   fin.tStorage = ee.tStorage` by
    (drule write_immutable_place_frame >> strip_tac >> simp[]) >>
  `eval_operand (Var src) s = SOME (n2w a)` by simp[eval_operand_def] >>
  drule_all body_assign_immutable_memory_dispatch >> strip_tac
  >- suspend "bytes"
  >- suspend "direct"
  >> suspend "normalize"
QED

Resume body_assign_immutable_memory_joint[direct]:
  `itv = stv` by fs[] >>
  `a < dimword (:256)` by decide_tac >>
  `off + type_memory_size itv < dimword (:256)` by decide_tac >>
  `off + type_memory_size itv <= a` by decide_tac >>
  `val_in_memory stv v a s.vs_memory` by fs[mem_agree_outside_def] >>
  `val_footprint stv v <= type_memory_size itv` by metis_tac[val_footprint_le] >>
  `ptr_val_ok cx ity v (Var src) G tn s` by
    (irule rawCallBufferPtrTheory.ptr_val_ok_from_type_covers >>
     fs[w2n_n2w, LESS_MOD] >> metis_tac[]) >>
  qabbrev_tac `k = type_memory_size itv` >>
  qabbrev_tac `n = if k <= 32 then 1 else (k+31) DIV 32` >>
  `32*n = k` by
    (`k = 32 * type_slot_size itv` by simp[Abbr `k`,type_memory_size_slots] >>
     Cases_on `k <= 32` >> simp[Abbr `n`]
     >- gvs[] >>
     `((32 * type_slot_size itv + 31) DIV 32) = type_slot_size itv` by
       (once_rewrite_tac[MULT_COMM] >> simp[DIV_MULT]) >>
     fs[]) >>
  `k <= 32*n /\ 32*n <= type_memory_size itv /\
   a+k < dimword (:256) /\ off+32*n < dimword (:256) /\
   off+32*n <= a /\ a+32*n <= s.vs_alloca_next /\ off+32*n <= lo` by
    (qpat_x_assum `off = compute_immutables_len _ _` kall_tac >>
     gvs[Abbr `k`] >> decide_tac) >>
  `n = (if k <= 32 then 1 else (k+31) DIV 32)` by simp[Abbr `n`] >>
  `!x. Var src = Var x ==> not_fresh_at sa x` by simp[] >>
  `!region x. ce.ce_imm_alloca = SOME region /\ region = Var x ==>
      not_fresh_at sa x` by simp[] >>
  `value_has_type itv v` by fs[] >>
  `ity = sty` by simp[] >>
  qpat_x_assum `sty = ity` kall_tac >>
  `a+k <= off \/ off+32*n <= a` suffices_by
    (disch_tac >>
     `k = (if is_bytestring_type ity then type_memory_bytes ce sty
           else type_memory_bytes ce ity)` by simp[] >>
     drule_all body_assign_immutable_direct_joint >>
     disch_then (qspecl_then [`lctx`,`explicit`,`PG`]
       (qx_choosel_then [`q`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS))) >>
     `stmt_post (storage_trace_horizon ee.storage_trace) ctx func cx lctx
       ce ce sa sb ee s (INL ()) fin q` by
       (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _ /\ stmt_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
          (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
        simp[]) >>
     qexistsl [`q`,`Gf`,`tf`] >> simp[] >>
     conj_tac
     >- (qpat_x_assum `stmt_post (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE[stmt_post_def]) >>
         first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     qpat_assum `!aid b sz i. FLOOKUP _ aid = SOME (b,sz) /\ _ /\
                 b <= i /\ i < b+sz /\ i IN tf.t_mem ==> _`
       irule >>
     conj_tac
     >- (qexistsl [`aid`,`b`,`sz`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  simp[]
QED

Resume body_assign_immutable_memory_joint[bytes]:
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by simp[Abbr `H0`] >>
  `stmt_state_rel H0 ctx func ce cx ee s /\ ghost_inv_at (DF H0) lo d ce cx ee G tn s` by simp[] >>
  `allocas_from lo s` by
    (qpat_assum `ghost_inv_at (DF H0) _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[ghost_inv_at_def]) >> first_assum ACCEPT_TAC) >>
  `dead_lo_ok H0 (DF H0) lo ce cx` by simp[] >>
  `!name b cap. local_region ce ee.scopes s name b cap /\ 0 < cap ==> lo <= b` by
    (rpt strip_tac >> drule_all (INST_TYPE [``:'a`` |-> ``:256``]
       body_full_local_region_lower_bound) >> simp[]) >>
  qabbrev_tac `cr = ce with ce_vars :=
    DRESTRICT ce.ce_vars {n | ?b k. local_region ce ee.scopes s n b k /\ lo <= b}` >>
  `!n b k. local_region cr ee.scopes s n b k <=>
          local_region ce ee.scopes s n b k /\ lo <= b` by
    (rpt gen_tac >> simp[Abbr `cr`, local_region_def, FLOOKUP_DRESTRICT_SOME] >>
     eq_tac >> rpt strip_tac >> gvs[SF SFY_ss]) >>
  `!n b k i. local_region ce ee.scopes s n b k /\ b <= i /\ i < b+k ==>
             local_region cr ee.scopes s n b k` by
    (rpt strip_tac >> simp[] >> qpat_assum `!n b k. local_region ce _ _ n b k /\ _ ==> _` irule >>
     qexistsl [`k`,`n`] >> simp[] >> decide_tac) >>
  `!aid u z. FLOOKUP s.vs_allocas aid = SOME (u,z) ==>
      ((!n b k. local_region cr ee.scopes s n b k ==> u+z <= b \/ b+k <= u) <=>
       (!n b k. local_region ce ee.scopes s n b k ==> u+z <= b \/ b+k <= u))` by
    (rpt gen_tac >> strip_tac >> simp[] >> eq_tac >> rpt strip_tac
     >- (Cases_on `lo <= b`
         >- (qpat_assum `!n b k. local_region ce _ _ n b k /\ lo <= b ==> _`
               (qspecl_then [`n`,`b`,`k`] mp_tac) >> simp[]) >>
         `lo <= u` by
           (qpat_assum `allocas_from lo s`
              (qspecl_then [`aid`,`u`,`z`] mp_tac o REWRITE_RULE[allocas_from_def]) >> simp[]) >>
         `0 < k ==> lo <= b` by
           (qpat_assum `!n b k. local_region ce _ _ n b k /\ 0 < k ==> _`
              (qspecl_then [`n`,`b`,`k`] mp_tac) >> simp[]) >>
         decide_tac) >>
     qpat_assum `!n b k. local_region ce _ _ n b k ==> _`
       (qspecl_then [`n`,`b`,`k`] mp_tac) >> simp[]) >>
  `alloca_frame cr ee sa s ce ee s` by
    (rewrite_tac[alloca_frame_def] >> rpt gen_tac >> strip_tac >>
     qpat_assum `!aid u z. FLOOKUP s.vs_allocas aid = SOME (u,z) ==> (_ <=> _)`
       (drule_then (once_rewrite_tac o single o GSYM)) >> simp[NoAsms] >>
     first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo cr ee sa G tn s G tn` by simp[ghost_kept_at_def] >>
  `well_formed_type_value itv` by
    (qpat_assum `evaluate_type _ ity = SOME itv`
       (mp_then Any ACCEPT_TAC (cj 1 evaluate_type_well_formed))) >>
  `value_has_type itv v` by
    (drule_all type_widens_to_value_has_type >> strip_tac >> gvs[]) >>
  `immutable_value_admissible itv v` by drule_all_then ACCEPT_TAC typed_immutable_admissible >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func ce cx ee s /\ ghost_inv_at (DF H) lo d ce cx ee G tn s /\
       dead_lo_ok H (DF H) lo ce cx` by simp[] >>
  mp_tac (Q.INST [`P` |-> `\H. valid_horizon cx st0 H ee.storage_trace`,
                  `dty` |-> `ity`, `dtv` |-> `itv`, `es` |-> `ee`, `es'` |-> `fin`,
                  `c0` |-> `cr`, `es0` |-> `ee`, `sa0` |-> `sa`,
                  `s0` |-> `s`, `G0` |-> `G`, `tn0` |-> `tn`]
    (INST_TYPE [``:'a`` |-> ``:256``] body_assign_immutable_bytes_joint_frame)) >>
  (impl_tac >-
    (simp[] >> once_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
     rewrite_tac[listTheory.APPEND] >>
     qpat_assum `tops = pre ++ _ :: post` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`q`,`Gf`,`tf`]
    (map_every assume_tac o CONJUNCTS o BETA_RULE)) >>
  `alloca_frame ce ee sa s ce fin q` by
    (rewrite_tac[alloca_frame_def] >> rpt gen_tac >> strip_tac >>
     qpat_assum `alloca_frame cr _ _ _ _ _ _`
       (irule o REWRITE_RULE[alloca_frame_def]) >>
     metis_tac[]) >>
  `!aid b sz i. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
      (!name a len. local_region ce ee.scopes s name a len ==>
        b+sz <= a \/ a+len <= b) /\ b <= i /\ i < b+sz /\ i IN tf.t_mem ==>
      i IN tn.t_mem` by
    (rpt strip_tac >>
     qpat_assum `!aid b sz i. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ _ /\
          (!name q k. local_region cr _ _ name q k ==> _) /\ _ ==> _`
       (qspecl_then [`aid`,`b`,`sz`,`i`] mp_tac) >>
     (impl_tac >-
       (qpat_assum `!aid u z. FLOOKUP s.vs_allocas aid = SOME (u,z) ==> (_ <=> _)`
          (drule_then (once_rewrite_tac o single)) >>
        rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `ghost_kept_at lo ce ee sa G tn s Gf tf` by
    (qpat_assum `ghost_kept_at lo cr ee sa G tn s Gf tf`
       (strip_assume_tac o REWRITE_RULE[ghost_kept_at_def]) >>
     rewrite_tac[ghost_kept_at_def] >> conj_tac
     >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt strip_tac >>
     qpat_assum `!n b k i. local_region cr _ _ n b k /\ _ ==> _`
       (qspecl_then [`n`,`b`,`sz`,`i`] mp_tac) >>
     (impl_tac >-
       (`local_region cr ee.scopes s n b sz` by
          (qpat_assum `!n b k i. local_region ce _ _ n b k /\ _ ==> local_region cr _ _ n b k`
             (qspecl_then [`n`,`b`,`sz`,`i`] mp_tac) >>
           rpt (first_assum ACCEPT_TAC ORELSE strip_tac) >> simp[]) >>
        rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  qexistsl [`q`,`Gf`,`tf`] >> simp[] >>
  rpt strip_tac >> simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >>
  metis_tac[storage_well_formed_on_backends]
QED

Resume body_assign_immutable_memory_joint[normalize]:
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb` by
    metis_tac[ci_mono_compile_alloc_buffer, cj 1 ci_mono_typed_memory_family,
              cj 1 ci_mono_stmt_helpers, pairTheory.SND] >>
  `ci_mono sa sn` by metis_tac[ci_mono_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  drule_all_then strip_assume_tac immutable_assign_copy_metadata >>
  `value_has_type itv v` by
    (drule_all type_widens_to_value_has_type >> strip_tac >> gvs[]) >>
  `val_wf itv v` by metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf] >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `stmt_state_rel H0 ctx func ce cx ee s /\ ghost_inv_at (DF H0) lo d ce cx ee G tn s` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
       (qspec_then `H0` mp_tac) >> simp[Abbr `H0`]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `a < dimword (:256) /\ type_memory_size itv < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`cenv` |-> `ce`, `es` |-> `ee`, `dty` |-> `ity`,
                  `dtv` |-> `itv`, `xs` |-> `src`, `sw` |-> `n2w a`, `sb` |-> `sn`]
    (INST_TYPE [``:'a`` |-> ``:256``, ``:'b`` |-> ``:256``] body_assign_immutable_normalize_joint)) >>
  (impl_tac >-
    (`compile_alloc_buffer (type_memory_size itv) sa = (buf,sm)` by metis_tac[] >>
     simp[w2n_n2w, LESS_MOD, IgnAsm `get_tenv cx = _`, IgnAsm `tops = _`] >>
     first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`t`,`root`,`b`,`Gm`,`tm`]
    (map_every assume_tac o CONJUNCTS)) >>
  `sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id` by fs[ci_mono_def] >>
  `local_ptrs_reserved ce sn` by metis_tac[local_ptrs_reserved_next_var] >>
  `return_buf_frame d ce sn t` by
    (irule return_buf_frame_frame >> qexistsl [`ce`,`s`,`sa`] >> simp[] >> metis_tac[]) >>
  `!region x. ce.ce_imm_alloca = SOME region /\ region = Var x ==>
     not_fresh_at sn x` by metis_tac[] >>
  `!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==>
     not_fresh_at sn x` by metis_tac[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee Gm tm t` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _ /\ _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     conj_tac
     >- (first_assum irule >> first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     first_assum irule >> first_assum ACCEPT_TAC) >>
  `eval_operand (Var root) t = SOME (n2w b)` by simp[eval_operand_def] >>
  `b < dimword (:256)` by decide_tac >>
  `val_in_memory itv v b t.vs_memory` by fs[mem_agree_outside_def] >>
  `ptr_val_ok cx ity v (Var root) Gm tm t` by
    (irule rawCallBufferPtrTheory.ptr_val_ok_from_type_covers >>
     fs[w2n_n2w, LESS_MOD] >> metis_tac[]) >>
  `val_footprint itv v <= type_memory_size itv` by metis_tac[val_footprint_le] >>
  qabbrev_tac `k = type_memory_size itv` >>
  qabbrev_tac `n = if k <= 32 then 1 else (k+31) DIV 32` >>
  `32*n = k` by
    (`k = 32 * type_slot_size itv` by simp[Abbr `k`,type_memory_size_slots] >>
     Cases_on `k <= 32`
     >- simp[Abbr `n`] >>
     `((32 * type_slot_size itv + 31) DIV 32) = type_slot_size itv` by
       (once_rewrite_tac[MULT_COMM] >> simp[DIV_MULT]) >>
     simp[Abbr `n`]) >>
  `k <= 32*n /\ 32*n <= type_memory_size itv /\
   b+k < dimword (:256) /\ off+32*n < dimword (:256) /\
   off+32*n <= b /\ b+32*n <= t.vs_alloca_next /\ off+32*n <= lo` by
    (qpat_x_assum `off = compute_immutables_len _ _` kall_tac >>
     fs[Abbr `k`] >> decide_tac) >>
  `!x. Var root = Var x ==> not_fresh_at sn x` by simp[] >>
  `n = (if k <= 32 then 1 else (k+31) DIV 32)` by simp[Abbr `n`] >>
  `k = (if is_bytestring_type ity then type_memory_bytes ce ity else type_memory_bytes ce ity)` by simp[] >>
  `compile_assign_value ce (Lit (n2w off)) LocCode (Var root) F loc ity ity
     (type_memory_bytes ce ity) sn = ((),sb)` by metis_tac[] >>
  mp_tac (Q.INST [`op` |-> `Var root`, `su` |-> `sn`, `s` |-> `t`,
      `G` |-> `Gm`, `tn` |-> `tm`, `sty` |-> `ity`, `stv` |-> `itv`,
      `a` |-> `b`, `bytes` |-> `type_memory_bytes ce ity`, `copy_size` |-> `k`]
    (INST_TYPE [``:'a`` |-> ``:256``] body_assign_immutable_direct_joint)) >>
  (impl_tac >-
    (rpt (first_assum ACCEPT_TAC ORELSE conj_tac ORELSE REFL_TAC) >>
     (disj2_tac >> first_assum ACCEPT_TAC))) >>
  disch_then (qx_choosel_then [`q`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS)) >>
  `!nm base len. local_region ce ee.scopes t nm base len <=>
                 local_region ce ee.scopes s nm base len` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     rpt gen_tac >> strip_tac >>
     rename1 `FLOOKUP ce.ce_vars nm' = SOME (PtrVar (Var p) cap)` >>
     `not_fresh_at sa p` by
       (qpat_assum `local_ptrs_reserved ce sa`
          (qspecl_then [`nm'`,`nm'`,`p`,`cap`,`cap`] mp_tac o
           CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[local_ptrs_reserved_def]) >>
        simp[]) >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sn x /\ _`
       (drule_then (assume_tac o CONJUNCT1 o CONJUNCT2)) >> simp[]) >>
  `ghost_kept_at lo ce ee sa G tn s Gf tf` by
    (irule wordArgsPtrTheory.ghost_kept_at_trans >>
     qexistsl [`Gm`,`ee`,`t`,`sn`,`tm`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `alloca_frame ce ee sa s ce fin q` by
    (irule stmtSimDefsTheory.alloca_frame_trans >>
     qexistsl [`ce`,`ee`,`t`,`sn`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sn x /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sn x ==> lookup_var x q = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
     FLOOKUP q.vs_allocas aid = SOME ent` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==>
       gas_origin_ptr_path _ (t,Gm,tm) _ (OK q,Gf,tf) /\ _`
       (qspec_then `H0` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o CONJUNCT1 o CONJUNCT2) >>
     rewrite_tac[stmt_post_def] >> strip_tac >>
     qpat_assum `!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> _`
       (drule_then assume_tac) >>
     first_assum irule >> first_assum ACCEPT_TAC) >>
  qexistsl [`q`,`Gf`,`tf`] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >-
    (qx_gen_tac `H` >> strip_tac >>
     `valid_horizon cx st0 H ee.storage_trace` by
       (qpat_assum `fin.storage_trace = ee.storage_trace`
          (once_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==>
       gas_origin_ptr_path _ (t,Gm,tm) _ (OK q,Gf,tf) /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     conj_tac >-
       (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
        qexistsl [`Gm`,`t`,`tm`] >>
        conj_tac >> (first_assum ACCEPT_TAC ORELSE first_assum MATCH_ACCEPT_TAC)) >>
     conj_tac >-
       (qpat_assum `stmt_post H ctx func cx lctx ce ce sn sb ee t (INL ()) fin q`
          mp_tac >>
        rewrite_tac[stmt_post_def] >>
        disch_then (qx_choose_then `cpost` strip_assume_tac) >>
        qpat_x_assum `cpost = ce` SUBST_ALL_TAC >>
        qexists `ce` >> simp[]) >>
     first_assum ACCEPT_TAC) >-
    (qpat_assum `q.vs_alloca_next = t.vs_alloca_next`
       (once_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`aid`,`addr`,`sz`,`i`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `FLOOKUP t.vs_allocas aid = SOME (addr,sz)` by
    (qpat_assum `!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
                               FLOOKUP t.vs_allocas aid = SOME ent` irule >>
     first_assum ACCEPT_TAC) >>
  `aid < sn.cs_next_id` by decide_tac >>
  `i IN tm.t_mem` by
    (qpat_assum `!aid addr sz i. FLOOKUP t.vs_allocas aid = SOME (addr,sz) /\ _ ==> _`
       (qspecl_then [`aid`,`addr`,`sz`,`i`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  qpat_assum `!aid addr sz i. FLOOKUP s.vs_allocas aid = SOME (addr,sz) /\ _ ==> _`
    (qspecl_then [`aid`,`addr`,`sz`,`i`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Finalise body_assign_immutable_memory_joint[local]

Theorem body_assign_other_immutable_nonword_write_full[local]:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    struct_args_unique tops /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              is_word_type ty) /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              ~is_word_type ty /\
              (expr_type e = ty \/ lowered_value_type cenv e = ty \/
               is_bytestring_type ty \/
               has_length_word (expr_type e) /\ is_empty_value_expr e)) /\
    ~(?nsid dty. t = TopLevelNameTarget nsid /\
          supported_scalar_target tops nsid /\
          type_place_target env t = SOME (Type dty) /\ is_word_type dty) /\
    ~(?nsid mut ty slot.
        t = TopLevelNameTarget nsid /\
        supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
        (mut = Storage \/ mut = Transient) /\
        ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
        ~is_bytestring_type ty /\
        0 < type_memory_bytes cenv ty /\ expr_type e = ty /\
        lowered_value_type cenv e = expr_type e) /\
    ~(?id fld sid fty.
        t = AttributeTarget (NameTarget id) fld /\
        FLOOKUP env.var_types id = SOME (StructT sid) /\
        attribute_type env.type_defs (StructT sid) fld = SOME fty /\
        is_word_type fty) /\
    ~(?nsid fld fty.
        t = AttributeTarget (TopLevelNameTarget nsid) fld /\
        supported_storage_field_write tops nsid fld /\
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    immutable_root cx t ==>
    !src id ity off vv op st0 sa sm su sb shadow_sa shadow_su shadow_sb
        s0 G0 tn0 marks v ee z G tn.
      t = TopLevelNameTarget (src,id) /\ src = NONE /\ src = cenv.ce_module /\
      cx.in_deploy /\ cenv.ce_is_ctor /\
      supported_immutable_type tops (src,id) = SOME ity /\
      ~cx_const_name cx (src,id) /\
      assignable_type env.type_defs (expr_type e) /\
      type_widens_to env.type_defs (expr_type e) ity /\
      FLOOKUP env.bare_globals (src,id) = SOME ity /\
      cenv.ce_module_var_type (src,id) = SOME ity /\
      FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
      (!tv. evaluate_type (get_tenv cx) ity = SOME tv ==>
            off + type_memory_size tv < dimword (:256)) /\
      stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e) sa = (cenv,sb) /\
      stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e))
        shadow_sa = (gas_shadow_env T cenv,shadow_sb) /\
      compile_get_target_ptr compile_expr cenv t =
        comp_return (Lit (n2w off), SOME LocCode, SOME (ValPT ity)) /\
      compile_expr cenv (expr_type e) e sa = (vv,sm) /\
      unwrap_value cenv vv sm = (op,su) /\
      lower_value compile_expr cenv (expr_type e) e sa = (op,su) /\
      lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa =
        (op,shadow_su) /\
      compile_assign_value cenv (Lit (n2w off)) LocCode op (is_word_type ity)
        (vv_location vv) ity (lowered_value_type cenv e)
        (type_memory_bytes cenv ity) su = ((),sb) /\
      cs_extends sa sm /\ cs_extends sm su /\ cs_extends su sb /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state su shadow_su /\
      gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa su func /\ fn_has_code su sb func /\
      fn_has_code shadow_sa shadow_su shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\ ret_pc_ok cenv sa s0 /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      ~block_is_terminated sa /\
      gas_admissible (eval_stmt cx (Assign (BaseTarget t) e)) (stmt_res_ok lctx) es /\
      expr_body_pre cenv cx env e es /\
      return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
           stmt_state_rel H ctx func cenv cx es s0 /\
           storage_well_formed_on cx es (FST H) /\
           ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!tail. bind (eval_expr cx e) (read_result cx)
         (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
         (INL v,ee with gas_obs := tail)) /\
      storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
      ~z.vs_halted /\
      (!tail. expr_sim_inv cenv cx env (ee with gas_obs := tail) /\
        eval_target_place cx t (ee with gas_obs := tail) =
          (INL (ImmutablePlace src id []),ee with gas_obs := tail)) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
         expr_post H ctx func cenv cx e es sa su s0 ee v op z /\
         expr_store_bound cx (post_value_type cenv e) v op z /\
         z.vs_current_bb = su.cs_current_bb /\ z.vs_inst_idx = LENGTH su.cs_current_insts /\
         alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
         s0.vs_alloca_next <= z.vs_alloca_next /\
         ghost_inv_at (DF H) lo d cenv cx ee G tn z /\
         ptr_val_ok cx (post_value_type cenv e) v op G tn z /\
         (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G z) /\
         ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) /\
      ~is_word_type ity /\
      (~is_word_type (post_value_type cenv e) ==> !rt w.
        evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
        eval_operand op z = SOME w ==>
        type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) ==>
      gas_outcome_full
        (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
        (write_place cx (ImmutablePlace src id []) v) (ee,z,G,tn)
        (\H res ff Gf tf u. ?ce.
          stmt_lands lctx sb res u /\ ~u.vs_halted /\
          (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
          cenv_top_ext cenv ce ff.scopes /\
          stmt_state_rel H ctx func ce cx ff u /\
          storage_well_formed_on cx ff (FST H) /\
          return_buf_frame d ce sb u /\ alloca_history func u /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
          s0.vs_alloca_next <= u.vs_alloca_next /\
          ghost_inv_at (DF H) lo d ce cx ff Gf tf u /\
          (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                 lookup_var x u = SOME w) /\
          (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                   FLOOKUP u.vs_allocas aid = SOME b) /\
          (!x. not_fresh_at sa x ==>
               FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
          alloca_frame cenv es sa s0 ce ff u /\
          (!aid off sz i.
             FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
             (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                        off + sz <= b \/ b + sz' <= off) /\
             off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tn0.t_mem))
        (\H res ff gt r.
           (!tail. stmt_exit_ptr (RetQ H) (ff with gas_obs := tail) res gt r) /\
           halt_exit H cx ff res r /\
           (ctx_has_dalloca ctx ==>
            !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by
    fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (qspec_then `H0` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `expr_sim_inv cenv cx env ee` by
    (qpat_assum `!tail. expr_sim_inv _ _ _ _ /\ _`
       (qspec_then `[]` (mp_tac o CONJUNCT1)) >>
     qpat_assum `ee with gas_obs := [] = ee` (fn th => rewrite_tac[th])) >>
  drule_all_then (qx_choosel_then [`itv`,`stv`,`p`,`w`,`fin`]
      (map_every assume_tac o CONJUNCTS)) body_assign_other_immutable_nonword_entry >>
  `~is_word_type (post_value_type cenv e)` by
    metis_tac[immutableDeployPhysicalSourceTheory.immutable_rhs_post_physical_classify,
              valueCopyBytesTheory.is_bytestring_word_type] >>
  `eval_operand op z = SOME w` by simp[eval_operand_def] >>
  `w2n w + type_memory_size stv <= z.vs_alloca_next` by gvs[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee z /\ storage_well_formed_on cx ee (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn z` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> expr_post H ctx func cenv cx e es sa su s0 ee v op z /\ _`
       (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
     fs[expr_post_def]) >>
  `stmt_state_rel H0 ctx func cenv cx ee z` by simp[] >>
  `z.vs_alloca_next < dimword (:256)` by
    (drule stateRelProjTheory.stmt_state_rel_alloca_room >>
     disch_then (mp_then Any ACCEPT_TAC alloca_room_next_lt)) >>
  `w2n w + type_memory_size stv < dimword (:256)` by decide_tac >>
  `dead_lo_ok H0 (DF H0) lo cenv cx` by simp[] >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `!n b k. local_region cenv ee.scopes z n b k /\ 0 < k ==> lo <= b` by
    (rpt strip_tac >> drule_all (INST_TYPE [``:'a`` |-> ``:256``]
       body_full_local_region_lower_bound) >> simp[]) >>
  `lo <= w2n w` by
    (`(?aid b k. FLOOKUP z.vs_allocas aid = SOME (b,k) /\ b <= w2n w) \/
      (?n b k. local_region cenv ee.scopes z n b k /\ 0 < k /\ b <= w2n w)` suffices_by
     (strip_tac
      >- (`lo <= b` by
            (qpat_assum `allocas_from lo z` (drule_then ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
          decide_tac) >>
      `lo <= b` by
        (qpat_assum `!n b k. local_region cenv ee.scopes z n b k /\ _ ==> _`
           (drule_all_then ACCEPT_TAC)) >> decide_tac) >>
     Cases_on `is_bytestring_type (lowered_value_type cenv e)`
     >- (`is_sized_type (lowered_value_type cenv e)` by
           (qpat_x_assum `is_bytestring_type _` mp_tac >>
            Cases_on `lowered_value_type cenv e` >> simp[is_bytestring_type_def] >>
            Cases_on `b` >> simp[is_bytestring_type_def,is_sized_type_def] >>
            Cases_on `b'` >> simp[is_bytestring_type_def,is_sized_type_def]) >>
         `32 <= val_footprint stv v` by
           (drule_all bodyPtrEnvBuiltinsLenTheory.sized_val_footprint_header >> simp[]) >>
         qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _`
           (qspec_then `stv` mp_tac o REWRITE_RULE[expr_val_at_def]) >> simp[] >>
         disch_then strip_assume_tac
         >- (disj1_tac >> rename1 `FLOOKUP z.vs_allocas aid = SOME (b,k)` >>
             qexistsl [`aid`,`b`,`k`] >> simp[]) >>
         disj2_tac >> rename1 `local_region cenv ee.scopes z n b k` >>
         qexistsl [`n`,`b`,`k`] >> simp[] >> decide_tac) >>
     drule_all immutableDeployAssignRangesTheory.immutable_assign_nonbytes_source_owned >>
     simp[] >> disch_then strip_assume_tac
     >- (disj1_tac >> rename1 `FLOOKUP z.vs_allocas aid = SOME (b,k)` >>
         qexistsl [`aid`,`b`,`k`] >> simp[]) >>
     disj2_tac >> rename1 `local_region cenv ee.scopes z n b k` >>
     qexistsl [`n`,`b`,`k`] >> simp[] >> decide_tac) >>
  `cenv.ce_module = NONE /\ cx_tops cx = tops /\
   ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
   cenv.ce_module_var_type = build_var_type_map tops /\
   ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    (drule_then strip_assume_tac body_inv_main_code >>
     qpat_assum `body_inv tops ctx _ cx` (assume_tac o assign_main_keys) >>
     drule_then (assume_tac o MATCH_MP contract_inv_singleton_source_modules)
       body_inv_contract >>
     drule_then (strip_assume_tac o REWRITE_RULE [cenv_module_pins_def])
       intcall_args_body_inv_pins >> simp[]) >>
  `get_tenv cx = type_env tops` by
    simp[get_tenv_def,type_env_all_modules_def,type_env_def] >>
  `?pre post vis ty slot.
    tops = pre ++ VariableDecl vis Immutable id ty slot :: post /\
    off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre` by
    (drule body_inv_immutable_section_layout >>
     simp[immutable_section_layout_def] >> metis_tac[]) >>
  `ty = ity` by
    (`MEM (VariableDecl vis Immutable id ty slot) tops` by simp[] >>
     drule_all build_maps_variable >> strip_tac >>
     `build_var_type_map tops (NONE,id) = SOME ity` by metis_tac[] >>
     gvs[]) >>
  qpat_x_assum `ty = ity` SUBST_ALL_TAC >>
  `lo = imm_len tops` by fs[dead_lo_ok_def] >>
  `off + type_memory_size itv <= lo` by
    (`type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ity = type_memory_size itv` by
       metis_tac[imm_frame_size] >>
     mp_tac (Q.INST [`off` |-> `0`, `prefix` |-> `pre`, `suffix` |-> `post`,
       `sft` |-> `get_struct_fields (make_struct_fields_map tops)`,
       `ty` |-> `ity`, `vis` |-> `vis`, `name` |-> `id`, `slot` |-> `slot`]
       immutable_declaration_interval_bound) >>
     simp[GSYM imm_len_def]) >>
  `lo < dimword (:256)` by decide_tac >>
  `(!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
       lookup_var x z = SOME w) /\
   (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b)` by
    fs[expr_post_def] >>
  `sa.cs_next_var <= su.cs_next_var /\ sa.cs_next_id <= su.cs_next_id` by
    (qpat_assum `lower_value compile_expr cenv (expr_type e) e sa = (op,su)`
       (fn th => qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac
         ci_mono_lower_value_compile_expr >> rewrite_tac[th]) >> simp[ci_mono_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at su x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `local_ptrs_reserved cenv su` by metis_tac[local_ptrs_reserved_next_var] >>
  `not_fresh_at su p` by
    (drule_all compile_lower_value_var >> simp[]) >>
  `!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at su x` by
    (rpt strip_tac >> first_assum irule >> fs[local_ptrs_reserved_def]) >>
  `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x` by
    metis_tac[] >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x` by
    (qpat_assum `ret_pc_ok cenv sa s0` (strip_assume_tac o REWRITE_RULE[ret_pc_ok_def]) >>
     metis_tac[]) >>
  `return_buf_frame d cenv su z` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`,`s0`,`sa`] >> simp[]) >>
  `~block_is_terminated sb` by
    drule_then ACCEPT_TAC immutableAssignOpenTheory.immutable_assign_loccode_open >>
  `!region. cenv.ce_imm_alloca = SOME region ==>
     eval_operand region z = SOME 0w /\ op_taint tn region = {} /\ op_prov G region = NONE` by
    (gen_tac >> disch_tac >> conj_tac
     >- (qpat_assum `stmt_state_rel H0 ctx func cenv cx ee z`
           (mp_tac o MATCH_MP stmt_state_rel_immutable_base_zero) >>
         simp[loweringStateRelDefsTheory.immutable_base_zero_def]) >>
     `lo <> 0` by decide_tac >>
     Cases_on `region` >> simp[op_taint_def,op_prov_def] >>
     qpat_assum `ghost_inv_at (DF H0) lo d cenv cx ee G tn z`
       (mp_tac o cj 6 o REWRITE_RULE[ghost_inv_at_def]) >>
     simp[op_taint_def] >> metis_tac[]) >>
  `compile_assign_value cenv (Lit (n2w off)) LocCode (Var p) F (vv_location vv)
     ity (lowered_value_type cenv e) (type_memory_bytes cenv ity) su = ((),sb)` by
    (qpat_assum `op = Var p` (SUBST1_TAC o SYM) >>
     qpat_assum `~is_word_type ity`
       (fn th => qpat_assum `compile_assign_value _ _ LocCode op (is_word_type ity) _ _ _ _ _ = _`
          (ACCEPT_TAC o REWRITE_RULE[th]))) >>
  qpat_assum `compile_assign_value _ _ LocCode (Var p) F _ _ _ _ _ = _`
    (mp_then (Pos hd) (qspecl_then
      [`vis`,`v`,`tops`,`tn`,`stv`,`sa`,`st0`,`slot`,`z`,`pre`,`post`,`lo`,`lctx`,
       `itv`,`id`,`func`,`fin`,`gas_explicit_sites ctx shadow_ctx`,`env`,`ee`,`d`,`cx`,
       `ctx`,`w2n w`,`PG`,`G`,`DF`] mp_tac) body_assign_immutable_memory_joint) >>
  (impl_tac >-
    (qpat_assum `src = cenv.ce_module` (SUBST1_TAC o SYM) >>
     qpat_assum `op = Var p` (SUBST1_TAC o SYM) >>
     rewrite_tac[wordsTheory.n2w_w2n] >> rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       sym_tac >> first_assum ACCEPT_TAC,
       disch_tac >> first_assum ACCEPT_TAC])) >>
  disch_then (qx_choosel_then [`q`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!tail. bind (eval_expr _ _) _ _ = _`
    (qspec_then `[]` assume_tac) >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       simp[storage_trace_frame_bind_all,cj 5 evaluate_storage_trace_frame,
            storage_trace_frame_read_result] >>
     drule valid_horizon_frame >> disch_then drule >> simp[]) >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
       (qspec_then `H0` (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (drule eval_read_preserves_scopes_dom >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv ee z` by
    drule_all_then ACCEPT_TAC expr_post_alloca_frame >>
  `alloca_frame cenv es sa s0 cenv fin q` by
    (irule alloca_frame_trans >> qexistsl [`cenv`,`ee`,`z`,`su`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `local_ptrs_rel func cenv es.scopes s0` by
    drule_then (ACCEPT_TAC o CONJUNCT1) stmt_state_rel_local_ptrs_alloca >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (sym_tac >> first_assum ACCEPT_TAC) >>
  `!n b k. local_region cenv ee.scopes z n b k <=> local_region cenv es.scopes s0 n b k` by
    drule_all_then ACCEPT_TAC bodyPtrHashBuiltinsGhostComposeTheory.hash_expr_post_local_regions >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf` by
    (irule wordArgsPtrTheory.ghost_kept_at_trans >>
     qexistsl [`G`,`ee`,`z`,`su`,`tn`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[ghost_kept_at_def]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x q = SOME w` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at su x ==> lookup_var x q = _ /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP q.vs_allocas aid = SOME b` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _`
       (drule_then assume_tac) >>
     qpat_assum `!aid b. FLOOKUP z.vs_allocas aid = SOME b ==> _`
       (drule_then ACCEPT_TAC)) >>
  `s0.vs_alloca_next <= q.vs_alloca_next` by decide_tac >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  irule gas_outcome_full_intro >>
  qexistsl [`Gf`,`fin`,`[]`,`OK q`,`INL ()`,`tf`] >>
  simp[gas_explicit_def,exit_result_def,IgnAsm `lo = _`] >>
  qx_gen_tac `H` >> disch_tac >>
  `valid_horizon cx st0 H fin.storage_trace` by simp[] >>
  qpat_assum `!h. valid_horizon _ _ h fin.storage_trace ==>
      gas_origin_ptr_path _ _ [] (OK q,Gf,tf) /\ _`
    (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `stmt_post H _ _ _ _ _ _ _ _ _ _ _ fin q`
    (mp_tac o REWRITE_RULE[stmt_post_def]) >>
  simp[SF CONJ_ss,IgnAsm `lo = _`] >> disch_tac >> first_assum ACCEPT_TAC
QED

(* In this snapshot arm the saved buffer already has the destination's
   layout. Replay identifies the observed write, not just its slot address. *)
Theorem body_assign_other_snapshot_equal_slots_write_full[local]:
  body_inv tops ctx cenv cx /\
  type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
  type_place_target env t = SOME (Type ty) /\
  target_pre cenv cx env t mid /\
  ty = lowered_value_type cenv e /\ ~is_word_type (lowered_value_type cenv e) /\
  (case FST (SND r) of
     SOME loc => compile_assign_value cenv (FST r) loc op
       (is_word_type (case SND (SND r) of SOME (ValPT tau) => tau
          | _ => lowered_value_type cenv e))
       (vv_location snap) (case SND (SND r) of SOME (ValPT tau) => tau
          | _ => lowered_value_type cenv e) (lowered_value_type cenv e)

       (type_memory_bytes cenv (case SND (SND r) of SOME (ValPT tau) => tau
          | _ => lowered_value_type cenv e)) su = ((),sb)
   | NONE => emit_void INVALID [] su = ((),sb)) /\
  st = su /\ ci_mono sa su /\ fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!tail. eval_target_place cx t
     (mid with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail) =
     (INL (StoragePlace tr k dtv),ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    target_post H ctx func cenv cx mid ss st u ee (PlaceR (StoragePlace tr k dtv)) (Type ty) r z /\
    ghost_inv_at (DF H) lo d cenv cx ee Gz tnz z) /\
  target_ptr_ok cenv (PlaceR (StoragePlace tr k dtv)) r Gz tnz z /\
  ee.gas_obs = [] /\ ~z.vs_halted /\ z.vs_current_bb = su.cs_current_bb /\
  z.vs_inst_idx = LENGTH su.cs_current_insts /\
  return_buf_frame d cenv su z /\ alloca_history func z /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
  value_has_type tv v /\
  (!x. op = Var x ==> not_fresh_at su x) /\
  op = Var xd /\ lookup_var xd z = SOME (n2w b) /\
  b + type_memory_size tv < dimword (:256) /\
  b + type_memory_size tv <= z.vs_alloca_next /\
  ptr_covers Gz tnz xd z (type_memory_size tv) /\
  (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==> val_in_memory tv v b mem) /\
  s0.vs_alloca_next <= z.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x z = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP Gz x = FLOOKUP G0 x /\ op_taint tnz (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame cenv es sa s0 cenv ee z /\
  (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
    off <= i /\ i < off + sz /\ i IN tnz.t_mem ==> i IN tn0.t_mem) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (write_place cx (StoragePlace tr k dtv) v) (ee,z,Gz,tnz)
    (\H res ef G tn t. ?ce.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
      cenv_top_ext cenv ce ef.scopes /\ stmt_state_rel H ctx func ce cx ef t /\
      storage_well_formed_on cx ef (FST H) /\ return_buf_frame d ce sb t /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d ce cx ef G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 ce ef t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem))
    (\H res ef gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ef with gas_obs := tail) res gt r) /\
      halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==>
        !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `st = su` SUBST_ALL_TAC >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qabbrev_tac `start = mid with gas_obs := gas_explicit marks u.vs_gas_readings` >>
  `eval_target_place cx t start = (INL (StoragePlace tr k dtv),ee)` by
    (simp[Abbr `start`] >>
     qpat_assum `!tail. eval_target_place _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `ee with gas_obs := [] = ee`
       (fn th => rewrite_tac[APPEND_NIL,th])) >>
  `expr_sim_inv cenv cx env ee` by
    (irule bodySimAugPlaceLoadTheory.aug_place_target_inv >>
     goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
     fs[Abbr `start`, target_pre_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> target_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` (drule_then strip_assume_tac)) >>
  `FST (SND r) = SOME (slot_loc tr) /\ SND (SND r) = SOME (ValPT ty) /\
   evaluate_type (get_tenv cx) ty = SOME dtv /\ eval_operand (FST r) z = SOME k /\
   (!x. FST r = Var x ==> not_fresh_at su x)` by
    (qhdtm_assum `target_post` mp_tac >>
     simp[NoAsms, target_post_def, place_ptr_rel_def, value_type_place_def] >>
     strip_tac >> fs[]) >>
  `tv = dtv` by metis_tac[SOME_11] >>
  qpat_x_assum `tv = dtv` SUBST_ALL_TAC >>
  `compile_store_slots cenv op (FST r) ty tr su = ((),sb)` by
    (qpat_x_assum `case FST (SND r) of SOME loc => _ | NONE => _` mp_tac >>
     simp[] >> Cases_on `tr` >>
     simp[slot_loc_def, compile_assign_value_def, comp_bind_def, comp_return_def]) >>
  suspend "slots_input"
QED

Resume body_assign_other_snapshot_equal_slots_write_full[slots_input]:
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    drule_then (ACCEPT_TAC o MATCH_MP contract_inv_acyclic_struct_metadata) body_inv_contract >>
  qpat_assum `expr_sim_inv cenv cx env ee`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_sim_inv_def]) >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def, env_context_consistent_def] >>
  `0 < type_slot_size dtv` by
    (drule body_assign_empty_target_typing >> simp[] >> strip_tac >>
     `assignable_type (get_tenv cx) ty` by
       (irule vyperTypeArgFitsTheory.type_widens_to_assignable_type >>
        qexists `expr_type e` >> simp[]) >>
     drule_all_then ACCEPT_TAC assignable_type_slot_size_pos) >>
  `sa.cs_next_var <= su.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv su` by drule_all_then ACCEPT_TAC local_ptrs_reserved_next_var >>
  `!x. not_fresh_at sa x ==> not_fresh_at su x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x` by simp[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x` by
    fs[ret_pc_ok_def] >>
  `op_taint tnz op = {} /\ op_taint tnz (FST r) = {}` by fs[ptr_covers_def, target_ptr_ok_def] >>
  `eval_operand op z = SOME (n2w b)` by simp[eval_operand_def] >>
  `b < dimword (:256)` by decide_tac >>
  `w2n (n2w b : 256 word) = b` by simp[w2n_n2w, LESS_MOD] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) z /\
    storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) Gz tnz z /\
    dead_lo_ok H (DF H) lo cenv cx /\ storage_place_observed H (StoragePlace tr k dtv)` by
    (gen_tac >> disch_tac >>
     `storage_place_observed H (StoragePlace tr k dtv)` by
       (irule stmtSimAugAssignPlaceStorageTheory.aug_place_target_observed >>
        goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
        qexists `st0` >> simp[]) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> target_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (mp_tac o REWRITE_RULE [target_post_def])) >>
     simp[SF CONJ_ss]) >>
  irule body_assign_other_direct_slots_write_full >>
  simp[] >> rpt conj_tac >> gvs[]
  >- (qexists `env` >> simp[]) >>
  qexistsl [`FST r`,`lowered_value_type cenv e`,`Var xd`,`su`,`n2w b`] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Finalise body_assign_other_snapshot_equal_slots_write_full[local]

(* The saved operand at z still has the lowered source layout.  Complete
   the emitted normalization before passing the new buffer to the slots. *)
Theorem body_assign_other_saved_normalized_slots_write_full[local]:
  body_inv tops ctx cenv cx /\
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  type_place_target env bt = SOME (Type ty) /\
  target_pre cenv cx env bt mid /\ expr_body_pre cenv cx env e es /\
  ~is_word_type ty /\ ~is_word_type (lowered_value_type cenv e) /\
  ty <> lowered_value_type cenv e /\
  ~(is_bytestring_type ty /\ is_bytestring_type (lowered_value_type cenv e)) /\
  type_memory_size dtv < dimword (:256) /\
  (!tail. eval_expr cx e (es with gas_obs := prefix ++ tail) =
    (INL tv,mid with gas_obs := tail)) /\
  read_result cx tv mid = (INL v,mid) /\
  (!tail. eval_target_place cx bt
      (mid with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL (StoragePlace tr k dtv),ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    target_post H ctx func cenv cx mid sm sb s ee
      (PlaceR (StoragePlace tr k dtv)) (Type ty) r u /\
    expr_post H ctx func cenv cx e ee sa sc u ee v op z /\
    ghost_inv_at (DF H) lo d cenv cx ee Gz tnz z) /\
  eval_operand (FST r) z = eval_operand (FST r) u /\
  target_ptr_ok cenv (PlaceR (StoragePlace tr k dtv)) r Gz tnz z /\
  ptr_val_ok cx (post_value_type cenv e) v op Gz tnz z /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op Gz z) /\
  (~is_word_type (post_value_type cenv e) ==>
    !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
           eval_operand op z = SOME w ==>
           type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  compile_get_target_ptr compile_expr cenv bt sm = (r,sb) /\
  unwrap_value cenv vv sb = (op,sc) /\
  (case FST (SND r) of
     SOME loc => compile_assign_value cenv (FST r) loc op
       (is_word_type (case SND (SND r) of SOME (ValPT tau) => tau
          | _ => lowered_value_type cenv e))
       (vv_location vv)
       (case SND (SND r) of SOME (ValPT tau) => tau
          | _ => lowered_value_type cenv e) (lowered_value_type cenv e)

       (type_memory_bytes cenv (case SND (SND r) of SOME (ValPT tau) => tau
          | _ => lowered_value_type cenv e)) sc = ((),sf)
   | NONE => emit_void INVALID [] sc = ((),sf)) /\
  fn_has_code sc sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
  z.vs_inst_idx = LENGTH sc.cs_current_insts /\
  alloca_history func z /\ return_buf_frame d cenv sc z /\
  s0.vs_alloca_next <= z.vs_alloca_next /\
  wb_frame cenv es ee sa s0 z /\ ghost_kept_at lo cenv es sa Gi ti s0 Gz tnz /\
  alloca_frame cenv es sa s0 cenv ee z /\
  (!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa.cs_next_id /\
     (!name b cap. local_region cenv es.scopes s0 name b cap ==>
       a+n <= b \/ b+cap <= a) /\ a <= i /\ i < a+n /\ i IN tnz.t_mem ==>
     i IN ti.t_mem) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (write_place cx (StoragePlace tr k dtv) v) (ee,z,Gz,tnz)
    (\H res ef G tn t. ?ce.
      stmt_lands lctx sf res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sf /\ ce = cenv) /\
      cenv_top_ext cenv ce ef.scopes /\ stmt_state_rel H ctx func ce cx ef t /\
      storage_well_formed_on cx ef (FST H) /\ return_buf_frame d ce sf t /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d ce cx ef G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP G x = FLOOKUP Gi x /\ op_taint tn (Var x) = op_taint ti (Var x)) /\
      alloca_frame cenv es sa s0 ce ef t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN ti.t_mem))
    (\H res ef gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ef with gas_obs := tail) res gt r) /\
      halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==>
        !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> target_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `FST (SND r) = SOME (slot_loc tr) /\ SND (SND r) = SOME (ValPT ty) /\
   evaluate_type (get_tenv cx) ty = SOME dtv /\ eval_operand (FST r) u = SOME k /\
   (!x. FST r = Var x ==> not_fresh_at sb x)` by
    (qhdtm_assum `target_post` mp_tac >>
     simp[NoAsms,target_post_def,place_ptr_rel_def,value_type_place_def] >>
     strip_tac >> fs[]) >>
  `eval_operand (FST r) z = SOME k` by simp[] >>
  `compile_assign_value cenv (FST r) (slot_loc tr) op (is_word_type ty)
      (vv_location vv) ty (lowered_value_type cenv e) (type_memory_bytes cenv ty) sc = ((),sf)` by
    (qpat_x_assum `case FST (SND r) of SOME loc => _ | NONE => _` mp_tac >> simp[]) >>
  drule placeStoreSlotsTheory.place_store_storage_compile >>
  asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`src'`,`sn`] (CONJUNCTS_THEN2
    (qx_choosel_then [`buf`,`sl`] (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac assume_tac))) assume_tac)) >>
  qpat_x_assum `src' = buf.buf_operand` SUBST_ALL_TAC >>
  suspend "source"
QED

Resume body_assign_other_saved_normalized_slots_write_full[source]:
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) =
     (INL v,mid with gas_obs := [])` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL])) >>
     simp[bind_def,exprSimSubscriptArrayComposeTheory.read_result_success_gas_iff]) >>
  `expr_body_pre cenv cx env e (es with gas_obs := prefix)` by simp[] >>
  drule_all_then (qx_choose_then `stv` (map_every assume_tac o CONJUNCTS))
    (SIMP_RULE (srw_ss() ++ ETA_ss) [] immutableDeployPhysicalSourceTheory.immutable_rhs_physical_typed) >>
  drule_then strip_assume_tac body_assign_empty_target_typing >>
  `type_widens_to env.type_defs (expr_type e) ty` by metis_tac[SOME_11,value_type_11] >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty` by
    (irule immutableDeployPhysicalSourceTheory.immutable_rhs_physical_widens >>
     qexistsl [`env`,`es`] >> simp[]) >>
  `~is_bytestring_type (lowered_value_type cenv e)` by
    metis_tac[typedMemoryCopyTheory.type_widens_from_bytestring] >>
  `post_value_type cenv e = lowered_value_type cenv e` by
    metis_tac[immutableDeployPhysicalSourceTheory.immutable_rhs_post_physical_classify] >>
  `0 < type_memory_size stv` by
    (irule immutableAssignRepresentationTheory.immutable_assign_rhs_memory_positive >>
     qexistsl [`cenv`,`cx`,`e`,`env`,`es`] >> simp[]) >>
  `expr_val_at cenv cx (lowered_value_type cenv e) sa sc ee v op z /\
   stmt_state_rel H0 ctx func cenv cx ee z /\ ?w. eval_operand op z = SOME w` by
    (qhdtm_assum `expr_post`
       (strip_assume_tac o REWRITE_RULE [expr_post_def,expr_val_rel_def]) >>
     fs[] >> metis_tac[]) >>
  `op_taint tnz op = {} /\
   (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==>
          val_in_memory stv v (w2n w) mem)` by
    (qhdtm_assum `ptr_val_ok` (strip_assume_tac o REWRITE_RULE [ptr_val_ok_def]) >>
     `ptr_mem_ok cx (lowered_value_type cenv e) v op Gz tnz z` by metis_tac[] >>
     qpat_x_assum `ptr_mem_ok cx (lowered_value_type cenv e) _ _ _ _ _`
       (qspecl_then [`stv`,`w`] mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >> simp[]) >>
  `?xs. op = Var xs /\ ptr_covers Gz tnz xs z (type_memory_size stv)` by
    (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
     simp[] >> qexistsl [`cenv`,`e`] >> simp[]) >>
  pop_assum strip_assume_tac >>
  `lookup_var xs z = SOME w` by fs[eval_operand_def] >>
  `w2n w + type_memory_size stv <= z.vs_alloca_next` by
    (`~is_word_type (post_value_type cenv e)` by simp[] >>
     qpat_assum `~is_word_type (post_value_type cenv e) ==> !rt w.
       evaluate_type _ _ = SOME rt /\ eval_operand _ _ = SOME w ==> _`
       (drule_then (qspecl_then [`stv`,`w`] mp_tac)) >> simp[] >> (gvs[])) >>
  `w2n w + type_memory_size stv < dimword (:256)` by
    (drule stmt_state_rel_alloca_room >> simp[alloca_room_def] >> decide_tac) >>
  suspend "normalize"
QED

Resume body_assign_other_saved_normalized_slots_write_full[normalize]:
  `ci_mono sa sm` by metis_tac[compile_expr_ci_mono,SND] >>
  `ci_mono sm sb` by metis_tac[ci_mono_compile_get_target_ptr,SND] >>
  `ci_mono sb sc` by metis_tac[ci_mono_unwrap_value,SND] >>
  `ci_mono sc sl` by metis_tac[ci_mono_compile_alloc_buffer,SND] >>
  `ci_mono sl sn` by metis_tac[cj 1 ci_mono_typed_memory_family,SND] >>
  `ci_mono sn sf` by metis_tac[cj 1 ci_mono_compile_store_slots,SND] >>
  `ci_mono sa sc /\ ci_mono sc sn /\ ci_mono sa sn` by metis_tac[ci_mono_trans] >>
  `fn_has_code sc sl func /\ fn_has_code sl sn func /\ fn_has_code sn sf func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split,cs_extends_trans]) >>
  `local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sn` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x /\ not_fresh_at sn x` by
    (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sc x /\ not_fresh_at sn x` by simp[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sc x /\ not_fresh_at sn x` by fs[ret_pc_ok_def] >>
  `not_fresh_at sc xs` by
    (`!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
       (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`,`vv`,`sm`] mp_tac
          (cj 1 compiler_compile_var) >> simp[]) >>
     `!x. vv_operand vv = Var x ==> not_fresh_at sb x` by
       (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
     drule compiler_unwrap_value_var >>
     Cases_on `vv` >> gvs[vv_operand_def]) >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    drule_then (ACCEPT_TAC o MATCH_MP contract_inv_acyclic_struct_metadata) body_inv_contract >>
  `expr_sim_inv cenv cx env es` by
    drule_then (ACCEPT_TAC o cj 1) expr_body_pre_static_facts >>
  qpat_assum `expr_sim_inv cenv cx env es`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_sim_inv_def]) >>
  `value_has_type dtv v` by
    (drule_all type_widens_to_value_has_type >> strip_tac >> gvs[]) >>
  `val_wf dtv v` by metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf] >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `type_memory_bytes cenv ty = type_memory_size dtv` by
    (irule typedMemoryCopyTheory.typed_copy_memory_size >>
     qexists `get_tenv cx` >> simp[] >> metis_tac[]) >>
  `compile_alloc_buffer (type_memory_size dtv) sc = (buf,sl)` by
    (qpat_assum `type_memory_bytes cenv ty = _` (fn th => rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
  qpat_assum `compile_alloc_buffer (type_memory_size dtv) sc = (buf,sl)`
    (mp_then Any mp_tac
      (INST_TYPE [``:'a`` |-> ``:256``, ``:'b`` |-> ``:256``]
        body_assign_immutable_normalize_joint)) >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (qspecl_then [`w : 256 word`,`lo`,`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >>
  (impl_tac >- (simp[SF CONJ_ss,FORALL_AND_THM] >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`q`,`root`,`b`,`Gq`,`tq`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "slots"
QED

Resume body_assign_other_saved_normalized_slots_write_full[slots]:
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qabbrev_tac `start = mid with gas_obs := gas_explicit marks s.vs_gas_readings` >>
  `eval_target_place cx bt start = (INL (StoragePlace tr k dtv),ee)` by
    (simp[Abbr `start`] >>
     qpat_assum `!tail. eval_target_place _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `ee with gas_obs := [] = ee`
       (fn th => rewrite_tac[APPEND_NIL,th])) >>
  `expr_sim_inv cenv cx env ee` by
    (irule bodySimAugPlaceLoadTheory.aug_place_target_inv >>
     goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
     fs[Abbr `start`, target_pre_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee q /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee Gq tq q /\
    dead_lo_ok H (DF H) lo cenv cx /\ storage_place_observed H (StoragePlace tr k dtv)` by
    (gen_tac >> disch_tac >>
     `storage_place_observed H (StoragePlace tr k dtv)` by
       (irule stmtSimAugAssignPlaceStorageTheory.aug_place_target_observed >>
        goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
        qexists `st0` >> simp[]) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> target_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
     qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ z`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_post_def]) >>
     simp[SF CONJ_ss]) >>
  `0 < type_slot_size dtv` by
    (`env.type_defs = get_tenv cx` by fs[env_consistent_def,env_context_consistent_def] >>
     `assignable_type (get_tenv cx) ty` by
       (irule vyperTypeArgFitsTheory.type_widens_to_assignable_type >>
        qexists `expr_type e` >> fs[]) >>
     drule_all_then ACCEPT_TAC assignable_type_slot_size_pos) >>
  `eval_operand (Var root) q = SOME (n2w b)` by simp[eval_operand_def] >>
  `w2n (n2w b : 256 word) = b` by
    (`b < dimword (:256)` by decide_tac >> simp[w2n_n2w,LESS_MOD]) >>
  `op_taint tq (Var root) = {}` by fs[ptr_covers_def] >>
  `!x. FST r = Var x ==> not_fresh_at sc x` by
    (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  `!l. FST r <> Label l` by
    drule_all_then ACCEPT_TAC targetSubscriptSplitTheory.target_subscript_typed_base_not_label >>
  `eval_operand (FST r) q = SOME k` by
    (irule exprBopSimPropsTheory.eval_operand_frame >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`sc`,`z`] >> simp[] >> metis_tac[]) >>
  `op_taint tq (FST r) = {}` by
    (`op_taint tnz (FST r) = {}` by fs[target_ptr_ok_def] >>
     Cases_on `FST r` >> gvs[op_taint_def] >> metis_tac[]) >>
  suspend "frame"
QED

Resume body_assign_other_saved_normalized_slots_write_full[frame]:
  `sc.cs_next_var <= sn.cs_next_var /\ sa.cs_next_var <= sn.cs_next_var /\
   sa.cs_next_id <= sc.cs_next_id` by fs[ci_mono_def] >>
  `return_buf_frame d cenv sn q` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`,`z`,`sc`] >> simp[SF CONJ_ss]) >>
  qpat_assum `wb_frame cenv es ee sa s0 z`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [wb_frame_def]) >>
  `alloca_frame cenv es sa s0 cenv ee q` by
    (irule alloca_frame_trans >> qexistsl [`cenv`,`ee`,`z`,`sc`] >> simp[]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x q = SOME w` by
    simp[SF CONJ_ss] >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP q.vs_allocas aid = SOME b` by
    simp[SF CONJ_ss] >>
  `!x. not_fresh_at sa x ==>
    FLOOKUP Gq x = FLOOKUP Gi x /\ op_taint tq (Var x) = op_taint ti (Var x)` by
    (qpat_assum `ghost_kept_at lo cenv es sa Gi ti s0 Gz tnz`
       (assume_tac o cj 1 o REWRITE_RULE [ghost_kept_at_def]) >> simp[SF CONJ_ss]) >>
  `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n a cap. local_region cenv es.scopes s0 n a cap ==> off+sz <= a \/ a+cap <= off) /\
    off <= i /\ i < off+sz /\ i IN tq.t_mem ==> i IN ti.t_mem` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `alloca_frame cenv es sa s0 cenv ee z`
       (drule_all_then strip_assume_tac o REWRITE_RULE [alloca_frame_def]) >>
     `FLOOKUP z.vs_allocas aid = SOME (off,sz) /\ aid < sc.cs_next_id` by simp[] >>
     `i IN tnz.t_mem` by
       (qpat_assum `!aid off sz i. FLOOKUP z.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
          (drule_all_then ACCEPT_TAC)) >>
     qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN ti.t_mem`
       (drule_all_then ACCEPT_TAC)) >>
  suspend "compose"
QED

Resume body_assign_other_saved_normalized_slots_write_full[compose]:
  irule gasOutcomeFullGuardedTheory.gas_outcome_full_zero_prefix_guarded >>
  simp[storage_trace_frame_write_place] >>
  qexistsl [`Gq`,`q`,`tq`] >>
  conj_tac >- simp[] >>
  irule body_assign_other_direct_slots_write_full >>
  simp[] >> rpt conj_tac >> gvs[]
  >- (qexists `env` >> simp[]) >>
  qexistsl [`FST r`,`dty`,`Var root`,`sn`,`n2w b`] >>
  simp[SF CONJ_ss,DISJ_IMP_THM,FORALL_AND_THM]
QED

Finalise body_assign_other_saved_normalized_slots_write_full[local]

Theorem body_assign_other_snapshot_normalized_slots_write_full[local]:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\
  type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
  type_place_target env t = SOME (Type ty) /\
  target_pre cenv cx env t mid /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  ~is_word_type ty /\ ty <> lowered_value_type cenv e /\
  ~(is_bytestring_type ty /\ is_bytestring_type (lowered_value_type cenv e)) /\
  compile_get_target_ptr compile_expr cenv t ss = (r,st) /\
  (case FST (SND r) of
     SOME loc => compile_assign_value cenv (FST r) loc (Var xd)
       (is_word_type (case SND (SND r) of SOME (ValPT tau) => tau
          | _ => lowered_value_type cenv e))
       (vv_location snap) (case SND (SND r) of SOME (ValPT tau) => tau
          | _ => lowered_value_type cenv e) (lowered_value_type cenv e)

       (type_memory_bytes cenv (case SND (SND r) of SOME (ValPT tau) => tau
          | _ => lowered_value_type cenv e)) su = ((),sb)
   | NONE => emit_void INVALID [] su = ((),sb)) /\
  st = su /\ ci_mono sa su /\ fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!tail. eval_target_place cx t
     (mid with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail) =
     (INL (StoragePlace tr k dtv),ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    target_post H ctx func cenv cx mid ss st u ee (PlaceR (StoragePlace tr k dtv)) (Type ty) r z /\
    ghost_inv_at (DF H) lo d cenv cx ee Gz tnz z) /\
  target_ptr_ok cenv (PlaceR (StoragePlace tr k dtv)) r Gz tnz z /\
  ee.gas_obs = [] /\ ~z.vs_halted /\ z.vs_current_bb = su.cs_current_bb /\
  z.vs_inst_idx = LENGTH su.cs_current_insts /\
  return_buf_frame d cenv su z /\ alloca_history func z /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  ~is_word_type (lowered_value_type cenv e) /\ not_fresh_at su xd /\
  lookup_var xd z = SOME (n2w b) /\
  FLOOKUP z.vs_allocas aid = SOME (b,type_memory_size tv) /\ aid < su.cs_next_id /\
  b + type_memory_size tv < dimword (:256) /\
  b + type_memory_size tv <= z.vs_alloca_next /\
  (!n off len. local_region cenv ee.scopes z n off len ==>
    loweringStateRelDefs$regions_disjoint b (type_memory_size tv) off len) /\
  ptr_covers Gz tnz xd z (type_memory_size tv) /\
  (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==> val_in_memory tv v b mem) /\
  s0.vs_alloca_next <= z.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x z = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP Gz x = FLOOKUP G0 x /\ op_taint tnz (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame cenv es sa s0 cenv ee z /\
  (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
    off <= i /\ i < off + sz /\ i IN tnz.t_mem ==> i IN tn0.t_mem) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (write_place cx (StoragePlace tr k dtv) v) (ee,z,Gz,tnz)
    (\H res ef G tn t. ?ce.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
      cenv_top_ext cenv ce ef.scopes /\ stmt_state_rel H ctx func ce cx ef t /\
      storage_well_formed_on cx ef (FST H) /\ return_buf_frame d ce sb t /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d ce cx ef G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 ce ef t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem))
    (\H res ef gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ef with gas_obs := tail) res gt r) /\
      halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==>
        !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `st = su` SUBST_ALL_TAC >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qabbrev_tac `start = mid with gas_obs := gas_explicit marks u.vs_gas_readings` >>
  `eval_target_place cx t start = (INL (StoragePlace tr k dtv),ee)` by
    (simp[Abbr `start`] >>
     qpat_assum `!tail. eval_target_place _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `ee with gas_obs := [] = ee`
       (fn th => rewrite_tac[APPEND_NIL,th])) >>
  `expr_sim_inv cenv cx env ee` by
    (irule bodySimAugPlaceLoadTheory.aug_place_target_inv >>
     goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
     fs[Abbr `start`, target_pre_def]) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> target_post H ctx func cenv cx mid ss su u ee _ _ r z /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `FST (SND r) = SOME (slot_loc tr) /\ SND (SND r) = SOME (ValPT ty) /\
   evaluate_type (get_tenv cx) ty = SOME dtv /\ eval_operand (FST r) z = SOME k /\
   (!x. FST r = Var x ==> not_fresh_at su x)` by
    (qhdtm_assum `target_post` mp_tac >>
     simp[NoAsms, target_post_def, place_ptr_rel_def, value_type_place_def] >>
     strip_tac >> fs[]) >>
  `assign_alloc_ok cenv t e` by
    fs[stmt_exprs_ok_def, Once allocLimitsTheory.alloc_limits_stmt_def] >>
  `type_memory_bytes cenv ty = type_memory_size dtv` by
    drule_all_then ACCEPT_TAC expr_sim_inv_memory_size >>
  `compile_get_target_ptr compile_expr cenv t ss =
     ((FST r,SOME (slot_loc tr),SOME (ValPT ty)),su)` by
    (qpat_assum `compile_get_target_ptr _ _ _ _ = _` (fn th => rewrite_tac[th]) >>
     PairCases_on `r` >> gvs[]) >>
  `type_memory_bytes cenv ty < 2 ** 64` by
    (drule placeDestinationBoundsTheory.storage_target_normalization_bound >>
     disch_then (qspec_then `e` mp_tac) >>
     Cases_on `tr` >> simp[slot_loc_def] >> metis_tac[]) >>
  `type_memory_size dtv < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  suspend "normalize"
QED

Resume body_assign_other_snapshot_normalized_slots_write_full[normalize]:
  markerLib.RESUME_TAC >>
  qabbrev_tac `sty = lowered_value_type cenv e` >>
  `compile_assign_value cenv (FST r) (slot_loc tr) (Var xd) (is_word_type ty)
     (vv_location snap) ty sty (type_memory_bytes cenv ty) su = ((),sb)` by
    (qpat_x_assum `case FST (SND r) of SOME loc => _ | NONE => _` mp_tac >> simp[]) >>
  `type_widens_to env.type_defs (expr_type e) ty` by
    (drule body_assign_empty_target_typing >> simp[]) >>
  `type_widens_to (get_tenv cx) sty ty` by
    (simp[Abbr `sty`] >> drule_all_then ACCEPT_TAC immutable_rhs_physical_widens) >>
  `~is_bytestring_type sty` by metis_tac[type_widens_from_bytestring] >>
  drule placeStoreSlotsTheory.place_store_storage_compile >>
  simp[] >> disch_then strip_assume_tac >>
  rename1 `compile_alloc_buffer _ su = (buf,sn)` >>
  rename1 `compile_store_memory_typed cenv buf.buf_operand ty (Var xd) sty sn = ((),sc)` >>
  `ci_mono su sn /\ ci_mono sn sc /\ ci_mono sc sb` by
    metis_tac[ci_mono_compile_alloc_buffer, cj 1 ci_mono_typed_memory_family,
              cj 1 ci_mono_compile_store_slots, pairTheory.SND] >>
  `fn_has_code su sn func /\ fn_has_code sn sc func /\ fn_has_code sc sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split,cs_extends_trans]) >>
  `value_has_type dtv v` by
    (drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> simp[]) >>
  `val_wf dtv v` by simp[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    drule_then (ACCEPT_TAC o MATCH_MP contract_inv_acyclic_struct_metadata) body_inv_contract >>
  qpat_assum `expr_sim_inv cenv cx env ee`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_sim_inv_def]) >>
  `sa.cs_next_var <= su.cs_next_var /\ su.cs_next_var <= sc.cs_next_var /\
   sa.cs_next_id <= su.cs_next_id` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv su` by drule_all_then ACCEPT_TAC local_ptrs_reserved_next_var >>
  `!x. not_fresh_at sa x ==> not_fresh_at su x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x` by simp[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x` by
    fs[ret_pc_ok_def] >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `stmt_state_rel H0 ctx func cenv cx ee z` by fs[target_post_def] >>
  `w2n (n2w b : 256 word) = b` by simp[w2n_n2w, LESS_MOD] >>
  `val_footprint tv v = type_memory_size tv` by
    drule_all_then MATCH_ACCEPT_TAC nonbytes_evaluated_val_footprint >>
  `expr_val_at cenv cx sty (su with cs_next_id := aid) su ee v (Var xd) z` by
    (simp[expr_val_at_def,eval_operand_def] >>
     disj1_tac >> qexistsl [`aid`,`b`,`type_memory_size tv`] >>
     simp[] >> fs[loweringStateRelDefsTheory.regions_disjoint_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  qpat_assum `compile_alloc_buffer (type_memory_size dtv) su = (buf,sn)`
    (mp_then Any mp_tac
      (INST_TYPE [``:'a`` |-> ``:256``, ``:'b`` |-> ``:256``]
        body_assign_immutable_normalize_joint)) >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (qspecl_then [`n2w b : 256 word`,`lo`,`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >>
  (impl_tac >- (simp[SF CONJ_ss] >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`q`,`root`,`a`,`Gq`,`tf`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "slots"
QED

Resume body_assign_other_snapshot_normalized_slots_write_full[slots]:
  markerLib.RESUME_TAC >>
  `!l. FST r <> Label l` by
    drule_all_then ACCEPT_TAC targetSubscriptSplitTheory.target_subscript_typed_base_not_label >>
  `eval_operand (FST r) q = SOME k` by
    (irule exprBopSimPropsTheory.eval_operand_frame >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`su`,`z`] >> simp[] >> metis_tac[]) >>
  `!x. FST r = Var x ==> not_fresh_at sc x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `op_taint tf (FST r) = {}` by
    (`op_taint tnz (FST r) = {}` by fs[target_ptr_ok_def] >>
     Cases_on `FST r` >> gvs[op_taint_def] >> metis_tac[]) >>
  `return_buf_frame d cenv sc q` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`,`z`,`su`] >> simp[] >> metis_tac[]) >>
  suspend "frames"
QED

Resume body_assign_other_snapshot_normalized_slots_write_full[frames]:
  markerLib.RESUME_TAC >>
  `sa.cs_next_var <= sc.cs_next_var /\ s0.vs_alloca_next <= q.vs_alloca_next` by decide_tac >>
  `local_ptrs_reserved cenv sc` by
    (qpat_assum `local_ptrs_reserved cenv su` (mp_then Any mp_tac local_ptrs_reserved_next_var) >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at su x ==> not_fresh_at sc x /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at su x ==> not_fresh_at sc x /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x q = SOME w` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at su x ==> not_fresh_at sc x /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP q.vs_allocas aid = SOME ent` by
    (rpt strip_tac >> qpat_assum `!aid ent. FLOOKUP z.vs_allocas aid = SOME ent ==> _`
       irule >> simp[]) >>
  `!x. not_fresh_at sa x ==>
    FLOOKUP Gq x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at su x ==> not_fresh_at sc x /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv ee q` by
    (irule alloca_frame_trans >> qexistsl [`cenv`,`ee`,`z`,`su`] >> simp[]) >>
  `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b len. local_region cenv es.scopes s0 n b len ==> off + sz <= b \/ b + len <= off) /\
    off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tn0.t_mem` by suspend "old_taint" >>
  suspend "execute_slots"
QED

Resume body_assign_other_snapshot_normalized_slots_write_full[old_taint]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  rename1 `FLOOKUP s0.vs_allocas j = SOME (off,sz)` >>
  `FLOOKUP z.vs_allocas j = SOME (off,sz)` by simp[] >>
  `!n b len. local_region cenv ee.scopes z n b len ==> off + sz <= b \/ b + len <= off` by
    (qpat_assum `alloca_frame cenv es sa s0 cenv ee z`
       (qspecl_then [`j`,`off`,`sz`] mp_tac o REWRITE_RULE [alloca_frame_def]) >>
     simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> first_assum ACCEPT_TAC) >>
  `j < su.cs_next_id` by decide_tac >>
  `i IN tnz.t_mem` by
    (qpat_assum `!aid off sz i. FLOOKUP z.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
       (qspecl_then [`j`,`off`,`sz`,`i`] mp_tac) >>
     simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
    (qspecl_then [`j`,`off`,`sz`,`i`] mp_tac) >> simp[] >>
  impl_tac >- first_assum ACCEPT_TAC >> simp[]
QED

Resume body_assign_other_snapshot_normalized_slots_write_full[execute_slots]:
  markerLib.RESUME_TAC >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def, env_context_consistent_def] >>
  `0 < type_slot_size dtv` by
    (drule body_assign_empty_target_typing >> simp[] >> strip_tac >>
     `assignable_type (get_tenv cx) ty` by
       (irule vyperTypeArgFitsTheory.type_widens_to_assignable_type >> qexists `expr_type e` >> simp[]) >>
     drule_all_then ACCEPT_TAC assignable_type_slot_size_pos) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) q /\
    storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) Gq tf q /\
    dead_lo_ok H (DF H) lo cenv cx /\ storage_place_observed H (StoragePlace tr k dtv)` by
    suspend "horizon" >>
  `op_taint tf (Var root) = {}` by fs[ptr_covers_def] >>
  `eval_operand (Var root) q = SOME (n2w a)` by simp[eval_operand_def] >>
  `w2n (n2w a : 256 word) = a` by simp[w2n_n2w, LESS_MOD] >>
  irule gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix >>
  qexistsl [`Gq`,`q`,`tf`] >>
  conj_tac >- (gen_tac >> qpat_assum `!D. gas_origin_ptr_path _ (z,Gz,tnz) [] _`
      MATCH_ACCEPT_TAC) >>
  irule body_assign_other_direct_slots_write_full >>
  pure_asm_rewrite_tac [] >>
  simp[] >> conj_tac
  >- (qexists `env` >> simp[]) >>
  qexistsl [`FST r`,`ty`,`Var root`,`sc`,`n2w a`] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  qpat_x_assum `src' = buf.buf_operand` SUBST_ALL_TAC >>
  qpat_x_assum `buf.buf_operand = Var root` SUBST_ALL_TAC >>
  first_assum ACCEPT_TAC
QED

Resume body_assign_other_snapshot_normalized_slots_write_full[horizon]:
  markerLib.RESUME_TAC >> gen_tac >> disch_tac >>
  `storage_place_observed H (StoragePlace tr k dtv)` by
    (irule stmtSimAugAssignPlaceStorageTheory.aug_place_target_observed >>
     goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
     qexists `st0` >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> target_post H ctx func cenv cx _ _ _ _ ee _ _ _ z /\ _`
    (qspec_then `H` (drule_then (strip_assume_tac o REWRITE_RULE [target_post_def]))) >>
  `stmt_state_rel H ctx func cenv cx ee q` by
    (first_assum irule >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at (DF H) lo d cenv cx ee Gq tf q` by
    (first_assum irule >> first_assum ACCEPT_TAC) >>
  simp[]
QED

Finalise body_assign_other_snapshot_normalized_slots_write_full[local]

(* The saved RHS is read before the target runs. Its physical buffer and the
   destination operand are both available after the intervening unwrap. *)
Theorem body_assign_other_saved_equal_slots_write_full[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget bt) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (BaseTarget bt) e) ==> occurs_abi_decode_target target tops) /\
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget bt) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget bt) e)) /\
  ~immutable_root cx bt /\ expr_sim_inv cenv cx env mid /\
  expr_body_pre cenv cx env e es /\
  type_place_target env bt = SOME (Type ty) /\
  ty = lowered_value_type cenv e /\ ~is_word_type (lowered_value_type cenv e) /\
  (!tail. eval_expr cx e (es with gas_obs := prefix ++ tail) =
    (INL tv,mid with gas_obs := tail)) /\
  read_result cx tv mid = (INL v,mid) /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  compile_get_target_ptr compile_expr cenv bt sm = (r,sb) /\
  unwrap_value cenv vv sb = (op,sc) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (case FST (SND r) of
     SOME loc => compile_assign_value cenv (FST r) loc op
       (is_word_type (case SND (SND r) of SOME (ValPT t) => t
          | _ => lowered_value_type cenv e))
                   (vv_location vv)
       (case SND (SND r) of SOME (ValPT t) => t
          | _ => lowered_value_type cenv e) (lowered_value_type cenv e)
       (type_memory_bytes cenv (case SND (SND r) of SOME (ValPT t) => t
          | _ => lowered_value_type cenv e))
   | NONE => emit_void INVALID []) sc = ((),sf) /\
  fn_has_code sc sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!tail. eval_target_place cx bt
     (mid with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
     (INL (StoragePlace tr k dtv),ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    target_post H ctx func cenv cx mid sm sb s ee (PlaceR (StoragePlace tr k dtv))
      (Type ty) r u /\
    expr_post H ctx func cenv cx e ee sa sc u ee v op z /\
    ghost_inv_at (DF H) lo d cenv cx ee Gz tnz z) /\
  ptr_val_ok cx (post_value_type cenv e) v op Gz tnz z /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op Gz z) /\
  (~is_word_type (post_value_type cenv e) ==>
    !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
      eval_operand op z = SOME w ==>
      type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
  ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
  z.vs_inst_idx = LENGTH sc.cs_current_insts /\
  alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
  return_buf_frame d cenv sc z /\
  eval_operand (FST r) z = eval_operand (FST r) u /\
  target_ptr_ok cenv (PlaceR (StoragePlace tr k dtv)) r Gz tnz z /\
  wb_frame cenv es ee sa s0 z /\ ghost_kept_at lo cenv es sa Gi ti s0 Gz tnz /\
  alloca_frame cenv es sa s0 cenv ee z ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (write_place cx (StoragePlace tr k dtv) v) (ee,z,Gz,tnz)
    (\H res ef G tn t. ?ce.
      stmt_lands lctx sf res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sf /\ ce = cenv) /\
      cenv_top_ext cenv ce ef.scopes /\ stmt_state_rel H ctx func ce cx ef t /\
      storage_well_formed_on cx ef (FST H) /\ return_buf_frame d ce sf t /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d ce cx ef G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP G x = FLOOKUP Gi x /\ op_taint tn (Var x) = op_taint ti (Var x)) /\
      alloca_frame cenv es sa s0 ce ef t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN ti.t_mem))
    (\H res ef gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ef with gas_obs := tail) res gt r) /\
      halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==>
        !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> target_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` (drule_then strip_assume_tac)) >>
  `FST (SND r) = SOME (slot_loc tr) /\ SND (SND r) = SOME (ValPT ty) /\
   evaluate_type (get_tenv cx) ty = SOME dtv /\ eval_operand (FST r) z = SOME k /\
   (!x. FST r = Var x ==> not_fresh_at sb x)` by
    (qhdtm_assum `target_post` mp_tac >>
     simp[NoAsms, target_post_def, place_ptr_rel_def, value_type_place_def] >>
     strip_tac >> fs[]) >>
  `compile_store_slots cenv op (FST r) ty tr sc = ((),sf)` by
    (qpat_x_assum `(case FST (SND r) of SOME loc => _ | NONE => _) sc = _` mp_tac >>
     simp[] >> Cases_on `tr` >>
     simp[slot_loc_def, compile_assign_value_def, comp_bind_def, comp_return_def]) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qabbrev_tac `start = mid with gas_obs := gas_explicit marks s.vs_gas_readings` >>
  `eval_target_place cx bt start = (INL (StoragePlace tr k dtv),ee)` by
    (simp[Abbr `start`] >>
     qpat_assum `!tail. eval_target_place _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `ee with gas_obs := [] = ee`
       (fn th => rewrite_tac[APPEND_NIL,th])) >>
  `target_pre cenv cx env bt mid` by
    (irule body_assign_saved_target_pre >> metis_tac[]) >>
  `expr_sim_inv cenv cx env ee` by
    (irule bodySimAugPlaceLoadTheory.aug_place_target_inv >>
     goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
     fs[Abbr `start`, target_pre_def]) >>
  `evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME dtv` by metis_tac[] >>
  `value_has_type dtv v /\ type_memory_bytes cenv (lowered_value_type cenv e) =
     type_memory_size dtv` by
    (`eval_expr cx e (es with gas_obs := prefix) = (INL tv,mid with gas_obs := [])` by
       (qpat_assum `!tail. eval_expr cx e (es with gas_obs := prefix ++ tail) = _`
          (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL]))) >>
     `(do pv <- eval_expr cx e; read_result cx pv od) (es with gas_obs := prefix) =
      (INL v,mid with gas_obs := [])` by
       (drule read_result_gas_obs >> simp[bind_def]) >>
     `expr_body_pre cenv cx env e (es with gas_obs := prefix)` by simp[] >>
     drule_all immutable_rhs_physical_typed >> simp[]) >>
  suspend "physical"
QED

Resume body_assign_other_saved_equal_slots_write_full[physical]:
  `~is_word_type (post_value_type cenv e)` by
    metis_tac[immutable_rhs_post_physical_classify,is_bytestring_word_type] >>
  `?sw. eval_operand op z = SOME sw` by
    fs[expr_post_def, expr_val_rel_def] >>
  `!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==>
    val_in_memory dtv v (w2n sw) mem` by
    (drule immutable_rhs_post_physical_classify >> strip_tac
     >- fs[ptr_val_ok_def, ptr_mem_ok_def] >>
     `type_widens_to (get_tenv cx) (lowered_value_type cenv e) (post_value_type cenv e)` by
       metis_tac[immutable_rhs_physical_post_widens] >>
     drule_all type_widens_to_value_has_type >> strip_tac >>
     rpt strip_tac >>
     `val_in_memory tu v (w2n sw) mem` by fs[ptr_val_ok_def, ptr_mem_ok_def] >>
     metis_tac[bytestring_val_in_memory_transfer]) >>
  suspend "slots_input"
QED

Resume body_assign_other_saved_equal_slots_write_full[slots_input]:
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    drule_then (ACCEPT_TAC o MATCH_MP contract_inv_acyclic_struct_metadata) body_inv_contract >>
  qpat_assum `expr_sim_inv cenv cx env ee`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_sim_inv_def]) >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def, env_context_consistent_def] >>
  `0 < type_slot_size dtv` by
    (drule body_assign_empty_target_typing >> simp[] >> strip_tac >>
     `assignable_type (get_tenv cx) ty` by
       (irule vyperTypeArgFitsTheory.type_widens_to_assignable_type >>
        qexists `expr_type e` >> simp[]) >>
     drule_all_then ACCEPT_TAC assignable_type_slot_size_pos) >>
  `0 < type_memory_size dtv` by simp[type_memory_size_pos] >>
  `w2n sw + type_memory_size dtv <= z.vs_alloca_next` by
    (qpat_assum `~is_word_type _ ==> !rt w. _ /\ eval_operand op z = SOME w ==> _`
       (drule_then (qspecl_then [`dtv`,`sw`] mp_tac)) >> gvs[]) >>
  `op_taint tnz op = {} /\ op_taint tnz (FST r) = {}` by
    fs[ptr_val_ok_def, target_ptr_ok_def] >>
  `?xs. op = Var xs /\ ptr_covers Gz tnz xs z (type_memory_size dtv)` by
    (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
     simp[] >> qexistsl [`cenv`,`e`] >> simp[]) >>
  suspend "freshness"
QED

Resume body_assign_other_saved_equal_slots_write_full[freshness]:
  `ci_mono sa sm` by metis_tac[compile_expr_ci_mono,SND] >>
  `ci_mono sm sb` by metis_tac[ci_mono_compile_get_target_ptr,SND] >>
  `ci_mono sb sc` by metis_tac[ci_mono_unwrap_value,SND] >>
  `sa.cs_next_var <= sc.cs_next_var /\ sm.cs_next_var <= sb.cs_next_var /\
   sb.cs_next_var <= sc.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv sc` by drule_all_then ACCEPT_TAC local_ptrs_reserved_next_var >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by simp[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by
    fs[ret_pc_ok_def] >>
  `!x. FST r = Var x ==> not_fresh_at sc x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. op = Var x ==> not_fresh_at sc x` by
    (drule compiler_unwrap_value_var >> Cases_on `vv` >> fs[vv_operand_def]) >>
  suspend "outcome"
QED

Resume body_assign_other_saved_equal_slots_write_full[outcome]:
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (drule_then (mp_tac o MATCH_MP stmt_state_rel_allocas_below_fmp)
      exprSimWordArgsTheory.expr_post_state >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) z /\
    storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) Gz tnz z /\
    dead_lo_ok H (DF H) lo cenv cx /\ storage_place_observed H (StoragePlace tr k dtv)` by
    (gen_tac >> disch_tac >>
     `storage_place_observed H (StoragePlace tr k dtv)` by
       (irule stmtSimAugAssignPlaceStorageTheory.aug_place_target_observed >>
        goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
        qexists `st0` >> simp[]) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> target_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (mp_tac o REWRITE_RULE [expr_post_def])) >>
     simp[SF CONJ_ss]) >>
  irule body_assign_other_direct_slots_write_full >>
  simp[] >> rpt conj_tac >> gvs[wb_frame_def, ghost_kept_at_def]
  >- (qexists `env` >> simp[]) >>
  qexistsl [`FST r`,`lowered_value_type cenv e`,`Var xs`,`sc`,`sw`] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Finalise body_assign_other_saved_equal_slots_write_full[local]

(* The nonword snapshot is already in memory when the target lands. *)
Theorem body_assign_other_snapshot_memory_write_full[local]:
  body_inv tops ctx cenv cx /\ struct_args_unique tops /\
  expr_sim_inv cenv cx env es /\ target_pre cenv cx env t mid /\
  type_place_target env t = SOME (Type ty) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget t) e)) (stmt_res_ok lctx) es /\
  (!tail. eval_expr cx e
    (es with gas_obs := gas_explicit rhsmarks s0.vs_gas_readings ++ tail) =
    (INL pv,mid with gas_obs := tail)) /\
  (!tail. read_result cx pv (mid with gas_obs := tail) =
    (INL v,mid with gas_obs := tail)) /\
  (!tail. eval_target_place cx t
    (mid with gas_obs := gas_explicit target_marks u.vs_gas_readings ++ tail) =
    (INL (MemoryPlace id path),ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    target_post H ctx func cenv cx mid ss st u ee (PlaceR (MemoryPlace id path)) (Type ty) r z /\
    ghost_inv_at (DF H) lo d cenv cx ee Gz tnz z) /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) r Gz tnz z /\
  (?entry w. lookup_scopes id ee.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL w) /\
  ee.gas_obs = [] /\ ~z.vs_halted /\ z.vs_current_bb = su.cs_current_bb /\
  z.vs_inst_idx = LENGTH su.cs_current_insts /\
  return_buf_frame d cenv su z /\ alloca_history func z /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ s0.vs_alloca_next <= z.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x z = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==> FLOOKUP Gz x = FLOOKUP G0 x /\
                             op_taint tnz (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame cenv es sa s0 cenv ee z /\
  (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b len. local_region cenv es.scopes s0 n b len ==> off + sz <= b \/ b + len <= off) /\
    off <= i /\ i < off + sz /\ i IN tnz.t_mem ==> i IN tn0.t_mem) /\
  ~is_word_type ty /\
  ~is_word_type (lowered_value_type cenv e) /\
  type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv /\
  op = Var xs /\ lookup_var xs z = SOME (n2w b) /\
  FLOOKUP z.vs_allocas aid = SOME (b,type_memory_size tv) /\ aid < su.cs_next_id /\
  lo <= b /\ b + type_memory_size tv < dimword (:256) /\
  b + type_memory_size tv <= z.vs_alloca_next /\
  (!n off len. local_region cenv ee.scopes z n off len ==>
    loweringStateRelDefs$regions_disjoint b (type_memory_size tv) off len) /\
  ptr_covers Gz tnz xs z (type_memory_size tv) /\
  (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==> val_in_memory tv v b mem) /\
  compile_snapshot_vv cenv T (vv_with_type (lowered_value_type cenv e) vv0) sm = (snap,ss) /\
  unwrap_value cenv snap st = (op,su) /\
  compile_get_target_ptr compile_expr cenv t ss = (r,st) /\
  (!loc. FST (SND r) = SOME loc ==>
    compile_assign_value cenv (FST r) loc op F (vv_location snap) ty
      (lowered_value_type cenv e) (type_memory_bytes cenv ty) su = ((),sb)) /\
  (!x. op = Var x ==> not_fresh_at su x) /\
  (!x. FST r = Var x ==> not_fresh_at st x) /\
  ci_mono sa su /\ ci_mono su sb /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  ~block_is_terminated su ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (write_place cx (MemoryPlace id path) v) (ee,z,Gz,tnz)
    (\H res ff Gf tf zf.
      ?ce. stmt_lands lctx sb res zf /\ ~zf.vs_halted /\
        (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
        cenv_top_ext cenv ce ff.scopes /\ stmt_state_rel H ctx func ce cx ff zf /\
        storage_well_formed_on cx ff (FST H) /\ return_buf_frame d ce sb zf /\
        alloca_history func zf /\ (ctx_has_dalloca ctx ==> allocas_below_fmp zf) /\
        s0.vs_alloca_next <= zf.vs_alloca_next /\ ghost_inv_at (DF H) lo d ce cx ff Gf tf zf /\
        (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x zf = SOME w) /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP zf.vs_allocas aid = SOME b) /\
        (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
                                   op_taint tf (Var x) = op_taint tn0 (Var x)) /\
        alloca_frame cenv es sa s0 ce ff zf /\
        (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
          (!n b len. local_region cenv es.scopes s0 n b len ==> off + sz <= b \/ b + len <= off) /\
          off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tn0.t_mem))
    (\H res ff gt q.
      (!tail. stmt_exit_ptr (RetQ H) (ff with gas_obs := tail) res gt q) /\
      halt_exit H cx ff res q /\
      (ctx_has_dalloca ctx ==>
        !s. (q = Halt s \/ ?ir. q = IntRet ir s) ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `target_gas = gas_explicit target_marks u.vs_gas_readings` >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `eval_target_place cx t (mid with gas_obs := target_gas) = (INL (MemoryPlace id path),ee)` by
    (qpat_assum `!tail. eval_target_place _ _ (_ with gas_obs := _ ++ tail) = _`
       (qspec_then `[]` mp_tac) >>
     qpat_assum `ee with gas_obs := [] = ee` (fn th => rewrite_tac [listTheory.APPEND_NIL,th])) >>
  Cases_on `write_place cx (MemoryPlace id path) v ee` >>
  rename1 `write_place cx (MemoryPlace id path) v ee = (res,ff)` >>
  `stmt_res_ok lctx res` by
    (qpat_assum `gas_admissible (eval_stmt _ _) _ _`
       (mp_then Any irule gas_admissible_result) >>
     qexistsl [`ff`,`gas_explicit rhsmarks s0.vs_gas_readings ++ target_gas`] >>
     simp[Once evaluate_def,bind_def]) >>
  drule_all_then assume_tac placeRelayoutOutcomeTheory.memory_write_admissible_success >>
  qpat_x_assum `res = INL ()` SUBST_ALL_TAC >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by
    gvs[Abbr `H0`, vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `?dw. eval_operand (FST r) z = SOME dw /\
        place_ptr_rel cenv cx z (PlaceR (MemoryPlace id path)) dw (FST (SND r)) (Type ty)` by
    fs[target_post_def] >>
  `FST (SND r) = SOME LocMemory /\ SND (SND r) = SOME (ValPT ty)` by
    fs[place_ptr_rel_def, target_post_def, value_type_place_def] >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    fs[place_ptr_rel_def] >>
  `ptr_covers Gz tnz p z sz` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     qpat_x_assum `?entry w. _` strip_assume_tac >> metis_tac[]) >>
  `?xd. FST r = Var xd` by
    (qpat_assum `target_ptr_ok _ _ _ _ _ _` (mp_tac o REWRITE_RULE [target_ptr_ok_def]) >>
     simp[] >> strip_tac >>
     `FLOOKUP Gz p <> NONE` by fs[ptr_covers_def] >>
     Cases_on `FST r` >> fs[ptrDisciplineTheory.op_prov_def]) >>
  `r = (Var xd,SOME LocMemory,SOME (ValPT ty))` by metis_tac[pairTheory.PAIR] >>
  `target_pre cenv cx env t (mid with gas_obs := target_gas)` by
    simp[body_assign_saved_resources_gas] >>
  `well_typed_target env t ty` by simp[well_typed_target_def] >>
  `call_evaluation_safe cx (int_calls_target t)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_stmt (Assign _ _))` mp_tac >>
     rewrite_tac[Once int_calls_stmt_def, Once int_calls_atarget_def] >>
     disch_then (mp_then Any ACCEPT_TAC call_evaluation_safe_append_left)) >>
  drule_all_then strip_assume_tac tuplePlaceSourceHeadTheory.tuple_place_source_target_endpoint >>
  `!entry t0. lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `expr_sim_inv _ _ _ ee`
       (mp_tac o REWRITE_RULE [expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `?et. FLOOKUP env.var_types id = SOME et` by
       metis_tac[optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  `stmt_state_rel H0 ctx func cenv cx ee z` by fs[target_post_def] >>
  `place_ptr_rel cenv cx z (PlaceR (MemoryPlace id path)) dw (SOME LocMemory) (Type ty)` by
    (qpat_assum `FST (SND r) = SOME LocMemory` (fn eq =>
       qpat_assum `place_ptr_rel _ _ z _ dw (FST (SND r)) _`
         (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  `!i ps entry t0. MemoryPlace id path = MemoryPlace i ps /\
      lookup_scopes i ee.scopes = SOME entry /\ cenv.ce_var_type i = SOME t0 ==>
      evaluate_type (get_tenv cx) t0 = SOME entry.type` by simp[] >>
  `?nm a len. local_region cenv ee.scopes z nm a len /\
      a <= w2n dw /\ w2n dw + type_memory_size dtv <= a + len` by
    (drule_all placeMemoryLiveRegionTheory.memory_place_live_region >> simp[]) >>
  `value_has_type dtv v` by metis_tac[type_widens_to_value_has_type, SOME_11] >>
  `val_wf dtv v` by metis_tac[memoryValueTypingTheory.value_has_type_val_wf] >>
  `type_memory_bytes cenv ty = type_memory_size dtv` by
    (irule expr_sim_inv_memory_size >> metis_tac[]) >>
  `w2n ((n2w b):bytes32) = b` by simp[LESS_MOD] >>
  `expr_val_at cenv cx (lowered_value_type cenv e) (su with cs_next_id := 0) su ee v (Var xs) z` by
    ((simp[expr_val_at_def, eval_operand_def] >> disj1_tac >>
     qexistsl [`aid`,`b`,`type_memory_size tv`] >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def, val_footprint_le] >> (metis_tac[expr_val_at_def, eval_operand_def, loweringStateRelDefsTheory.regions_disjoint_def, val_footprint_le]))) >>
  `vv_location snap = SOME LocMemory` by
    (drule bodyMemSnapshotSourceLocationTheory.snapshot_saved_representation >> simp[]) >>
  `compile_assign_value cenv (Var xd) LocMemory (Var xs) F (SOME LocMemory) ty
       (lowered_value_type cenv e) (type_memory_bytes cenv ty) su = ((),sb)` by
    (qpat_assum `!loc. FST (SND r) = SOME loc ==> _` (qspec_then `LocMemory` mp_tac) >>
     gvs[]) >>
  `0 < type_memory_size dtv ==> lo <= w2n dw` by
    (strip_tac >> `0 < len` by decide_tac >>
     qpat_assum `!H. dead_lo_ok H (DF H) lo cenv cx` (qspec_then `H0` assume_tac) >>
     drule_all_then assume_tac body_full_local_region_lower_bound >> decide_tac) >>
  drule_all_then strip_assume_tac immutable_assign_copy_metadata >>
  `type_memory_size tv < dimword (:256)` by decide_tac >>
  `ci_mono st su` by
    (mp_tac (Q.SPECL [`cenv`,`snap`,`st`] ci_mono_unwrap_value) >> simp[]) >>
  `sa.cs_next_var <= su.cs_next_var /\ sa.cs_next_id <= su.cs_next_id /\
   st.cs_next_var <= su.cs_next_var` by fs[ci_mono_def] >>
  `not_fresh_at su xs /\ not_fresh_at su xd` by
    (conj_tac >- simp[] >> irule freshWritesTheory.not_fresh_at_mono >> qexists `st` >> simp[]) >>
  `local_ptrs_reserved cenv su` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `lookup_var xd z = SOME dw` by fs[eval_operand_def] >>
  Q.SUBGOAL_THEN
    `type_memory_size tv = 0 \/ w2n ((n2w b):bytes32) + type_memory_size tv <= z.vs_alloca_next`
    assume_tac >- simp[] >>
  `target_ptr_ok cenv (PlaceR (MemoryPlace id path))
     (Var xd,SOME LocMemory,SOME (ValPT ty)) Gz tnz z` by
    (qpat_assum `r = (Var xd,_,_)` (fn eq =>
       qpat_assum `target_ptr_ok _ _ r _ _ _` (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  `~block_is_terminated sb` by
    (drule_all stmtSimDeclTypedCodeTheory.compile_assign_value_typed_open >> simp[]) >>
  `ff.storage_trace = ee.storage_trace` by
    (drule tuplePlaceStepTheory.write_place_storage_trace >> simp[]) >>
  `!H. valid_horizon cx st0 H ff.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee z /\
       ghost_inv_at (DF H) lo d cenv cx ee Gz tnz z /\
       storage_well_formed_on cx ff (FST H)` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H ee.storage_trace` by metis_tac[] >>
     qpat_assum `!h. valid_horizon _ _ h ee.storage_trace ==> target_post h _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     `stmt_state_rel H ctx func cenv cx ee z /\ storage_well_formed_on cx ee (FST H)`
       by fs[target_post_def] >>
     drule_then assume_tac vyperPlaceFramesTheory.write_memory_place_storage >>
     fs[vyperStorageFootprintTheory.storage_well_formed_on_def]) >>
  `?zf Gf tf.
     (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (z,Gz,tnz) [] (OK zf,Gf,tf)) /\
     (!H. valid_horizon cx st0 H ff.storage_trace /\
       stmt_state_rel H ctx func cenv cx ee z /\
       ghost_inv_at (DF H) lo d cenv cx ee Gz tnz z ==>
       stmt_state_rel H ctx func cenv cx ff zf /\
       ghost_inv_at (DF H) lo d cenv cx ff Gf tf zf) /\
     ~zf.vs_halted /\ zf.vs_current_bb = sb.cs_current_bb /\
     zf.vs_inst_idx = LENGTH sb.cs_current_insts /\
     alloca_history func zf /\ z.vs_alloca_next <= zf.vs_alloca_next /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp zf) /\ return_buf_frame d cenv sb zf /\
     (!a ent. FLOOKUP z.vs_allocas a = SOME ent ==> FLOOKUP zf.vs_allocas a = SOME ent) /\
     (!x. not_fresh_at su x ==> lookup_var x zf = lookup_var x z /\
       FLOOKUP Gf x = FLOOKUP Gz x /\ op_taint tf (Var x) = op_taint tnz (Var x)) /\
     alloca_frame cenv ee su z cenv ff zf /\
     (!a off sz i. FLOOKUP z.vs_allocas a = SOME (off,sz) /\ a < su.cs_next_id /\
       (!n b len. local_region cenv ee.scopes z n b len ==> off + sz <= b \/ b + len <= off) /\
       off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tnz.t_mem)` suffices_by
    (strip_tac >>
     `ff with gas_obs := [] = ff` by
       (drule tuplePlaceSourceGasTheory.tuple_place_write_preserves_gas_obs >>
        simp[evaluation_state_component_equality]) >>
     rewrite_tac[gas_outcome_full_def] >> qexists `[]` >>
     disj2_tac >> disj1_tac >> qexistsl [`INL ()`,`ff`,`OK zf`,`Gf`,`tf`] >>
     simp[] >> conj_tac >-
       (drule stmtSimAugAssignPlaceMemoryTheory.aug_place_memory_write_gas_obs >> simp[]) >>
     gen_tac >> strip_tac >> simp[] >> disj1_tac >>
     `valid_horizon cx st0 H ff.storage_trace` by metis_tac[] >>
     qpat_assum `!h. valid_horizon _ _ h ff.storage_trace ==> stmt_state_rel h _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     `stmt_state_rel H ctx func cenv cx ff zf /\ ghost_inv_at (DF H) lo d cenv cx ff Gf tf zf`
       by (qpat_assum `!h. valid_horizon _ _ h ff.storage_trace /\ _ ==> _`
             (qspec_then `H` mp_tac) >> simp[]) >>
     simp[stmt_lands_def,cenv_top_ext_refl] >>
     `!x. not_fresh_at sa x ==> not_fresh_at su x` by
       (gen_tac >> strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
     rpt conj_tac
     >- (rpt strip_tac >>
         `not_fresh_at su x` by simp[] >>
         qpat_assum `!x. not_fresh_at su x ==> _`
           (qspec_then `x` mp_tac) >> simp[])
     >- (rpt strip_tac >>
         `not_fresh_at su x` by simp[] >>
         qpat_assum `!x. not_fresh_at su x ==> _`
           (qspec_then `x` mp_tac) >> simp[])
     >- (irule alloca_frame_trans >> qexistsl [`cenv`,`ee`,`z`,`su`] >> simp[]) >>
     map_every qx_gen_tac [`old_id`,`old_off`,`old_sz`,`i`] >> strip_tac >>
     `FLOOKUP z.vs_allocas old_id = SOME (old_off,old_sz)` by simp[] >>
     `!n b len. local_region cenv ee.scopes z n b len ==>
        old_off + old_sz <= b \/ b + len <= old_off` by
       (qpat_assum `alloca_frame cenv es sa s0 cenv ee z`
         (qspecl_then [`old_id`,`old_off`,`old_sz`] mp_tac o REWRITE_RULE [alloca_frame_def]) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
        disch_then (ACCEPT_TAC o CONJUNCT2)) >>
     `old_id < su.cs_next_id` by decide_tac >>
     `i IN tnz.t_mem` by
       (qpat_assum `!a off sz i. FLOOKUP z.vs_allocas a = SOME (off,sz) /\ _ ==> _`
          (qspecl_then [`old_id`,`old_off`,`old_sz`,`i`] mp_tac) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
     qpat_assum `!a off sz i. FLOOKUP s0.vs_allocas a = SOME (off,sz) /\ _ ==> _`
       (qspecl_then [`old_id`,`old_off`,`old_sz`,`i`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  Cases_on `0 < type_memory_size dtv`
  >- (drule_then
        (drule_at_then (Pat `stmt_state_rel _ _ _ _ _ _ _`)
          (drule_at_then (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)
            (drule_at_then (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)
              (drule_at_then (Pat `write_place _ _ _ _ = _`) mp_tac))))
        (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
           body_assign_memory_place_joint) >>
      disch_then (qspecl_then [`n2w b`,`tv`,`shadow_ctx`,`env`,`dw`,`dtv`,`PG`] mp_tac) >>
      (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
      strip_tac >> qexistsl [`t'`,`Gf`,`tf`] >> simp[] >>
      conj_tac
      >- (gen_tac >> strip_tac >>
          qpat_assum `!H D d. stmt_state_rel _ _ _ _ _ _ _ /\ _ ==> _`
            (qspecl_then [`H`,`DF H`,`d`] mp_tac) >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  `type_memory_size dtv = 0` by decide_tac >>
  `type_memory_size tv = 0` by
    (drule_all placeMemoryTypeInterfacesTheory.type_widens_to_zero_memory_size >> simp[]) >>
  `lowered_value_type cenv e = ty` by
    (irule wideningZeroLayoutTheory.type_widens_to_zero_layout >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `~is_bytestring_type ty` by
    (strip_tac >> drule bytestring_memory_bytes_positive >>
     disch_then (qspec_then `cenv` mp_tac) >> simp[]) >>
  `?buf. compile_alloc_buffer 0 su = (buf,sb)` by
    (qpat_x_assum `compile_assign_value cenv (Var xd) LocMemory (Var xs) F (SOME LocMemory) _ _ _ su = _`
       mp_tac >>
     Cases_on `compile_alloc_buffer 0 su` >>
     simp[compile_assign_value_def, contextTheory.compile_store_memory_def,
       contextPropsTheory.compile_copy_memory_zero, comp_bind_def, comp_return_def,
       comp_ignore_bind_def]) >>
  `0 < dimword (:256)` by simp[] >>
  drule_all (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
    body_full_alloc_buffer_path) >>
  disch_then (qspecl_then [`tnz`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`Gz`]
    (qx_choose_then `za` (qx_choose_then `aroot` (qx_choose_then `ab`
      (qx_choose_then `Ga` (qx_choose_then `ta` strip_assume_tac)))))) >>
  `ta.t_mem = tnz.t_mem` by
    (qpat_assum `!i. _ ==> (i IN ta.t_mem <=> _)` mp_tac >> simp[pred_setTheory.EXTENSION]) >>
  `alloca_inv z` by metis_tac[rest_word_state_alloca_inv] >>
  `alloca_history func za /\ z.vs_alloca_next <= za.vs_alloca_next` by
    (qpat_assum `!D. gas_origin_ptr_path _ (z,Gz,tnz) [] _`
       (qspec_then `cx_dead H0 cx` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_origin_path_erase >> strip_tac >>
     drule_all rest_word_marked_allocation_posts >> simp[]) >>
  qexistsl [`za`,`Ga`,`ta`] >> simp[] >>
  reverse conj_tac
  >- (conj_tac
      >- (irule return_buf_frame_frame >> qexistsl [`cenv`,`z`,`su`] >>
          fs[ci_mono_def] >> rpt strip_tac >> simp[]) >>
      qpat_assum `stmt_state_rel H0 _ _ _ _ _ _`
        (mp_then Any (fn th => irule th) alloca_frame_of_mem_frame) >>
      `MAP FDOM ff.scopes = MAP FDOM ee.scopes` by
        metis_tac[vyperScopePreservationTheory.write_place_scopes_dom] >>
      simp[]) >>
  `place_ptr_rel cenv cx za (PlaceR (MemoryPlace id path)) dw (SOME LocMemory) (Type ty)` by
    (`not_fresh_at su p` by (fs[local_ptrs_reserved_def] >> (metis_tac[local_ptrs_reserved_def])) >>
     `lookup_var p za = lookup_var p z` by simp[] >>
     qpat_assum `place_ptr_rel _ _ z _ _ (SOME LocMemory) _`
       (strip_assume_tac o REWRITE_RULE [place_ptr_rel_def]) >>
     fs[] >> simp[place_ptr_rel_def] >> metis_tac[]) >>
  `typed_copy_effect ctx func sb sb za za (w2n dw) (type_memory_size dtv)` by
    (irule placeMemoryCopyEffectTheory.typed_copy_effect_identity >> simp[]) >>
  `!mem. val_in_memory dtv v (w2n dw) mem` by
    (irule valueEncodingProofsTheory.return_zero_wf_memory >> simp[]) >>
  (* The zero-width write changes the source value but no memory bytes.
     Instantiate the store post at floor 0; keep the nonlocal floor-lo facts. *)
  gen_tac >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee za /\ ghost_inv_at (DF H) lo d cenv cx ee Ga ta za`
    by (conj_tac >> first_assum (fn th => MATCH_MP_TAC th >> first_assum ACCEPT_TAC)) >>
  `ghost_inv_at (DF H) 0 d cenv cx ee Ga ta za` by
    (qpat_assum `ghost_inv_at (DF H) lo d cenv cx ee Ga ta za` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ghost_inv_at_def,allocas_from_def] >>
     strip_tac >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx ff za /\ ghost_inv_at (DF H) 0 d cenv cx ff Ga ta za` by
    (qpat_assum `typed_copy_effect ctx func sb sb za za _ _`
       (mp_then (Pos hd)
          (drule_at_then (Pat `write_place _ _ _ _ = _`)
             (drule_at_then (Pat `stmt_state_rel _ _ _ _ _ _ _`)
                (fn th => qpat_assum `ghost_inv_at (DF H) 0 d cenv cx ee Ga ta za`
                   (mp_then (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`) mp_tac th))))
          (Q.INST [`lo` |-> `0`, `Gf` |-> `G`, `tf` |-> `tn`]
            body_assign_memory_place_store_post)) >>
     disch_then (qspecl_then [`env`,`ty`] mp_tac) >>
     simp[SF boolSimps.CONJ_ss]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `ghost_inv_at (DF H) 0 d cenv cx ff Ga ta za` mp_tac >>
  qpat_assum `ghost_inv_at (DF H) lo d cenv cx ee Ga ta za` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[ghost_inv_at_def, AND_IMP_INTRO] >>
  strip_tac >> simp[]
QED

(* Saved RHS, with the copy staging selected by the original value location. *)
Theorem body_assign_other_saved_staged_memory_write_full[local]:
  body_inv tops ctx cenv cx /\ struct_args_unique tops /\
  supported_stmt tops bindings (Assign (BaseTarget bt) e) /\
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget bt) e)) /\
  ~expr_can_mutate cenv (target_to_expr bt) /\
  expr_body_pre cenv cx env e es /\ target_pre cenv cx env bt mid /\
  runtime_consistent env cx es /\ functions_well_typed cx /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e)) (stmt_res_ok lctx) es /\
  (!tail. eval_expr cx e (es with gas_obs := prefix ++ tail) =
    (INL tv,mid with gas_obs := tail)) /\
  read_result cx tv mid = (INL v,mid) /\
  type_place_target env bt = SOME (Type ty) /\
  ~is_word_type ty /\ ~is_word_type (lowered_value_type cenv e) /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  compile_get_target_ptr compile_expr cenv bt sm = (r,sb) /\
  unwrap_value cenv vv sb = (op,sc) /\ vv_location vv = SOME LocMemory /\
  (case FST (SND r) of
     SOME loc => compile_assign_value cenv (FST r) loc op
       (is_word_type (case SND (SND r) of SOME (ValPT tau) => tau
          | _ => lowered_value_type cenv e))
                   (vv_location vv)
       (case SND (SND r) of SOME (ValPT tau) => tau
          | _ => lowered_value_type cenv e) (lowered_value_type cenv e)
       (type_memory_bytes cenv (case SND (SND r) of SOME (ValPT tau) => tau
          | _ => lowered_value_type cenv e))
   | NONE => emit_void INVALID []) sc = ((),sf) /\
  fn_has_code sa sf func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\ ret_pc_ok cenv sa s0 /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!tail. eval_target_place cx bt
    (mid with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL (MemoryPlace id path),ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    target_post H ctx func cenv cx mid sm sb s ee (PlaceR (MemoryPlace id path)) (Type ty) r u /\
    expr_post H ctx func cenv cx e ee sa sc u ee v op z /\
    ghost_inv_at (DF H) lo d cenv cx ee Gz tnz z) /\
  (?entry w. lookup_scopes id ee.scopes = SOME entry /\
             evaluate_subscripts entry.type entry.value path = INL w) /\
  (~is_word_type (post_value_type cenv e) ==>
    vv_at cenv cx (post_value_type cenv e) sa sc ee tv
      (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
  expr_store_bound cx (post_value_type cenv e) v op z /\
  ptr_val_ok cx (post_value_type cenv e) v op Gz tnz z /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op Gz z) /\
  (~is_word_type (post_value_type cenv e) ==>
   !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
          eval_operand op z = SOME w ==>
          type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
  ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
  z.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func z /\
  s0.vs_alloca_next <= z.vs_alloca_next /\ return_buf_frame d cenv sc z /\
  eval_operand (FST r) z = eval_operand (FST r) u /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) r Gz tnz z /\
  wb_frame cenv ee ee sb u z /\
  wb_frame cenv es ee sa s0 z /\ ghost_kept_at lo cenv es sa Gi ti s0 Gz tnz /\
  alloca_frame cenv es sa s0 cenv ee z /\
  (!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa.cs_next_id /\
    (!name b cap. local_region cenv es.scopes s0 name b cap ==>
      a+n <= b \/ b+cap <= a) /\ a <= i /\ i < a+n /\ i IN tnz.t_mem ==>
    i IN ti.t_mem) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (write_place cx (MemoryPlace id path) v) (ee,z,Gz,tnz)
    (\H res ef G tn q. ?ce.
      stmt_lands lctx sf res q /\ ~q.vs_halted /\
      (res = INL () ==> ~block_is_terminated sf /\ ce = cenv) /\
      cenv_top_ext cenv ce ef.scopes /\ stmt_state_rel H ctx func ce cx ef q /\
      storage_well_formed_on cx ef (FST H) /\ return_buf_frame d ce sf q /\
      alloca_history func q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
      s0.vs_alloca_next <= q.vs_alloca_next /\ ghost_inv_at (DF H) lo d ce cx ef G tn q /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x q = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP q.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP G x = FLOOKUP Gi x /\ op_taint tn (Var x) = op_taint ti (Var x)) /\
      alloca_frame cenv es sa s0 ce ef q /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN ti.t_mem))
    (\H res ef gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ef with gas_obs := tail) res gt r) /\
      halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==>
        !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qabbrev_tac `start = mid with gas_obs := gas_explicit marks s.vs_gas_readings` >>
  `eval_target_place cx bt start = (INL (MemoryPlace id path),ee)` by
    (simp[Abbr `start`] >>
     qpat_assum `!tail. eval_target_place _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `ee with gas_obs := [] = ee`
       (fn th => rewrite_tac[APPEND_NIL,th])) >>
  Cases_on `write_place cx (MemoryPlace id path) v ee` >>
  rename1 `write_place _ _ _ _ = (wr,ff)` >>
  `stmt_res_ok lctx wr` by
    (`read_result cx tv start = (INL v,start)` by
       (simp[Abbr `start`] >> drule read_result_gas_obs >> simp[]) >>
     drule gas_admissible_result >> disch_then irule >>
     qexistsl [`ff`,`prefix ++ gas_explicit marks s.vs_gas_readings`] >>
     simp[Once evaluate_def, bind_def]) >>
  `wr = INL ()` by drule_all_then ACCEPT_TAC placeRelayoutOutcomeTheory.memory_write_admissible_success >>
  qpat_x_assum `wr = INL ()` SUBST_ALL_TAC >>
  `ci_mono sa sm` by metis_tac[compile_expr_ci_mono,SND] >>
  `ci_mono sm sb` by metis_tac[ci_mono_compile_get_target_ptr,SND] >>
  `ci_mono sb sc` by metis_tac[ci_mono_unwrap_value,SND] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [target_post_def, value_type_place_def]) >>
  rename1 `eval_operand (FST r) u = SOME dw` >>
  qpat_assum `place_ptr_rel _ _ u _ _ _ _`
    (strip_assume_tac o SRULE [place_ptr_rel_def]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def] >>
     decide_tac) >>
  `place_ptr_rel cenv cx z (PlaceR (MemoryPlace id path)) dw (SOME LocMemory) (Type ty)` by
    (rename1 `lookup_var xp u = SOME xb` >>
     `not_fresh_at sb xp` by metis_tac[local_ptrs_reserved_def] >>
     `lookup_var xp z = SOME xb` by drule_all_then ACCEPT_TAC wb_frame_vars >>
     simp[place_ptr_rel_def] >> metis_tac[]) >>
  `expr_sim_inv cenv cx env ee` by
    (irule bodySimAugPlaceLoadTheory.aug_place_target_inv >>
     goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
     fs[Abbr `start`,target_pre_def]) >>
  `eval_expr cx e (es with gas_obs := prefix) = (INL tv,mid with gas_obs := [])` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     rewrite_tac[APPEND_NIL]) >>
  `read_result cx tv (mid with gas_obs := []) = (INL v,mid with gas_obs := [])` by
    simp[read_result_gas_obs] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) =
   (INL v,mid with gas_obs := [])` by simp[bind_def] >>
  `expr_body_pre cenv cx env e (es with gas_obs := prefix)` by simp[] >>
  drule_all_then (qx_choose_then `stv` strip_assume_tac)
    (SIMP_RULE (srw_ss() ++ ETA_ss) [] immutable_rhs_physical_typed) >>
  `~is_word_type (post_value_type cenv e)` by
    metis_tac[immutable_rhs_post_physical_classify,is_bytestring_word_type] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty /\
   assignable_type (get_tenv cx) ty` by
    (drule body_assign_empty_target_typing >> simp[] >> strip_tac >>
     conj_tac >- (irule immutable_rhs_physical_widens >> metis_tac[]) >>
     metis_tac[vyperTypeArgFitsTheory.type_widens_to_assignable_type]) >>
  `0 < type_memory_size stv` by
    (drule_all_then mp_tac placeMemoryTypeInterfacesTheory.type_widens_to_zero_memory_size >>
     rename1 `evaluate_type (get_tenv cx) ty = SOME dtv` >>
     `0 < type_slot_size dtv` by drule_all_then ACCEPT_TAC assignable_type_slot_size_pos >>
     simp[valueEncodingPropsTheory.type_memory_size_slots]) >>
  `expr_val_at cenv cx (lowered_value_type cenv e) sa sc ee v op z` by
    (irule abiEncodeArgsSimTheory.abi_args_expr_post_lowered_at >>
     conj_tac >- (strip_tac >> qexists `stv` >> simp[]) >>
     conj_tac >- (qexistsl [`env`,`es`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  `?sw. eval_operand op z = SOME sw` by
    (qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _`
       (qspec_then `stv` mp_tac o REWRITE_RULE [expr_val_at_def]) >>
     simp[] >> disch_then (qx_choose_then `w` strip_assume_tac) >>
     qexists `w` >> simp[]) >>
  rename1 `eval_operand op z = SOME sw` >>
  `!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==>
     val_in_memory stv v (w2n sw) mem` by
    (`ptr_mem_ok cx (post_value_type cenv e) v op Gz tnz z` by
       fs[ptr_val_ok_def] >>
     drule immutable_rhs_post_physical_classify >> strip_tac
     >- metis_tac[bodyPtrBopHashFootprintTheory.ptr_mem_ok_robust] >>
     `type_widens_to (get_tenv cx) (lowered_value_type cenv e) (post_value_type cenv e)` by
       metis_tac[immutable_rhs_physical_post_widens] >>
     drule_all_then (qx_choose_then `ptv` strip_assume_tac)
       vyperTypeArgFitsTheory.type_widens_to_value_has_type >>
     rpt gen_tac >> disch_tac >>
     irule bytestring_val_in_memory_transfer >> simp[] >>
     qexistsl [`post_value_type cenv e`,`lowered_value_type cenv e`,`get_tenv cx`,`ptv`] >>
     simp[] >>
     qpat_assum `ptr_mem_ok _ _ _ _ _ _ _`
       (qspecl_then [`ptv`,`sw`] mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >> simp[]) >>
  `op_taint tnz op = {}` by fs[ptr_val_ok_def] >>
  `ptr_buf_ok cenv e op Gz z` by simp[] >>
  `?xs. op = Var xs /\ ptr_covers Gz tnz xs z (type_memory_size stv)` by
    (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
     simp[] >> qexistsl [`cenv`,`e`] >> simp[]) >>
  `lookup_var xs z = SOME sw` by fs[eval_operand_def] >>
  qpat_assum `?entry w. lookup_scopes id ee.scopes = SOME entry /\ _`
    (qx_choosel_then [`entry`,`elt`] strip_assume_tac) >>
  `ptr_covers Gz tnz p z sz` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ ee Gz tnz z`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [ghost_inv_at_def]) >>
     disch_then (qspecl_then [`id`,`entry`,`p`,`sz`] mp_tac) >> simp[]) >>
  `op_prov Gz (FST r) = FLOOKUP Gz p` by
    (qpat_assum `target_ptr_ok _ _ r _ _ _`
       (qspecl_then [`id`,`path`,`p`,`sz`] mp_tac o
        cj 2 o REWRITE_RULE [target_ptr_ok_def]) >> simp[]) >>
  `?xd. FST r = Var xd` by
    (qpat_x_assum `ptr_covers Gz tnz p z sz`
       (mp_tac o CONJUNCT2 o REWRITE_RULE [ptr_covers_def]) >>
     strip_tac >> Cases_on `FST r` >> gvs[op_prov_def]) >>
  `lookup_var xd z = SOME dw` by fs[eval_operand_def] >>
  `not_fresh_at sb xd` by simp[] >>
  `not_fresh_at sc xd` by fs[ci_mono_def,not_fresh_at_def] >>
  `r = (Var xd,SOME LocMemory,SOME (ValPT ty))` by
    (PairCases_on `r` >> gvs[]) >>
  `compile_assign_value cenv (Var xd) LocMemory (Var xs) F (SOME LocMemory)
      ty (lowered_value_type cenv e) (type_memory_bytes cenv ty) sc = ((),sf)` by
    gvs[LET_THM] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee z` by
    (qhdtm_assum `expr_post` (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [expr_post_def])) >>
  drule_all_then strip_assume_tac immutableDeployAssignRangesTheory.immutable_assign_copy_metadata >>
  rename1 `evaluate_type (get_tenv cx) ty = SOME dtv` >>
  `type_memory_bytes cenv ty = type_memory_size dtv` by
    (irule typedMemoryCopyTheory.typed_copy_memory_size >> simp[] >> metis_tac[]) >>
  `value_has_type dtv v` by
    (drule_all_then (strip_assume_tac o SIMP_RULE std_ss [])
      vyperTypeArgFitsTheory.type_widens_to_value_has_type >> (gvs[vyperTypeArgFitsTheory.type_widens_to_value_has_type])) >>
  `val_wf dtv v` by simp[value_has_type_val_wf] >>
  `0 < type_memory_size dtv` by
    (`0 < type_slot_size dtv` by drule_all_then ACCEPT_TAC assignable_type_slot_size_pos >>
     simp[valueEncodingPropsTheory.type_memory_size_slots]) >>
  `w2n sw + type_memory_size stv <= z.vs_alloca_next` by
    (qpat_assum `~is_word_type (post_value_type cenv e) ==> !rt w. _`
       (qspecl_then [`stv`,`sw:bytes32`] mp_tac o UNDISCH) >>
     asm_rewrite_tac[] >> gvs[]) >>
  `z.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ ee z`
       (mp_then Any mp_tac stmt_state_rel_alloca_room) >>
     disch_then (ACCEPT_TAC o MATCH_MP alloca_room_next_lt)) >>
  `w2n sw + type_memory_size stv < dimword (:256) /\
   type_memory_size stv < dimword (:256)` by decide_tac >>
  `ci_mono sa sc` by metis_tac[ci_mono_trans] >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\ cs_extends sa sc` by
    fs[ci_mono_def] >>
  `cs_extends sc sf` by
    (qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ sc = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[cj 1 externalEntryShapeTheory.compile_assign_value_labels, SND]) >>
  `fn_has_code sc sf func` by metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sc` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC freshWritesTheory.not_fresh_at_mono) >>
  `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sc x` by metis_tac[] >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sc x` by
    fs[ret_pc_ok_def] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    (`sm.cs_next_var <= sb.cs_next_var` by fs[ci_mono_def] >>
     rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sm` >>
     simp[] >>
     irule (CONJUNCT1 exprOperandVarTheory.compiler_compile_var) >>
     metis_tac[]) >>
  `not_fresh_at sc xs` by
    (irule exprOperandVarTheory.compiler_unwrap_value_var >>
     qexistsl [`cenv`,`op`,`sb`,`vv`] >> simp[] >>
     Cases_on `vv` >> gvs[vv_operand_def]) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    (qhdtm_assum `ghost_inv_at` (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp[]) >>
  `!j q en t0. MemoryPlace id path = MemoryPlace j q /\
       lookup_scopes j ee.scopes = SOME en /\ cenv.ce_var_type j = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME en.type` by
    (simp[NoAsms] >> rpt gen_tac >> strip_tac >>
     irule bodySimAugPlaceLoadTheory.aug_place_entry_type_agrees >>
     qexistsl [`cenv`,`env`,`id`,`ee`,`ee`] >> simp[]) >>
  `lo <= w2n dw` by
    (`dead_lo_ok (storage_trace_horizon ee.storage_trace)
        (DF (storage_trace_horizon ee.storage_trace)) lo cenv cx` by simp[] >>
     drule_all body_assign_memory_place_lower_bound >> simp[]) >>
  suspend "staged_suffix"
QED

Resume body_assign_other_saved_staged_memory_write_full[staged_suffix]:
  qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
  `target_ptr_ok cenv (PlaceR (MemoryPlace id path))
     (Var xd,SOME LocMemory,SOME (ValPT ty)) Gz tnz z` by metis_tac[] >>
  Q.SUBGOAL_THEN `type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= z.vs_alloca_next`
    assume_tac >- simp[] >>
  drule_then
    (fn th => qpat_assum `stmt_state_rel _ _ _ _ _ ee z`
      (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`)
        (drule_at_then (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)
          (drule_at_then (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)
            (drule_at_then (Pat `write_place _ _ _ _ = _`) mp_tac))) th))
    (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
      body_assign_memory_place_joint) >>
  disch_then (qspecl_then [`sw`,`stv`,`shadow_ctx`,`env`,`dw`,`dtv`,`PG`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]]) >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac) >>
  suspend "staged_landing"
QED

Resume body_assign_other_saved_staged_memory_write_full[staged_landing]:
  `~block_is_terminated sf` by
    (`0 < type_memory_bytes cenv (lowered_value_type cenv e)` by simp[] >>
     qpat_x_assum `type_memory_bytes cenv (lowered_value_type cenv e) = _` kall_tac >>
     Cases_on `compile_alloc_buffer (type_memory_bytes cenv (lowered_value_type cenv e)) sc` >>
     rename1 `compile_alloc_buffer _ sc = (buf,smem)` >>
     Cases_on `compile_copy_memory buf.buf_operand (Var xs)
        (type_memory_bytes cenv (lowered_value_type cenv e)) smem` >>
     rename1 `compile_copy_memory _ _ _ smem = (unit,ss)` >> Cases_on `unit` >>
     qpat_x_assum `compile_assign_value _ _ LocMemory _ F (SOME LocMemory) _ _ _ _ = _` mp_tac >>
     simp[Once compile_assign_value_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     strip_tac >>
     irule exprOpenCopiesTheory.compile_store_memory_open >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     simp[] >>
     qpat_x_assum `compile_copy_memory _ _ _ _ = _` mp_tac >>
     Cases_on `type_memory_bytes cenv (lowered_value_type cenv e)` >- gvs[] >>
     simp[compile_copy_memory_def] >>
     disch_then (mp_tac o MATCH_MP exprOpenPrimitivesTheory.emit_void_terminated) >>
     simp[is_terminator_def]) >>
  drule_then assume_tac stmtSimAugAssignPlaceMemoryTheory.aug_place_memory_write_gas_obs >>
  drule vyperPlaceFramesTheory.write_memory_place_frame >>
  disch_then (qx_choose_then `scopes` assume_tac) >>
  `ff with gas_obs := [] = ff /\ ff.storage_trace = ee.storage_trace` by
    simp[evaluation_state_component_equality] >>
  irule gas_outcome_full_pure >>
  conj_tac >- (
    qexistsl [`Gf`,`ff`,`INL ()`,`t`,`tf`] >>
    simp[stmt_lands_def,cenv_top_ext_refl] >> qx_gen_tac `H` >> strip_tac >>
    `stmt_state_rel H ctx func cenv cx ee z /\ storage_well_formed_on cx ee (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx ee Gz tnz z` by
      (qpat_assum `!H. valid_horizon _ _ H _ ==> target_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
         (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >>
       disch_then strip_assume_tac >>
       qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ z`
         (mp_tac o REWRITE_RULE [expr_post_def]) >> simp[]) >>
    `stmt_state_rel H ctx func cenv cx ff t /\ ghost_inv_at (DF H) lo d cenv cx ff Gf tf t` by
      (qpat_assum `!H D d. stmt_state_rel H _ _ _ _ ee z /\ _ ==> _`
         (qspecl_then [`H`,`DF H`,`d`] mp_tac) >> simp[]) >>
    `storage_well_formed_on cx ff (FST H)` by
      (qpat_assum `ff = ee with scopes := _`
         (fn th => simp[th,storage_well_formed_on_def,vyperStorageBackendTheory.get_storage_scopes]) >>
       fs[storage_well_formed_on_def]) >>
    `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b` by
      (qhdtm_assum `wb_frame` (mp_tac o REWRITE_RULE [wb_frame_def]) >> simp[]) >>
    qpat_x_assum `ff = ee with scopes := _` SUBST_ALL_TAC >>
    simp[] >>
    conj_tac >- (rpt strip_tac >> drule_all_then ACCEPT_TAC wb_frame_vars) >>
    conj_tac >-
      (qhdtm_assum `ghost_kept_at` (mp_tac o REWRITE_RULE [ghost_kept_at_def]) >> simp[]) >>
    conj_tac >- drule_all_then ACCEPT_TAC alloca_frame_trans >>
    rpt gen_tac >> strip_tac >>
    rename1 `FLOOKUP s0.vs_allocas old_id = SOME (off,old_sz)` >>
    `FLOOKUP z.vs_allocas old_id = SOME (off,old_sz)` by simp[] >>
    `old_id < sc.cs_next_id` by decide_tac >>
    `!n b cap. local_region cenv ee.scopes z n b cap ==>
       off + old_sz <= b \/ b + cap <= off` by
      (qpat_assum `alloca_frame cenv es sa s0 cenv ee z`
         (mp_tac o REWRITE_RULE [alloca_frame_def]) >>
       disch_then (qspecl_then [`old_id`,`off`,`old_sz`] mp_tac) >>
       (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
       disch_then (ACCEPT_TAC o CONJUNCT2)) >>
    `i IN tnz.t_mem` by
      (qpat_assum `!a b c j. _ ==> j IN tnz.t_mem`
         (qspecl_then [`old_id`,`off`,`old_sz`,`i`] mp_tac) >>
       (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
    qpat_assum `!a b c j. _ ==> j IN ti.t_mem`
      (qspecl_then [`old_id`,`off`,`old_sz`,`i`] mp_tac) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >> simp[]
QED

Finalise body_assign_other_saved_staged_memory_write_full[local]

(* The saved RHS may point into the target's local allocation.  The byte
   store reads the live padded interval from the initial memory. *)
Theorem body_assign_saved_bytestring_copy_effect[local]:
  compile_store_bytestring (Var xs) (Var xd) sa = ((),sb) /\
  is_bytestring_type dty /\ type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  (!m. mem_agree_outside tn.t_mem z.vs_memory m ==>
       val_in_memory stv v (w2n sw) m) /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs z = SOME sw /\ lookup_var xd z = SOME dw /\
  ptr_covers G tn xs z (type_memory_size stv) /\
  ptr_covers G tn xd z (type_memory_size dtv) /\
  w2n sw + type_memory_size stv <= z.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= z.vs_alloca_next /\
  z.vs_alloca_next < dimword (:256) /\
  allocas_from lo z /\ lo <= z.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  fn_has_code sa sb func /\ ~z.vs_halted /\
  z.vs_current_bb = sa.cs_current_bb /\ z.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,G,tn) [] (OK t,Gf,tf)) /\
    typed_copy_effect ctx func sa sb z t (w2n dw) (type_memory_size dtv) /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
       val_in_memory dtv v (w2n dw) m) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x z /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac typedMemoryCopyTheory.typed_copy_bytestring_source >>
  Q.SUBGOAL_THEN
    `?len. ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
            (?str. v = StringV str /\ len = LENGTH str)) /\
           val_store_size stv v = 32 + 32 * word_size len`
    (qx_choose_then `len` (map_every assume_tac o CONJUNCTS))
  >- (drule_all (Q.SPECL [`tenv`,`sty`,`stv`] bytestring_type_value) >>
      qpat_x_assum `value_has_type stv v` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >> strip_tac >>
      Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def,val_store_size_def]) >>
  `val_store_size stv v = val_store_size dtv v` by
    (irule bytestring_val_store_size_eq >> simp[] >>
     qexistsl [`sty`,`dty`,`tenv`] >> simp[]) >>
  qabbrev_tac `n = 32 + 32 * word_size len` >>
  `val_wf stv v /\ val_wf dtv v` by simp[cj 1 value_has_type_val_wf] >>
  `n <= type_memory_size stv /\ n <= type_memory_size dtv` by
    metis_tac[val_store_size_le] >>
  `len <= 32 * word_size len` by simp[exprSimPropsTheory.le_word_size_mul] >>
  `n = 32 + 32 * word_size len` by simp[Abbr `n`] >>
  `len+31 < dimword (:256) /\ n < dimword (:256) /\
   w2n (sw:bytes32) + n <= z.vs_alloca_next /\
   w2n (dw:bytes32) + n <= z.vs_alloca_next` by decide_tac >>
  `n = 32 + 32 * ((len+31) DIV 32)` by simp[word_size_def,Abbr `n`] >>
  `ptr_covers G tn xs z n /\ ptr_covers G tn xd z n` by
    metis_tac[reasonCopySourcePtrTheory.ptr_covers_mono] >>
  `?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,G,tn) [] (OK t,Gf,tf)) /\
    typed_copy_effect ctx func sa sb z t (w2n dw) (type_memory_size dtv) /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
       val_in_memory dtv v (w2n dw) m) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x z /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+n) ==> (i IN tf.t_mem <=> i IN tn.t_mem))` by
    (irule body_assign_local_memory_bytes_copy_effect >> asm_rewrite_tac[] >>
     conj_tac >- (qexists `len` >> simp[]) >>
     qexistsl [`dty`,`stv`,`sty`,`sw`,`tenv`,`xd`,`xs`] >>
     qpat_assum `n = 32 + 32 * ((_+31) DIV 32)` (SUBST1_TAC o SYM) >> simp[]) >>
  qexistsl [`t`,`Gf`,`tf`] >> simp[] >>
  gen_tac >> strip_tac >>
  `~(w2n (dw:bytes32) <= i /\ i < w2n dw+n)` by decide_tac >> simp[]
QED

Theorem body_assign_other_saved_unstaged_memory_write_full[local]:
  body_inv tops ctx cenv cx /\ ~block_is_terminated sa /\
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  type_place_target env bt = SOME (Type ty) /\ target_pre cenv cx env bt mid /\
  expr_body_pre cenv cx env e es /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e)) (stmt_res_ok lctx) es /\
  ~is_word_type ty /\ ~is_word_type (lowered_value_type cenv e) /\
  vv_location vv <> SOME LocMemory /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  compile_get_target_ptr compile_expr cenv bt sm = (r,sb) /\
  unwrap_value cenv vv sb = (op,sc) /\
  (case FST (SND r) of
     SOME loc => compile_assign_value cenv (FST r) loc op
       (is_word_type (case SND (SND r) of SOME (ValPT t) => t
          | _ => lowered_value_type cenv e))
        (vv_location vv)
       (case SND (SND r) of SOME (ValPT t) => t
          | _ => lowered_value_type cenv e) (lowered_value_type cenv e)

       (type_memory_bytes cenv (case SND (SND r) of SOME (ValPT t) => t
          | _ => lowered_value_type cenv e)) sc = ((),sf)
   | NONE => emit_void INVALID [] sc = ((),sf)) /\
  fn_has_code sc sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!tail. eval_expr cx e (es with gas_obs := prefix ++ tail) =
     (INL tv,mid with gas_obs := tail)) /\
  read_result cx tv mid = (INL v,mid) /\
  (!tail. eval_target_place cx bt
     (mid with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
     (INL (MemoryPlace id path),ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    target_post H ctx func cenv cx mid sm sb s ee (PlaceR (MemoryPlace id path))
      (Type ty) r u /\
    expr_post H ctx func cenv cx e ee sa sc u ee v op z /\
    ghost_inv_at (DF H) lo d cenv cx ee Gz tnz z) /\
  (?entry w. lookup_scopes id ee.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL w) /\
  (!ann pp. vv = LocatedValue ann pp /\ ~is_word_type ann /\
     (pp.ptr_location = LocStorage \/ pp.ptr_location = LocTransient \/
      pp.ptr_location = LocCode) ==>
     vv_own cenv cx (post_value_type cenv e) sb sc ee (Value v)
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
  (~is_word_type (post_value_type cenv e) ==>
    vv_at cenv cx (post_value_type cenv e) sa sc ee tv
      (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
  (~is_word_type (post_value_type cenv e) ==>
    vv_at cenv cx (post_value_type cenv e) sa sm ee tv
      (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z \/
    vv_at cenv cx (post_value_type cenv e) sb sc ee tv
      (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
  ptr_val_ok cx (post_value_type cenv e) v op Gz tnz z /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op Gz z) /\
  (~is_word_type (post_value_type cenv e) ==>
   !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
          eval_operand op z = SOME w ==>
          type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
  ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
  z.vs_inst_idx = LENGTH sc.cs_current_insts /\
  alloca_history func z /\ return_buf_frame d cenv sc z /\
  s0.vs_alloca_next <= z.vs_alloca_next /\
  eval_operand (FST r) z = eval_operand (FST r) u /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) r Gz tnz z /\
  wb_frame cenv ee ee sb u z /\ wb_frame cenv es ee sa s0 z /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tnz /\
  alloca_frame cenv es sa s0 cenv ee z /\
  (!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa.cs_next_id /\
    (!name b cap. local_region cenv es.scopes s0 name b cap ==>
      a+n <= b \/ b+cap <= a) /\ a <= i /\ i < a+n /\ i IN tnz.t_mem ==>
    i IN tn0.t_mem) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (write_place cx (MemoryPlace id path) v) (ee,z,Gz,tnz)
    (\H res ef G tn t. ?ce.
      stmt_lands lctx sf res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sf /\ ce = cenv) /\
      cenv_top_ext cenv ce ef.scopes /\ stmt_state_rel H ctx func ce cx ef t /\
      storage_well_formed_on cx ef (FST H) /\ return_buf_frame d ce sf t /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d ce cx ef G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 ce ef t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off+sz <= b \/ b+sz' <= off) /\
        off <= i /\ i < off+sz /\ i IN tn.t_mem ==> i IN tn0.t_mem))
    (\H res ef gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ef with gas_obs := tail) res gt r) /\
      halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==>
        !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (qspec_then `H0` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `stmt_state_rel H0 ctx func cenv cx ee z` by fs[expr_post_def] >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `z.vs_alloca_next < dimword (:256)` by
    (drule stateRelProjTheory.stmt_state_rel_alloca_room >>
     disch_then (mp_then Any ACCEPT_TAC alloca_room_next_lt)) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp z)` by
    (drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  qabbrev_tac `gs = gas_explicit marks s.vs_gas_readings` >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `eval_target_place cx bt (mid with gas_obs := gs) = (INL (MemoryPlace id path),ee)` by
    (simp[Abbr `gs`] >>
     qpat_assum `!tail. eval_target_place _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `ee with gas_obs := [] = ee` (fn th => rewrite_tac[APPEND_NIL,th])) >>
  `expr_sim_inv cenv cx env ee` by
    (irule bodySimAugPlaceLoadTheory.aug_place_target_inv >>
     goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
     fs[target_pre_def,expr_sim_inv_gas_obs]) >>
  suspend "destination"
QED

Resume body_assign_other_saved_unstaged_memory_write_full[destination]:
  `ci_mono sa sm` by
    (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac
      (cj 1 ci_mono_compile_expr_sa) >> simp[]) >>
  `ci_mono sm sb` by
    (qspecl_then [`bt`,`cenv`,`sm`] mp_tac ci_mono_compile_get_target_ptr >> simp[]) >>
  `ci_mono sb sc` by
    (qspecl_then [`cenv`,`vv`,`sb`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  `local_ptrs_reserved cenv sb /\ local_ptrs_reserved cenv sc` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var]) >>
  qpat_assum `target_post H0 _ _ _ _ _ _ _ _ _ _ _ r u`
    (strip_assume_tac o REWRITE_RULE [target_post_def]) >>
  rename1 `eval_operand (FST r) u = SOME dw` >>
  `FST (SND r) = SOME LocMemory` by fs[place_ptr_rel_def] >>
  `eval_operand (FST r) z = SOME dw` by simp[] >>
  `place_ptr_rel cenv cx z (PlaceR (MemoryPlace id path)) dw
     (SOME LocMemory) (Type ty)` by
    (qpat_assum `place_ptr_rel _ _ u _ _ _ _`
       (qx_choosel_then [`p`,`sz`,`b`,`t0`,`tv0`,`k`,`dtv`,`t'`]
         (map_every assume_tac o CONJUNCTS) o REWRITE_RULE [place_ptr_rel_def]) >>
     simp[place_ptr_rel_def] >>
     `not_fresh_at sb p` by
       (qpat_assum `local_ptrs_reserved cenv sb`
         (mp_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
        disch_then (mp_tac o cj 2) >>
        disch_then (qspecl_then [`id`,`id`,`p`,`sz`,`sz`] mp_tac) >> simp[]) >>
     `lookup_var p z = SOME b` by drule_all_then ACCEPT_TAC wb_frame_vars >>
     fs[]) >>
  `compile_assign_value cenv (FST r) LocMemory op F (vv_location vv) ty
     (lowered_value_type cenv e) (type_memory_bytes cenv ty) sc = ((),sf)` by
    gs[value_type_place_def] >>
  `?ff. write_place cx (MemoryPlace id path) v ee = (INL (),ff)` by
    (Cases_on `write_place cx (MemoryPlace id path) v ee` >>
     rename1 `write_place _ _ _ ee = (wr,ff)` >>
     `stmt_res_ok lctx wr` by
       (drule gas_admissible_result >> disch_then irule >>
        qexistsl [`ff`,`prefix ++ gs`] >>
        drule read_result_gas_obs >> strip_tac >>
        simp[Once evaluate_def,bind_def]) >>
     metis_tac[placeRelayoutOutcomeTheory.memory_write_admissible_success]) >>
  `?dtv. evaluate_type (get_tenv cx) ty = SOME dtv` by fs[place_ptr_rel_def] >>
  `!i q entry t0. MemoryPlace id path = MemoryPlace i q /\
     lookup_scopes i ee.scopes = SOME entry /\ cenv.ce_var_type i = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (drule stmtSimAugAssignPlaceMemoryTheory.aug_place_store_entry_types >>
     metis_tac[]) >>
  `?name b len. local_region cenv ee.scopes z name b len /\
     b <= w2n dw /\ w2n dw + type_memory_size dtv <= b + len` by
    drule_all_then ACCEPT_TAC memory_place_live_region >>
  `b + len <= z.vs_alloca_next` by drule_all_then ACCEPT_TAC body_local_region_frontier >>
  `w2n dw + type_memory_size dtv <= z.vs_alloca_next` by decide_tac >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) =
     (INL v,mid with gas_obs := [])` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [APPEND_NIL])) >>
     drule read_result_gas_obs >> simp[bind_def]) >>
  `expr_body_pre cenv cx env e (es with gas_obs := prefix)` by simp[] >>
  `~block_is_terminated sc` by
    (`storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
       drule_then ACCEPT_TAC stmt_state_rel_vars_rels >>
     `eval_expr cx e (es with gas_obs := prefix) =
        (INL tv,mid with gas_obs := [])` by
       qpat_assum `!tail. eval_expr _ _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL])) >>
     `~block_is_terminated sm` by
       drule_all_then ACCEPT_TAC exprOpenMainTheory.compile_expr_open_general >>
     `~block_is_terminated sb` by
       drule_all_then ACCEPT_TAC placeRelayoutOpenTheory.compile_get_target_ptr_endpoint_open >>
     drule_all_then ACCEPT_TAC exprOpenTerminalsTheory.unwrap_value_open) >>
  drule_all_then strip_assume_tac
    (SIMP_RULE (srw_ss() ++ ETA_ss) [] immutable_rhs_physical_typed) >>
  `type_widens_to env.type_defs (expr_type e) ty /\
   assignable_type env.type_defs ty` by
    (drule body_assign_empty_target_typing >> strip_tac >>
     `dty = ty` by fs[] >>
     metis_tac[vyperTypeArgFitsTheory.type_widens_to_assignable_type]) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
  `0 < type_memory_size dtv` by
    (`0 < type_slot_size dtv` by
       (mp_tac (Q.SPECL [`get_tenv cx`,`ty`,`dtv`] assignable_type_slot_size_pos) >> fs[]) >>
     simp[valueEncodingPropsTheory.type_memory_size_slots]) >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty` by
    drule_all_then ACCEPT_TAC immutable_rhs_physical_widens >>
  `value_has_type dtv v` by
    (drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> simp[]) >>
  `?sw. eval_operand op z = SOME sw` by fs[expr_post_def,expr_val_rel_def] >>
  `~is_word_type (post_value_type cenv e)` by
    metis_tac[immutable_rhs_post_physical_classify,is_bytestring_word_type] >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) (post_value_type cenv e)` by
    drule_then ACCEPT_TAC immutable_rhs_physical_post_widens >>
  `?ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv` by
    (drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >>
     strip_tac >> metis_tac[]) >>
  `!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==> val_in_memory stv v (w2n sw) mem` by
    (`!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==>
       val_in_memory ptv v (w2n sw) mem` by fs[ptr_val_ok_def,ptr_mem_ok_def] >>
     qpat_assum `expr_body_pre cenv cx env e es`
       (mp_then Any (DISJ_CASES_THEN2 assume_tac strip_assume_tac)
          immutable_rhs_post_physical_classify)
     >- gvs[] >>
     metis_tac[bytestring_val_in_memory_transfer]) >>
  qsuff_tac `?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
           (z,Gz,tnz) [] (OK t,Gf,tf)) /\
    ~block_is_terminated sf /\ ~t.vs_halted /\
    t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    z.vs_alloca_next <= t.vs_alloca_next /\ return_buf_frame d cenv sf t /\
    (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x z /\
      FLOOKUP Gf x = FLOOKUP Gz x /\ op_taint tf (Var x) = op_taint tnz (Var x)) /\
    (!aid pair. FLOOKUP z.vs_allocas aid = SOME pair ==> FLOOKUP t.vs_allocas aid = SOME pair) /\
    alloca_frame cenv ee sc z cenv ff t /\
    (!aid off sz i. FLOOKUP z.vs_allocas aid = SOME (off,sz) /\ aid < sc.cs_next_id /\
       (!n a k. local_region cenv ee.scopes z n a k ==> off+sz <= a \/ a+k <= off) /\
       off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tnz.t_mem) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ff t /\ ghost_inv_at (DF H) lo d cenv cx ff Gf tf t)`
  >- suspend "land_write" >>
  Cases_on `~is_bytestring_type ty /\
    ~(ty = lowered_value_type cenv e \/ tuple_memory_layout_eq ty (lowered_value_type cenv e))`
  >- (`compile_store_memory_typed cenv (FST r) ty op (lowered_value_type cenv e) sc = ((),sf)` by
        (qpat_assum `compile_assign_value _ _ LocMemory _ F _ _ _ _ _ = _`
           (mp_tac o REWRITE_RULE [compile_assign_value_def]) >>
         fs[compile_store_memory_def]) >>
      suspend "typed_memory") >>
  qsuff_tac `?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (z,Gz,tnz) [] (OK t,Gf,tf)) /\
    typed_copy_effect ctx func sc sf z t (w2n dw) (type_memory_size dtv) /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==> val_in_memory dtv v (w2n dw) m) /\
    (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x z /\
      FLOOKUP Gf x = FLOOKUP Gz x /\ op_taint tf (Var x) = op_taint tnz (Var x)) /\
    tf.t_stor = tnz.t_stor /\ tf.t_trans = tnz.t_trans /\ tf.t_imm = tnz.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
      (i IN tf.t_mem <=> i IN tnz.t_mem)) /\
    lo <= w2n dw /\ ~block_is_terminated sf /\ sc.cs_next_var <= sf.cs_next_var`
  >- suspend "effect_land" >>
  Cases_on `is_bytestring_type ty`
  >- suspend "bytes_write" >>
  suspend "direct_memory"
QED

Resume body_assign_other_saved_unstaged_memory_write_full[land_write]:
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS)) >>
  `!tail. write_place cx (MemoryPlace id path) v (ee with gas_obs := tail) =
      (INL (),ff with gas_obs := tail)` by
    drule_all_then ACCEPT_TAC placeRelayoutFragTheory.place_pointer_write_gas_obs >>
  `ff.storage_trace = ee.storage_trace /\ ff.gas_obs = []` by
    (drule write_memory_place_entry_update >> strip_tac >>
     qpat_assum `ff = ee with scopes := _` (once_rewrite_tac o single) >> simp[]) >>
  `ci_mono sa sc` by metis_tac[ci_mono_trans] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sa` >> fs[ci_mono_def]) >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl [`Gf`,`ff`,`INL ()`,`t`,`tf`] >>
  simp[NoAsms] >> conj_tac >- simp[] >>
  qpat_assum `ff.storage_trace = ee.storage_trace` (once_rewrite_tac o single) >>
  qx_gen_tac `H` >> disch_tac >>
  `storage_well_formed_on cx ff (FST H)` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> target_post _ _ _ _ _ _ _ _ _ _ _ _ r u /\ _`
       (drule_then strip_assume_tac) >>
     `storage_well_formed_on cx ee (FST H)` by fs[expr_post_def] >>
     `storage_well_formed_on cx ff (FST H) = storage_well_formed_on cx ee (FST H)`
       suffices_by simp[] >>
     irule storage_well_formed_on_backends >>
     drule write_memory_place_entry_update >> strip_tac >>
     qpat_assum `ff = ee with scopes := _` (once_rewrite_tac o single) >> simp[]) >>
  `ff with gas_obs := [] = ff` by simp[evaluation_state_component_equality] >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w` by
    (rpt strip_tac >> `lookup_var x z = SOME w` by drule_all_then ACCEPT_TAC wb_frame_vars >>
     `not_fresh_at sc x` by simp[] >>
     qpat_assum `!x. not_fresh_at sc x ==> lookup_var x t = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  qpat_assum `wb_frame cenv es ee sa s0 z`
    (assume_tac o cj 2 o REWRITE_RULE [wb_frame_def]) >>
  `!aid pair. FLOOKUP s0.vs_allocas aid = SOME pair ==> FLOOKUP t.vs_allocas aid = SOME pair` by
    (rpt strip_tac >> `FLOOKUP z.vs_allocas aid = SOME pair` by
       (qpat_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b`
         (drule_then ACCEPT_TAC)) >>
     qpat_assum `!aid b. FLOOKUP z.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b`
       (drule_then ACCEPT_TAC)) >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tnz`
    (assume_tac o cj 1 o REWRITE_RULE [ghost_kept_at_def]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
       op_taint tf (Var x) = op_taint tn0 (Var x)` by
    (gen_tac >> disch_tac >> `not_fresh_at sc x` by simp[] >>
     qpat_assum `!x. not_fresh_at sc x ==> lookup_var x t = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP Gz x = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv ff t` by
    (irule alloca_frame_trans >> qexistsl [`cenv`,`ee`,`z`,`sc`] >> simp[] >> fs[ci_mono_def]) >>
  simp[stmt_lands_def,cenv_top_ext_refl] >> rpt strip_tac >>
  qpat_assum `alloca_frame cenv es sa s0 cenv ee z`
    (drule_all_then strip_assume_tac o REWRITE_RULE [alloca_frame_def]) >>
  `aid < sc.cs_next_id` by fs[ci_mono_def] >>
  `i IN tnz.t_mem` by
    (qpat_assum `!a b k j. FLOOKUP z.vs_allocas a = SOME (b,k) /\ _ ==> j IN tnz.t_mem`
      (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
     simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  qpat_assum `!a b k j. FLOOKUP s0.vs_allocas a = SOME (b,k) /\ _ ==> j IN tn0.t_mem`
    (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> simp[]
QED

Resume body_assign_other_saved_unstaged_memory_write_full[bytes_write]:
  `compile_store_bytestring op (FST r) sc = ((),sf)` by
    ((qpat_assum `compile_assign_value cenv _ LocMemory op F _ _ _ _ sc = _` mp_tac >>
     simp[compile_assign_value_def,compile_store_memory_def] >> (gvs[compile_assign_value_def, compile_store_memory_def]))) >>
  `is_bytestring_type (lowered_value_type cenv e)` by
    drule_all_then ACCEPT_TAC typedMemoryCopyTheory.typed_copy_bytestring_source >>
  `0 < type_memory_bytes cenv (lowered_value_type cenv e)` by
    simp[bytestring_memory_bytes_positive] >>
  `op_taint tnz op = {}` by fs[ptr_val_ok_def] >>
  `?xs. op = Var xs /\ ptr_covers Gz tnz xs z (type_memory_size stv)` by
    (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
     simp[] >> qexistsl [`cenv`,`e`] >> simp[]) >>
  `type_memory_size stv <> 0` by decide_tac >>
  `w2n sw + type_memory_size stv <= z.vs_alloca_next` by
    (qpat_assum `~is_word_type (post_value_type cenv e) ==> !rt w. _`
       (drule_then (qspecl_then [`stv`,`sw`] mp_tac)) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (DISJ_CASES_THEN2 (fn th => fs[th]) ACCEPT_TAC)) >>
  `sm.cs_next_var <= sb.cs_next_var` by fs[ci_mono_def] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sm` >> simp[] >> first_x_assum irule >> simp[]) >>
  `not_fresh_at sc xs` by
    (drule exprOperandVarTheory.compiler_unwrap_value_var >>
     disch_then (qspec_then `xs` mp_tac) >>
     Cases_on `vv` >> fs[vv_operand_def]) >>
  `?xd. FST r = Var xd /\ ptr_covers Gz tnz xd z (type_memory_size dtv)` by
    (qpat_assum `place_ptr_rel cenv cx z _ dw _ _`
       (strip_assume_tac o REWRITE_RULE [place_ptr_rel_def]) >>
     qpat_x_assum `?entry w. lookup_scopes id ee.scopes = SOME entry /\ _`
       strip_assume_tac >>
     qpat_assum `ghost_inv_at (DF H0) lo d cenv cx ee Gz tnz z`
       (drule_all_then strip_assume_tac o CONJUNCT1 o REWRITE_RULE [ghost_inv_at_def]) >>
     `op_taint tnz (FST r) = {} /\ op_prov Gz (FST r) = FLOOKUP Gz p` by
       fs[target_ptr_ok_def] >>
     qpat_assum `stmt_state_rel H0 ctx func cenv cx ee z`
       (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
     qpat_assum `local_ptrs_rel func cenv ee.scopes z`
       (drule_all_then strip_assume_tac o CONJUNCT1 o REWRITE_RULE [local_ptrs_rel_def]) >>
     drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >>
     fs[] >>
     `w2n b' + k < dimword (:256) /\ k < dimword (:256)` by gvs[] >>
     `w2n (b' + n2w k) = w2n b' + k` by
       (`w2n (b' + n2w k) = w2n b' + w2n ((n2w k):bytes32)` suffices_by simp[] >>
        irule w2n_add_2 >> simp[]) >>
     Cases_on `FST r` >> gvs[op_prov_def, ptr_covers_def,eval_operand_def]) >>
  `not_fresh_at sc xd` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `sb` >>
     fs[ci_mono_def,target_ptr_ok_def]) >>
  `lookup_var xs z = SOME sw /\ lookup_var xd z = SOME dw` by fs[eval_operand_def] >>
  `compile_store_bytestring (Var xs) (Var xd) sc = ((),sf)` by fs[] >>
  drule_all body_assign_saved_bytestring_copy_effect >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  `type_memory_bytes cenv ty = type_memory_size dtv` by
    (`?base. ty = BaseT base` by
       (qpat_assum `is_bytestring_type ty` mp_tac >> POP_ASSUM_LIST kall_tac >>
        Cases_on `ty` >> simp[is_bytestring_type_def]) >>
     simp[] >> irule typeLayoutPropsTheory.type_memory_bytes_base_evaluated >>
     qexists `get_tenv cx` >> fs[]) >>
  `0 < type_memory_size dtv` by metis_tac[bytestring_memory_bytes_positive] >>
  `0 < len` by decide_tac >>
  `lo <= b` by
    (qpat_assum `!H. dead_lo_ok H (DF H) lo cenv cx`
       (qspec_then `H0` assume_tac) >>
     drule_all_then ACCEPT_TAC body_full_local_region_lower_bound) >>
  `lo <= w2n dw` by decide_tac >>
  `~block_is_terminated sf` by
    (irule stmtSimDeclMemTheory.compile_assign_value_memory_widen_open >>
     goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`)) >> simp[]) >>
  `sc.cs_next_var <= sf.cs_next_var` by
    (drule_then strip_assume_tac buffer_store_bytestring_shape >> simp[]) >>
  qexistsl [`t`,`Gf`,`tf`] >> simp[]
QED

Resume body_assign_other_saved_unstaged_memory_write_full[effect_land]:
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS)) >>
  drule_then strip_assume_tac typed_copy_effect_endpoint >>
  `t.vs_alloca_next = z.vs_alloca_next /\ t.vs_allocas = z.vs_allocas /\
   t.vs_initial_fmp = z.vs_initial_fmp /\ t.vs_fmp = z.vs_fmp` by
    (drule typed_copy_effect_record >> simp[venom_state_component_equality]) >>
  `return_buf_frame d cenv sf t` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`,`z`,`sc`] >> simp[] >>
     rpt strip_tac >> drule_all_then ACCEPT_TAC typed_copy_effect_lookup) >>
  `alloca_history func t` by
    (irule body_full_path_alloca_history >>
     qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
       (qspec_then `DF H0` (irule_at Any)) >> simp[] >>
     qpat_assum `stmt_state_rel H0 ctx func cenv cx ee z`
       (mp_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (strip_tac >> `allocas_below_fmp z` by simp[] >>
     simp[allocas_below_fmp_def] >>
     qpat_assum `allocas_below_fmp z`
       (ACCEPT_TAC o SIMP_RULE (srw_ss()) [allocas_below_fmp_def])) >>
  `ci_mono sa sc` by metis_tac[ci_mono_trans] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sa` >> fs[ci_mono_def]) >>
  `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sc x` by metis_tac[] >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sc x` by
    (qpat_assum `ret_pc_ok cenv sa s0` (strip_assume_tac o REWRITE_RULE [ret_pc_ok_def]) >>
     rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sc x` irule >>
     qpat_assum `!x sz. cenv.ce_return_pc = _ ==> _` (drule_then strip_assume_tac) >>
     first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at sc x ==> FLOOKUP Gf x = FLOOKUP Gz x /\
         op_taint tf (Var x) = op_taint tnz (Var x)` by
    (rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> simp[]) >>
  drule_all_then strip_assume_tac body_assign_memory_place_store_post >>
  qexistsl [`t`,`Gf`,`tf`] >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `stmt_state_rel H0 ctx func cenv cx ee z` kall_tac >>
  qpat_x_assum `ghost_inv_at (DF H0) lo d cenv cx ee Gz tnz z` kall_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `stmt_state_rel H ctx func cenv cx ee z` by fs[expr_post_def] >>
  drule_all_then strip_assume_tac body_assign_memory_place_store_post >> simp[]
QED

Resume body_assign_other_saved_unstaged_memory_write_full[direct_memory]:
  `compile_copy_memory (FST r) op (type_memory_bytes cenv ty) sc = ((),sf)` by
    (qpat_assum `compile_assign_value _ _ LocMemory _ F _ _ _ _ _ = _`
       (mp_tac o REWRITE_RULE [compile_assign_value_def]) >>
     Cases_on `ty = lowered_value_type cenv e` >- simp[compile_store_memory_def] >>
     `tuple_memory_layout_eq ty (lowered_value_type cenv e)` by metis_tac[] >>
     simp[compile_store_memory_def]) >>
  `!t tv. evaluate_type (get_tenv cx) t = SOME tv ==>
      type_memory_bytes cenv t = type_memory_size tv` by
    (rpt strip_tac >> irule typed_copy_memory_size >> qexists `get_tenv cx` >>
     fs[expr_sim_inv_def] >> metis_tac[]) >>
  `type_memory_size dtv = type_memory_size stv` by
    (Cases_on `ty = lowered_value_type cenv e` >- metis_tac[SOME_11] >>
     `tuple_memory_layout_eq ty (lowered_value_type cenv e)` by metis_tac[] >>
     metis_tac[memoryLayoutDefsTheory.tuple_memory_layout_eq_bytes]) >>
  `!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==>
      val_in_memory dtv v (w2n sw) mem` by
    (Cases_on `ty = lowered_value_type cenv e`
     >- metis_tac[SOME_11] >>
     `tuple_memory_layout_eq ty (lowered_value_type cenv e)` by metis_tac[] >>
     `punnable cenv (lowered_value_type cenv e) ty` by
       (drule exprSimIfExpWidenedAggregateTheory.tuple_memory_layout_eq_same_layout >>
        simp[same_memory_layout_def]) >>
     `arg_type_fits (lowered_value_type cenv e) ty` by
       (qpat_assum `type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty` mp_tac >>
        qpat_assum `ty <> lowered_value_type cenv e` mp_tac >>
        POP_ASSUM_LIST kall_tac >> rewrite_tac[type_widens_to_def] >> metis_tac[]) >>
     rpt strip_tac >>
     drule_then (mp_tac o CONJUNCT1) exprSimLayoutTransportTheory.compatible_layout_memory >>
     disch_then drule_all >>
     disch_then (qspecl_then [`v`,`w2n sw`,`mem`] (irule o iffLR)) >>
     first_x_assum (drule_then ACCEPT_TAC)) >>
  `compile_copy_memory (FST r) op (type_memory_size dtv) sc = ((),sf)` by metis_tac[] >>
  `val_wf dtv v` by simp[cj 1 value_has_type_val_wf] >>
  `val_footprint dtv v <= type_memory_size dtv` by simp[exprSimPropsTheory.val_footprint_le] >>
  suspend "direct_positive"
QED
Resume body_assign_other_saved_unstaged_memory_write_full[direct_positive]:
  `0 < type_memory_bytes cenv (lowered_value_type cenv e)` by decide_tac >>
  `op_taint tnz op = {}` by fs[ptr_val_ok_def] >>
  `?xs. op = Var xs /\ ptr_covers Gz tnz xs z (type_memory_size stv)` by
    (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
     simp[] >> qexistsl [`cenv`,`e`] >> simp[]) >>
  `w2n sw + type_memory_size stv <= z.vs_alloca_next` by
    (qpat_assum `~is_word_type (post_value_type cenv e) ==> !rt w. _`
       (drule_then (qspecl_then [`stv`,`sw`] mp_tac)) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     decide_tac) >>
  `sm.cs_next_var <= sb.cs_next_var` by fs[ci_mono_def] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sm` >> simp[] >> first_x_assum irule >> simp[]) >>
  `not_fresh_at sc xs` by
    (drule exprOperandVarTheory.compiler_unwrap_value_var >>
     disch_then (qspec_then `xs` mp_tac) >>
     Cases_on `vv` >> fs[vv_operand_def]) >>
  `?xd. FST r = Var xd /\ ptr_covers Gz tnz xd z (type_memory_size dtv)` by
    (qpat_assum `place_ptr_rel cenv cx z _ dw _ _`
       (strip_assume_tac o REWRITE_RULE [place_ptr_rel_def]) >>
     qpat_x_assum `?entry w. lookup_scopes id ee.scopes = SOME entry /\ _`
       strip_assume_tac >>
     qpat_assum `ghost_inv_at (DF H0) lo d cenv cx ee Gz tnz z`
       (drule_all_then strip_assume_tac o CONJUNCT1 o REWRITE_RULE [ghost_inv_at_def]) >>
     `op_taint tnz (FST r) = {} /\ op_prov Gz (FST r) = FLOOKUP Gz p` by
       fs[target_ptr_ok_def] >>
     qpat_assum `stmt_state_rel H0 ctx func cenv cx ee z`
       (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
     qpat_assum `local_ptrs_rel func cenv ee.scopes z`
       (drule_all_then strip_assume_tac o CONJUNCT1 o REWRITE_RULE [local_ptrs_rel_def]) >>
     drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >>
     fs[] >>
     `w2n b' + k < dimword (:256) /\ k < dimword (:256)` by gvs[] >>
     `w2n (b' + n2w k) = w2n b' + k` by
       (`w2n (b' + n2w k) = w2n b' + w2n ((n2w k):bytes32)` suffices_by simp[] >>
        irule w2n_add_2 >> simp[]) >>
     qpat_assum `ptr_covers Gz tnz p z sz` (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
     qpat_assum `op_taint tnz (FST r) = {}` mp_tac >>
     qpat_assum `op_prov Gz (FST r) = FLOOKUP Gz p` mp_tac >>
     qpat_assum `eval_operand (FST r) z = SOME _` mp_tac >>
     qpat_assum `lookup_var p z = SOME w'` mp_tac >>
     qpat_assum `w' = b'` mp_tac >>
     qpat_assum `w2n (b' + n2w k) = w2n b' + k` mp_tac >>
     qpat_assum `k + type_memory_size tv' <= type_memory_size tv0` mp_tac >>
     qpat_assum `type_memory_size entry.type <= sz` mp_tac >>
     qpat_assum `tv0 = entry.type` mp_tac >>
     qpat_assum `tv' = dtv` mp_tac >>
     qpat_assum `type_memory_size dtv = type_memory_size stv` mp_tac >>
     POP_ASSUM_LIST kall_tac >>
     Cases_on `FST r` >> simp[op_prov_def,ptr_covers_def,eval_operand_def] >>
     rpt strip_tac >> gvs[] >> decide_tac) >>
  `not_fresh_at sc xd` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `sb` >>
     fs[ci_mono_def,target_ptr_ok_def]) >>
  `lookup_var xs z = SOME sw /\ lookup_var xd z = SOME dw` by fs[eval_operand_def] >>
  `compile_copy_memory (Var xd) (Var xs) (type_memory_size dtv) sc = ((),sf)` by fs[] >>
  `w2n sw + type_memory_size dtv < dimword(:256) /\
   w2n dw + type_memory_size dtv < dimword(:256)` by decide_tac >>
  `0 < type_memory_size dtv /\
   w2n sw + type_memory_size dtv <= z.vs_alloca_next` by decide_tac >>
  `ptr_covers Gz tnz xs z (type_memory_size dtv)` by simp[] >>
  `type_memory_size dtv = type_memory_size dtv` by simp[] >>
  drule_all body_assign_local_memory_flat_copy_effect >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  `~block_is_terminated sf` by
    (Cases_on `type_memory_size dtv` >- fs[] >>
     qpat_assum `compile_copy_memory (Var xd) (Var xs) (SUC _) sc = _` mp_tac >>
     rewrite_tac[compile_copy_memory_def] >>
     disch_then (mp_tac o MATCH_MP exprOpenPrimitivesTheory.emit_void_terminated) >>
     simp[is_terminator_def]) >>
  `sc.cs_next_var = sf.cs_next_var` by metis_tac[buffer_copy_memory_shape] >>
  `0 < len` by decide_tac >>
  `lo <= b` by
    (qpat_assum `!H. dead_lo_ok H (DF H) lo cenv cx`
       (qspec_then `H0` assume_tac) >>
     drule_all_then ACCEPT_TAC body_full_local_region_lower_bound) >>
  `lo <= w2n dw` by decide_tac >>
  qexistsl [`t`,`Gf`,`tf`] >> simp[]
QED

Resume body_assign_other_saved_unstaged_memory_write_full[typed_memory]:
  `~is_bytestring_type (lowered_value_type cenv e)` by
    metis_tac[typedMemoryCopyTheory.type_widens_from_bytestring] >>
  `post_value_type cenv e = lowered_value_type cenv e` by
    metis_tac[immutable_rhs_post_physical_classify] >>
  `0 < type_memory_size stv` by
    (mp_tac (Q.INST [`tenv` |-> `get_tenv cx`,`sty` |-> `lowered_value_type cenv e`,
        `dty` |-> `ty`,`stv` |-> `stv`,`dtv` |-> `dtv`]
       exprSimAggregateChildrenTheory.widening_zero_memory_size) >>
     (impl_tac >- simp[]) >> decide_tac) >>
  `0 < type_memory_bytes cenv (lowered_value_type cenv e)` by decide_tac >>
  `val_wf stv v /\ val_wf dtv v` by simp[value_has_type_val_wf] >>
  `type_memory_bytes cenv ty = type_memory_size dtv` by
    (irule typed_copy_memory_size >> qexists `get_tenv cx` >>
     fs[expr_sim_inv_def] >> metis_tac[]) >>
  drule_all_then strip_assume_tac immutableDeployAssignRangesTheory.immutable_assign_copy_metadata >>
  `op_taint tnz op = {}` by fs[ptr_val_ok_def] >>
  `?xs. op = Var xs /\ ptr_covers Gz tnz xs z (type_memory_size stv)` by
    (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
     simp[] >> qexistsl [`cenv`,`e`] >> simp[]) >>
  `w2n sw + type_memory_size stv <= z.vs_alloca_next` by
    (qpat_assum `~is_word_type (post_value_type cenv e) ==> !rt w. _`
       (drule_then (qspecl_then [`stv`,`sw`] mp_tac)) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> decide_tac) >>
  `w2n sw + type_memory_size stv < dimword (:256) /\
   type_memory_size stv < dimword (:256)` by decide_tac >>
  `sm.cs_next_var <= sb.cs_next_var` by fs[ci_mono_def] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sm` >> simp[] >> first_x_assum irule >> simp[]) >>
  `not_fresh_at sc xs` by
    (drule exprOperandVarTheory.compiler_unwrap_value_var >>
     disch_then (qspec_then `xs` mp_tac) >> Cases_on `vv` >> fs[vv_operand_def]) >>
  `expr_val_at cenv cx (lowered_value_type cenv e) sa sc ee v op z` by
    (irule abiEncodeArgsSimTheory.abi_args_expr_post_lowered_at >>
     conj_tac >- (strip_tac >> qexists `stv` >> simp[]) >>
     conj_tac >- (qexistsl [`env`,`es`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  `0 < len` by decide_tac >>
  `lo <= w2n dw` by
    (qpat_assum `!H. dead_lo_ok H (DF H) lo cenv cx`
       (qspec_then `H0` assume_tac) >>
     `lo <= b` by drule_all_then ACCEPT_TAC body_full_local_region_lower_bound >> decide_tac) >>
  suspend "typed_separation"
QED

Resume body_assign_other_saved_unstaged_memory_write_full[typed_separation]:
  `lowered_value_type cenv e <> ty` by (CCONTR_TAC >> fs[]) >>
  `w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n sw` by
    (mp_tac (Q.INST
       [`sty` |-> `lowered_value_type cenv e`, `dty` |-> `ty`,
        `sb` |-> `sc`, `s` |-> `z`, `w` |-> `dw`,
        `p` |-> `MemoryPlace id path`, `H` |-> `H0`]
       (horizonTypeLib.at_horizon_named "H"
          assignPlaceProvenanceTheory.nonbytes_expr_val_at_memory_separation)) >>
     (impl_tac >- simp[]) >> decide_tac) >>
  `?xd. FST r = Var xd` by
    (qpat_assum `place_ptr_rel cenv cx z _ dw _ _`
       (strip_assume_tac o REWRITE_RULE [place_ptr_rel_def]) >>
     qpat_x_assum `?entry w. lookup_scopes id ee.scopes = SOME entry /\ _`
       strip_assume_tac >>
     qpat_assum `ghost_inv_at (DF H0) lo d cenv cx ee Gz tnz z`
       (drule_all_then strip_assume_tac o CONJUNCT1 o REWRITE_RULE [ghost_inv_at_def]) >>
     `op_prov Gz (FST r) = FLOOKUP Gz p` by fs[target_ptr_ok_def] >>
     qpat_assum `ptr_covers Gz tnz p z sz`
        (mp_tac o CONJUNCT2 o REWRITE_RULE [ptr_covers_def]) >>
     Cases_on `FST r`
     >- (gvs[op_prov_def] >> metis_tac[])
     >- simp[]
     >- (gvs[op_prov_def] >> metis_tac[])) >>
  `not_fresh_at sc xd` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `sb` >>
     fs[ci_mono_def,target_ptr_ok_def]) >>
  `r = (Var xd,SOME LocMemory,SOME (ValPT ty))` by
    (PairCases_on `r` >> gvs[value_type_place_def]) >>
  `lookup_var xd z = SOME dw /\ lookup_var xs z = SOME sw` by fs[eval_operand_def] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sa` >> fs[ci_mono_def] >> decide_tac) >>
  `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sc x` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sc x` irule >>
     simp[]) >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sc x` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sc x` irule >>
     fs[ret_pc_ok_def]) >>
  `~block_is_terminated sf` by
    drule_all_then ACCEPT_TAC exprOpenCopiesTheory.compile_store_memory_typed_open >>
  `compile_assign_value cenv (Var xd) LocMemory (Var xs) F (vv_location vv)
     ty (lowered_value_type cenv e) (type_memory_bytes cenv ty) sc = ((),sf)` by
    (qpat_assum `FST r = Var xd` (fn dst_eq =>
       qpat_assum `op = Var xs` (fn src_eq =>
         qpat_assum `compile_assign_value cenv (FST r) LocMemory op F _ _ _ _ sc = _`
           (ACCEPT_TAC o REWRITE_RULE [dst_eq,src_eq])))) >>
  `target_ptr_ok cenv (PlaceR (MemoryPlace id path))
     (Var xd,SOME LocMemory,SOME (ValPT ty)) Gz tnz z` by
    (qpat_assum `r = (Var xd,SOME LocMemory,SOME (ValPT ty))` (fn r_eq =>
       qpat_assum `target_ptr_ok _ _ r Gz tnz z` (ACCEPT_TAC o REWRITE_RULE [r_eq]))) >>
  qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
  mp_tac (Q.INST
    [`loc` |-> `vv_location vv`, `dty` |-> `ty`,
     `sty` |-> `lowered_value_type cenv e`, `bytes` |-> `type_memory_bytes cenv ty`,
     `sa` |-> `sc`, `sb` |-> `sf`, `start` |-> `sa`,
     `s` |-> `z`, `p` |-> `MemoryPlace id path`,
     `G` |-> `Gz`, `tn` |-> `tnz`, `D0` |-> `DF H0`, `d0` |-> `d`,
     `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (horizonTypeLib.at_horizon_named "H0" body_assign_memory_place_joint)) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]])) >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`t`,`Gf`,`tf`] >> simp[] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!H D d. stmt_state_rel H ctx func cenv cx ee z /\ _ ==> _`
    (qspecl_then [`H`, `DF H`, `d`] mp_tac) >>
  fs[expr_post_def]
QED

Finalise body_assign_other_saved_unstaged_memory_write_full[local]

Theorem body_assign_other_nonempty_target_full[local]:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    struct_args_unique tops /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              is_word_type ty) /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              ~is_word_type ty /\
              (expr_type e = ty \/ lowered_value_type cenv e = ty \/
               is_bytestring_type ty \/
               has_length_word (expr_type e) /\ is_empty_value_expr e)) /\
    ~(?nsid dty. t = TopLevelNameTarget nsid /\
          supported_scalar_target tops nsid /\
          type_place_target env t = SOME (Type dty) /\ is_word_type dty) /\
    ~(?nsid mut ty slot.
        t = TopLevelNameTarget nsid /\
        supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
        (mut = Storage \/ mut = Transient) /\
        ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
        ~is_bytestring_type ty /\
        0 < type_memory_bytes cenv ty /\ expr_type e = ty /\
        lowered_value_type cenv e = expr_type e) /\
    ~(?id fld sid fty.
        t = AttributeTarget (NameTarget id) fld /\
        FLOOKUP env.var_types id = SOME (StructT sid) /\
        attribute_type env.type_defs (StructT sid) fld = SOME fty /\
        is_word_type fty) /\
    ~(?nsid fld fty.
        t = AttributeTarget (TopLevelNameTarget nsid) fld /\
        supported_storage_field_write tops nsid fld /\
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    ~immutable_root cx t ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e)))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule body_assign_other_value_rhs_bind >>
  rpt (CHANGED_TAC (first_assum (irule_at Any))) >>
  asm_rewrite_tac[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `mid with gas_obs := [] = mid` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `read_result cx tv mid = (INL v,mid)` by
    (qpat_assum `!tail. read_result cx tv (mid with gas_obs := tail) = _`
       (qspec_then `[]` mp_tac) >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
                vv_post H ctx func cenv cx e es sa sr s0 mid tv vv0 s /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  `return_buf_frame d cenv sr s` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`,`s0`,`sa`] >>
     fs[ci_mono_def, vv_post_def]) >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,mid)` by
    (qpat_assum `!tail. eval_expr cx e _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => simp[NoAsms, listTheory.APPEND_NIL, th])) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\
       vv_post H ctx func cenv cx e es sa sr s0 mid tv vv0 s /\
       ghost_inv_at (DF H) lo d cenv cx mid G tn s` by
    (rpt gen_tac >> strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       (drule_at (Pos (el 2)) valid_horizon_frame >>
        simp[cj 5 evaluate_storage_trace_frame]) >>
     metis_tac[]) >>
  drule body_assign_saved_target_type >> strip_tac >>
  `type_widens_to env.type_defs (expr_type e) ty` by
    (drule body_assign_empty_target_typing >> simp[]) >>
  drule_all immutable_rhs_physical_widens >> strip_tac >>
  `is_word_type ty ==> expr_type e = ty /\
      lowered_value_type cenv e = ty /\ post_value_type cenv e = ty` by
    (strip_tac >> imp_res_tac compileEnvTheory.type_widens_to_word >> simp[]) >>
  `(do pv <- eval_expr cx e; read_result cx pv od)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    simp[bind_def] >>
  `expr_body_pre cenv cx env e
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all immutable_rhs_physical_typed >> strip_tac >>
  drule_all type_widens_to_value_has_type >> strip_tac >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`well_typed_expr env e` by
       qpat_assum `expr_body_pre cenv cx env e es`
         (ACCEPT_TAC o cj 2 o MATCH_MP expr_body_pre_static_facts) >>
     irule body_const_cells_agree_expr_read >>
     qexistsl_tac [`e`, `INL v`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`] >>
     simp[] >>
     qpat_assum `(do pv <- eval_expr cx e; read_result cx pv od) _ = (INL v,mid)`
       (ACCEPT_TAC o CONV_RULE (DEPTH_CONV ETA_CONV))) >>
  `target_pre cenv cx env t mid` by
    (mp_tac body_assign_saved_target_pre >> simp[]) >>
  `target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx env t mid` by
    (irule body_target_place_sim_full >> simp[] >> qexists `tops` >> simp[]) >>
  `assign_target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx env t mid` by
    (irule assign_target_place_sim_full >> simp[]) >>
  `target_indices_pre cenv cx env t` by fs[target_pre_def] >>
  `gas_admissible (eval_target_place cx t) target_place_res_ok mid` by
    (mp_tac (Q.INST [`prefix` |-> `gas_explicit marks s0.vs_gas_readings`]
       body_assign_saved_target_admissible) >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  `(cenv.ce_is_ctor /\ vv_location vv0 = SOME LocCode) ==>
     !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
       eval_operand (vv_operand vv0) s = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v (w2n w) mem)` by
    (strip_tac >> qpat_x_assum `_ ==> ?val. read_result cx tv mid = _ /\ _` mp_tac >> simp[]) >>
  qpat_x_assum `(expr_can_mutate _ _ /\ _) \/ _`
    (DISJ_CASES_THEN (map_every assume_tac o CONJUNCTS))
  >- (irule body_assign_other_snapshot_target_bind >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      qexistsl [`G0`,`cenv`,`d`,`e`,`env`,`es`,`op`,`tv`,`r`,`marks`,
                `s0`,`sa`,`shadow_func`,`ts`,`tt`,`sr`,`vv`,`ss`,`st`,
                `su`,`tn0`,`tops`,`ty`,`vv0`] >> simp[] >>
      suspend "snapshot_write") >>
  qpat_x_assum `ss = sr` SUBST_ALL_TAC >>
  qpat_x_assum `ts = tr` SUBST_ALL_TAC >>
  qpat_x_assum `vv = vv0` SUBST_ALL_TAC >>
  `runtime_consistent env cx es /\ functions_well_typed cx` by
    fs[expr_sim_inv_def, runtime_consistent_def] >>
  `!x. vv_operand vv0 = Var x ==> not_fresh_at sr x` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var] >>
  `!l. vv_operand vv0 <> Label l` by
    (drule_all assignPlaceOperandFactsTheory.assign_place_operand_not_label >> simp[]) >>
  irule body_assign_other_saved_target_bind >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`G0`,`bindings`,`cenv`,`d`,`e`,`env`,`env'`,`es`,`lctx`,`op`,
            `gas_explicit marks s0.vs_gas_readings`,`r`,`ret_ty`,`s0`,`sa`,
            `st`,`su`,`sb`,`shadow_func`,`tr`,`tt`,`sr`,`tn0`,`tops`,`tv`,`vv0`] >>
  simp[] >> reverse conj_tac
  >- (Cases_on `FST (SND r)` >> fs[]) >>
  suspend "saved_write"
QED

Resume body_assign_other_nonempty_target_full[saved_write]:
  map_every qx_gen_tac [`target_marks`,`p`,`ee`,`Gu`,`tnu`,`u`,`z`,`Gz`,`tnz`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `~immutable_root cx t` (fn ordinary =>
    qpat_x_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
         assign_target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
      (assume_tac o SIMP_RULE std_ss [assign_target_post_def,ordinary])) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
      target_post H _ _ _ _ _ _ _ _ ee (PlaceR p) (Type ty') r u /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2
    (strip_assume_tac o REWRITE_RULE [target_post_def,value_type_place_def]) strip_assume_tac) >>
  `eval_operand (FST r) z = SOME w` by simp[] >>
  `place_ptr_rel cenv cx z (PlaceR p) w (FST (SND r)) (Type ty)` by
    (qpat_x_assum `place_ptr_rel _ _ u (PlaceR p) _ _ (Type ty)` mp_tac >>
     Cases_on `p` >> simp[place_ptr_rel_def] >>
     rpt strip_tac >> goal_assum drule >> simp[] >>
     qpat_assum `wb_frame cenv ee ee st u z`
       (mp_then Any irule exprSimWordArgsTheory.wb_frame_vars) >>
     simp[] >>
     `not_fresh_at sa p` by
       (qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
        qpat_assum `FLOOKUP cenv.ce_vars _ = SOME (PtrVar (Var p) _)` mp_tac >>
        POP_ASSUM_LIST kall_tac >> metis_tac[local_ptrs_reserved_def]) >>
     `not_fresh_at sr p` by (irule compiler_ci_mono_not_fresh >> qexists `sa` >> simp[]) >>
     irule compiler_ci_mono_not_fresh >> qexists `sr` >> simp[]) >>
  `?loc. FST (SND r) = SOME loc` by
    (qpat_x_assum `place_ptr_rel _ _ z (PlaceR p) _ _ (Type ty)` mp_tac >>
     Cases_on `p` >> simp[place_ptr_rel_def] >> strip_tac >> simp[]) >>
  `compile_assign_value cenv (FST r) loc op (is_word_type ty) (vv_location vv0) ty
      (lowered_value_type cenv e) (type_memory_bytes cenv ty) su = ((),sb)` by
    (qpat_assum `case FST (SND r) of SOME loc => _ | NONE => _` mp_tac >> simp[] >> gvs[]) >>
  `!x. FST r = Var x ==> not_fresh_at su x` by
    metis_tac[compiler_ci_mono_not_fresh] >>
  qabbrev_tac `target_gas = gas_explicit target_marks s.vs_gas_readings` >>
  Cases_on `is_word_type ty`
  >- (`post_value_type cenv e = ty` by metis_tac[] >>
      `eval_operand op z = SOME (typed_val_to_w256 tu' v)` by
        (qpat_assum `expr_post _ _ _ _ _ e _ _ _ _ ee v op z` mp_tac >>
         qpat_assum `evaluate_type (get_tenv cx) ty = SOME tu'` mp_tac >>
         qpat_assum `post_value_type cenv e = ty` mp_tac >>
         qpat_assum `is_word_type ty` mp_tac >>
         POP_ASSUM_LIST kall_tac >> simp[expr_post_def,expr_val_rel_def] >> metis_tac[]) >>
      `op_taint tnz op = {}` by
        (qpat_assum `ptr_val_ok cx (post_value_type cenv e) v op Gz tnz z`
           (assume_tac o cj 1 o REWRITE_RULE [ptr_val_ok_def]) >> simp[]) >>
      `op_taint tnz (FST r) = {}` by
        (qpat_assum `target_ptr_ok cenv (PlaceR p) r Gz tnz z`
           (ACCEPT_TAC o cj 1 o REWRITE_RULE [target_ptr_ok_def])) >>
      Cases_on `p` >>
      qpat_x_assum `place_ptr_rel _ _ z (PlaceR _) _ _ (Type ty)` mp_tac >>
      simp[place_ptr_rel_def] >> strip_tac
      >- suspend "saved_storage_word" >>
      suspend "saved_memory_word") >>
  suspend "saved_nonword"
QED

Resume body_assign_other_nonempty_target_full[snapshot_write]:
  map_every qx_gen_tac [`target_marks`,`p`,`ee`,`z`,`Gz`,`tnz`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `~immutable_root cx t` (fn ordinary =>
    qpat_x_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
         assign_target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
      (assume_tac o SIMP_RULE std_ss [assign_target_post_def,ordinary])) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
      target_post H _ _ _ _ _ _ _ _ ee (PlaceR p) (Type ty) r z /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2
    (strip_assume_tac o REWRITE_RULE [target_post_def,value_type_place_def]) assume_tac) >>
  `?loc. FST (SND r) = SOME loc` by
    (qpat_x_assum `place_ptr_rel _ _ z (PlaceR p) _ _ (Type ty)` mp_tac >>
     Cases_on `p` >> simp[place_ptr_rel_def] >> strip_tac >> simp[]) >>
  `compile_assign_value cenv (FST r) loc op (is_word_type ty) (vv_location vv) ty
      (lowered_value_type cenv e) (type_memory_bytes cenv ty) su = ((),sb)` by
    (qpat_assum `case FST (SND r) of SOME loc => _ | NONE => _` mp_tac >> simp[] >> gvs[]) >>
  `!x. FST r = Var x ==> not_fresh_at su x` by
    metis_tac[compiler_ci_mono_not_fresh] >>
  qabbrev_tac `target_gas = gas_explicit target_marks u.vs_gas_readings` >>
  Cases_on `is_word_type ty`
  >- (`lowered_value_type cenv e = ty` by metis_tac[] >>
      `stv = tu'` by fs[] >>
      qpat_x_assum `is_word_type (lowered_value_type cenv e) /\ _ \/ _` mp_tac >>
      simp[] >> strip_tac >>
      `op_taint tnz (FST r) = {}` by
        (qpat_assum `target_ptr_ok cenv (PlaceR p) r Gz tnz z`
           (ACCEPT_TAC o cj 1 o REWRITE_RULE [target_ptr_ok_def])) >>
      Cases_on `p` >>
      qpat_x_assum `place_ptr_rel _ _ z (PlaceR _) _ _ (Type ty)` mp_tac >>
      simp[place_ptr_rel_def] >> strip_tac
      >- suspend "storage_word" >>
      suspend "memory_word") >>
  suspend "snapshot_nonword"
QED

(* At either target cursor, the word write uses the same original-entry frame. *)
fun residual_word_entry_frame g =
  (qx_gen_tac `H` >> disch_tac >>
   qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
       target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
     (drule_then strip_assume_tac) >>
   (if List.exists (can (match_term ``wb_frame cenv es ee sa s0 z``)) (fst g)
    then
      qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ ee _ _ z`
        (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
      qpat_assum `wb_frame cenv es ee sa s0 z`
        (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
      qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tnz`
        (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
      simp[] >> conj_tac
      >- (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
      qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN tn0.t_mem`
        (fn th => simp[th])
    else
      qpat_assum `target_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [target_post_def]) >> simp[])) g;

fun residual_storage_word g =
  (rename1 `write_place cx (StoragePlace trans slot leaf) v` >>
  `leaf = tu'` by simp[] >>
  qpat_x_assum `leaf = tu'` (SUBST_ALL_TAC o SYM) >>
  `loc = slot_loc trans` by simp[] >>
  qpat_x_assum `loc = slot_loc trans` SUBST_ALL_TAC >>
  `eval_operand (FST r) z = SOME slot` by simp[] >>
  `emit_void (if trans then TSTORE else SSTORE) [FST r;op] su = ((),sb)` by
    (qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ su = ((),sb)` mp_tac >>
     qpat_assum `is_word_type ty` mp_tac >>
     POP_ASSUM_LIST kall_tac >> Cases_on `trans` >>
     simp[compile_assign_value_def,slot_loc_def,comp_bind_def,comp_return_def]) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `eval_target_place cx t (mid with gas_obs := target_gas) =
      (INL (StoragePlace trans slot leaf),ee)` by
    (qpat_assum `!tail. eval_target_place _ _ (_ with gas_obs := _ ++ tail) = _`
       (qspec_then `[]` mp_tac) >>
     qpat_assum `ee with gas_obs := [] = ee`
       (fn th => rewrite_tac [listTheory.APPEND_NIL,th])) >>
  drule_then strip_assume_tac vyperFiniteStoragePreservationTheory.eval_target_place_observed_region >>
  Cases_on `write_place cx (StoragePlace trans slot leaf) v ee` >>
  drule_then assume_tac tuplePlaceStepTheory.write_place_storage_trace >>
  irule gas_outcome_full_post_mono >>
  irule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)
    augAssignFullWritebackTheory.augassign_storage_writeback_full >>
  goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `MEM (StorageRoot _ _ _) _`)) >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  goal_assum (drule_at (Pat `is_word_type _`)) >>
  simp[] >>
  qexistsl [`tn0`,`sa`,`s0`,`lctx`,`es`,`d`,`cenv`,`cenv`,`RetQ`,`G0`] >>
  simp[]) g;

fun residual_storage_word_posts g =
  (conj_tac >- (rpt gen_tac >> strip_tac >> qexists `cenv` >> simp[] >>
     first_assum ACCEPT_TAC) >>
   rpt gen_tac >> strip_tac >> res_tac) g;

fun residual_memory_word_setup g =
  (rename1 `write_place cx (MemoryPlace id path) v` >>
  `emit_void MSTORE [FST r;op] su = ((),sb)` by
    (qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ su = ((),sb)` mp_tac >>
     qpat_assum `is_word_type ty` mp_tac >>
     qpat_assum `loc = LocMemory` (fn th => rewrite_tac[th]) >>
     POP_ASSUM_LIST kall_tac >>
     simp[compile_assign_value_def,comp_bind_def,comp_return_def]) >>
  `place_ptr_rel cenv cx z (PlaceR (MemoryPlace id path)) w (SOME LocMemory) (Type ty)` by
    (simp[place_ptr_rel_def] >> goal_assum drule >> simp[]) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `eval_target_place cx t (mid with gas_obs := target_gas) =
      (INL (MemoryPlace id path),ee)` by
    (qpat_assum `!tail. eval_target_place _ _ (_ with gas_obs := _ ++ tail) = _`
       (qspec_then `[]` mp_tac) >>
     qpat_assum `ee with gas_obs := [] = ee`
       (fn th => rewrite_tac [listTheory.APPEND_NIL,th])) >>
  `target_pre cenv cx env t (mid with gas_obs := target_gas)` by
    simp[body_assign_saved_resources_gas] >>
  `expr_sim_inv cenv cx env ee` by
    (drule tuplePlaceSourceHeadTheory.tuple_place_target_base_inversion >> strip_tac >>
     drule_all eval_base_place_sim_inv >> simp[]) >>
  `store_lays_out tu' tu' v` by
    (drule_all store_lays_out_typed >> simp[])) g;

fun residual_memory_word_source g =
  (Cases_on `write_place cx (MemoryPlace id path) v ee` >>
  drule_then assume_tac tuplePlaceStepTheory.write_place_storage_trace >>
  `stmt_res_ok lctx q` by
    (qpat_assum `gas_admissible (eval_stmt _ _) _ _`
       (mp_then Any irule gas_admissible_result) >>
     qexistsl [`r'`,`gas_explicit marks s0.vs_gas_readings ++ target_gas`] >>
     simp[Once evaluate_def,bind_def]) >>
  qpat_assum `!i xs. MemoryPlace id path = MemoryPlace i xs ==> _`
    (qspecl_then [`id`,`path`] (strip_assume_tac o REWRITE_RULE []))) g;

fun residual_memory_word_write g =
  (irule gas_outcome_full_post_mono >>
  irule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)
    augAssignFullWritebackTheory.augassign_memory_writeback_full >>
  qpat_assum `emit_void MSTORE [FST r;op] su = ((),sb)`
    (irule_at (Pat `emit_void MSTORE _ _ = _`)) >>
  qpat_assum `write_place cx (MemoryPlace id path) v ee = (q,r')`
    (irule_at (Pat `write_place _ _ _ _ = _`)) >>
  qpat_assum `place_ptr_rel _ _ z (PlaceR (MemoryPlace id path)) w (SOME LocMemory) (Type ty)`
    (irule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
  qpat_assum `store_lays_out tu' tu' v`
    (irule_at (Pat `store_lays_out _ _ _`))) g;

fun residual_memory_word_posts g =
  (simp[] >>
  qexistsl [`tops`,`tn0`,`sa`,`s0`,`SND (SND r)`,`FST (SND r)`,`lctx`,`es`,
            `env`,`d`,`cenv`,`\H res ee gt r. F`,`G0`] >>
  simp[pairTheory.PAIR] >>
  (conj_tac >- (residual_word_entry_frame >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> qexists `cenv` >> simp[] >>
  first_assum ACCEPT_TAC)) g;

Resume body_assign_other_nonempty_target_full[storage_word]:
  residual_storage_word >>
  (conj_tac >- (residual_word_entry_frame >> gvs[])) >>
  residual_storage_word_posts
QED

Resume body_assign_other_nonempty_target_full[memory_word]:
  residual_memory_word_setup >>
  residual_memory_word_source >>
  residual_memory_word_write >>
  residual_memory_word_posts
QED

Resume body_assign_other_nonempty_target_full[saved_storage_word]:
  residual_storage_word >>
  (conj_tac >- (residual_word_entry_frame >> gvs[])) >>
  residual_storage_word_posts
QED

Resume body_assign_other_nonempty_target_full[saved_memory_word]:
  residual_memory_word_setup >>
  residual_memory_word_source >>
  residual_memory_word_write >>
  residual_memory_word_posts
QED

Resume body_assign_other_nonempty_target_full[snapshot_nonword]:
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `eval_target_place cx t (mid with gas_obs := target_gas) = (INL p,ee)` by
    (qpat_assum `!tail. eval_target_place _ _ (_ with gas_obs := _ ++ tail) = _`
       (qspec_then `[]` mp_tac) >>
     qpat_assum `ee with gas_obs := [] = ee`
       (fn th => rewrite_tac [listTheory.APPEND_NIL,th])) >>
  Cases_on `p` >>
  qpat_x_assum `place_ptr_rel _ _ z (PlaceR _) _ _ (Type ty)` mp_tac >>
  simp[place_ptr_rel_def] >> strip_tac
  >- suspend "snapshot_slots" >>
  suspend "snapshot_memory"
QED

Resume body_assign_other_nonempty_target_full[snapshot_memory]:
  `~is_word_type (lowered_value_type cenv e)` by
    (qpat_assum `type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty` mp_tac >>
     qpat_assum `~is_word_type ty` mp_tac >> POP_ASSUM_LIST kall_tac >>
     simp[type_widens_to_def] >> metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type]) >>
  qpat_x_assum `is_word_type (lowered_value_type cenv e) /\ _ \/ _` mp_tac >>
  simp[] >> strip_tac >>
  `ci_mono sa su` by (irule ci_mono_trans >> qexists `st` >> simp[] >>
    irule ci_mono_trans >> qexists `ss` >> simp[] >>
    irule ci_mono_trans >> qexists `sr` >> simp[]) >>
  rename1 `write_place cx (MemoryPlace id path) v` >>
  `?entry w. lookup_scopes id ee.scopes = SOME entry /\
     evaluate_subscripts entry.type entry.value path = INL w` by
    (qpat_assum `!i p. MemoryPlace id path = MemoryPlace i p ==> _`
       (qspecl_then [`id`,`path`] mp_tac) >> simp[]) >>
  irule body_assign_other_snapshot_memory_write_full >>
  simp[] >> rpt conj_tac
  >- gvs[]
  >- (qexists `tops` >> simp[]) >>
  qexistsl [`aid`,`b'`,`tu'`,`e`,`env`,`mid`,`tv`,`r`,`marks`,`sr`,
            `vv`,`ss`,`st`,`su`,`t`,`target_marks`,`stv`,`ty`,`u`,`vv0`,`xd`] >>
  simp[Abbr `target_gas`] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  conj_tac
  >- (qpat_assum `compile_assign_value _ _ loc op _ _ _ _ _ su = _` mp_tac >> gvs[]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    drule_then ACCEPT_TAC stmt_state_rel_vars_rels >>
  `~block_is_terminated sr` by
    drule_all_then ACCEPT_TAC exprOpenMainTheory.compile_expr_open_general >>
  `~block_is_terminated ss` by
    (`vv_type (vv_with_type (lowered_value_type cenv e) vv0) = lowered_value_type cenv e` by
       (Cases_on `vv0` >> simp[vv_with_type_def,vv_type_def]) >>
     Cases_on `compile_alloc_buffer (type_memory_bytes cenv (lowered_value_type cenv e)) sr` >>
     rename1 `compile_alloc_buffer _ sr = (buf,sn)` >>
     Cases_on `unwrap_value cenv (vv_with_type (lowered_value_type cenv e) vv0) sn` >>
     rename1 `unwrap_value cenv _ sn = (src,sk)` >>
     Cases_on `compile_store_memory cenv src buf.buf_operand
                 (lowered_value_type cenv e) (lowered_value_type cenv e) sk` >>
     qpat_x_assum `compile_snapshot_vv _ _ _ sr = _` mp_tac >>
     simp[compile_snapshot_vv_def,compile_materialize_vv_def,
          comp_bind_def,comp_ignore_bind_def,comp_return_def] >> strip_tac >>
     gvs[] >>
     `~block_is_terminated sn` by
       drule_then ACCEPT_TAC exprOpenPrimitivesTheory.compile_alloc_buffer_open >>
     `~block_is_terminated sk` by drule_all_then ACCEPT_TAC exprOpenTerminalsTheory.unwrap_value_open >>
     qpat_assum `compile_store_memory _ _ _ _ _ sk = _`
       (mp_then Any mp_tac exprOpenCopiesTheory.compile_store_memory_open) >> simp[]) >>
  `~block_is_terminated st` by
    drule_all_then ACCEPT_TAC placeRelayoutOpenTheory.compile_get_target_ptr_endpoint_open >>
  drule_all_then ACCEPT_TAC exprOpenTerminalsTheory.unwrap_value_open
QED

Resume body_assign_other_nonempty_target_full[snapshot_slots]:
  `~is_word_type (lowered_value_type cenv e)` by
    (qpat_assum `type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty` mp_tac >>
     qpat_assum `~is_word_type ty` mp_tac >> POP_ASSUM_LIST kall_tac >>
     simp[type_widens_to_def] >> metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type]) >>
  qpat_x_assum `is_word_type (lowered_value_type cenv e) /\ _ \/ _` mp_tac >>
  simp[] >> strip_tac >>
  `ci_mono sa su` by (irule ci_mono_trans >> qexists `st` >> simp[] >>
    irule ci_mono_trans >> qexists `ss` >> simp[] >>
    irule ci_mono_trans >> qexists `sr` >> simp[]) >>
  `vv_location vv = SOME LocMemory /\ st = su` by
    (qpat_assum `compile_snapshot_vv _ _ _ sr = _`
       (mp_then Any mp_tac bodyMemSnapshotSourceLocationTheory.snapshot_saved_representation) >>
     disch_then (qspec_then `st` strip_assume_tac) >> fs[]) >>
  Cases_on `ty = lowered_value_type cenv e`
  >- (irule body_assign_other_snapshot_equal_slots_write_full >>
      simp[] >> rpt conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN tn0.t_mem`
            irule >> metis_tac[])
      >- (qexists `tops` >> simp[]) >>
      qexistsl [`b'`,`e`,`env`,`env'`,`target_marks`,`mid`,`r`,`ret_ty`,
                `vv`,`ss`,`su`,`t`,`stv`,`u`,`xd`] >>
      simp[Abbr `target_gas`] >> conj_tac
      >- ((gen_tac >> strip_tac >>
          qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> target_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
            (drule_then (mp_tac o CONJUNCT1)) >> simp[] >> (metis_tac[]))) >>
      qpat_assum `compile_assign_value _ _ loc op _ _ _ _ _ su = _` mp_tac >> gvs[]) >>
  Cases_on `is_bytestring_type ty /\ is_bytestring_type (lowered_value_type cenv e)`
  >- suspend "snapshot_bytes_slots" >>
  `not_fresh_at su xd` by metis_tac[] >>
  irule body_assign_other_snapshot_normalized_slots_write_full >>
  simp[] >> (rpt conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN tn0.t_mem`
        irule >> metis_tac[])
  >- (qexists `tops` >> simp[])) >>
  qexistsl [`aid`,`b'`,`e`,`env`,`env'`,`target_marks`,`mid`,`r`,`ret_ty`,
            `vv`,`ss`,`su`,`t`,`stv`,`ty`,`u`,`xd`] >>
  qpat_assum `compile_assign_value _ _ loc op _ _ _ _ _ su = _` mp_tac >>
  gvs[Abbr `target_gas`] >> metis_tac[]
QED

Resume body_assign_other_nonempty_target_full[saved_nonword]:
  `~is_word_type (lowered_value_type cenv e)` by
    (qpat_assum `type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty` mp_tac >>
     qpat_assum `~is_word_type ty` mp_tac >> POP_ASSUM_LIST kall_tac >>
     simp[type_widens_to_def] >> metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type]) >>
  namedCases_on `p` ["trans k dtv", "id path", "nsid iid ipath"]
  >- suspend "saved_slots"
  >- suspend "saved_memory" >>
  qpat_x_assum `place_ptr_rel _ _ z (PlaceR (ImmutablePlace _ _ _)) _ _ _`
    mp_tac >> simp[place_ptr_rel_def]
QED

Resume body_assign_other_nonempty_target_full[saved_memory]:
  `?entry w. lookup_scopes id ee.scopes = SOME entry /\
     evaluate_subscripts entry.type entry.value path = INL w` by
    (qpat_assum `!i p. MemoryPlace id path = MemoryPlace i p ==> _`
       (qspecl_then [`id`,`path`] mp_tac) >> simp[]) >>
  Cases_on `vv_location vv0 = SOME LocMemory`
  >- (irule body_assign_other_saved_staged_memory_write_full >> simp[] >>
      conj_tac
      >- (rpt strip_tac >> qpat_assum `!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ _ ==> i IN tn0.t_mem` irule >> metis_tac[]) >>
      qexistsl [`bindings`,`t`,`e`,`env`,`env'`,`target_marks`,`mid`,`op`,
                `gas_explicit marks s0.vs_gas_readings`,`r`,`ret_ty`,`s`,`st`,`su`,`sr`,`tops`,`tv`,`ty`,`u`,`vv0`] >>
      simp[Abbr `target_gas`] >> conj_tac
      >- metis_tac[] >>
      qpat_assum `compile_assign_value _ _ loc op _ _ _ _ _ su = _` mp_tac >> gvs[]) >>
  irule body_assign_other_saved_unstaged_memory_write_full >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ _ ==> i IN tn0.t_mem`
        irule >> metis_tac[]) >>
  conj_tac >- (qexists `tops` >> simp[]) >>
  qexistsl [`t`,`e`,`env`,`env'`,`target_marks`,`mid`,`op`,
            `gas_explicit marks s0.vs_gas_readings`,`r`,`ret_ty`,`s`,`st`,`su`,`sr`,`tv`,`ty`,`u`,`vv0`] >>
  simp[Abbr `target_gas`] >>
  qpat_assum `compile_assign_value _ _ loc op _ _ _ _ _ su = _` mp_tac >> gvs[]
  >> gvs[]
QED

Resume body_assign_other_nonempty_target_full[saved_slots]:
  `w = k /\ loc = slot_loc trans /\ evaluate_type (get_tenv cx) ty = SOME dtv` by
    (qpat_assum `place_ptr_rel _ _ z (PlaceR (StoragePlace _ _ _)) _ _ _`
       mp_tac >>
     qpat_assum `FST (SND r) = SOME loc` mp_tac >>
     POP_ASSUM_LIST kall_tac >> Cases_on `trans` >>
     simp[place_ptr_rel_def,slot_loc_def] >> metis_tac[]) >>
  Cases_on `ty = lowered_value_type cenv e`
  >- (irule body_assign_other_saved_equal_slots_write_full >>
      simp[] >>
      qexistsl [`bindings`,`t`,`e`,`env`,`env'`,`target_marks`,`mid`,`op`,
                `gas_explicit marks s0.vs_gas_readings`,`r`,`ret_ty`,`s`,`st`,`su`,`sr`,
                `tops`,`tv`,`u`,`vv0`] >>
      simp[Abbr `target_gas`] >> conj_tac
      >- (gen_tac >> strip_tac >>
          qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> target_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
            (drule_then (mp_tac o CONJUNCT1)) >> asm_rewrite_tac[]) >>
      gvs[]) >>
  Cases_on `is_bytestring_type ty /\ is_bytestring_type (lowered_value_type cenv e)`
  >- suspend "saved_bytes_slots" >>
  `assign_alloc_ok cenv t e` by
    fs[stmt_exprs_ok_def, Once allocLimitsTheory.alloc_limits_stmt_def] >>
  `compile_get_target_ptr compile_expr cenv t sr =
     ((FST r,SOME (slot_loc trans),SOME (ValPT ty)),st)` by
    (qpat_assum `compile_get_target_ptr _ _ _ sr = _` (fn th => rewrite_tac[th]) >>
     PairCases_on `r` >> gvs[]) >>
  `type_memory_bytes cenv ty < 2 ** 64` by
    (drule placeDestinationBoundsTheory.storage_target_normalization_bound >>
     disch_then (qspec_then `e` mp_tac) >>
     Cases_on `trans` >> simp[slot_loc_def] >>
     qpat_assum `~(has_length_word (expr_type e) /\ is_empty_value_expr e)`
       (mp_tac o REWRITE_RULE [DE_MORGAN_THM]) >>
     qpat_assum `~(is_bytestring_type ty /\ is_bytestring_type (lowered_value_type cenv e))`
       (mp_tac o REWRITE_RULE [DE_MORGAN_THM]) >>
     POP_ASSUM_LIST kall_tac >> metis_tac[]) >>
  `type_memory_bytes cenv ty = type_memory_size dtv` by
    drule_all_then ACCEPT_TAC expr_sim_inv_memory_size >>
  `type_memory_size dtv < dimword (:256)` by
    (irule arithmeticTheory.LESS_TRANS >> qexists `2 ** 64` >>
     conj_tac
     >- (qpat_assum `type_memory_bytes cenv ty = type_memory_size dtv`
           (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
     POP_ASSUM_LIST kall_tac >> simp[wordsTheory.dimword_def]) >>
  irule body_assign_other_saved_normalized_slots_write_full >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN tn0.t_mem`
        irule >> metis_tac[])
  >- (qexists `tops` >> simp[]) >>
  qexistsl [`t`,`e`,`env`,`env'`,`target_marks`,`mid`,`op`,
            `gas_explicit marks s0.vs_gas_readings`,`r`,`ret_ty`,`s`,`st`,`su`,`sr`,
            `tv`,`ty`,`u`,`vv0`] >>
  simp[Abbr `target_gas`] >> conj_tac
  >- (qpat_assum `~(is_bytestring_type ty /\ is_bytestring_type (lowered_value_type cenv e))`
        (ACCEPT_TAC o REWRITE_RULE [DE_MORGAN_THM])) >>
  qpat_assum `compile_assign_value _ _ loc op _ _ _ _ _ su = _` mp_tac >> gvs[]
QED

Resume body_assign_other_nonempty_target_full[snapshot_bytes_slots]:
  rename1 `write_place cx (StoragePlace trans k dtv) v` >>
  qpat_x_assum `tu' = dtv` SUBST_ALL_TAC >>
  `compile_store_slots cenv op (FST r) ty trans su = ((),sb)` by
    (qpat_assum `compile_assign_value _ _ loc op _ _ _ _ _ su = _` mp_tac >>
     qpat_assum `loc = slot_loc trans` (fn th => rewrite_tac [th]) >>
     disch_then (mp_tac o MATCH_MP placeStoreSlotsTheory.place_store_storage_compile) >>
     simp[SF CONJ_ss]) >>
  `expr_sim_inv cenv cx env ee` by
    (irule bodySimAugPlaceLoadTheory.aug_place_target_inv >>
     goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
     fs[target_pre_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) z /\
    storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) Gz tnz z /\
    dead_lo_ok H (DF H) lo cenv cx /\ storage_place_observed H (StoragePlace trans k dtv)` by
    (gen_tac >> disch_tac >>
     `storage_place_observed H (StoragePlace trans k dtv)` by
       (irule stmtSimAugAssignPlaceStorageTheory.aug_place_target_observed >>
        goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
        qexists `st0` >> simp[]) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> target_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (mp_tac o REWRITE_RULE [target_post_def])) >>
     simp[SF CONJ_ss]) >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    drule_then (ACCEPT_TAC o MATCH_MP contract_inv_acyclic_struct_metadata) body_inv_contract >>
  qpat_assum `expr_sim_inv cenv cx env ee`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_sim_inv_def]) >>
  `sa.cs_next_var <= su.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv su` by drule_all_then ACCEPT_TAC local_ptrs_reserved_next_var >>
  `!x. not_fresh_at sa x ==> not_fresh_at su x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x` by simp[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x` by fs[ret_pc_ok_def] >>
  `op_taint tnz op = {} /\ op_taint tnz (FST r) = {}` by fs[ptr_covers_def,target_ptr_ok_def] >>
  `eval_operand op z = SOME (n2w b')` by simp[eval_operand_def] >>
  `b' < dimword (:256)` by decide_tac >>
  `w2n (n2w b' : 256 word) = b'` by simp[w2n_n2w, LESS_MOD] >>
  irule body_assign_other_bytes_slots_write_full >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN tn0.t_mem`
        (drule_all_then ACCEPT_TAC)) >>
  conj_tac >- (qexists `env` >> simp[]) >>
  qexistsl [`FST r`,`ty`,`op`,`stv`,`lowered_value_type cenv e`,`su`,`n2w b'`] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  qexists `xd` >> simp[]
QED

Resume body_assign_other_nonempty_target_full[saved_bytes_slots]:
  qpat_x_assum `is_bytestring_type ty /\ is_bytestring_type (lowered_value_type cenv e)`
    strip_assume_tac >>
  `tu' = dtv` by metis_tac[SOME_11] >>
  qpat_x_assum `tu' = dtv` SUBST_ALL_TAC >>
  `compile_store_slots cenv op (FST r) ty trans su = ((),sb)` by
    (qpat_assum `compile_assign_value _ _ loc op _ _ _ _ _ su = _` mp_tac >>
     qpat_assum `loc = slot_loc trans` (fn th => rewrite_tac [th]) >>
     disch_then (mp_tac o MATCH_MP placeStoreSlotsTheory.place_store_storage_compile) >>
     simp[SF CONJ_ss]) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `eval_target_place cx t (mid with gas_obs := target_gas) = (INL (StoragePlace trans k dtv),ee)` by
    (qpat_assum `!tail. eval_target_place _ _ (_ with gas_obs := _ ++ tail) = _`
       (qspec_then `[]` mp_tac) >>
     qpat_assum `ee with gas_obs := [] = ee`
       (fn th => rewrite_tac [listTheory.APPEND_NIL,th])) >>
  `expr_sim_inv cenv cx env ee` by
    (irule bodySimAugPlaceLoadTheory.aug_place_target_inv >>
     goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
     fs[target_pre_def]) >>
  `~is_word_type (post_value_type cenv e)` by
    metis_tac[immutable_rhs_post_physical_classify,is_bytestring_word_type] >>
  `?sw. eval_operand op z = SOME sw` by fs[expr_post_def,expr_val_rel_def] >>
  `!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==> val_in_memory stv v (w2n sw) mem` by
    (drule immutable_rhs_post_physical_classify >> strip_tac
     >- fs[ptr_val_ok_def,ptr_mem_ok_def] >>
     `type_widens_to (get_tenv cx) (lowered_value_type cenv e) (post_value_type cenv e)` by
       metis_tac[immutable_rhs_physical_post_widens] >>
     drule_all type_widens_to_value_has_type >> strip_tac >>
     rpt strip_tac >>
     rename1 `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv` >>
     `val_in_memory ptv v (w2n sw) mem` by fs[ptr_val_ok_def,ptr_mem_ok_def] >>
     metis_tac[bytestring_val_in_memory_transfer]) >>
  `0 < type_memory_size stv` by
    (`(?n. stv = BaseTV (BytesT (Dynamic n))) \/ (?n. stv = BaseTV (StringT n))` by
       (qpat_assum `is_bytestring_type (lowered_value_type cenv e)` mp_tac >>
        qpat_assum `evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv` mp_tac >>
        POP_ASSUM_LIST kall_tac >> metis_tac[valueCopyBytesTheory.bytestring_type_value]) >>
     simp[valueEncodingTheory.type_memory_size_def]) >>
  `w2n sw + type_memory_size stv <= z.vs_alloca_next` by
    (qpat_assum `~is_word_type (post_value_type cenv e) ==> !w. eval_operand op z = SOME w ==> _`
       (drule_then (qspec_then `sw` mp_tac)) >>
     qpat_assum `0 < type_memory_size stv` mp_tac >>
     qpat_assum `eval_operand op z = SOME sw` mp_tac >>
     POP_ASSUM_LIST kall_tac >> simp[ADD_COMM,arithmeticTheory.NOT_ZERO_LT_ZERO]) >>
  `op_taint tnz op = {} /\ op_taint tnz (FST r) = {}` by fs[ptr_val_ok_def,target_ptr_ok_def] >>
  `?xs. op = Var xs /\ ptr_covers Gz tnz xs z (type_memory_size stv)` by
    (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
     simp[] >> qexistsl [`cenv`,`e`] >> simp[]) >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    drule_then (ACCEPT_TAC o MATCH_MP contract_inv_acyclic_struct_metadata) body_inv_contract >>
  qpat_assum `expr_sim_inv cenv cx env ee`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_sim_inv_def]) >>
  `sa.cs_next_var <= su.cs_next_var /\ sr.cs_next_var <= st.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv su` by drule_all_then ACCEPT_TAC local_ptrs_reserved_next_var >>
  `!x. not_fresh_at sa x ==> not_fresh_at su x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x` by simp[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x` by simp[] >>
  `!x. vv_operand vv0 = Var x ==> not_fresh_at st x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. op = Var x ==> not_fresh_at su x` by
    (qpat_assum `unwrap_value cenv vv0 st = (op,su)` mp_tac >>
     qpat_assum `!x. vv_operand vv0 = Var x ==> not_fresh_at st x` mp_tac >>
     POP_ASSUM_LIST kall_tac >> rpt disch_tac >>
     drule compiler_unwrap_value_var >> Cases_on `vv0` >> fs[vv_operand_def]) >>
  `eval_operand (FST r) z = SOME k` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (drule_then (mp_tac o MATCH_MP stmt_state_rel_allocas_below_fmp)
      exprSimWordArgsTheory.expr_post_state >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) z /\
    storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) Gz tnz z /\
    dead_lo_ok H (DF H) lo cenv cx /\ storage_place_observed H (StoragePlace trans k dtv)` by
    (gen_tac >> disch_tac >>
     `storage_place_observed H (StoragePlace trans k dtv)` by
       (irule stmtSimAugAssignPlaceStorageTheory.aug_place_target_observed >>
        goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
        qexists `st0` >> simp[]) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> target_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (mp_tac o REWRITE_RULE [expr_post_def])) >>
     simp[SF CONJ_ss]) >>
  qpat_assum `wb_frame cenv es ee sa s0 z`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [wb_frame_def]) >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tnz`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [ghost_kept_at_def]) >>
  irule body_assign_other_bytes_slots_write_full >> simp[] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN tn0.t_mem`
        irule >> conj_tac
      >- (qexistsl_tac [`aid`,`off`,`sz`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists `env` >> simp[]) >>
  qexistsl [`FST r`,`ty`,`op`,`stv`,`lowered_value_type cenv e`,`su`,`sw`] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  qexists `xs` >> simp[]
QED

Finalise body_assign_other_nonempty_target_full[local]

(* Every other base target: subscripts, nested attributes, immutables. *)
Theorem body_assign_nested_empty_immutable_full:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    struct_args_unique tops /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              is_word_type ty) /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              ~is_word_type ty /\
              (expr_type e = ty \/ lowered_value_type cenv e = ty \/
               is_bytestring_type ty \/
               has_length_word (expr_type e) /\ is_empty_value_expr e)) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\ supported_scalar_target tops nsid) /\
    ~(?nsid mut ty slot.
        t = TopLevelNameTarget nsid /\
        supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
        (mut = Storage \/ mut = Transient) /\
        ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
        0 < type_memory_bytes cenv ty /\ expr_type e = ty /\
        lowered_value_type cenv e = expr_type e) /\
    ~(?id fld sid fty.
        t = AttributeTarget (NameTarget id) fld /\
        FLOOKUP env.var_types id = SOME (StructT sid) /\
        attribute_type env.type_defs (StructT sid) fld = SOME fty /\
        is_word_type fty) /\
    ~(?nsid fld fty.
        t = AttributeTarget (TopLevelNameTarget nsid) fld /\
        supported_storage_field_write tops nsid fld /\
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) /\
    has_length_word (expr_type e) /\ is_empty_value_expr e /\ immutable_root cx t /\
    ~supported_stmt_expr_exists (const_name_root cx) (Assign (BaseTarget t) e) /\
    ~(?nsid. t = TopLevelNameTarget nsid) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e)))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule body_assign_empty_target_typing >> strip_tac >>
  drule_all body_assign_empty_target_rhs_pre >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv` by
    (drule expr_body_pre_type_evaluates >> simp[IS_SOME_EXISTS]) >>
  `?dtv. evaluate_type (get_tenv cx) dty = SOME dtv` by
    (fs[type_widens_to_def, well_formed_type_def] >> metis_tac[IS_SOME_EXISTS]) >>
  `body_base_target_full_ok cx t` by
    (drule_all immutable_assign_empty_read >>
     disch_then (qspec_then `es.gas_obs` mp_tac) >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `get_module_code cx NONE = SOME tops /\ cx_tops cx = tops` by
    drule_then ACCEPT_TAC bodyInvCodePropsTheory.body_inv_main_code >>
  `target_indices_pre cenv cx env t` by
    drule_all_then ACCEPT_TAC body_assign_target_indices_pre >>
  `IS_SOME (type_place_target env t)` by simp[] >>
  drule_all bodyFullTargetRootsTheory.typed_immutable_target_root >>
  disch_then (qx_choosel_then [`id`,`ty`] strip_assume_tac) >>
  `has_length_word dty` by metis_tac[type_widens_to_has_length_word] >>
  simp[stmt_frag_full_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all assignPlacePureCodeTheory.assign_place_pure_empty_code >> strip_tac >>
  `?shadow_st. compile_get_target_ptr compile_expr (gas_shadow_env T cenv) (gas_shadow_target t)
      shadow_sa = (tr,shadow_st) /\ gas_shadow_state st shadow_st` by
    (Cases_on `compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
       (gas_shadow_target t) shadow_sa` >>
     `FST (compile_get_target_ptr compile_expr cenv t sa) =
        FST (compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
          (gas_shadow_target t) shadow_sa) /\
        gas_shadow_state
          (SND (compile_get_target_ptr compile_expr cenv t sa))
          (SND (compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
            (gas_shadow_target t) shadow_sa))` by
       (irule (REWRITE_RULE [gas_shadow_compiles_def]
         (Q.INST [`sd` |-> `T`] gas_shadow_stmt_get_target_ptr_env)) >> simp[]) >>
     gvs[]) >>
  `compile_store_at_loc cenv.ce_imm_alloca (FST tr) (Lit 0w) (FST (SND tr))
      shadow_st = ((),shadow_sb)` by
    (qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
       (mp_then Any mp_tac assignPlacePureCodeTheory.assign_place_pure_empty_code o
        REWRITE_RULE [gas_shadow_stmt_def, gas_shadow_assignment_def]) >>
     simp[]) >>
  gvs[] >>
  `ci_mono sa st /\ ci_mono shadow_sa shadow_st` by
    metis_tac[ci_mono_compile_get_target_ptr, pairTheory.SND] >>
  `ci_mono st sb /\ ci_mono shadow_st shadow_sb` by
    metis_tac[cj 2 ci_mono_stmt_helpers, pairTheory.SND] >>
  `fn_has_code sa st func /\ fn_has_code st sb func /\
   fn_has_code shadow_sa shadow_st shadow_func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  `gas_admissible (eval_target_place cx t) target_place_res_ok es` by
    metis_tac[assignPlaceEmptyComposeTheory.assign_place_empty_target_admissible] >>
  drule_all bodyFullTargetTheory.body_imm_target_place_sim_full >>
  disch_then (qspecl_then [`DF`,`lo`,`d`,`PG`,`func`,`shadow_func`]
    (mp_tac o REWRITE_RULE [imm_target_place_sim_full_def])) >>
  disch_then (qspecl_then [`st0`,`dty`,`sa`,`st`,`shadow_sa`,`shadow_st`,
                           `tr`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> fs[ret_pc_ok_def] >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  irule assign_return_buf_sep >> asm_rewrite_tac[] >>
  irule body_assign_empty_target_source >>
  simp[] >> qexistsl [`cenv`,`dtv`,`dty`,`env`] >> simp[] >>
  irule body_assign_empty_target_bind >>
  qpat_assum `gas_outcome_full _ _ _ _ (eval_target_place _ _) _ _ _` (irule_at Any) >>
  BETA_TAC >> reverse (rpt conj_tac)
  >- (rpt gen_tac >> Cases_on `res` >> simp[] >> strip_tac >>
      conj_tac >- (simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]) >>
      conj_tac >- metis_tac[halt_exit_INR_type] >>
      rpt strip_tac >> gvs[] >> fs[expr_exit_def])
  >- (rpt strip_tac >> qexists_tac `ImmutablePlace NONE id' path` >> simp[]) >>
  suspend "write"
QED

Resume body_assign_nested_empty_immutable_full[write]:
  qx_genl_tac [`marks`,`p`,`mid`,`G1`,`tn1`,`u`] >> simp[] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  `eval_target_place cx t (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL p,mid)` by
    (qpat_assum `!tail. eval_target_place _ _ _ = _` (qspec_then `[]` mp_tac) >>
     `mid with gas_obs := [] = mid` by gvs[evaluation_state_component_equality] >>
     qpat_assum `mid with gas_obs := [] = mid`
       (fn th => rewrite_tac[APPEND_NIL,th])) >>
  `expr_sim_inv cenv cx env mid` by
    (irule bodySimAugPlaceLoadTheory.aug_place_target_inv >>
     goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
     simp[expr_sim_inv_gas_obs]) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_target_place_preserves_scopes_dom >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H (es with gas_obs := gas_explicit marks s0.vs_gas_readings).storage_trace`
       suffices_by simp[] >>
     qpat_assum `eval_target_place _ _ _ = _`
       (mp_then (Pos (el 2)) mp_tac valid_horizon_frame) >>
     simp[cj 8 evaluate_storage_trace_frame]) >>
  qpat_assum `imm_target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ u`
    (strip_assume_tac o REWRITE_RULE [imm_target_post_def]) >>
  `ptv = dtv` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `ptv = dtv` SUBST_ALL_TAC >>
  `cenv.ce_is_ctor` by
    (drule_then (assume_tac o MATCH_MP contract_inv_constructor) body_inv_contract >> simp[]) >>
  `?imms. ALOOKUP mid.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables NONE imms) id = SOME (itv,iv)` by
    (Cases_on `ALOOKUP mid.immutables cx.txn.target` >> gvs[]) >>
  `evaluate_type (get_tenv cx) ty = SOME itv` by
    (fs[expr_sim_inv_def, env_consistent_def, env_immutables_consistent_def] >>
     metis_tac[]) >>
  drule_all immutable_assign_target_layout >>
  disch_then (qspec_then `compile_expr` strip_assume_tac) >>
  qpat_x_assum `NONE = cenv.ce_module` (assume_tac o SYM) >>
  `off' = off` by metis_tac[optionTheory.SOME_11, compileEnvTheory.var_location_11] >>
  qpat_x_assum `off' = off` SUBST_ALL_TAC >>
  `off + type_memory_size itv <= lo` by
    (mp_tac (Q.INST [`ce` |-> `cenv`, `es` |-> `mid`, `tops` |-> `cx_tops cx`,
       `H` |-> `storage_trace_horizon mid.storage_trace`,
       `D` |-> `DF (storage_trace_horizon mid.storage_trace)`, `itv` |-> `itv`]
       (INST_TYPE [alpha |-> ``:256``]
         immutableDeployAssignPathGhostTheory.immutable_assign_section_root)) >>
     impl_tac >- simp[] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `off + type_memory_size itv < dimword (:256)` by
    (qpat_assum `!tv. evaluate_type _ _ = SOME tv ==> _`
       (qspec_then `itv` mp_tac) >> simp[]) >>
  drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >>
  `32 <= type_memory_size dtv` by
    (mp_tac (Q.SPECL [`get_tenv cx`,`dty`,`dtv`,`off+k`,
                        `(mstore (off+k) 0w u).vs_memory`]
        stmtSimDeclMemTheory.memory_length_word_layout) >>
     simp[mstore_mem_word_at_same]) >>
  `off + k + 32 <= lo /\ off+k < dimword (:256) /\ lo <> 0` by decide_tac >>
  `w2n (n2w (off+k) : bytes32) = off+k` by simp[wordsTheory.w2n_n2w_compute] >>
  `op_taint tn1 (FST tr) = {}` by fs[target_ptr_ok_def] >>
  `op_prov G1 (FST tr) = NONE` by first_assum ACCEPT_TAC >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `!reg. cenv.ce_imm_alloca = SOME reg ==>
    eval_operand reg u = SOME 0w /\ op_taint tn1 reg = {} /\ op_prov G1 reg = NONE` by
    (gen_tac >> disch_tac >> conj_tac
     >- (qpat_assum `stmt_state_rel _ _ _ _ _ _ u`
         (mp_tac o MATCH_MP stmt_state_rel_immutable_base_zero) >>
         simp[immutable_base_zero_def]) >>
     Cases_on `reg` >> gvs[ghost_inv_at_def,op_taint_def,op_prov_def] >>
     metis_tac[]) >>
  `compile_imm_store_word cenv.ce_imm_alloca (FST tr) (Lit 0w) st = ((),sb)` by
    fs[compile_store_at_loc_def] >>
  `w2n (n2w (off+k) : bytes32) + 32 <= lo` by simp[] >>
  mp_tac (Q.INST [`operand` |-> `Lit 0w`, `value` |-> `0w`,
                  `imm` |-> `cenv.ce_imm_alloca`,
                  `dst` |-> `FST (tr : operand # data_location option # place_ty option)`,
                  `a` |-> `n2w (off+k) : bytes32`, `sa` |-> `st`,
                  `s` |-> `u`, `G` |-> `G1`, `tn` |-> `tn1`,
                  `explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`]
    immutableWordStorePathTheory.immutable_word_store_path_clean) >>
  `eval_operand (Lit 0w) u = SOME 0w /\ op_taint tn1 (Lit 0w) = {}` by
    simp[eval_operand_def,op_taint_def] >>
  impl_tac >- simp[] >> strip_tac >>
  suspend "write_post"
QED

Resume body_assign_nested_empty_immutable_full[write_post]:
  qpat_x_assum `p = ImmutablePlace NONE id path` SUBST_ALL_TAC >>
  Cases_on `write_place cx (ImmutablePlace NONE id path) (default_value dtv) mid` >>
  rename1 `write_place cx (ImmutablePlace NONE id path) (default_value dtv) mid = (wr,ff)` >>
  `stmt_res_ok lctx wr` by
    (`eval_stmt cx (Assign (BaseTarget t) e)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (wr,ff)` by
       (`eval_stmt cx (Assign (BaseTarget t) e)
           (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
         bind (eval_target_place cx t) (\p. write_place cx p (default_value dtv))
           (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
          (irule assignPlaceEmptyTheory.assign_place_empty_source_action >> simp[] >>
           qexistsl_tac [`cenv`,`dty`,`env`] >> simp[]) >>
        simp[bind_def]) >>
     metis_tac[gas_admissible_result]) >>
  drule_all immutable_augassign_path_write_source >>
  strip_tac >> gvs[] >>
  `!tail. write_place cx (ImmutablePlace NONE id path) (default_value dtv)
      (mid with gas_obs := tail) = (INL (),ff with gas_obs := tail)` by
    (qpat_assum `write_place cx (ImmutablePlace NONE id path) _ mid = _`
       (ACCEPT_TAC o MATCH_MP bodyImmutableAugAssignExecTheory.immutable_write_place_gas_obs)) >>
  `ff.scopes = mid.scopes /\ ff.storage_trace = mid.storage_trace /\
   ff.accounts = mid.accounts /\ ff.tStorage = mid.tStorage` by
    (drule vyperPlaceFramesTheory.write_immutable_place_frame >> strip_tac >> simp[]) >>
  `ff with gas_obs := [] = ff` by
    (`mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. write_place _ _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_x_assum `mid with gas_obs := [] = mid` (rewrite_tac o single) >>
     qpat_assum `write_place cx (ImmutablePlace NONE id path) _ mid = _`
       (rewrite_tac o single) >> simp[]) >>
  qabbrev_tac `q = u' with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `q.vs_allocas = u.vs_allocas /\ q.vs_alloca_next = u.vs_alloca_next /\
   q.vs_current_bb = sb.cs_current_bb /\ ~q.vs_halted /\
   q.vs_memory = (mstore (off+k) 0w u).vs_memory /\
   (q with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
      vs_immutables := u.vs_immutables; vs_prev_bb := u.vs_prev_bb;
      vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx|>) = u` by
    (qpat_assum `u' with <|vs_memory := _; vs_vars := _; vs_immutables := _|> = u`
       mp_tac >> simp[Abbr `q`,venom_state_component_equality,ADD_COMM]) >>
  `(!x. not_fresh_at st x ==> lookup_var x q = lookup_var x u) /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp q)` by
    (conj_tac
     >- (qpat_assum `!x. not_fresh_at st x ==> lookup_var x u' = _` mp_tac >>
         simp[NoAsms,Abbr `q`,lookup_var_def]) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u'` mp_tac >>
     simp[NoAsms,Abbr `q`,allocas_below_fmp_def] >> metis_tac[]) >>
  `alloca_history func q` by
    (`?bb rest. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
       DROP u.vs_inst_idx bb.bb_instructions = emitted_insts st sb ++ rest` by
       (drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >>
        metis_tac[rich_listTheory.IS_PREFIX_APPEND]) >>
     mp_tac (Q.SPECL [`func`,`u`,`q`,`bb`,`emitted_insts st sb`,`rest`]
       bodyBinopFragMemoryTheory.alloca_history_no_alloca_slice) >>
     simp[Abbr `q`, listTheory.LENGTH_APPEND,venom_state_fupdselfid]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at st x` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     goal_assum (drule_at (Pat `not_fresh_at sa x`)) >> fs[ci_mono_def]) >>
  `local_ptrs_reserved cenv st` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
     fs[ci_mono_def]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x` by
    metis_tac[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x` by
    (fs[ret_pc_ok_def] >> metis_tac[]) >>
  `return_buf_frame d cenv sb q` by
    (irule return_buf_frame_frame >>
     goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
     fs[ci_mono_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `tf.t_mem SUBSET tn1.t_mem` by simp[DIFF_SUBSET] >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`,`ff`,`INL ()`,`q`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `H` >> strip_tac >>
  conj_tac
  >- (qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
        (qspec_then `DF H` mp_tac) >> simp[Abbr `q`]) >>
  qpat_assum `ff with gas_obs := [] = ff` (rewrite_tac o single) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `ff.storage_trace = mid.storage_trace` (fn eq =>
       qpat_assum `valid_horizon cx st0 H ff.storage_trace`
         (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  qpat_assum `!h. valid_horizon cx st0 h mid.storage_trace ==>
       imm_target_post h _ _ _ _ _ _ _ _ _ _ _ _ _ u /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (qspec_then `H` mp_tac) >> (impl_tac >- metis_tac[]) >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx mid u /\
   storage_well_formed_on cx mid (FST H)` by
    (qpat_assum `imm_target_post H _ _ _ _ _ _ _ _ _ _ _ _ _ u`
       (mp_tac o REWRITE_RULE [imm_target_post_def]) >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx ff q` by
    (mp_tac (Q.INST [`ce` |-> `cenv`,`es` |-> `mid`,`s` |-> `u`,
                     `sa` |-> `st`,`root_ty` |-> `ty`,`ptv` |-> `dtv`,
                     `ty` |-> `dty`,`ee` |-> `ff`]
       (INST_TYPE [alpha |-> ``:256``]
         bodyFullAssignImmutableEmptyTheory.immutable_empty_path_store_restore)) >>
     simp[ADD_COMM]) >>
  `ghost_inv_at (DF H) lo d cenv cx ff Gf tf q` by
    (mp_tac (Q.INST [`ce` |-> `cenv`,`es` |-> `mid`,`s` |-> `u`,
                     `sa` |-> `st`,`off` |-> `off+k`,`tops` |-> `cx_tops cx`,
                     `D` |-> `DF H`,`G` |-> `G1`,`tn` |-> `tn1`,
                     `ee` |-> `ff`]
       (INST_TYPE [alpha |-> ``:256``]
         bodyFullAssignImmutableEmptyTheory.immutable_empty_store_ghost)) >>
     simp[ADD_COMM]) >>
  `alloca_frame cenv es sa s0 cenv ff q` by
    (mp_tac (Q.INST [`es'` |-> `ff`,`s` |-> `q`]
       (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame)) >>
     impl_tac >- (simp[] >> rpt gen_tac >> strip_tac >>
       `FLOOKUP u.vs_allocas aid = SOME (off',sz)` by
         (qpat_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _`
            (qspecl_then [`aid`,`(off',sz)`] mp_tac) >> simp[]) >>
       `lo <= off'` by
         (qpat_assum `allocas_from lo u`
           (qspecl_then [`aid`,`off'`,`sz`] mp_tac o REWRITE_RULE [allocas_from_def]) >> simp[]) >>
       `mem_bytes_at off' sz (mstore (k+off) 0w u).vs_memory =
        mem_bytes_at off' sz u.vs_memory` by
         (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
       simp[] >>
       qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
         (qspecl_then [`aid`,`off'`,`sz`] mp_tac) >> simp[] >>
       impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
     simp[]) >>
  `storage_well_formed_on cx ff (FST H)` by
    (irule (iffRL vyperStorageFootprintTheory.storage_well_formed_on_backends) >>
     qexists_tac `mid` >> simp[]) >>
  `stmt_lands lctx sb (INL ()) q` by simp[stmt_lands_def,Abbr `q`] >>
  BETA_TAC >> qexists_tac `cenv` >>
  simp[cenv_top_ext_refl] >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  (qpat_assum `!aid b sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> i IN tn0.t_mem`
     (qspecl_then [`aid`,`off'`,`sz`,`i`] mp_tac) >>
   impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
   disch_then ACCEPT_TAC)
QED

Finalise body_assign_nested_empty_immutable_full


fun nested_immutable_target_post g =
  (qpat_x_assum `assign_target_post _ H0 _ _ _ _ _ _ _ _ ee p _ r _ _`
     (qx_choosel_then [`root_id`,`path`] strip_assume_tac o
      SIMP_RULE std_ss [assign_target_post_def]) >>
   qpat_x_assum `imm_target_post H0 _ _ _ _ _ _ _ _ ee _ _ _ r _`
     (strip_assume_tac o REWRITE_RULE [imm_target_post_def]) >>
   qpat_x_assum `p = ImmutablePlace _ _ _` SUBST_ALL_TAC) g;

fun nested_immutable_target_eval g =
  (`ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
   `eval_target_place cx t (mid with gas_obs := target_gas) =
      (INL (ImmutablePlace NONE root_id path),ee)` by
     (qpat_assum `!tail. eval_target_place _ _ _ = _`
        (qspec_then `[]` (mp_tac o REWRITE_RULE [APPEND_NIL])) >>
      qpat_assum `ee with gas_obs := [] = ee`
        (fn th => simp[NoAsms, th, Abbr `target_gas`]))) g;

fun nested_immutable_target_writable g =
  (rename1 `evaluate_subscripts itv iv path = INL stored` >>
   `expr_sim_inv cenv cx env ee /\
    ?fin. write_place cx (ImmutablePlace NONE root_id path) v ee = (INL (),fin)` by
     (match_mp_tac (Q.INST [`mid` |-> `mid`,`bt` |-> `t`,`ty` |-> `ty`,
         `gs` |-> `target_gas`,`itv` |-> `itv`,`old` |-> `iv`,
         `k` |-> `k`,`tv` |-> `ptv`,`selected` |-> `stored`]
        bodyFullTargetImmutableWriteTheory.immutable_target_write_entry) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)) g;

fun nested_immutable_target_layout g =
  (`root_id = id /\ cenv.ce_module = NONE /\
    cenv.ce_module_var_type (NONE,id) = SOME ity /\ evaluate_type (get_tenv cx) ity = SOME itv` by
     (match_mp_tac (Q.INST [`bt` |-> `t`,`es` |-> `mid with gas_obs := target_gas`,
        `ee` |-> `ee`,`env` |-> `env`,`path` |-> `path`,`old` |-> `iv`]
        bodyFullTargetImmutableWriteTheory.immutable_target_write_root) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
   qpat_x_assum `root_id = id` SUBST_ALL_TAC) g;

fun nested_immutable_target_section g =
  (`off + type_memory_size itv <= lo` by
     (`dead_lo_ok H0 (DF H0) lo cenv cx` by simp[] >>
      qpat_assum `dead_lo_ok H0 (DF H0) lo cenv cx` mp_tac >>
      qpat_assum `body_inv tops ctx cenv cx` mp_tac >>
      qpat_assum `expr_sim_inv cenv cx env ee` mp_tac >>
      qpat_assum `cenv.ce_is_ctor` mp_tac >>
      qpat_assum `cenv.ce_module = NONE` mp_tac >>
      qpat_assum `FLOOKUP cenv.ce_module_vars (NONE,id) = SOME (ImmutableLoc off)` mp_tac >>
      qpat_assum `cenv.ce_module_var_type (NONE,id) = SOME ity` mp_tac >>
      qpat_assum `evaluate_type (get_tenv cx) ity = SOME itv` mp_tac >>
      POP_ASSUM_LIST kall_tac >>
      metis_tac[immutableDeployAssignPathGhostTheory.immutable_assign_section_root])) g;

fun nested_immutable_target_bounds g =
  (qpat_assum `mem_path_offset itv path = SOME (k,ptv)`
     (strip_assume_tac o MATCH_MP exprSimPropsTheory.mem_path_offset_sound) >>
   `allocas_from lo z /\ lo <= z.vs_alloca_next` by
     (qpat_assum `ghost_inv_at (DF H0) lo d cenv cx ee Gz tnz z`
        (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp[]) >>
   `lo < dimword (:256)` by
     (qpat_assum `stmt_state_rel H0 ctx func cenv cx ee z`
        (assume_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_alloca_room) >>
      drule_then assume_tac alloca_room_next_lt >> decide_tac) >>
   `off+k+type_memory_size ptv <= lo` by decide_tac) g;

fun nested_immutable_target_size g =
  (`type_memory_bytes cenv ty = type_memory_size ptv` by
     (irule expr_sim_inv_memory_size >> qexistsl [`cx`,`env`,`ee`] >> simp[]) >>
   `value_has_type ptv v` by
     (`ptv = tu'` by
       (qpat_assum `evaluate_type (get_tenv cx) ty = SOME ptv` (fn lhs =>
        qpat_assum `evaluate_type (get_tenv cx) ty = SOME tu'`
          (ACCEPT_TAC o REWRITE_RULE [optionTheory.SOME_11] o TRANS (SYM lhs)))) >> simp[])) g;

fun nested_immutable_target_operands g =
  (`sa.cs_next_var <= su.cs_next_var /\ sa.cs_next_id <= su.cs_next_id /\
     su.cs_next_var <= sb.cs_next_var` by fs[ci_mono_def] >>
   `local_ptrs_reserved cenv su` by
     (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
   `!x. not_fresh_at sa x ==> not_fresh_at su x` by
     metis_tac[freshWritesTheory.not_fresh_at_mono] >>
   `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x` by simp[] >>
   `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x` by simp[] >>
   `copy_old_operand su (FST r)` by
     (rw[exprSimCopyTheory.copy_old_operand_def] >>
      irule compiler_ci_mono_not_fresh >> qexists_tac `st` >> simp[]) >>
   `eval_operand (FST r) z = SOME (n2w (off+k)) /\
     op_prov Gz (FST r) = NONE /\ op_taint tnz (FST r) = {}` by
     (qpat_assum `target_ptr_ok cenv (PlaceR (ImmutablePlace NONE id path)) r Gz tnz z`
        (strip_assume_tac o REWRITE_RULE [target_ptr_ok_def]) >>
      simp[arithmeticTheory.ADD_COMM])) g;

fun nested_immutable_target_assign origin g =
  (`compile_assign_value cenv (FST r) LocCode op (is_word_type ty) (vv_location ^origin)
       ty (lowered_value_type cenv e) (type_memory_bytes cenv ty) su = ((),sb)` by
     (qpat_assum `FST (SND r) = SOME LocCode` (fn loc =>
        qpat_assum `SND (SND r) = SOME (ValPT ty)` (fn pty =>
          qpat_assum `case FST (SND r) of SOME loc => _ | NONE => _`
            (ACCEPT_TAC o CONJUNCT1 o SIMP_RULE (srw_ss()) [loc,pty])))) >>
   `~block_is_terminated sb` by
     drule_then ACCEPT_TAC immutableAssignOpenTheory.immutable_assign_loccode_open) g;

fun nested_immutable_base_operand state comp ghost taint g =
  (`lo <> 0` by decide_tac >>
   qpat_assum `stmt_state_rel H0 ctx func cenv cx ee ^state` (fn state_rel =>
     qpat_assum `ghost_inv_at (DF H0) lo d cenv cx ee ^ghost ^taint ^state` (fn ghost_inv =>
       qpat_assum `local_ptrs_reserved cenv ^comp` (fn reserved =>
         qpat_assum `lo <> 0` (fn positive =>
           assume_tac (MATCH_MP immutable_path_store_base_operand
             (LIST_CONJ [state_rel,ghost_inv,reserved,positive]))))))) g;

fun nested_immutable_write_base g =
  nested_immutable_base_operand ``z:venom_state`` ``su:compile_state``
    ``Gz:(string,num # num) fmap`` ``tnz:taint`` g;

fun nested_immutable_class_compile tag g =
  (qpat_assum tag (fn flag =>
     qpat_assum `compile_assign_value cenv (FST r) LocCode op (is_word_type ty) _ _ _ _ su = ((),sb)`
       (assume_tac o SIMP_RULE (srw_ss()) [flag]))) g;

fun nested_immutable_finish state comp ghost taint g =
  (disch_then (qx_choosel_then [`q`,`Gf`,`tf`]
     (strip_assume_tac o REWRITE_RULE[immutable_path_store_post_def])) >>
   qpat_assum `~block_is_terminated sb` (fn open_block =>
     rewrite_tac [open_block] >>
     qpat_assum `cenv.ce_module = NONE` (fn md =>
       match_mp_tac (SIMP_RULE std_ss [md,open_block] (Q.INST [`ce` |-> `cenv`,`tops` |-> `tops`,
       `env` |-> `env`,`ity` |-> `ity`,`itv` |-> `itv`,
       `off` |-> `off`,`k` |-> `k`,`ptv` |-> `ptv`,
       `fin` |-> `fin`,`q` |-> `q`,`Gf` |-> `Gf`,`tf` |-> `tf`,
       `s` |-> state,`su` |-> comp,`G` |-> ghost,`tn` |-> taint]
       immutable_path_write_outcome)))) >>
   rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
   rpt strip_tac >> TRY (first_assum ACCEPT_TAC) >>
   qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee ^(Parse.Term state) /\ _`
     (qspec_then `H` (drule_then strip_assume_tac)) >> simp[]) g;

fun nested_immutable_word_width g =
  (`type_memory_size ptv = 32` by metis_tac[localValueStorePropsTheory.evaluated_word_memory_size] >>
   nested_immutable_class_compile `is_word_type ty` >>
   `off+k+32 <= lo` by simp[] >>
   `copy_old_operand su op` by simp[copy_old_operand_def]) g;

fun nested_immutable_word_execution origin g =
  (mp_tac (Q.INST [`ce` |-> `cenv`,`dst` |-> `FST (r : operand # data_location option # place_ty option)`,`off` |-> `off+k`,
     `s` |-> `z`,`G` |-> `Gz`,`tn` |-> `tnz`,`sa` |-> `su`,
     `tv` |-> `ptv`,`tenv` |-> `get_tenv cx`,`loc` |-> `vv_location ^origin`,
     `sty` |-> `lowered_value_type cenv e`,`bytes` |-> `type_memory_bytes cenv ty`,
     `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] immutable_path_store_word) >>
   (impl_tac >-
      (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       qpat_assum `!base. cenv.ce_imm_alloca = SOME base ==> eval_operand base z = _ /\ _` mp_tac >>
       POP_ASSUM_LIST kall_tac >> metis_tac[]))) g;

fun nested_immutable_footprints g =
  (`0 < type_memory_size stv` by
     drule_all_then ACCEPT_TAC immutableAssignRepresentationTheory.immutable_assign_rhs_memory_positive >>
   `0 < type_memory_size ptv` by
     (`env.type_defs = get_tenv cx` by
        (drule exprSimAbiDecodeEntryTypingTheory.abi_decode_inv_type_env >> simp[]) >>
      `?etv. evaluate_type env.type_defs (expr_type e) = SOME etv` by
        metis_tac[exprSimHypsTheory.expr_body_pre_type_evaluates,optionTheory.IS_SOME_EXISTS] >>
      pop_assum strip_assume_tac >>
      `evaluate_type env.type_defs ty = SOME ptv` by simp[] >>
      drule_all_then (ACCEPT_TAC o cj 2)
        immutableAssignRepresentationTheory.immutable_assign_widened_memory_positive)) g;

fun nested_immutable_bytes_suffix g =
  (`!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at su x` by
     metis_tac[local_ptrs_reserved_imm_base] >>
   drule_all body_assign_immutable_memory_dispatch >>
   simp[] >> strip_tac >>
   mp_tac (Q.INST [`dst` |-> `FST (r : operand # data_location option # place_ty option)`,`off` |-> `off+k`,`s` |-> `z`,
     `a` |-> `b`,`sa` |-> `su`,`G` |-> `Gz`,`tn` |-> `tnz`,
     `sty` |-> `lowered_value_type cenv e`,`dty` |-> `ty`,`dtv` |-> `ptv`,
     `imm` |-> `cenv.ce_imm_alloca`,
     `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
     body_assign_immutable_bytes_path_store) >>
   (impl_tac >- simp[SF CONJ_ss]) >> nested_immutable_finish `z:venom_state` `su` `Gz` `tnz`) g;

fun nested_immutable_fixed_suffix origin g =
  (`stv = ptv` by fs[] >>
   qpat_x_assum `stv = ptv` SUBST_ALL_TAC >>
   qpat_assum `lowered_value_type cenv e = ty` (fn src_type =>
     qpat_assum `type_memory_bytes cenv ty = type_memory_size ptv` (fn width =>
       qpat_assum `compile_assign_value cenv (FST r) LocCode (Var src) F
           (vv_location ^origin) ty (lowered_value_type cenv e) (type_memory_bytes cenv ty) su = ((),sb)`
         (assume_tac o REWRITE_RULE [src_type,width]))) >>
   mp_tac (Q.INST [`ce` |-> `cenv`,`dst` |-> `FST (r : operand # data_location option # place_ty option)`,`off` |-> `off+k`,
     `s` |-> `z`,`G` |-> `Gz`,`tn` |-> `tnz`,`sa` |-> `su`,
     `tv` |-> `ptv`,`a` |-> `b`,`loc` |-> `vv_location ^origin`,
     `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] immutable_path_store_fixed) >>
   (impl_tac >- simp[]) >>
   nested_immutable_finish `z:venom_state` `su` `Gz` `tnz`) g;


fun nested_immutable_normalize_compile g =
  (qpat_assum `compile_assign_value cenv (FST r) LocCode (Var src) F _ ty
       (lowered_value_type cenv e) _ su = ((),sb)` (fn compiled =>
     qpat_assum `type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty`
       (mp_tac o MATCH_MP body_assign_immutable_memory_dispatch o CONJ compiled)) >> simp[] >>
   disch_then (CONJUNCTS_THEN2 assume_tac
     (qx_choosel_then [`buf`,`sm`,`sn`] strip_assume_tac))) g;

fun nested_immutable_normalize_code g =
  (`ci_mono su sm` by
     (qpat_assum `compile_alloc_buffer _ su = (buf,sm)` mp_tac >>
      POP_ASSUM_LIST kall_tac >> metis_tac[ci_mono_compile_alloc_buffer,pairTheory.SND]) >>
   `ci_mono sm sn` by
     (qpat_assum `compile_store_memory_typed _ _ _ _ _ sm = ((),sn)` mp_tac >>
      POP_ASSUM_LIST kall_tac >> metis_tac[cj 1 ci_mono_typed_memory_family,pairTheory.SND]) >>
   `ci_mono sn sb` by
     (qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ sn = ((),sb)` mp_tac >>
      POP_ASSUM_LIST kall_tac >> metis_tac[cj 1 ci_mono_stmt_helpers,pairTheory.SND]) >>
   `ci_mono su sn` by (irule ci_mono_trans >> qexists `sm` >> simp[]) >>
   map_every (fn pat => qpat_assum pat (strip_assume_tac o REWRITE_RULE [ci_mono_def]))
     [`ci_mono su sm`,`ci_mono sm sn`,`ci_mono sn sb`,`ci_mono su sn`] >>
   qspecl_then [`su`,`sn`,`sb`,`func`] mp_tac fn_has_code_split >> simp[] >> strip_tac >>
   qspecl_then [`su`,`sm`,`sn`,`func`] mp_tac fn_has_code_split >> simp[] >> strip_tac) g;

fun nested_immutable_normalize_metadata g =
  (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
     qpat_assum `expr_sim_inv cenv cx env ee`
       (strip_assume_tac o MATCH_MP immutable_assign_copy_metadata o CONJ inv))) g;

fun nested_immutable_normalize_execute start g =
  (`w2n (n2w b:bytes32) = b /\ type_memory_size ptv < dimword (:256)` by
     (simp[w2n_n2w,LESS_MOD] >> decide_tac) >>
   `val_wf ptv v` by metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf] >>
   `compile_alloc_buffer (type_memory_size ptv) su = (buf,sm)` by simp[] >>
   mp_tac (Q.INST [`s` |-> `z`,`es` |-> `ee`,`dty` |-> `ty`,`dtv` |-> `ptv`,
     `sty` |-> `lowered_value_type cenv e`,`xs` |-> `src`,`sw` |-> `n2w b`,
     `start` |-> start,`sa` |-> `su`,`sb` |-> `sn`,`G` |-> `Gz`,`tn` |-> `tnz`,
     `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
     (INST_TYPE [``:'a`` |-> ``:256``,``:'b`` |-> ``:256``]
       body_assign_immutable_normalize_joint)) >>
   (impl_tac >- (simp[SF CONJ_ss] >> first_assum ACCEPT_TAC)) >>
   disch_then (qx_choosel_then [`zn`,`root`,`bn`,`Gn`,`tnn`]
      (map_every assume_tac o CONJUNCTS))) g;

fun nested_immutable_normalize_reserved g =
  (`sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
       sn.cs_next_var <= sb.cs_next_var` by
     decide_tac >>
   `local_ptrs_reserved cenv sn` by
     (irule local_ptrs_reserved_next_var >> qexists `su` >> simp[]) >>
   `return_buf_frame d cenv sn zn` by
     (irule return_buf_frame_frame >> qexistsl [`cenv`,`z`,`su`] >> simp[SF CONJ_ss]) >>
   `!x. not_fresh_at sa x ==> not_fresh_at sn x` by
     (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
   `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x` by simp[] >>
   `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x` by simp[]) g;

fun nested_immutable_normalize_horizon g =
  (`!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee zn /\ storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx ee Gn tnn zn /\ dead_lo_ok H (DF H) lo cenv cx` by
     (gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
           stmt_state_rel H ctx func cenv cx ee z /\ _`
        (qspec_then `H` (drule_then strip_assume_tac)) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      first_assum irule >> first_assum ACCEPT_TAC)) g;

fun nested_immutable_normalize_pointer g =
  (`!l. FST r <> Label l` by
     (qpat_assum `compile_get_target_ptr compile_expr cenv t _ = (r,_)`
        (mp_then Any mp_tac targetSubscriptSplitTheory.target_subscript_typed_base_not_label) >>
      disch_then (drule_at (Pat `type_place_target _ _ = _`)) >>
      disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >> simp[]) >>
   `copy_old_operand sn (FST r) /\ eval_operand (FST r) zn = SOME (n2w (off+k)) /\
       op_taint tnn (FST r) = {} /\ op_prov Gn (FST r) = NONE` by
     (qpat_assum `copy_old_operand su (FST r)` mp_tac >>
      qpat_assum `eval_operand (FST r) z = SOME (n2w (off+k))` mp_tac >>
      qpat_assum `op_taint tnz (FST r) = {}` mp_tac >>
      qpat_assum `op_prov Gz (FST r) = NONE` mp_tac >>
      qpat_assum `!l. FST r <> Label l` mp_tac >>
      qpat_assum `!x. not_fresh_at su x ==> not_fresh_at sn x /\ _` mp_tac >>
      POP_ASSUM_LIST kall_tac >>
      Cases_on `FST r` >> simp[copy_old_operand_def,eval_operand_def,op_taint_def,op_prov_def] >>
      metis_tac[])) g;

fun nested_immutable_normalize_base g =
  (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee zn /\ _`
     (qspec_then `H0` (drule_then strip_assume_tac)) >>
   nested_immutable_base_operand ``zn:venom_state`` ``sn:compile_state``
     ``Gn:(string,num # num) fmap`` ``tnn:taint``) g;

fun nested_immutable_normalize_alloca_frame g =
  (`alloca_frame cenv es sa s0 cenv ee zn` by
     (irule alloca_frame_trans >> qexistsl [`cenv`,`ee`,`z`,`su`] >> simp[]) >>
   `!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa.cs_next_id /\
       (!nm b cap. local_region cenv es.scopes s0 nm b cap ==> a+n <= b \/ b+cap <= a) /\
       a <= i /\ i < a+n /\ i IN tnn.t_mem ==> i IN tn0.t_mem` by
     (qx_genl_tac [`old_aid`,`old_off`,`old_size`,`i`] >> strip_tac >>
      `FLOOKUP z.vs_allocas old_aid = SOME (old_off,old_size)` by simp[] >>
      `old_aid < su.cs_next_id` by decide_tac >>
      `!nm b cap. local_region cenv ee.scopes z nm b cap ==>
         old_off+old_size <= b \/ b+cap <= old_off` by
        (qpat_assum `alloca_frame cenv es sa s0 cenv ee z`
          (qspecl_then [`old_aid`,`old_off`,`old_size`] mp_tac o REWRITE_RULE [alloca_frame_def]) >>
         simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> first_assum ACCEPT_TAC) >>
      `i IN tnz.t_mem` by
        (qpat_assum `!aid a n i. FLOOKUP z.vs_allocas aid = _ /\ _ ==> i IN tnz.t_mem`
          (qspecl_then [`old_aid`,`old_off`,`old_size`,`i`] mp_tac) >>
         simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
      qpat_assum `!aid a n i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> i IN tn0.t_mem`
        (qspecl_then [`old_aid`,`old_off`,`old_size`,`i`] mp_tac) >>
      simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> simp[])) g;

fun nested_immutable_normalize_origin_frames g =
  (`s0.vs_alloca_next <= zn.vs_alloca_next` by decide_tac >>
   `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x zn = SOME w` by
     simp[SF CONJ_ss] >>
   `!a b. FLOOKUP s0.vs_allocas a = SOME b ==> FLOOKUP zn.vs_allocas a = SOME b` by
     (rpt strip_tac >>
      qpat_assum `!aid b. FLOOKUP z.vs_allocas aid = SOME b ==> _` irule >> simp[]) >>
   `!x. not_fresh_at sa x ==>
       FLOOKUP Gn x = FLOOKUP G0 x /\ op_taint tnn (Var x) = op_taint tn0 (Var x)` by
     simp[SF CONJ_ss]) g;

fun nested_immutable_normalize_store origin g =
  (irule gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix >>
   qexistsl [`Gn`,`zn`,`tnn`] >> conj_tac >- simp[] >>
   qpat_assum `buf.buf_operand = Var root` (fn src =>
     qpat_assum `type_memory_bytes cenv ty = type_memory_size ptv` (fn width =>
       qpat_assum `compile_assign_value cenv (FST r) LocCode buf.buf_operand F
           (vv_location ^origin) ty ty _ sn = ((),sb)`
         (assume_tac o REWRITE_RULE [src,width]))) >>
   mp_tac (Q.INST [`ce` |-> `cenv`,`dst` |-> `FST (r : operand # data_location option # place_ty option)`,`off` |-> `off+k`,
     `s` |-> `zn`,`G` |-> `Gn`,`tn` |-> `tnn`,`sa` |-> `sn`,
     `tv` |-> `ptv`,`a` |-> `bn`,`src` |-> `root`,`loc` |-> `vv_location ^origin`,
     `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] immutable_path_store_fixed) >>
   (impl_tac >- simp[eval_operand_def]) >>
   nested_immutable_finish `zn:venom_state` `sn` `Gn` `tnn`) g;

Theorem body_assign_nested_nonempty_immutable_full:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    struct_args_unique tops /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    immutable_root cx t /\ ~(?nsid. t = TopLevelNameTarget nsid) /\
    ~supported_stmt_expr_exists (const_name_root cx) (Assign (BaseTarget t) e) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e)))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule body_assign_other_value_rhs_bind >>
  rpt (CHANGED_TAC (first_assum (irule_at Any))) >>
  asm_rewrite_tac[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `mid with gas_obs := [] = mid` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `read_result cx tv mid = (INL v,mid)` by
    (qpat_assum `!tail. read_result cx tv (mid with gas_obs := tail) = _`
       (qspec_then `[]` mp_tac) >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
                vv_post H ctx func cenv cx e es sa sr s0 mid tv vv0 s /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  `return_buf_frame d cenv sr s` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`,`s0`,`sa`] >>
     fs[ci_mono_def, vv_post_def]) >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,mid)` by
    (qpat_assum `!tail. eval_expr cx e _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => simp[NoAsms, listTheory.APPEND_NIL, th])) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\
       vv_post H ctx func cenv cx e es sa sr s0 mid tv vv0 s /\
       ghost_inv_at (DF H) lo d cenv cx mid G tn s` by
    (rpt gen_tac >> strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       (drule_at (Pos (el 2)) valid_horizon_frame >>
        simp[cj 5 evaluate_storage_trace_frame]) >>
     metis_tac[]) >>
  drule body_assign_empty_target_typing >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `ty` strip_assume_tac))) >>
  drule_all immutable_rhs_physical_widens >> strip_tac >>
  `is_word_type ty ==> expr_type e = ty /\
      lowered_value_type cenv e = ty /\ post_value_type cenv e = ty` by
    (strip_tac >> imp_res_tac compileEnvTheory.type_widens_to_word >> simp[]) >>
  `(do pv <- eval_expr cx e; read_result cx pv od)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    simp[bind_def] >>
  `expr_body_pre cenv cx env e
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all immutable_rhs_physical_typed >> strip_tac >>
  drule_all type_widens_to_value_has_type >> strip_tac >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`well_typed_expr env e` by
       qpat_assum `expr_body_pre cenv cx env e es`
         (ACCEPT_TAC o cj 2 o MATCH_MP expr_body_pre_static_facts) >>
     irule body_const_cells_agree_expr_read >>
     qexistsl_tac [`e`, `INL v`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`] >>
     simp[] >>
     qpat_assum `(do pv <- eval_expr cx e; read_result cx pv od) _ = (INL v,mid)`
       (ACCEPT_TAC o CONV_RULE (DEPTH_CONV ETA_CONV))) >>
  `target_indices_pre cenv cx env t` by
    (drule_all body_assign_target_indices_pre >> simp[]) >>
  `IS_SOME (type_place_target env t)` by simp[] >>
  drule_all_then (qx_choosel_then [`id`,`ity`] strip_assume_tac)
    bodyFullTargetRootsTheory.typed_immutable_target_root >>
  `call_evaluation_safe cx (int_calls_target t)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_stmt (Assign _ _))`
       (mp_tac o REWRITE_RULE [Once int_calls_stmt_def,Once int_calls_atarget_def]) >>
     disch_then (mp_then Any ACCEPT_TAC call_evaluation_safe_append_left)) >>
  `allocas_from lo s0` by
    (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
          es.storage_trace` by fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon es.storage_trace` (drule_then strip_assume_tac)) >>
     qpat_assum `ghost_inv_at _ lo d cenv cx es G0 tn0 s0`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     first_assum ACCEPT_TAC) >>
  `ci_mono sa su` by metis_tac[ci_mono_trans] >>
  `assign_target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx env t mid` by
    (irule assign_target_place_sim_full >> simp[] >>
     irule body_imm_target_place_sim_full >> simp[] >>
     qexists_tac `tops` >> simp[]) >>
  `gas_admissible (eval_target_place cx t) target_place_res_ok mid` by
    (mp_tac (Q.INST [`prefix` |-> `gas_explicit marks s0.vs_gas_readings`]
       body_assign_saved_target_admissible) >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  `(cenv.ce_is_ctor /\ vv_location vv0 = SOME LocCode) ==>
     !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
       eval_operand (vv_operand vv0) s = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v (w2n w) mem)` by
    (strip_tac >> qpat_x_assum `_ ==> ?val. read_result cx tv mid = _ /\ _` mp_tac >> simp[]) >>
  qpat_x_assum `(expr_can_mutate _ _ /\ _) \/ _`
    (DISJ_CASES_THEN (map_every assume_tac o CONJUNCTS))
  >- (irule body_assign_other_snapshot_target_bind >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      qexistsl [`G0`,`cenv`,`d`,`e`,`env`,`es`,`op`,`tv`,`r`,`marks`,
                `s0`,`sa`,`shadow_func`,`ts`,`tt`,`sr`,`vv`,`ss`,`st`,
                `su`,`tn0`,`tops`,`ty`,`vv0`] >> simp[] >>
      suspend "snapshot_write") >>
  qpat_x_assum `ss = sr` SUBST_ALL_TAC >>
  qpat_x_assum `ts = tr` SUBST_ALL_TAC >>
  qpat_x_assum `vv = vv0` SUBST_ALL_TAC >>
  `runtime_consistent env cx es /\ functions_well_typed cx` by
    fs[expr_sim_inv_def, runtime_consistent_def] >>
  `!x. vv_operand vv0 = Var x ==> not_fresh_at sr x` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var] >>
  `!l. vv_operand vv0 <> Label l` by
    (drule_all assignPlaceOperandFactsTheory.assign_place_operand_not_label >> simp[]) >>
  irule body_assign_other_saved_target_bind >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`G0`,`bindings`,`cenv`,`d`,`e`,`env`,`env'`,`es`,`lctx`,`op`,
            `gas_explicit marks s0.vs_gas_readings`,`r`,`ret_ty`,`s0`,`sa`,
            `st`,`su`,`sb`,`shadow_func`,`tr`,`tt`,`sr`,`tn0`,`tops`,`tv`,`vv0`] >>
  simp[] >> reverse conj_tac
  >- (Cases_on `FST (SND r)` >> fs[]) >>
  suspend "saved_write"
QED


Resume body_assign_nested_nonempty_immutable_full[saved_write]:
  qx_genl_tac [`target_marks`,`p`,`ee`,`Gu`,`tnu`,`u`,`z`,`Gz`,`tnz`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `target_gas = gas_explicit target_marks s.vs_gas_readings` >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by
    fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> assign_target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  qsuff_tac `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee z /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee Gz tnz z /\ dead_lo_ok H (DF H) lo cenv cx`
  >- suspend "saved_target" >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> assign_target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  fs[expr_post_def]
QED

Resume body_assign_nested_nonempty_immutable_full[snapshot_write]:
  qx_genl_tac [`target_marks`,`p`,`ee`,`z`,`Gz`,`tnz`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `target_gas = gas_explicit target_marks u.vs_gas_readings` >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by
    fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> assign_target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  qsuff_tac `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee z /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee Gz tnz z /\ dead_lo_ok H (DF H) lo cenv cx`
  >- suspend "snapshot_target" >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> assign_target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  fs[assign_target_post_def,imm_target_post_def]
QED

Resume body_assign_nested_nonempty_immutable_full[snapshot_target]:
  strip_tac >>
  nested_immutable_target_post >>
  nested_immutable_target_eval >>
  nested_immutable_target_writable >>
  nested_immutable_target_layout >>
  nested_immutable_target_section >>
  nested_immutable_target_bounds >>
  nested_immutable_target_size >>
  nested_immutable_target_operands >>
  nested_immutable_target_assign ``vv:vyper_value`` >>
  `is_word_type ty <=> is_word_type (lowered_value_type cenv e)` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq] >>
  Cases_on `is_word_type ty`
  >- (`lowered_value_type cenv e = ty` by metis_tac[] >>
      qpat_x_assum `is_word_type (lowered_value_type cenv e) /\ _ \/ _` mp_tac >>
      simp[] >> strip_tac >>
      `stv = ptv` by metis_tac[optionTheory.SOME_11] >>
      `eval_operand op z = SOME (typed_val_to_w256 ptv v)` by simp[] >>
      suspend "snapshot_word") >>
  suspend "snapshot_nonword"
QED

Resume body_assign_nested_nonempty_immutable_full[saved_target]:
  strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee z /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  nested_immutable_target_post >>
  nested_immutable_target_eval >>
  nested_immutable_target_writable >>
  nested_immutable_target_layout >>
  nested_immutable_target_section >>
  nested_immutable_target_bounds >>
  nested_immutable_target_size >>
  nested_immutable_target_operands >>
  nested_immutable_target_assign ``vv0:vyper_value`` >>
  qpat_assum `stmt_state_rel H0 ctx func cenv cx ee z`
    (assume_tac o MATCH_MP stmt_state_rel_allocas_below_fmp) >>
  qpat_assum `wb_frame cenv es ee sa s0 z`
    (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tnz`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  `!x. vv_operand vv0 = Var x ==> not_fresh_at st x` by
    (rpt strip_tac >> irule compiler_ci_mono_not_fresh >> qexists_tac `sr` >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at su x` by
    (qpat_assum `unwrap_value cenv vv0 st = (op,su)` mp_tac >>
     qpat_assum `!x. vv_operand vv0 = Var x ==> not_fresh_at st x` mp_tac >>
     POP_ASSUM_LIST kall_tac >> rpt disch_tac >>
     drule compiler_unwrap_value_var >> Cases_on `vv0` >> fs[vv_operand_def]) >>
  Cases_on `is_word_type ty`
  >- (`post_value_type cenv e = ty` by metis_tac[] >>
      `eval_operand op z = SOME (typed_val_to_w256 ptv v)` by
        (qpat_assum `expr_post H0 _ _ _ _ e _ _ _ _ ee v op z` mp_tac >>
         qpat_assum `evaluate_type (get_tenv cx) ty = SOME ptv` mp_tac >>
         qpat_assum `post_value_type cenv e = ty` mp_tac >>
         qpat_assum `is_word_type ty` mp_tac >>
         POP_ASSUM_LIST kall_tac >> simp[expr_post_def,expr_val_rel_def] >> metis_tac[]) >>
      qpat_assum `ptr_val_ok cx (post_value_type cenv e) v op Gz tnz z`
        (assume_tac o CONJUNCT1 o REWRITE_RULE [ptr_val_ok_def]) >>
      suspend "saved_word") >>
  suspend "saved_nonword"
QED

Resume body_assign_nested_nonempty_immutable_full[snapshot_word]:
  nested_immutable_word_width >>
  nested_immutable_write_base >>
  nested_immutable_word_execution ``vv:vyper_value`` >>
  nested_immutable_finish `z:venom_state` `su` `Gz` `tnz`
QED

Resume body_assign_nested_nonempty_immutable_full[saved_word]:
  nested_immutable_word_width >>
  nested_immutable_write_base >>
  nested_immutable_word_execution ``vv0:vyper_value`` >>
  nested_immutable_finish `z:venom_state` `su` `Gz` `tnz`
QED

Resume body_assign_nested_nonempty_immutable_full[snapshot_nonword]:
  nested_immutable_class_compile `~is_word_type ty` >>
  `~is_word_type (lowered_value_type cenv e)` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq] >>
  qpat_x_assum `is_word_type (lowered_value_type cenv e) /\ _ \/ _` mp_tac >>
  simp[] >>
  disch_then (qx_choosel_then [`aid`,`src`,`b`] strip_assume_tac) >>
  `op = Var src` by first_assum ACCEPT_TAC >>
  `eval_operand op z = SOME (n2w b)` by fs[eval_operand_def] >>
  qpat_x_assum `op = Var src` SUBST_ALL_TAC >>
  nested_immutable_footprints >>
  nested_immutable_write_base >>
  Cases_on `is_bytestring_type ty` >- nested_immutable_bytes_suffix >>
  Cases_on `lowered_value_type cenv e = ty` >- (nested_immutable_fixed_suffix ``vv:vyper_value``) >>
  `w2n (n2w b:bytes32) = b` by (simp[w2n_n2w,LESS_MOD] >> decide_tac) >>
  `expr_val_at cenv cx (lowered_value_type cenv e) (su with cs_next_id := aid)
    su ee v (Var src) z` by
    (simp[expr_val_at_def,eval_operand_def] >>
     disj1_tac >> qexistsl [`aid`,`b`,`type_memory_size stv`] >>
     simp[] >> fs[loweringStateRelDefsTheory.regions_disjoint_def] >>
     metis_tac[val_footprint_le,ADD_COMM]) >>
  suspend "snapshot_normalize"
QED

Resume body_assign_nested_nonempty_immutable_full[saved_nonword]:
  nested_immutable_class_compile `~is_word_type ty` >>
  `~is_word_type (lowered_value_type cenv e)` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq] >>
  `~is_word_type (post_value_type cenv e)` by
    metis_tac[immutable_rhs_post_physical_classify,valueCopyBytesTheory.is_bytestring_word_type] >>
  `expr_val_at cenv cx (lowered_value_type cenv e) sa su ee v op z` by
    (irule abi_args_expr_post_lowered_at >>
     rpt (CHANGED_TAC (first_assum (irule_at Any))) >>
     fs[valueTypingMemoryPropsTheory.value_has_type_memory_wf]) >>
  nested_immutable_footprints >>
  `?sw. eval_operand op z = SOME sw` by
    fs[expr_post_def,expr_val_rel_def] >>
  qpat_assum `ptr_val_ok cx (post_value_type cenv e) v op Gz tnz z`
    (assume_tac o CONJUNCT1 o REWRITE_RULE [ptr_val_ok_def]) >>
  `!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==>
     val_in_memory stv v (w2n sw) mem` by
    (drule immutable_rhs_post_physical_classify >> strip_tac
     >- fs[ptr_val_ok_def,ptr_mem_ok_def] >>
     `type_widens_to (get_tenv cx) (lowered_value_type cenv e) (post_value_type cenv e)` by
       metis_tac[immutable_rhs_physical_post_widens] >>
     drule_all_then (qx_choose_then `post_tv` strip_assume_tac)
       (Q.INST [`u` |-> `post_value_type cenv e`] type_widens_to_value_has_type) >>
     rpt strip_tac >>
     `val_in_memory post_tv v (w2n sw) mem` by fs[ptr_val_ok_def,ptr_mem_ok_def] >>
     metis_tac[bytestring_val_in_memory_transfer]) >>
  `?src. op = Var src /\ ptr_covers Gz tnz src z (type_memory_size stv)` by
    (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
     simp[] >> qexistsl [`cenv`,`e`] >> simp[]) >>
  `w2n sw + type_memory_size stv <= z.vs_alloca_next` by
    (qpat_assum `~is_word_type (post_value_type cenv e) ==> !w. eval_operand op z = SOME w ==> _`
       (drule_then (qspec_then `sw` (drule_then strip_assume_tac))) >>
     decide_tac) >>
  `z.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx ee z`
       (ACCEPT_TAC o MATCH_MP alloca_room_next_lt o
        MATCH_MP stateRelProjTheory.stmt_state_rel_alloca_room)) >>
  `w2n sw + type_memory_size stv < dimword (:256)` by decide_tac >>
  `!n a k. local_region cenv ee.scopes z n a k /\ 0 < k ==> lo <= a` by
    (rpt strip_tac >> drule_all (INST_TYPE [``:'a`` |-> ``:256``]
       body_full_local_region_lower_bound) >> simp[]) >>
  `lo <= w2n sw` by
    (`(?aid a k. FLOOKUP z.vs_allocas aid = SOME (a,k) /\ a <= w2n sw) \/
      (?n a k. local_region cenv ee.scopes z n a k /\ 0 < k /\ a <= w2n sw)` suffices_by
     (strip_tac
      >- (`lo <= a` by
            (qpat_assum `allocas_from lo z` (drule_then ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
          decide_tac) >>
      `lo <= a` by
        (qpat_assum `!n a k. local_region cenv ee.scopes z n a k /\ _ ==> _`
           (drule_all_then ACCEPT_TAC)) >> decide_tac) >>
     Cases_on `is_bytestring_type (lowered_value_type cenv e)`
     >- (`is_sized_type (lowered_value_type cenv e)` by
           (qpat_x_assum `is_bytestring_type _` mp_tac >>
            Cases_on `lowered_value_type cenv e` >> simp[is_bytestring_type_def] >>
            Cases_on `b` >> simp[is_bytestring_type_def,is_sized_type_def] >>
            Cases_on `b'` >> simp[is_bytestring_type_def,is_sized_type_def]) >>
         `32 <= val_footprint stv v` by
           (drule_all bodyPtrEnvBuiltinsLenTheory.sized_val_footprint_header >> simp[]) >>
         qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _`
           (qspec_then `stv` mp_tac o REWRITE_RULE[expr_val_at_def]) >> simp[] >>
         disch_then strip_assume_tac
         >- (disj1_tac >> rpt (goal_assum (drule_at Any) >> simp[])) >>
         disj2_tac >> rpt (goal_assum (drule_at Any) >> simp[]) >> decide_tac) >>
     drule_all immutableDeployAssignRangesTheory.immutable_assign_nonbytes_source_owned >>
     simp[] >> disch_then strip_assume_tac
     >- (disj1_tac >> rpt (goal_assum (drule_at Any) >> simp[])) >>
     disj2_tac >> rpt (goal_assum (drule_at Any) >> simp[]) >> decide_tac) >>
  qabbrev_tac `b = w2n sw` >>
  `b < dimword (:256)` by simp[Abbr `b`] >>
  `n2w b : bytes32 = sw` by simp[Abbr `b`] >>
  qpat_x_assum `op = Var src` SUBST_ALL_TAC >>
  `lookup_var src z = SOME (n2w b)` by fs[eval_operand_def] >>
  nested_immutable_write_base >>
  Cases_on `is_bytestring_type ty` >- nested_immutable_bytes_suffix >>
  Cases_on `lowered_value_type cenv e = ty` >- (nested_immutable_fixed_suffix ``vv0:vyper_value``) >>
  suspend "saved_normalize"
QED

Resume body_assign_nested_nonempty_immutable_full[snapshot_normalize]:
  nested_immutable_normalize_compile >>
  nested_immutable_normalize_code >>
  nested_immutable_normalize_metadata >>
  nested_immutable_normalize_execute `su with cs_next_id := aid` >>
  nested_immutable_normalize_reserved >>
  nested_immutable_normalize_horizon >>
  nested_immutable_normalize_pointer >>
  nested_immutable_normalize_base >>
  nested_immutable_normalize_alloca_frame >>
  nested_immutable_normalize_origin_frames >>
  nested_immutable_normalize_store ``vv:vyper_value``
QED

Resume body_assign_nested_nonempty_immutable_full[saved_normalize]:
  nested_immutable_normalize_compile >>
  nested_immutable_normalize_code >>
  nested_immutable_normalize_metadata >>
  nested_immutable_normalize_execute `sa` >>
  nested_immutable_normalize_reserved >>
  nested_immutable_normalize_horizon >>
  nested_immutable_normalize_pointer >>
  nested_immutable_normalize_base >>
  nested_immutable_normalize_alloca_frame >>
  nested_immutable_normalize_origin_frames >>
  nested_immutable_normalize_store ``vv0:vyper_value``
QED

Finalise body_assign_nested_nonempty_immutable_full

Theorem body_assign_other_full:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    struct_args_unique tops /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              is_word_type ty) /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              ~is_word_type ty /\
              (expr_type e = ty \/ lowered_value_type cenv e = ty \/
               is_bytestring_type ty \/
               has_length_word (expr_type e) /\ is_empty_value_expr e)) /\
    ~(?nsid dty. t = TopLevelNameTarget nsid /\
          supported_scalar_target tops nsid /\
          type_place_target env t = SOME (Type dty) /\ is_word_type dty) /\
    ~(?nsid mut ty slot.
        t = TopLevelNameTarget nsid /\
        supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
        (mut = Storage \/ mut = Transient) /\
        ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
        ~is_bytestring_type ty /\
        0 < type_memory_bytes cenv ty /\ expr_type e = ty /\
        lowered_value_type cenv e = expr_type e) /\
    ~(?id fld sid fty.
        t = AttributeTarget (NameTarget id) fld /\
        FLOOKUP env.var_types id = SOME (StructT sid) /\
        attribute_type env.type_defs (StructT sid) fld = SOME fty /\
        is_word_type fty) /\
    ~(?nsid fld fty.
        t = AttributeTarget (TopLevelNameTarget nsid) fld /\
        supported_storage_field_write tops nsid fld /\
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e)))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e`
  >- (qpat_x_assum `has_length_word _ /\ is_empty_value_expr _` strip_assume_tac >>
      Cases_on `immutable_root cx t`
      >- (Cases_on `?nsid. t = TopLevelNameTarget nsid`
          >- (qspecl_then
                [`cx`,`t`,`e`,`DF`,`lo`,`d`,`PG`,`tops`,`bindings`,`ctx`,
                 `shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`env'`,`ret_ty`,
                 `lctx`,`RetQ`,`es`] MATCH_MP_TAC body_assign_other_empty_immutable_full >>
              rpt conj_tac >> first_assum ACCEPT_TAC) >>
          drule_all bodySimTheory.body_inv_stmt_const_name_free >> strip_tac >>
          qspecl_then
            [`cx`,`t`,`e`,`DF`,`lo`,`d`,`PG`,`tops`,`bindings`,`ctx`,
             `shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`env'`,`ret_ty`,
             `lctx`,`RetQ`,`es`] MATCH_MP_TAC body_assign_nested_empty_immutable_full >>
          rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac[])) >>
      irule body_assign_other_empty_target_full >>
      rpt (CHANGED_TAC (first_assum (irule_at Any))) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  reverse (Cases_on `immutable_root cx t`)
  >- (irule body_assign_other_nonempty_target_full >>
      rpt (CHANGED_TAC (first_assum (irule_at Any))) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  reverse (Cases_on `?nsid. t = TopLevelNameTarget nsid`)
  >- (drule_all bodySimTheory.body_inv_stmt_const_name_free >> strip_tac >>
      irule body_assign_nested_nonempty_immutable_full >> metis_tac[]) >>
  qpat_x_assum `?nsid. t = TopLevelNameTarget nsid`
    (qx_choose_then `root` assume_tac) >>
  irule body_assign_other_immutable_frontier_bind >>
  rpt (CHANGED_TAC (first_assum (irule_at Any))) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type ity`
  >| [irule body_assign_other_immutable_word_write_full,
      irule body_assign_other_immutable_nonword_write_full] >>
  qpat_assum `supported_stmt tops bindings (Assign (BaseTarget t) e)` (irule_at Any) >>
  qpat_assum `type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env'` (irule_at Any) >>
  qpat_assum `compile_get_target_ptr compile_expr cenv t =
    comp_return (Lit (n2w off),SOME LocCode,SOME (ValPT ity))` (irule_at Any) >>
  qpat_assum `compile_expr cenv (expr_type e) e sa = (vv,sm)` (irule_at Any) >>
  qpat_assum `lower_value compile_expr _ _ (gas_shadow_expr _) _ = _` (irule_at Any) >>
  qexistsl [`su`, `shadow_sb`, `shadow_func`, `marks`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* A static aggregate storage or transient variable. *)
Theorem body_assign_toplevel_copy_full:
  !cx nsid mut ty slot e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (TopLevelNameTarget nsid)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    struct_args_unique tops /\
    supported_stmt tops bindings (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (TopLevelNameTarget nsid)) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
    (mut = Storage \/ mut = Transient) /\
    ~is_word_type ty /\
    ~is_bytestring_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
    0 < type_memory_bytes cenv ty /\
    expr_type e = ty /\ lowered_value_type cenv e = expr_type e ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[evaluate_storage_trace_frame] >>
  simp[] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule_all body_assign_toplevel_copy_entry >> strip_tac >> gnvs[] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by metis_tac[body_expr_full_ok_def] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,
    `op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q1 _` >>
  irule body_assign_toplevel_word_full_source >>
  conj_tac >- (qexists `lctx` >> simp[]) >> qexists `Q1` >>
  reverse conj_tac >-
    (irule gas_outcome_full_post_mono >> goal_assum (drule_at Any) >>
     simp[] >> rpt gen_tac >> POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     Cases_on `res` >> fs[expr_exit_def] >> Cases_on `y` >> Cases_on `r` >>
     gvs[stmt_exit_ptr_def,expr_exit_def,halt_exit_INR_type] >>
     rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]) >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  simp[Abbr `Q1`, NoAsms] >> (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >> gnvs[post_value_type_lowered] >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    drule_then (ACCEPT_TAC o MATCH_MP contract_inv_acyclic_struct_metadata) body_inv_contract >>
  `!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x` by
    metis_tac[local_ptrs_reserved_imm_base] >>
  irule body_assign_toplevel_copy_after_rhs_frame >>
  qpat_assum `find_var_decl_by_name _ _ = _` (irule_at Any) >>
  qpat_assum `lookup_var_slot_from_layout _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_store_slots _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr _ _ e sa = _` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >>
  qexistsl [`v`,`tv`,`tn1`,`t`,`mid`,`marks`,`G1`] >>
  simp[SF CONJ_ss] >>
  qpat_x_assum `expr_sim_inv cenv cx env es` mp_tac >>
  simp[expr_sim_inv_def] >> strip_tac >> simp[]
QED
