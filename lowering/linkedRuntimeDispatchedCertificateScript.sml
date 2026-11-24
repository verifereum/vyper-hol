(* Fix the compiled GAS shadow before taking the raw runtime state. *)
Theory linkedRuntimeDispatchedCertificate
Ancestors
  sourceUnitExecutionMods gasShadowRunLowering gasShadowUnit
  gasShadowModuleDefs compileUnit compileVyper vyperCompiler list pair option
  linkedContractInvProducer bodyInvSplit runtimeUnitShapeMods
  e2eModsDefs vyperInterpreter linkedLinearShadowBodyInv linkedDispatchedSource
  dispatchedCallAssemblyMods dispatchedSignatureOriginMods dispatchedSignatureLookupMods
  linkedGroupedSignatureRoutes linkedGroupedDefaultSource linkedGroupedDefaultSyntax
  groupedEntryPackage calldataSelectorProps selectorCompilerProps
  dispatchedClassifierMods dispatchedClassifiedRouteMods
  defaultDispatchModsFallback defaultDispatchModsRun entryRejectCode
  defaultDispatchModsGetter defaultDispatchModsNames entryDispatchProps
  runtimeFallbackSourceAlignment[qualified] loweringShapeProps[qualified]
  linkedExternalParameterTypes linkedRegistrationPackageInputs linkedLinearSelectedCode
  constSubstMods compileEnv moduleLowering vyperTypeContractContext vyperTypeContract
  vyperCalldata vyperABIEntries alist venomInst sourceValueRejection venomState
  linkedLinearDispatchPath linkedEntryCheckResources linkedRawUnitShape
  entryChecksPassPtr emitHelperProps defaultConcreteRegistrationDefs
  loweringStateRelDefs fragExec fragGasOriginPtrLoop vyperLoweringCorrect moduleLoweringProps
  selectedAcceptedFold selectedAcceptedDecoder selectedAcceptedSingleton
  acceptedContextPhi actualEntryAllocationFrame entryLocals entryStateRel
  externalEntryChecks ctorRegisterArgs allocaFrontierBound allocaFrontierRoom
  exprLoweringProps ptrDiscipline
  vyperCall finite_map venomFnInstsProofs vyperTypeContractGetter
  entryPtrSeamRegister entryPtrSeamRegisterMods decoderOriginAllocationFrame entryReachBodyFmp
  bodyPtrDefs fragGasOriginPtr bodyLoopCalls linkedBodyLoopCalls
  externalBodySupport externalBodyFrame bodyInvCodeProps vyperTypeInvariants nonreentrantEntryPath
  vyperTypeContractSoundness vyperTypeExternalDefaults vyperTypeCallStackSoundness
  gasShadowRuntimeBodies gasShadowState gasShadowRuntimeOps gasShadowRuntimeRegisterEnv
  gasShadowCompileStmtBase gasShadowUnitExtract gasShadowUnitGuards runtimeBodyRetainedInterval
  loweringShapeDefs bodyFullShadowInternalRun bodyFullShadowBodyInv[qualified]
  linkedLiveBodyEntry vyperTypeCallGraphSoundness
  vyperGetter groupedInternalLabels groupedRuntimeBodyCode groupedDispatchPath
  groupedLegacyPairedCode
  groupedLegacyCheckSeam groupedDefaultArguments linkedRuntimeValueRejection
  groupedDefaultSuppliedCut abiDecoderCoherence groupedEntryCounters groupedEntryAllocation abiAllocationHistory constSubst rich_list vyperTypeEvalProofs
  vyperReadOnlySyntax bodyFullPathHistory allocaHistory bodyFullPostsMods vyperExternalEntryStorageFrame
  linkedGroupedShadowBodyInv externalBodyWidths exprSimHypsDefs
  bodyFullPredsMods vyperSubscriptOverlap vyperTypeInvariants linkedExternalEntryExprInvariant vyperTypeContractStaticMaps
  externalEntryValueRevert entryJointRevertExit vyperTypeABI vyperStorageFootprint gasSummary
  fragGasPathMem venomInstIdsProps venomMemDefs venomMemProps venomWf words
  linkedCallPremises vyperTypeBindArguments vyperTypeInitialState
  entryModuleLocations bodySim bodySimEntry whitelistCheckerDecls
  vyperContext vyperState vyperTypeContractFunction bodyCallSupport linkedBodyConstantCells constSubstCorrect e2eDefs
  linkedEntryImmutableGuards[qualified] groupedDefaultPre[qualified] callRejectMemory[qualified]
  bodyFullIfExpReach[qualified] deployBodyReachability[qualified]
  contextRawReachable[qualified] unitTransformDefs[qualified] contextCodegenRel[qualified] supportedExprTraverse[qualified]
  exprSimSource[qualified] runtimeDefaultCompile[qualified] gasShadowCompileBase[qualified]
  supportedStmtTraverse[qualified] typedCopyProducer[qualified] bodySimFullMain[qualified]
  venomExecProps[qualified] linkedGroupedKeywordInitialize[qualified]
  entryRejectAllocationIds exprSafeOperand allocLimitsProps whitelistLinkedBodyCalls
  whitelistLinkedBodyData whitelistLinkedBodyTypes whitelistLinkedBodyEnv placeTypingProps
  whitelistCheckerFnSigs[qualified] whitelistLinkedBodyExprs[qualified] supportedExprs[qualified] supportedStmts[qualified]
  moduleVariableKeyProps linkedStructMemorySize structFieldsProps linkedGetterConstantSubstitution
  linkedConstantReplacementTyping linkedConstantReplacementValue vyperTypeSystem vyperAST
  linkedEntryBodyTables linkedFlagCount linkedStructFields linkedStorageMetadataProps
  linkedStorageLocationOrigin linkedConstAnnotations linkedTypedBodySupport linkedConstantSubstitutionIdempotence
  supportedProgram vyperImportRefs vyperImportRefsProps abiCallerStructSize
  vyperTypeConstantFold stmtSimProps[qualified] externalCallSelected[qualified] stmtsEnvRetTy[qualified]
  selectedAcceptedInterfaces[qualified] entryDispatchPtr[qualified] selectedEntryPrefixCode[qualified] externalEntryJoint[qualified]
  loweringPosts[qualified] context[qualified] externalEntryBound[qualified] bodySelectedLockedReplayMods[qualified]
  constSubstModsCorrect[qualified]
  linkedExternalFrameRet[qualified] linkedReturnAbiLayout[qualified]
  linkedSubstitutionAbiTargets[qualified] bodyAbiDecodeTarget[qualified]
  gasShadowStmtEnv[qualified] gasShadowModuleOps[qualified]
  gasContext[qualified] stmtSimDefs[qualified]
  vyperTypeStmtSoundness[qualified] vyperTypeExprSoundness[qualified]
  linkedRuntimeSourceLookup[qualified]
  gasPathDataSection[qualified] bodyFullHashKeccakFixed[qualified]
  linkedRuntimeSelectedTrace[qualified] unitExecutionComposeResult[qualified]
  linkedRuntimeDefaultReplay[qualified] linkedDefaultSourceFrame[qualified]
  groupedEntryCommon[qualified] calldataRegistrationLocals[qualified]
  dispatchedDecodeCast[qualified] dispatchedDecodeDomain[qualified]
  linkedDefaultError[qualified] gasExemptCertMods[qualified] gasOutcomeFullMods[qualified]
  loweringHalt[qualified] nonreentrantExit[qualified] sourceUnitExecution[qualified]
  stmtFragPtr[qualified] vyperCallFiniteStorageSupport[qualified] vyperEvalReadingErrors[qualified]
  groupedRejectCutObserver[qualified] linkedOwnedImmutableLocation[qualified]
  linkedConstAccessSubset[qualified]
  loweringShapeRules[qualified] loweringShapeSource compileUnitPackageShape fragFuel[qualified]
Libs runtimeDefaultRejectSyntaxLib groupedRejectCutLib

val _ = Parse.hide "tops";

(* Inputs for the successful omitted-default registration.  Keep the selected
   package's ordinary argument locations separate from the keyword overlay. *)
val linked_default_keyword_names_tac =
  `MAP FST kw = MAP (\(name,_,_,_). name) vars /\ LENGTH kw = LENGTH vars` by
    (qpat_assum `MAP (\(n,_,ty,_). (n,ty)) vars = kw` (SUBST1_TAC o SYM) >>
     simp[NoAsms, MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]);

val linked_default_source_bind_tac =
  `LIST_REL value_has_type kwtvs kwvals` by
    (qpat_assum `kwtvs = MAP _ slots` SUBST1_TAC >>
     pure_rewrite_tac[LIST_REL_MAP1] >>
     qpat_assum `LIST_REL (\(aid,p,base,tv) v. aid < keyword_end.cs_next_id /\ _) slots kwvals`
       mp_tac >> match_mp_tac LIST_REL_mono >> simp[NoAsms, FORALL_PROD]) >>
  `LIST_REL value_has_type (ptvs ++ kwtvs) (pvals ++ kwvals)` by
    (irule LIST_REL_APPEND_suff >> conj_tac >> first_assum ACCEPT_TAC) >>
  irule calldataRegistrationLocalsTheory.decoded_arguments_bind >>
  pure_rewrite_tac[LIST_REL_EL_EQN] >> conj_tac
  >- (qpat_assum `LIST_REL value_has_type (ptvs ++ kwtvs) _`
        (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
      qpat_assum `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) (MAP SND (pos ++ kw)) _`
        (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
      simp[NoAsms] >> decide_tac) >>
  qx_gen_tac `i` >> strip_tac >> BETA_TAC >>
  Cases_on `EL i (pos ++ kw)` >> REWRITE_TAC[pairTheory.UNCURRY] >> BETA_TAC >>
  qexists_tac `EL i (ptvs ++ kwtvs)` >>
  qpat_assum `LIST_REL value_has_type (ptvs ++ kwtvs) _`
    (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  qpat_assum `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) (MAP SND (pos ++ kw)) _`
    (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  qpat_assum `i < LENGTH (pos ++ kw)` (fn bound =>
    simp_tac bool_ss [LENGTH_MAP, EL_MAP, bound]) >>
  strip_tac >> strip_tac >>
  `i < LENGTH (ptvs ++ kwtvs)` by
    (qpat_assum `LENGTH (pos ++ kw) = LENGTH (ptvs ++ kwtvs)` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!j. j < LENGTH (pos ++ kw) ==> _` (qspec_then `i` mp_tac) >>
  qpat_assum `!j. j < LENGTH (ptvs ++ kwtvs) ==> _` (qspec_then `i` mp_tac) >>
  qpat_assum `EL i (pos ++ kw) = _` (fn pair =>
    qpat_assum `i < LENGTH (pos ++ kw)` (fn b =>
      qpat_assum `i < LENGTH (ptvs ++ kwtvs)` (fn b' =>
        simp[NoAsms, EL_MAP, pair, b, b'])));

val linked_default_initialized_owners_tac =
  `ALL_DISTINCT (MAP (\(name,_,_,_). name) vars)` by
    (qpat_assum `MAP FST kw = _` (SUBST1_TAC o SYM) >>
     qpat_assum `ALL_DISTINCT (MAP FST (pos ++ kw))` mp_tac >>
     simp[NoAsms, MAP_APPEND, ALL_DISTINCT_APPEND]) >>
  `LIST_REL (\(aid,p,base,tv) v. aid < keyword_end.cs_next_id /\
    FLOOKUP keyword_state.vs_allocas aid = SOME (base,type_memory_size tv) /\
    lookup_var p keyword_state = SOME (n2w base) /\
    ptr_covers Ginit tninit p keyword_state (type_memory_size tv) /\ value_has_type tv v /\
    (!mem. mem_agree_outside tninit.t_mem keyword_state.vs_memory mem ==> val_in_memory tv v base mem))
    slots kwvals` by
    (qpat_assum `LIST_REL (\(aid,p,base,tv) v. aid < keyword_end.cs_next_id /\ not_fresh_at _ _ /\ _) slots kwvals`
       mp_tac >> match_mp_tac LIST_REL_mono >> simp[NoAsms, FORALL_PROD]) >>
  map_every (fn pat => qpat_assum pat SUBST1_TAC)
    [`cekw = compile_register_kwarg_vars common.ec_env vars`,
     `MAP FST kw = _`, `LENGTH kw = LENGTH vars`, `kwtvs = MAP _ slots`] >>
  irule groupedEntryCommonTheory.grouped_initialized_keyword_owners >>
  rpt conj_tac >> first_assum ACCEPT_TAC;

val linked_default_landed_owners_tac =
  `selected_registration_owners fn (MAP FST kw) kwtvs kwvals (LENGTH kw)
      cekw keyword_end keyword_state Ginit tninit` by linked_default_initialized_owners_tac >>
  qpat_assum `landed = jump_to common_entry.cs_current_bb keyword_state` SUBST1_TAC >>
  irule groupedEntryCommonTheory.grouped_jump_registration_owners >>
  qexists_tac `keyword_end` >> conj_tac >> first_assum ACCEPT_TAC;

(* Apply the selected declaration's source equation at a specified gas observation. *)
val linked_default_kw_overlay_tac =
  qabbrev_tac `kwmap = MAP (\(id,op,ty,e).
    (id,PtrVar op (type_memory_bytes common.ec_env ty))) (REVERSE vars)` >>
  `MAP FST kwmap = REVERSE (MAP FST kw)` by
    (qpat_assum `MAP FST kw = _` SUBST1_TAC >>
     simp[NoAsms, Abbr `kwmap`, MAP_MAP_o, MAP_REVERSE, combinTheory.o_DEF,
          pairTheory.LAMBDA_PROD]) >>
  `!id. FLOOKUP cekw.ce_vars id =
     case ALOOKUP kwmap id of SOME loc => SOME loc | NONE => FLOOKUP common.ec_env.ce_vars id` by
    (qpat_assum `cekw = _` SUBST1_TAC >>
     simp[NoAsms, Abbr `kwmap`, compile_register_kwarg_vars_cenv]) >>
  `!id. ~MEM id (MAP FST kw) ==> FLOOKUP cekw.ce_vars id = FLOOKUP common.ec_env.ce_vars id` by
    (gen_tac >> strip_tac >>
     `ALOOKUP kwmap id = NONE` by
       (qpat_assum `MAP FST kwmap = _` (fn eq => simp[NoAsms,ALOOKUP_NONE, eq]) >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `!id. FLOOKUP cekw.ce_vars id = _` (qspec_then `id` mp_tac) >>
     qpat_assum `ALOOKUP kwmap id = NONE` (fn miss => simp[NoAsms, miss]));

val linked_default_pos_overlay_tac =
  `!id. MEM id (MAP FST pos) ==> ~MEM id (MAP FST kw)` by
    (qpat_assum `ALL_DISTINCT (MAP FST (pos ++ kw))` mp_tac >>
     simp_tac bool_ss [MAP_APPEND, ALL_DISTINCT_APPEND] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `LIST_REL (\(name,ty) tv. ?loc. FLOOKUP cekw.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) pos ptvs` by
    (qpat_assum `LIST_REL (\(name,ty) tv. ?loc.
        FLOOKUP common.ec_env.ce_vars name = SOME loc /\ _) pos ptvs` mp_tac >>
     PURE_REWRITE_TAC [LIST_REL_EL_EQN] >> strip_tac >>
     conj_tac >- first_assum ACCEPT_TAC >> qx_gen_tac `i` >> strip_tac >>
     `MEM (FST (EL i pos)) (MAP FST pos)` by
       (PURE_REWRITE_TAC [MEM_MAP] >> qexists_tac `EL i pos` >>
        REWRITE_TAC [MEM_EL] >> qexists_tac `i` >> simp[]) >>
     qpat_assum `!id. MEM id (MAP FST pos) ==> _` (drule_then assume_tac) >>
     qpat_assum `!id. ~MEM id (MAP FST kw) ==> _` (drule_then assume_tac) >>
     qpat_assum `!j. j < LENGTH pos ==> _` (qspec_then `i` mp_tac) >>
     Cases_on `EL i pos` >>
     fs[NoAsms, pairTheory.UNCURRY] >>
     qpat_assum `i < LENGTH pos` (fn bound =>
       qpat_assum `FLOOKUP cekw.ce_vars _ = FLOOKUP common.ec_env.ce_vars _`
         (fn lookup => simp[NoAsms, bound, lookup])));

val linked_default_registered_domain_tac =
  `!id. ~MEM id (MAP FST (pos ++ kw)) ==> FLOOKUP cekw.ce_vars id = NONE` by
    (gen_tac >> strip_tac >>
     `~MEM id (MAP FST kw)` by
       (qpat_assum `~MEM id (MAP FST (_ ++ _))` mp_tac >> simp[NoAsms, MAP_APPEND]) >>
     qpat_assum `!id. ~MEM id (MAP FST kw) ==> _` (drule_then SUBST1_TAC) >>
     first_assum irule >> first_assum ACCEPT_TAC) >>
  `!id. ~MEM id (MAP FST (pos ++ kw)) ==> FLOOKUP body_env.ce_vars id = NONE` by
    (rpt strip_tac >> Cases_on `FLOOKUP body_env.ce_vars id` >> simp[NoAsms] >>
     drule_all bodySimEntryTheory.compile_register_positional_args_bound >>
     qpat_assum `!id. ~MEM id (MAP FST (pos ++ kw)) ==> FLOOKUP cekw.ce_vars id = NONE`
       (drule_then (fn th => simp[NoAsms, th])));

val linked_default_positional_installs_proof_tac =
  qx_genl_tac [`id`,`op`,`ty`,`e`] >> PURE_REWRITE_TAC [MEM_EL] >>
  disch_then (qx_choose_then `i` strip_assume_tac) >>
  qpat_assum `LIST_REL (\(name,dst,ty,e) (aid,q,p,tv). dst = Var q /\ _) vars slots`
    (strip_assume_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  qpat_assum `LIST_REL (\(aid,p,base,tv) v. aid < keyword_end.cs_next_id /\ not_fresh_at _ _ /\ _) slots kwvals`
    (strip_assume_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  `i < LENGTH slots` by
    (qpat_assum `LENGTH vars = LENGTH slots` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!j. j < LENGTH vars ==> _` (drule_then assume_tac) >>
  qpat_assum `!j. j < LENGTH slots ==> _` (drule_then assume_tac) >>
  qabbrev_tac `slot = EL i slots` >> PairCases_on `slot` >>
  qpat_assum `(id,op,ty,e) = EL i vars` (SUBST_ALL_TAC o SYM) >>
  pop_assum kall_tac >> ntac 2 (pop_assum mp_tac) >>
  simp[NoAsms,pairTheory.UNCURRY] >> rpt strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `keyword_end` >>
  conj_tac >> first_assum ACCEPT_TAC;

val linked_default_positional_installs_tac =
  `!id op ty e. MEM (id,op,ty,e) vars ==> ?p. op = Var p /\ not_fresh_at common_entry p` by
    linked_default_positional_installs_proof_tac;

val linked_default_kwmap_entries_tac =
  `!id loc. ALOOKUP kwmap id = SOME loc ==>
     ?op ty e. MEM (id,op,ty,e) vars /\ loc = PtrVar op (type_memory_bytes common.ec_env ty)` by
    (rpt gen_tac >> disch_then (mp_tac o MATCH_MP (SPEC_ALL ALOOKUP_MEM)) >>
     simp[NoAsms, Abbr `kwmap`, MEM_MAP, MEM_REVERSE, EXISTS_PROD] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!id p sz. FLOOKUP cekw.ce_vars id = SOME (PtrVar (Var p) sz) ==>
     ?ty e. MEM (id,Var p,ty,e) vars` by
    (rpt gen_tac >>
     qpat_assum `!id. FLOOKUP cekw.ce_vars id = _`
       (fn eq => PURE_ONCE_REWRITE_TAC [Q.SPEC `id` eq]) >>
     Cases_on `ALOOKUP kwmap id` >> simp[NoAsms]
     >- (qpat_assum `!id. FLOOKUP common.ec_env.ce_vars id = NONE \/ _`
           (qspec_then `id` strip_assume_tac) >> simp[var_location_distinct]) >>
     strip_tac >>
     qpat_assum `!id loc. ALOOKUP kwmap id = SOME loc ==> _`
       (drule_then (qx_choosel_then [`dst`,`ty`,`e`] strip_assume_tac)) >>
     qexistsl_tac [`ty`,`e`] >>
     qpat_assum `MEM (id,dst,ty,e) vars` mp_tac >>
     qpat_assum `_ = PtrVar dst (type_memory_bytes common.ec_env ty)` mp_tac >>
     qpat_assum `_ = PtrVar (Var p) sz` mp_tac >>
     simp[NoAsms, var_location_11] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]);

val linked_default_kwptr_unique_tac =
  `!id1 ty1 e1 id2 ty2 e2 p. MEM (id1,Var p,ty1,e1) vars /\
     MEM (id2,Var p,ty2,e2) vars ==> id1 = id2` by
    (rpt gen_tac >> pure_rewrite_tac[MEM_EL] >>
     disch_then (CONJUNCTS_THEN2 (qx_choose_then `i` strip_assume_tac)
       (qx_choose_then `j` strip_assume_tac)) >>
     `i = j` by
       (qspecl_then [`MAP (\(_,op,_,_). op) vars`,`i`,`j`] mp_tac ALL_DISTINCT_EL_IMP >>
        qpat_assum `(id1,Var p,ty1,e1) = EL i vars` (fn row1 =>
          qpat_assum `(id2,Var p,ty2,e2) = EL j vars` (fn row2 =>
            qpat_assum `i < LENGTH vars` (fn b => qpat_assum `j < LENGTH vars` (fn b' =>
              qpat_assum `ALL_DISTINCT (MAP (\(_,op,_,_). op) vars)` (fn distinct =>
                simp[NoAsms,EL_MAP,GSYM row1,GSYM row2,b,b',distinct])))))) >>
     qpat_assum `i = j` SUBST_ALL_TAC >>
     qpat_assum `(id1,Var p,ty1,e1) = _` mp_tac >>
     qpat_assum `(id2,Var p,ty2,e2) = _` (fn eq => simp[NoAsms, GSYM eq]));

val linked_default_memloc_key_tac =
     qx_genl_tac [`id`,`z`,`n`] >> strip_tac >>
     `ALOOKUP kwmap id = NONE` by
       (qpat_assum `FLOOKUP cekw.ce_vars id = SOME (MemLoc _ _)` mp_tac >>
        qpat_assum `!id. FLOOKUP cekw.ce_vars id = _`
          (fn eq => PURE_ONCE_REWRITE_TAC [Q.SPEC `id` eq]) >>
        Cases_on `ALOOKUP kwmap id` >> simp[NoAsms] >>
        strip_tac >>
        qpat_assum `!id loc. ALOOKUP kwmap id = SOME loc ==> _`
          (drule_then strip_assume_tac) >>
        qpat_assum `_ = PtrVar _ _` mp_tac >>
        qpat_assum `_ = MemLoc _ _` (fn eq => simp[NoAsms,eq,var_location_distinct])) >>
     `~MEM id (MAP FST kw)` by
       (qpat_assum `ALOOKUP kwmap id = NONE` (mp_tac o REWRITE_RULE [ALOOKUP_NONE]) >>
        qpat_assum `MAP FST kwmap = _` (fn eq => simp[NoAsms,eq])) >>
     CCONTR_TAC >>
     `~MEM id (MAP FST (pos ++ kw))` by
       (qpat_assum `~MEM id (MAP FST pos)` (fn no_pos =>
         qpat_assum `~MEM id (MAP FST kw)` (fn no_kw =>
           simp[NoAsms,MAP_APPEND,no_pos,no_kw]))) >>
     qpat_assum `!id. ~MEM id (MAP FST (_ ++ _)) ==> FLOOKUP cekw.ce_vars id = NONE`
       (drule_then (fn miss =>
         qpat_assum `FLOOKUP cekw.ce_vars id = SOME _`
           (fn hit => mp_tac miss >> simp[NoAsms,hit])));

val linked_default_kwmap_reserve_inputs_tac =
  `!id z n. FLOOKUP cekw.ce_vars id = SOME (MemLoc z n) ==> MEM id (MAP FST pos)` by
    linked_default_memloc_key_tac >>
  `!id1 id2 p sz1 sz2. FLOOKUP cekw.ce_vars id1 = SOME (PtrVar (Var p) sz1) ==>
     not_fresh_at common_entry p /\
     (FLOOKUP cekw.ce_vars id2 = SOME (PtrVar (Var p) sz2) ==> id1 = id2)` by
    (qx_genl_tac [`id1`,`id2`,`p`,`sz1`,`sz2`] >> strip_tac >>
     qpat_assum `!id p sz. FLOOKUP cekw.ce_vars id = SOME (PtrVar (Var p) sz) ==> _`
       (drule_then (qx_choosel_then [`ty1`,`e1`] assume_tac)) >>
     conj_tac
     >- (qpat_assum `!id op ty e. MEM (id,op,ty,e) vars ==> _`
           (qspecl_then [`id1`,`Var p`,`ty1`,`e1`] (drule_then mp_tac)) >>
         simp[NoAsms,venomStateTheory.operand_11]) >>
     strip_tac >>
     qpat_assum `!id p sz. FLOOKUP cekw.ce_vars id = SOME (PtrVar (Var p) sz) ==> _`
       (qspecl_then [`id2`,`p`,`sz2`] (drule_then (qx_choosel_then [`ty2`,`e2`] assume_tac))) >>
     qpat_assum `!id1 ty1 e1 id2 ty2 e2 p. MEM (id1,Var p,ty1,e1) vars /\ _ ==> _`
       (qspecl_then [`id1`,`ty1`,`e1`,`id2`,`ty2`,`e2`,`p`] mp_tac) >>
     qpat_assum `MEM (id1,Var p,ty1,e1) vars` (fn row1 =>
       qpat_assum `MEM (id2,Var p,ty2,e2) vars` (fn row2 => simp[NoAsms,row1,row2])));

val linked_default_kwmap_reserved_tac =
  qpat_assum `compile_register_positional_args cekw (build_positional_args cekw pos) 4 common_entry =
      (body_env,registered)`
    (mp_tac o MATCH_MP (SIMP_RULE bool_ss [GSYM AND_IMP_INTRO]
      (SPEC_ALL compile_register_positional_args_reserved))) >>
  PURE_REWRITE_TAC [build_positional_args_FST, AND_IMP_INTRO] >>
  impl_tac
  >- (rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC,
        qpat_assum `cekw.ce_imm_alloca = NONE` (fn eq => simp[NoAsms,eq])]) >>
  disch_then (ACCEPT_TAC o CONJUNCT1);

val linked_default_package_vars_tac =
  `common.ec_env.ce_vars = FST (allocate_args
     (get_struct_fields (make_struct_fields_map_mods mods)) args 0 FEMPTY)` by
    (qpat_assum `set_external_package_target _ (package_external_fn_unit mods _ _ _) =
                 (_,common.ec_env,_,_,_,_,_,_,_,_,_)`
       (mp_tac o Q.AP_TERM `\p. (FST (SND p)).ce_vars`) >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case => simp[NoAsms, ret_case, set_external_package_target_def,
       package_external_fn_unit_def, update_cenv_nonreentrant_def,
       update_cenv_ret_abi_def, build_compile_env_unit_def, pairTheory.ELIM_UNCURRY, LET_THM]));

val linked_default_package_domain_tac =
  `(!id. ~MEM id (MAP FST (pos ++ kw)) ==> FLOOKUP common.ec_env.ce_vars id = NONE) /\
   (!id. FLOOKUP common.ec_env.ce_vars id = NONE \/
      ?off sz. FLOOKUP common.ec_env.ce_vars id = SOME (MemLoc off sz))` by
    (qpat_assum `common.ec_env.ce_vars = _` SUBST1_TAC >>
     qpat_assum `pos ++ kw = args` SUBST1_TAC >>
     namedCases_on `allocate_args (get_struct_fields (make_struct_fields_map_mods mods)) args 0 FEMPTY`
       ["argmap argend"] >> simp[NoAsms] >>
     `!id. ~MEM id (MAP FST args) ==> FLOOKUP argmap id = NONE` by
       (qx_gen_tac `id` >> strip_tac >>
        drule_all_then mp_tac (Q.INST [`n` |-> `id`] (SPEC_ALL allocate_args_FLOOKUP_other)) >>
        simp[NoAsms]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qx_gen_tac `id` >> Cases_on `MEM id (MAP FST args)`
     >- (disj2_tac >> drule_all_then ACCEPT_TAC allocate_args_FLOOKUP_arg) >>
     disj1_tac >> first_assum irule >> first_assum ACCEPT_TAC);

val linked_default_package_positions_tac =
  `LIST_REL (\(name,ty) tv. ?loc. FLOOKUP common.ec_env.ce_vars name = SOME loc /\
     var_location_memory_size loc = SOME (type_memory_size tv)) args all_tvs` by
    (PURE_REWRITE_TAC [LIST_REL_EL_EQN] >> conj_tac >- (sym_tac >> first_assum ACCEPT_TAC) >>
     qx_gen_tac `i` >> strip_tac >>
     qpat_assum `LIST_REL _ args (ZIP (MAP SND args,all_tvs))`
       (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     Cases_on `EL i args` >>
     qpat_assum `LENGTH all_tvs = LENGTH args` (fn len =>
       qpat_assum `i < LENGTH args` (fn bound =>
         simp[NoAsms,len,bound, EL_MAP,EL_ZIP]))) >>
  `LIST_REL (\(name,ty) tv. ?loc. FLOOKUP common.ec_env.ce_vars name = SOME loc /\
     var_location_memory_size loc = SOME (type_memory_size tv)) pos ptvs` by
    (qpat_assum `pos = TAKE _ args` SUBST1_TAC >>
     qpat_assum `ptvs = TAKE _ all_tvs` SUBST1_TAC >>
     irule LIST_REL_TAKE >> first_assum ACCEPT_TAC);

val linked_default_split_types_tac =
  `ptvs ++ kwtvs = all_tvs` by
    (map_every (fn pat => qpat_assum pat SUBST1_TAC)
      [`ptvs = TAKE _ all_tvs`,`kwtvs = DROP _ all_tvs`] >> simp[NoAsms,TAKE_DROP]) >>
  `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) (MAP SND (pos ++ kw)) (ptvs ++ kwtvs)` by
    (qpat_assum `ptvs ++ kwtvs = all_tvs` SUBST1_TAC >>
     qpat_assum `pos ++ kw = args` SUBST1_TAC >>
     drule_then ACCEPT_TAC vyperTypeABITheory.OPT_MMAP_LIST_REL) >>
  `LENGTH pos = LENGTH ptvs /\ LENGTH kw = LENGTH kwtvs` by
    (map_every (fn pat => qpat_assum pat SUBST1_TAC)
       [`pos = TAKE _ args`,`kw = DROP _ args`,`ptvs = TAKE _ all_tvs`,`kwtvs = DROP _ all_tvs`] >>
     qpat_assum `LENGTH all_tvs = LENGTH args` (fn len => simp[NoAsms,LENGTH_TAKE_EQ,LENGTH_DROP,len])) >>
  `ALL_DISTINCT (MAP FST (pos ++ kw))` by
    (qpat_assum `pos ++ kw = args` SUBST1_TAC >> first_assum ACCEPT_TAC);

val linked_default_pos_values_tac =
  `EVERY dispatchedDecodeDomain$cd_cast_domain ptvs` by
    (qpat_assum `ptvs = TAKE _ all_tvs` SUBST1_TAC >>
     irule EVERY_TAKE >> drule_then ACCEPT_TAC dispatchedDecodeDomainTheory.evaluate_types_cd_cast_domain) >>
  `LIST_REL value_has_type ptvs pvals` by
    (qpat_assum `calldata_decode_args _ ptvs 0 = SOME pvals` (fn decode =>
      qpat_assum `EVERY dispatchedDecodeDomain$cd_cast_domain ptvs` (fn domains =>
        mp_tac (MATCH_MP (SPEC_ALL dispatchedDecodeCastTheory.calldata_decode_args_safe_cast)
                        (CONJ domains decode)))) >>
     match_mp_tac LIST_REL_mono >> POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[vyperTypingTheory.safe_cast_result_well_typed]) >>
  `LENGTH pos = LENGTH pvals` by
    (qpat_assum `calldata_decode_args _ ptvs 0 = SOME pvals`
       (mp_tac o MATCH_MP (SPEC_ALL calldata_decode_args_length)) >>
     qpat_assum `LENGTH pos = LENGTH ptvs` (fn len => simp[NoAsms,len]) >> metis_tac[]);

val linked_default_keyword_lengths_tac =
  `LENGTH kw = LENGTH kwvals` by
    (qpat_assum `LIST_REL (\(aid,p,base,tv) v. aid < keyword_end.cs_next_id /\ _) slots kwvals`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     qpat_assum `kwtvs = MAP _ slots` (mp_tac o Q.AP_TERM `LENGTH`) >>
     qpat_assum `LENGTH kw = LENGTH kwtvs` (fn len => simp[NoAsms,len]));

val linked_default_decoder_abi_tac =
  rpt gen_tac >> strip_tac >>
  `MEM (arg,tv) (ZIP (args,all_tvs))` by
    (qpat_assum `MEM (arg,tv) (ZIP (pos ++ kw,ptvs ++ kwtvs))` mp_tac >>
     qpat_assum `pos ++ kw = args` (fn args =>
       qpat_assum `ptvs ++ kwtvs = all_tvs` (fn tys => simp[NoAsms,args,tys]))) >>
  `abi_decoder_coherent common.ec_env tenv common.ec_env.ce_struct_fields (SND arg) tv` by
    (qpat_assum `LIST_REL (\arg tv. abi_decoder_coherent common.ec_env tenv _ _ _) args all_tvs`
       (mp_tac o REWRITE_RULE [LIST_REL_EVERY_ZIP,EVERY_MEM]) >>
     strip_tac >> qpat_assum `!x. MEM x (ZIP (args,all_tvs)) ==> _`
       (drule_then (mp_tac o REWRITE_RULE [pairTheory.UNCURRY])) >> simp[NoAsms]) >>
  `c with ce_vars := common.ec_env.ce_vars = common.ec_env` by
    (qpat_assum `c = cekw with ce_vars := c.ce_vars`
       (fn eq => PURE_ONCE_REWRITE_TAC [eq]) >>
     qpat_assum `cekw = compile_register_kwarg_vars common.ec_env vars` SUBST1_TAC >>
     simp[NoAsms,compile_register_kwarg_vars_cenv]) >>
  `abi_decoder_coherent c tenv c.ce_struct_fields (SND arg) tv` by
    (qpat_assum `abi_decoder_coherent common.ec_env tenv _ _ _` mp_tac >>
     qpat_assum `c with ce_vars := common.ec_env.ce_vars = common.ec_env`
       (fn eq => PURE_ONCE_REWRITE_TAC [GSYM eq]) >>
     simp[NoAsms,ctor_decoder_coherent_vars]) >>
  conj_tac >- (irule selected_register_one >> irule selected_argument_decoder_accepts >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC;

val linked_default_bounds_tac =
  `EVERY (\tv. type_memory_size tv < dimword (:256)) (ptvs ++ kwtvs)` by
    (qpat_assum `ptvs ++ kwtvs = all_tvs` SUBST1_TAC >>
     PURE_REWRITE_TAC [EVERY_EL] >> qx_gen_tac `i` >> strip_tac >>
     qpat_assum `LIST_REL _ args (ZIP (MAP SND args,all_tvs))`
       (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     Cases_on `EL i args` >>
     qpat_assum `LENGTH all_tvs = LENGTH args` (fn len =>
       qpat_assum `i < LENGTH all_tvs` (fn b =>
         simp[NoAsms,b,GSYM len,EL_MAP,EL_ZIP]))) >>
  `4 + SUM (MAP tv_abi_size ptvs) < dimword (:256)` by
    (qpat_assum `4 + SUM (MAP tv_abi_size all_tvs) < dimword (:256)` mp_tac >>
     qpat_assum `ptvs ++ kwtvs = all_tvs` (fn tys =>
       simp[NoAsms,GSYM tys,MAP_APPEND,SUM_APPEND]) >> decide_tac);

val linked_default_kwenv_frame_tac =
  `cekw with ce_vars := common.ec_env.ce_vars = common.ec_env` by
    (qpat_assum `cekw = compile_register_kwarg_vars common.ec_env vars` SUBST1_TAC >>
     simp[NoAsms,compile_register_kwarg_vars_cenv]) >>
  `cekw.ce_imm_alloca = NONE` by
    (qpat_assum `cekw with ce_vars := common.ec_env.ce_vars = common.ec_env`
       (fn eq => PURE_ONCE_REWRITE_TAC [GSYM eq] >>
          qpat_assum `common.ec_env.ce_imm_alloca = NONE` (mp_tac o PURE_ONCE_REWRITE_RULE [GSYM eq])) >>
     simp[NoAsms]);


fun linked_selected_trace_premises_tac ret_ty gas res es unlocked =
  mp_tac (Q.INST [`ret` |-> ret_ty, `gobs` |-> gas, `res` |-> res, `ee` |-> es,
      `unlocked` |-> unlocked, `dflts` |-> `[]:expr list`,
      `defaults` |-> `[]:value list`, `os` |-> `vs.vs_outcomes`,
      `paid` |-> (`es0 with <|scopes := [FEMPTY]; gas_obs := ` @ gas @ `|>`),
      `after_defaults` |-> (`es0 with <|scopes := [FEMPTY]; gas_obs := ` @ gas @ `|>`),
      `locked` |-> (`es_lock with gas_obs := ` @ gas)]
      (INST [fst (dest_abs ``\body:stmt list. body``) |-> ``fbody:stmt list``]
        (SPEC_ALL linkedRuntimeSelectedTraceTheory.linked_runtime_selected_trace))) >>
  impl_tac;

fun linked_positional_trace_inputs_tac gas =
  let val rules = [APPEND_NIL, Excl "eval_external_defaults_def",
      Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"]
  in
    qpat_assum `LENGTH args = LENGTH tx.args` (fn argc => simp (NoAsms :: argc :: rules)) >>
    let fun specialize pat = qpat_assum pat
          (qspec_then gas (assume_tac o SIMP_RULE (srw_ss()) rules))
    in
      specialize `!gas. send_call_value mut cx _ = _` >>
      specialize `!gas. lock_if_nr cx nr (is_view_mut mut) _ = _` >>
      specialize `!gas. eval_external_defaults cx [] _ = _` >>
      rpt conj_tac >> first_assum ACCEPT_TAC
    end
  end;

fun linked_selected_trace_ret_tac ret_ty names gas res es unlocked =
  linked_selected_trace_premises_tac ret_ty gas res es unlocked
  >- linked_positional_trace_inputs_tac gas >>
  disch_then (qx_choosel_then names (map_every assume_tac o CONJUNCTS));

fun linked_selected_trace_as_tac names gas res es unlocked =
  linked_selected_trace_ret_tac `ret` names gas res es unlocked;

val linked_selected_trace_tac =
  linked_selected_trace_as_tac [`call_res`,`call_am`,`call_rqs`,`call_obs`];

(* Transfer an exact body continuation from the substituted body to the source. *)
val linked_body_eval_tac =
  `!tail. eval_stmts cx fbody (es_lock with gas_obs := gx ++ tail) =
    (res,ee with gas_obs := tail)` by
    (qx_gen_tac `body_tail` >>
     qpat_assum `!gas. eval_stmts cx body_code _ = eval_stmts cx fbody _`
       (qspec_then `gx ++ body_tail` (fn replay => PURE_REWRITE_TAC [GSYM replay])) >>
     qpat_assum `!tail. eval_stmts cx body_code _ = (res,ee with gas_obs := tail)`
       (qspec_then `body_tail` ACCEPT_TAC)) >>
  `eval_stmts cx fbody (es_lock with gas_obs := gx) = (res,ee with gas_obs := [])` by
    (qpat_assum `!tail. eval_stmts cx fbody _ = (res,ee with gas_obs := tail)`
       (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL])));

val linked_unlock_at_empty_gas_tac =
  qpat_assum `!ee. ?eu. unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),eu)`
    (qspec_then `ee with gas_obs := []` (qx_choose_then `eu` assume_tac));

Theorem linked_runtime_dispatched_readings_certificate:
  lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit /\
  source_typing_ok_mods mods exps am tx /\
  source_deployment_rel_mods mods exps am tx ==>
  ?shadow_ctx. !vs.
    calldata_dispatch_mods mods exps vs.vs_call_ctx.cc_calldata =
      SOME (tx.function_name,tx.args) /\
    LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64 /\
    initial_venom_state_rel_mods mods am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    LENGTH vs.vs_outcomes < 2 ** 64 /\
    (ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_fmp_headroom inst s) /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254) ==>
    ?marks.
      source_unit_execution_correct_with_mods shadow_ctx marks mods exps
        (external_return_type_mods mods exps tx.function_name) am tx unit vs /\
      ((?tail. call_storage_ok am tx vs.vs_outcomes
         (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
       !tail. FST (call_external (SOME vs.vs_outcomes)
         (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
         INR (Error (RuntimeError "msg.gas: no gas reading")))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `classify_functions_unit mods exps` >> PairCases_on `r` >>
  rename1 `classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors)` >>
  qpat_assum `lower_vyper_runtime_unit_mods _ _ _ = _` mp_tac >>
  qpat_assum `classify_functions_unit _ _ = _` (fn classified =>
    pure_rewrite_tac[lower_vyper_runtime_unit_mods_def, classified, LET_THM]) >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  rpt IF_CASES_TAC >> simp[] >> strip_tac
  >~ [`run_grouped_lowering _ _ _ _ _ = SOME unit`]
  >- (qmatch_asmsub_abbrev_tac `run_grouped_lowering groups ips fall rpolicy "__entry"` >>
      qspecl_then [`groups`,`ips`,`fall`,`rpolicy`,`"__entry"`] mp_tac
        gas_shadow_run_grouped_lowering >>
      asm_rewrite_tac[] >> simp[OPTREL_def, AllCaseEqs()] >>
      disch_then (qx_choose_then `shadow_unit` strip_assume_tac) >>
      qexists_tac `shadow_unit.cu_context` >> fs[gas_shadow_unit_def] >>
      suspend "linked_runtime_grouped_dispatch") >>
  qmatch_asmsub_abbrev_tac `run_lowering sels packs ips fall rpolicy 0 0 [] info "__entry"` >>
  qspecl_then [`sels`,`packs`,`ips`,`fall`,`rpolicy`,`0`,`0`,`[]`,`info`,`"__entry"`]
    mp_tac gas_shadow_run_lowering >>
  asm_rewrite_tac[] >> simp[OPTREL_def, AllCaseEqs()] >>
  disch_then (qx_choose_then `shadow_unit` strip_assume_tac) >>
  qexists_tac `shadow_unit.cu_context` >> fs[gas_shadow_unit_def] >>
  suspend "linked_runtime_linear_dispatch"
QED

val prepare_linked_runtime_call_tac =
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `source_typing_ok_mods _ _ _ _`
    (qx_choose_then `art` (map_every assume_tac o CONJUNCTS) o
     REWRITE_RULE [source_typing_ok_mods_def]) >>
  qpat_assum `source_deployment_rel_mods _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [source_deployment_rel_mods_def]) >>
  drule_all_then strip_assume_tac lower_vyper_runtime_unit_source_unit_ok_mods >>
  `!sid ts vis mut nr raw name args dflts ret body.
      ALOOKUP mods sid = SOME ts /\
      MEM (FunctionDecl vis mut nr raw name args dflts ret body) ts ==>
      stmts_loop_calls_ok mods
        (subst_consts_stmts_mods (consts_env_mods mods) body)` by
    (rpt gen_tac >> strip_tac >>
     drule_then assume_tac ALOOKUP_MEM >>
     drule_all_then assume_tac checked_function_loop_calls_ok >>
     drule_all_then ACCEPT_TAC checked_subst_consts_loop_calls_ok_mods) >>
  qabbrev_tac `src = ALOOKUP exps tx.function_name` >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  `!mut args ret stmts.
     contract_inv mods exps unit.cu_context
       (build_compile_env_unit mods src External mut tx.function_name args ret stmts T
          with ce_target := rpolicy.rpol_target) cx` by
    (rpt gen_tac >>
     irule checked_linked_contract_inv >>
     simp[Abbr `cx`, initial_evaluation_context_def,
          optionTheory.IS_SOME_EQ_NOT_NONE] >>
     qexistsl_tac [`am`,`tx`] >> simp[]);

Resume linked_runtime_dispatched_readings_certificate[linked_runtime_grouped_dispatch]:
  prepare_linked_runtime_call_tac >>
  suspend "linked_grouped_active_body"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_runtime_linear_dispatch]:
  prepare_linked_runtime_call_tac >>
  suspend "linked_linear_active_body"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_active_body]:
  `~EXISTS (external_has_defaults o SND) exts` by
    (qpat_assum `EVERY ($~ o external_has_defaults o SND) exts` mp_tac >>
     simp_tac bool_ss [listTheory.EVERY_NOT_EXISTS, combinTheory.o_DEF]) >>
  `shadow_body_inv_mods mods exps unit.cu_context shadow_unit.cu_context` by
    (map_every (fn pattern =>
       qpat_assum pattern (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]))
       [`Abbrev (sels = _)`, `Abbrev (packs = _)`, `Abbrev (ips = _)`,
        `Abbrev (fall = _)`, `Abbrev (info = _)`] >>
     drule_all_then ACCEPT_TAC linear_runtime_shadow_body_inv_mods) >>
  drule_all_then
    (qx_choosel_then [`tops`,`mut`,`nr`,`args`,`ret`,`fbody`]
      (map_every assume_tac o CONJUNCTS))
    calldata_dispatch_linear_has_source_entry_mods >>
  `external_return_type_mods mods exps tx.function_name = ret` by
    (qpat_assum `ALOOKUP mods (ALOOKUP exps tx.function_name) = SOME tops`
       (fn tops_eq =>
          qpat_assum `vyperInterpreter$lookup_function (ALOOKUP exps tx.function_name)
            tx.function_name External tops = _`
            (fn lookup_eq => simp_tac (srw_ss())
              [external_return_type_mods_def, LET_THM, tops_eq, lookup_eq]))) >>
  qpat_assum `external_return_type_mods _ _ _ = _`
    (fn ret_eq => PURE_REWRITE_TAC [ret_eq]) >>
  qspecl_then [`\marks.
    source_unit_execution_correct_with_mods shadow_unit.cu_context marks
      mods exps ret am tx unit vs /\
    ((?tail. call_storage_ok am tx vs.vs_outcomes
           (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
       !tail. FST (call_external (SOME vs.vs_outcomes)
         (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
         INR (Error (RuntimeError "msg.gas: no gas reading"))) `]
    mp_tac (Q.INST [`shadow_ctx` |-> `shadow_unit.cu_context`]
      dispatched_call_correct_with_readings_mods) >>
  BETA_TAC >> simp[] >>
  disch_then irule >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "linked_linear_value_accepted"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_value_accepted]:
  drule_then (assume_tac o SIMP_RULE (srw_ss())
    [Abbr `cx`, initial_evaluation_context_def]) send_call_value_success_condition >>
  qabbrev_tac `cd = vs.vs_call_ctx.cc_calldata` >>
  Cases_on `if LENGTH cd < 4 then NONE else
    FIND (\(name,tys). abi_method_id (type_env_all_modules mods) name tys = cd_selector cd)
      (abi_deployed_signatures mods exps)`
  >- suspend "linked_linear_accepted_fallback" >>
  PairCases_on `x` >>
  rename1 `(if LENGTH cd < 4 then NONE else _) = SOME (name,tys)` >>
  Cases_on `LENGTH cd < 4`
  >- (qpat_assum `LENGTH cd < 4` (fn short =>
        qpat_assum `(if LENGTH cd < 4 then NONE else _) = SOME _` mp_tac >>
        simp[NoAsms, short])) >>
  qpat_assum `~(LENGTH cd < 4)` (fn long =>
    qpat_x_assum `(if LENGTH cd < 4 then NONE else _) = SOME _`
       (assume_tac o SIMP_RULE (srw_ss()) [long])) >>
  `?decoded_tys.
    name = tx.function_name /\
    OPT_MMAP (evaluate_type (type_env_all_modules mods)) tys = SOME decoded_tys /\
    4 + SUM (MAP tv_abi_size decoded_tys) <= LENGTH cd /\
    calldata_decode_args cd decoded_tys 0 = SOME tx.args` by
    (qpat_assum `calldata_dispatch_mods _ _ cd = SOME _` mp_tac >>
     qpat_assum `~(LENGTH cd < 4)` (fn long =>
       qpat_assum `FIND _ _ = SOME (name,tys)` (fn hit =>
         simp[NoAsms, calldata_dispatch_mods_def, LET_THM, long, hit, AllCaseEqs()])) >>
     strip_tac >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `name = tx.function_name` SUBST_ALL_TAC >>
  `4 <= LENGTH cd` by decide_tac >>
  `MEM (tx.function_name,tys) (abi_deployed_signatures mods exps)` by
    (drule_then ACCEPT_TAC FIND_MEM) >>
  suspend "linked_linear_accepted_hit"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_accepted_hit]:
  drule_all (SRULE [LET_THM] deployed_signature_selected_decl) >>
  disch_then (qx_choose_then `top` strip_assume_tac) >>
  drule_all_then assume_tac source_typing_ok_mods_external_names_distinct >>
  drule_all selected_decl_lookup_args >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac) >>
  `?raw. (tx.function_name <> "__default__" /\
          top = FunctionDecl External mut nr raw tx.function_name args [] ret fbody) \/
         public_getter_src (ALOOKUP exps tx.function_name) top =
           SOME (mut,nr,raw,tx.function_name,args,([]:expr list),ret,fbody)`
    suffices_by (disch_then (qx_choose_then `raw` assume_tac) >>
      suspend "linked_linear_accepted_hit_package") >>
  qpat_assum `(_ /\ ?rr. top = FunctionDecl _ _ _ _ _ _ _ _ _) \/ _`
    (DISJ_CASES_THEN2
      (CONJUNCTS_THEN2 assume_tac (qx_choose_then `rr` assume_tac))
      assume_tac)
  >- (qexists_tac `rr` >> asm_rewrite_tac[]) >>
  qexists_tac `F` >> asm_rewrite_tac[]
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_accepted_hit_package]:
  qabbrev_tac `name = tx.function_name` >>
  qabbrev_tac `body_code = subst_consts_stmts_mods (consts_env_mods mods) fbody` >>
  `MEM (src,(mut,nr,raw,name,args,[],ret,body_code)) exts` by
    (drule_all selected_external_member_mods >>
     simp[Abbr `src`, Abbr `body_code`, subst_consts_fn_mods_def, subst_consts_expr_mods_def]) >>
  `params_ok (type_env_all_modules mods) args` by
    (irule checked_external_parameter_types_mods >>
     rpt (goal_assum (drule_at Any)) >> metis_tac[Abbr `src`]) >>
  `contract_namespaces_ok F mods` by
    (drule_then ACCEPT_TAC check_contract_namespaces_ok) >>
  `fn_allocs_ok_unit mods (src,(mut,nr,raw,name,args,[],ret,body_code))` by
    (qpat_assum `EVERY (fn_allocs_ok_unit mods) exts`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >> disch_then drule >> simp[]) >>
  `?lbl ce pos mc pay key tr view rt.
    set_external_package_target rpolicy.rpol_target
      (package_external_fn_unit mods T (K global_nonreentrant_slot)
        (src,(mut,nr,raw,name,args,([]:expr list),ret,body_code))) =
      (lbl,ce,pos,mc,pay,nr,key,tr,view,body_code,rt)` by
    (Cases_on `ret = NoneT` >>
     simp[set_external_package_target_def, package_external_fn_unit_def]) >>
  drule_all linked_registration_package_inputs >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (qx_choose_then `decode_tvs` strip_assume_tac)))) >>
  drule_all linked_linear_selected_registration_code >>
  disch_then (qx_choosel_then [`fn`,`fl`,`ds`,`de`,`opened`,`checked`,
    `registered_env`,`registered`,`last`] strip_assume_tac) >>
  suspend "linked_linear_accepted_hit_code"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_accepted_hit_code]:
  drule_then strip_assume_tac lower_vyper_runtime_unit_raw_shape_mods >>
  qabbrev_tac `selectors = MAP (\(sel,l,z). (sel,l))
    (build_selectors (type_env_all_modules mods) (MAP SND exts))` >>
  `EVERY (\(sel,l). sel < 2 ** 32) selectors` by
    simp[Abbr `selectors`, linear_selectors_lt] >>
  `linear_dispatch_target cd selectors fl = lbl` by
    (drule_all (SRULE [LET_THM] linked_classified_linear_routes) >>
     disch_then (qspec_then `cd` (mp_tac o cj 2)) >>
     disch_then (qspecl_then
       [`src`,`mut`,`nr`,`raw`,`name`,`args`,`[]`,`ret`,`body_code`] mp_tac) >>
     fs[Abbr `selectors`]) >>
  `compile_selector_dispatch_linear selectors fl ds = ((),de)` by
    simp[Abbr `selectors`] >>
  drule_all linked_linear_dispatch_entry_path >>
  disch_then (qx_choosel_then [`p`,`G0`,`tn0`] strip_assume_tac) >>
  `fresh_vars_wrt opened p` by
    (irule fresh_vars_wrt_mono >> qexists_tac `de` >> simp[]) >>
  `p.vs_current_bb = opened.cs_current_bb` by simp[Abbr `cd`] >>
  `pay = (mut = Payable)` by
    (qpat_assum `set_external_package_target _ _ = _` mp_tac >>
     Cases_on `ret = NoneT` >>
     simp[NoAsms, set_external_package_target_def, package_external_fn_unit_def]) >>
  `p.vs_call_ctx.cc_callvalue = n2w tx.value` by
    (qpat_assum `p.vs_call_ctx = vs.vs_call_ctx` SUBST1_TAC >>
     qpat_assum `initial_venom_state_rel_mods mods am tx vs` mp_tac >>
     simp[NoAsms, initial_venom_state_rel_mods_def, venom_env_rel_def, call_ctx_rel_def]) >>
  `cx.txn = tx` by simp[Abbr `cx`, initial_evaluation_context_def] >>
  SUBGOAL_THEN ``pay \/ p.vs_call_ctx.cc_callvalue = 0w`` ASSUME_TAC
  >- (qpat_assum `cx.txn = tx` (fn txn =>
       qpat_assum `mut = Payable \/ cx.txn.value = 0`
         (mp_tac o PURE_REWRITE_RULE [txn])) >>
     qpat_assum `pay = (mut = Payable)` (fn payable =>
       qpat_assum `p.vs_call_ctx.cc_callvalue = n2w tx.value` (fn callvalue =>
         simp[NoAsms, payable, callvalue])) >>
     disch_then (DISJ_CASES_THEN (fn h => simp[NoAsms, h]))) >>
  `decode_tvs = decoded_tys` by
    (qpat_assum `OPT_MMAP _ (MAP SND args) = SOME decode_tvs` (fn evaluated =>
       qpat_assum `OPT_MMAP _ (MAP SND args) = SOME decoded_tys`
         (ACCEPT_TAC o REWRITE_RULE [evaluated, optionTheory.SOME_11]))) >>
  qpat_x_assum `decode_tvs = decoded_tys` SUBST_ALL_TAC >>
  `mc <= LENGTH p.vs_call_ctx.cc_calldata` by simp[Abbr `cd`] >>
  mp_tac (Q.INST [`PG` |-> `[]`, `lo` |-> `0`, `ctx` |-> `unit.cu_context`,
    `s` |-> `p`, `m` |-> `mc`, `st` |-> `opened`, `st'` |-> `checked`,
    `tn` |-> `tn0`, `G` |-> `G0`] compile_entry_checks_ptr_endpoint) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`u`,`G1`,`tn1`] strip_assume_tac) >>
  `vars_pc_only vs u` by (irule vars_pc_only_trans >> qexists_tac `p` >> simp[]) >>
  qabbrev_tac `site = ARB:instruction` >>
  mp_tac (Q.INST [`ctx` |-> `unit.cu_context`, `initial` |-> `vs`, `s` |-> `u`,
      `tn` |-> `tn1`, `site` |-> `site`] linked_post_checks_resources) >>
  impl_tac >- simp[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "linked_linear_accepted_hit_register"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_accepted_hit_register]:
  qpat_assum `default_registration_entry_frame vs u`
    (strip_assume_tac o REWRITE_RULE [default_registration_entry_frame_def]) >>
  `calldata_decode_args u.vs_call_ctx.cc_calldata decoded_tys 0 = SOME tx.args` by
    fs[Abbr `cd`] >>
  `!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC lowering_context_ok_block_phi) >>
  `LENGTH args = LENGTH decoded_tys /\ LENGTH args = LENGTH tx.args` by
    (conj_tac
     >- (qpat_assum `OPT_MMAP _ (MAP SND args) = SOME decoded_tys`
           (mp_tac o MATCH_MP (SPEC_ALL vyperTypeABITheory.OPT_MMAP_LENGTH)) >> simp[]) >>
     drule_then ACCEPT_TAC bind_arguments_length) >>
  `LIST_REL (\ty tv. evaluate_type (type_env_all_modules mods) ty = SOME tv)
     (MAP SND args) decoded_tys` by
    (drule_then ACCEPT_TAC vyperTypeABITheory.OPT_MMAP_LIST_REL) >>
  `!i. i < LENGTH args ==>
     abi_decoder_coherent ce (type_env_all_modules mods) ce.ce_struct_fields
       (SND (EL i args)) (EL i decoded_tys) /\
     (?loc. FLOOKUP ce.ce_vars (FST (EL i args)) = SOME loc /\
       var_location_memory_size loc = SOME (type_memory_size (EL i decoded_tys))) /\
     type_memory_size (EL i decoded_tys) < dimword (:256)` by
    (gen_tac >> strip_tac >>
     qpat_assum `LIST_REL _ args (ZIP (MAP SND args,decoded_tys))`
       (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     qpat_assum `LENGTH args = LENGTH decoded_tys` (fn len =>
       qpat_assum `i < LENGTH args` (fn bound =>
         Cases_on `EL i args` >>
         qpat_assum `EL i args = _` (fn arg =>
           simp[NoAsms, bound, GSYM len, EL_ZIP, EL_MAP, arg])))) >>
  `!ce' i. i < LENGTH args /\ ce' = ce with ce_vars := ce'.ce_vars ==>
      selected_slot_accepts ce' (type_env_all_modules mods) ce'.ce_struct_fields
        (SND (EL i args)) (EL i decoded_tys) /\
      abi_decoder_coherent ce' (type_env_all_modules mods) ce'.ce_struct_fields
        (SND (EL i args)) (EL i decoded_tys)` by
    (rpt gen_tac >> strip_tac >>
     `abi_decoder_coherent ce' (type_env_all_modules mods) ce'.ce_struct_fields
        (SND (EL i args)) (EL i decoded_tys)` by
       (qpat_assum `ce' = _` SUBST1_TAC >>
        simp[ctor_decoder_coherent_vars]) >>
     simp[] >> irule selected_register_one >>
     irule selected_argument_decoder_accepts >> first_assum ACCEPT_TAC) >>
  `ce.ce_imm_alloca = NONE /\ ce.ce_vars =
     FST (allocate_args (get_struct_fields (make_struct_fields_map_mods mods))
       args 0 FEMPTY)` by
    (qpat_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[NoAsms, set_external_package_target_def, package_external_fn_unit_def,
          update_cenv_nonreentrant_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `(if _ then _ else _) with
         <|ce_target := _; ce_nonreentrant := _|> = ce`
       (mp_tac o AP_TERM ``\ce:compile_env. (ce.ce_imm_alloca,ce.ce_vars)``) >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case =>
       simp[NoAsms, ret_case, update_cenv_ret_abi_def, build_compile_env_unit_def,
            pairTheory.ELIM_UNCURRY, pairTheory.FST, LET_THM])) >>
  `(!k. ~MEM k (MAP FST args) ==> FLOOKUP ce.ce_vars k = NONE) /\
    EVERY (\a. ?off. FLOOKUP ce.ce_vars (FST a) =
      SOME (MemLoc off (type_mem_bytes (get_struct_fields (make_struct_fields_map_mods mods))
         (SND a)))) args` by
    (qpat_assum `ce.ce_vars = _` SUBST1_TAC >>
     drule_then
       (qspecl_then [`get_struct_fields (make_struct_fields_map_mods mods)`,`0`,`FEMPTY`] mp_tac)
       allocate_args_lookup >> simp[]) >>
  `compile_register_positional_args ce (build_positional_args ce args) 4 checked =
    (registered_env,registered)` by
    (qpat_assum `pos = build_positional_args _ _` (fn pos =>
       qpat_assum `compile_register_positional_args ce _ 4 checked = _`
         (ACCEPT_TAC o REWRITE_RULE [pos]))) >>
  `!n p sz. FLOOKUP ce.ce_vars n <> SOME (PtrVar (Var p) sz)` by
    (rpt gen_tac >> Cases_on `MEM n (MAP FST args)`
     >- (qpat_assum `MEM n (MAP FST args)`
          (qx_choose_then `arg` strip_assume_tac o REWRITE_RULE [MEM_MAP]) >>
         qpat_assum `EVERY (\a. ?off. FLOOKUP ce.ce_vars (FST a) = _) args`
           (qspec_then `arg` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
         impl_tac >- first_assum ACCEPT_TAC >>
         BETA_TAC >>
         disch_then (qx_choose_then `off` (fn lookup =>
           qpat_assum `n = FST arg` (fn name =>
             simp[NoAsms, name, lookup, var_location_distinct])))) >>
     qpat_assum `!k. ~MEM k (MAP FST args) ==> FLOOKUP ce.ce_vars k = NONE`
       (qspec_then `n` mp_tac) >> simp[]) >>
  `local_ptrs_reserved registered_env registered` by
    (qspecl_then [`build_positional_args ce args`,`ce`,`4`,`checked`,
                    `registered_env`,`registered`] mp_tac
       compile_register_positional_args_reserved >>
     impl_tac
     >- (rpt conj_tac
         >- first_assum ACCEPT_TAC
         >- (simp[NoAsms, build_positional_args_names] >> rpt strip_tac >>
             Cases_on `MEM n (MAP FST args)` >> simp[] >>
             qpat_assum `!k. ~MEM k (MAP FST args) ==> FLOOKUP ce.ce_vars k = NONE`
               (qspec_then `n` mp_tac) >> simp[])
         >- (rpt strip_tac >>
             qpat_assum `FLOOKUP ce.ce_vars _ = SOME (PtrVar (Var _) _)`
               (fn lookup => qpat_assum
                 `!n p sz. FLOOKUP ce.ce_vars n <> SOME (PtrVar (Var p) sz)`
                 (CONTR_TAC o (fn excluded => MATCH_MP (SPEC_ALL excluded) lookup)))) >>
         qpat_assum `ce.ce_imm_alloca = NONE` (fn imm => simp[NoAsms, imm])) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `u.vs_allocas = FEMPTY` by
    (drule vars_pc_only_allocas >> fs[initial_venom_state_rel_mods_def]) >>
  qpat_assum `default_registration_resources _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [default_registration_resources_def]) >>
  `alloca_frontier_inv unit.cu_context fn site u` by
    (qpat_assum `alloca_frontier_inv_from 0 _ _ _ _` mp_tac >>
     simp[NoAsms, alloca_frontier_inv_def, alloca_frontier_inv_from_def]) >>
  `selected_registration_resources unit.cu_context fn site 0 checked u` by
    simp[selected_registration_resources_def] >>
  `ctx_has_dalloca unit.cu_context ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size fn u <= w2n u.vs_initial_fmp` by
    (simp[allocas_below_fmp_def] >> strip_tac >>
     qpat_assum `fmp_room _ _ _` (mp_tac o REWRITE_RULE [fmp_room_def]) >>
     simp[] >> decide_tac) >>
  `fresh_vars_wrt registered u` by
    (irule fresh_vars_wrt_mono >> qexists_tac `checked` >>
     simp[] >>
     qpat_assum `compile_register_positional_args _ _ _ checked = (_,registered)`
       (mp_tac o MATCH_MP compile_register_positional_args_next_var) >>
     simp[NoAsms, arithmeticTheory.GREATER_EQ]) >>
  drule_at (Pat `calldata_decode_args _ _ _ = _`)
    (Q.INST [`PG` |-> `[]`] (SPEC_ALL selected_registration_fold)) >>
  disch_then (drule_at (Pat `compile_register_positional_args _ (build_positional_args _ _) _ _ = _`)) >>
  disch_then (drule_at (Pat `selected_registration_resources _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `bind_arguments _ _ _ = _`)) >>
  disch_then (qspecl_then [`tn1`,`registered`,`G1`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
  disch_then (qx_choosel_then [`s0`,`G2`,`tn2`] strip_assume_tac) >>
  suspend "linked_linear_accepted_hit_body"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_accepted_hit_body]:
  `vyperInterpreter$lookup_function src tx.function_name External tops =
    SOME (mut,nr,args,[],ret,fbody)` by simp[Abbr `src`, Abbr `name`] >>
  `ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel src) tops))` by
    simp[Abbr `src`, Abbr `name`] >>
  `lookup_raw_return_or_F src tx.function_name External tops = raw` by
    (qpat_assum `(_ /\ top = FunctionDecl _ _ _ _ _ _ _ _ _) \/
        public_getter_src _ top = _`
       (DISJ_CASES_THEN2 strip_assume_tac
         (strip_assume_tac o REWRITE_RULE [tagged_getter_source_tuple]))
     >- (`MEM (src,tx.function_name) (external_name_keys_toplevel src top)` by
           simp[external_name_keys_toplevel_def] >>
         qpat_assum `vyperInterpreter$lookup_function src tx.function_name External tops = _`
           (mp_tac o MATCH_MP (SPEC_ALL lookup_function_external_raw_cases)) >>
         disch_then (DISJ_CASES_THEN strip_assume_tac)
         >- (`top = FunctionDecl External mut nr rr tx.function_name args [] ret fbody` by
              (qspecl_then [`tops`, `external_name_keys_toplevel src`, `top`,
                 `FunctionDecl External mut nr rr tx.function_name args [] ret fbody`,
                 `(src,tx.function_name)`] mp_tac all_distinct_flat_map_unique >>
               simp[external_name_keys_toplevel_def]) >>
             fs[lookup_raw_return_or_F_def]) >>
         `public_getter_src src decl = SOME (mut,nr,F,tx.function_name,args,
            ([]:expr list),ret,fbody)` by simp[tagged_getter_source_tuple] >>
         `MEM (src,tx.function_name) (external_name_keys_toplevel src decl)` by
           (drule tagged_getter_name_key >> simp[fn_decl_name_def]) >>
         `top = decl` by
           (qspecl_then [`tops`, `external_name_keys_toplevel src`, `top`, `decl`,
              `(src,tx.function_name)`] mp_tac all_distinct_flat_map_unique >> simp[]) >>
         qpat_assum `top = FunctionDecl _ _ _ _ _ _ _ _ _` (fn decl =>
           qpat_assum `top = decl` (fn same =>
             qpat_assum `is_public_getter_decl _ decl`
               (CONTR_TAC o REWRITE_RULE [GSYM same, decl, is_public_getter_decl_def])))) >>
     qspecl_then [`tops`,`src`,`tx.function_name`,`top`] mp_tac public_getter_raw_return_none >>
     impl_tac >- simp[Abbr `src`, Abbr `name`] >>
     disch_then (fn ret => simp[Abbr `name`, lookup_raw_return_or_F_def, ret])) >>
  suspend "linked_linear_accepted_endpoint"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_accepted_endpoint]:
  qpat_assum `selected_registration_resources _ _ _ _ registered s0`
    (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
  qpat_assum `selected_registration_frame u tn1 s0 tn2`
    (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]) >>
  `tn2.t_stor = {} /\ tn2.t_trans = {} /\ tn2.t_imm = {}` by
    (rpt conj_tac >> first_assum (fn eq => SUBST1_TAC eq >> first_assum ACCEPT_TAC)) >>
  `!j. j < LENGTH args ==> ?aid q p n.
    FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
    FLOOKUP registered_env.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
    lookup_var q s0 = SOME (n2w p) /\ ptr_covers G2 tn2 q s0 n /\
    (!mem. mem_agree_outside tn2.t_mem s0.vs_memory mem ==>
      val_in_memory (EL j decoded_tys) (EL j tx.args) p mem)` by
    (rpt strip_tac >>
     qpat_assum `selected_registration_owners _ _ _ _ _ _ _ _ _ _`
       (qspec_then `j` mp_tac o REWRITE_RULE [selected_registration_owners_def]) >>
     simp[EL_MAP] >> strip_tac >> rename1 `FLOOKUP s0.vs_allocas aid = SOME (addr,n)` >>
     qexistsl_tac [`aid`,`q`,`addr`,`n`] >> simp[]) >>
  `s0.vs_initial_fmp = u.vs_initial_fmp` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ (u,G1,tn1) [] (OK s0,G2,tn2)`
       (qspecl_then [`ARB`,`ARB`] assume_tac) >>
     drule_all decoder_origin_path_allocation_frame >> simp[]) >>
  `u.vs_initial_fmp = vs.vs_initial_fmp /\ u.vs_fmp = vs.vs_fmp /\
    vs.vs_fmp = vs.vs_initial_fmp` by
    (qpat_assum `vars_pc_only vs u` mp_tac >>
     simp[NoAsms, vars_pc_only_def, venomStateTheory.venom_state_component_equality] >>
     strip_tac >> qpat_assum `initial_venom_state_rel_mods _ _ _ vs` mp_tac >>
     simp[NoAsms, initial_venom_state_rel_mods_def]) >>
  `fmp_room unit.cu_context fn s0` by
    (mp_tac (Q.INST [`ctx` |-> `unit.cu_context`, `fn` |-> `fn`,
                `site` |-> `site`, `s` |-> `s0`] entry_frontier_fmp_room) >>
     impl_tac
     >- (conj_tac >- fs[selected_registration_resources_def] >>
         conj_tac >- simp[] >> fs[]) >>
     DISCH_THEN ACCEPT_TAC) >>
  `vars_pc_only (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
            vs_inst_idx := 0|>) u` by
    (qpat_assum `vars_pc_only vs u` mp_tac >>
     simp[NoAsms, vars_pc_only_def, venomStateTheory.venom_state_component_equality]) >>
  `ALOOKUP mods src = SOME tops /\ src = ALOOKUP exps tx.function_name` by
    simp[Abbr `src`, Abbr `name`] >>
  `set_external_package_target rpolicy.rpol_target
    (package_external_fn_unit mods T (K global_nonreentrant_slot)
      (src,subst_consts_fn_mods (consts_env_mods mods)
        (mut,nr,lookup_raw_return_or_F src tx.function_name External tops,
         tx.function_name,args,[],ret,fbody))) =
    (lbl,ce,pos,mc,pay,nr,key,tr,view,body_code,rt)` by
    (qpat_assum `Abbrev (name = tx.function_name)` (fn name =>
       qpat_assum `Abbrev (body_code = _)` (fn body =>
         qpat_assum `lookup_raw_return_or_F _ _ _ _ = raw` (fn raw =>
           PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] name),
             GSYM (REWRITE_RULE [markerTheory.Abbrev_def] body), raw,
             subst_consts_fn_mods_def]))) >>
     qpat_assum `lookup_raw_return_or_F _ _ _ _ = raw` (fn raw =>
       qpat_assum `Abbrev (name = tx.function_name)` (fn name =>
         PURE_REWRITE_TAC [PURE_REWRITE_RULE
           [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] name)] raw])) >>
     simp[NoAsms, subst_consts_expr_mods_def] >>
     FIRST_ASSUM ACCEPT_TAC) >>
  qpat_assum `initial_venom_state_rel_mods _ _ _ vs`
    (strip_assume_tac o PURE_REWRITE_RULE [initial_venom_state_rel_mods_def]) >>
  `send_call_value mut (initial_evaluation_context am.sources am.layouts tx src)
      (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
      (INL (),es0)` by
    (qpat_assum `Abbrev (cx = _)` (fn cx =>
       PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] cx)]) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `!H:(bool # 256 word # type_value) list # num list.
    stmt_state_rel H unit.cu_context fn registered_env cx es0 s0 /\
    ghost_inv H NONE registered_env cx es0 G2 tn2 s0` by
    (gen_tac >>
     qpat_assum `Abbrev (cx = _)` (fn cx =>
       PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] cx]) >>
     mp_tac (Q.INST [`efn` |-> `fn`, `cenv0` |-> `ce`,
       `pos_args` |-> `pos`, `mincd` |-> `mc`, `ut'` |-> `tr`, `iv` |-> `view`,
       `lowered_body` |-> `body_code`, `st` |-> `checked`,
       `cenv` |-> `registered_env`, `sa` |-> `registered`,
       `elbl` |-> `"__entry"`, `s1` |-> `u`, `tvs` |-> `decoded_tys`,
       `G0` |-> `G2`, `tn0` |-> `tn2`]
        (Q.INST_TYPE [`:'a` |-> `:256`]
          registration_actual_endpoint_relations_from_prefix_mods)) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  suspend "linked_linear_accepted_guarded_body"
QED

(* Common positional source preparation. The dispatcher supplies the selected
   package (name and lbl), the registration witnesses and the installed code. *)
val linked_positional_package_env_tac =
  qabbrev_tac `base_env =
    build_compile_env_unit mods src External mut name args ret body_code T` >>
  `contract_inv mods exps unit.cu_context
    (base_env with ce_target := rpolicy.rpol_target) cx` by
    (qpat_assum `!mut args ret ss. contract_inv _ _ _ _ _`
      (qspecl_then [`mut`,`args`,`ret`,`body_code`] mp_tac) >>
     simp[NoAsms, Abbr `base_env`]) >>
  `ce =
    update_cenv_nonreentrant
      (if ret = NoneT then base_env with ce_raw_return := raw
       else update_cenv_ret_abi (base_env with ce_raw_return := raw) ret)
      nr global_nonreentrant_slot T (mut = View)
    with ce_target := rpolicy.rpol_target /\
    key = global_nonreentrant_slot /\ tr /\ view = (mut = View) /\
    rt = (if ret = NoneT then NONE else SOME ret)` by
    (qpat_assum `set_external_package_target rpolicy.rpol_target
        (package_external_fn_unit mods T (K global_nonreentrant_slot)
           (src,(mut,nr,raw,name,args,[],ret,body_code))) = _` mp_tac >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case =>
       simp[NoAsms, ret_case, Abbr `base_env`, LET_THM, combinTheory.K_THM,
            package_external_fn_unit_def, set_external_package_target_def]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `mut = View <=> view` (fn view_eq => PURE_REWRITE_TAC [GSYM view_eq]) >>
     first_assum (ACCEPT_TAC o SYM));

val linked_positional_module_inv_tac =
  `module_body_inv mods src tops registered_env cx` by
    (qpat_assum `registered_env = ce with ce_vars := registered_env.ce_vars` SUBST1_TAC >>
     qpat_assum `ce = _` SUBST1_TAC >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case =>
       simp[NoAsms, ret_case, module_body_inv_def, Abbr `base_env`,
            build_compile_env_unit_def, pairTheory.ELIM_UNCURRY,
            update_cenv_nonreentrant_def, update_cenv_ret_abi_def]) >>
     FIRST_ASSUM ACCEPT_TAC);

val linked_positional_contract_inv_tac =
  `contract_inv mods exps unit.cu_context registered_env cx` by
    (qpat_assum `contract_inv mods exps _ (base_env with ce_target := _) cx` mp_tac >>
     qpat_assum `registered_env = ce with ce_vars := registered_env.ce_vars` SUBST1_TAC >>
     qpat_assum `ce = _` SUBST1_TAC >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case =>
       simp[NoAsms, ret_case, contract_inv_def, cenv_module_pins_mods_def,
            immutable_section_layout_mods_def,
            update_cenv_nonreentrant_def, update_cenv_ret_abi_def]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     asm_rewrite_tac[] >> rpt conj_tac >>
     FIRST [
       qpat_assum `base_env.ce_struct_fields = _`
         (fn fields => PURE_REWRITE_TAC [GSYM fields] >> FIRST_ASSUM ACCEPT_TAC),
       qpat_assum `base_env.ce_module_vars = _`
         (fn locations => PURE_REWRITE_TAC [GSYM locations] >> FIRST_ASSUM ACCEPT_TAC),
       rpt gen_tac >> strip_tac >>
       qpat_assum `!sid ts. ALOOKUP mods sid = SOME ts ==> supported_module_headers ts /\ _`
         (drule_then (fn headers => simp[NoAsms, headers]))]);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_accepted_guarded_body]:
  linked_positional_package_env_tac >>
  linked_positional_module_inv_tac >>
  linked_positional_contract_inv_tac >>
  qpat_assum `compile_guarded_body registered_env nr key tr view body_code rt registered = ((),last)`
    (fn body => qpat_assum `fn_has_code registered last fn` (fn installed =>
      mp_tac (MATCH_MP guarded_body_code_from_registration (CONJ body installed)))) >>
  disch_then (qx_choosel_then [`locked`,`body_end`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "linked_linear_accepted_guarded_source_frame"
QED

val linked_positional_source_frame_tac =
  `get_module_code cx src = SOME tops` by
    drule_all_then ACCEPT_TAC contract_inv_module_code >>
  `es0.scopes = [env] /\ es0.immutables = am.immutables /\
   es0.outcomes = SOME vs.vs_outcomes /\ es0.requests = [] /\
   state_well_typed es0 /\ accounts_well_typed es0.accounts` by
    drule_all_then ACCEPT_TAC external_body_prefix_state >>
  `popped_keys_indexed es0.scopes` by
    (qpat_assum `es0.scopes = [env]` SUBST1_TAC >>
     drule_then ACCEPT_TAC external_bind_arguments_popped);

val linked_positional_module_alloc_tac =
  `module_allocated am.layouts tx.target src tops` by
    (Cases_on `src`
     >- drule_all_then ACCEPT_TAC check_contract_main_module_allocated >>
     rename1 `ALOOKUP mods (SOME sid) = SOME tops` >>
     `MEM (tx.function_name,sid) exps` by
       (irule ALOOKUP_MEM >>
        qpat_assum `SOME sid = ALOOKUP exps tx.function_name` (ACCEPT_TAC o SYM)) >>
     qpat_assum `exports_ok _ _ mods exps`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [exports_ok_def]) >>
     simp[NoAsms, EVERY_MEM, FORALL_PROD] >>
     disch_then (qspecl_then [`tx.function_name`,`sid`] mp_tac) >>
     qpat_assum `ALOOKUP mods (SOME sid) = SOME tops` (fn lookup =>
       qpat_assum `MEM (tx.function_name,sid) exps` (fn exported =>
         simp[NoAsms, lookup, exported])));

val linked_positional_int_calls_tac =
  `int_calls_stmts body_code = int_calls_stmts fbody` by
    (qpat_assum `check_contract F _ _ mods = SOME art`
       (fn checked => qpat_assum `Abbrev (body_code = _)` (fn body =>
          PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] body,
            CONJUNCT2 (MATCH_MP checked_subst_consts_int_calls_mods checked)])) >>
     REFL_TAC);

fun linked_positional_selected_decl_tac continuation =
  `(tx.function_name <> "__default__" /\
       MEM (FunctionDecl External mut nr raw tx.function_name args [] ret fbody) tops) \/
    (is_public_getter_decl tx.function_name top /\
     external_getter_tuple src top = SOME (mut,nr,args,([]:expr list),ret,fbody))`
    suffices_by (disch_then (mk_asm "selected_decl") >> continuation) >>
    (qpat_assum `Abbrev (name = tx.function_name)` (fn selected_name =>
       qpat_assum `(_ /\ top = FunctionDecl External _ _ _ _ _ _ _ _) \/
          public_getter_src _ top = _`
         (DISJ_CASES_THEN2 strip_assume_tac
           (strip_assume_tac o REWRITE_RULE [tagged_getter_source_tuple]) o
          PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] selected_name]))
     >- (disj1_tac >> conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
         qpat_assum `top = FunctionDecl External _ _ _ _ _ _ _ _` (fn decl =>
           qpat_assum `MEM top tops` (ACCEPT_TAC o PURE_REWRITE_RULE [decl]))) >>
     disj2_tac >> simp[Abbr `src`, Abbr `name`] >> FIRST_ASSUM ACCEPT_TAC);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_accepted_guarded_source_frame]:
  linked_positional_source_frame_tac >>
  linked_positional_module_alloc_tac >>
  linked_positional_int_calls_tac >>
  linked_positional_selected_decl_tac (suspend "linked_linear_accepted_guarded_execution")
QED

val linked_positional_checked_body_tac =
  qabbrev_tac `entry_types = function_entry_env art mods src External args` >>
  `!fn. MEM (FunctionDecl External mut nr raw fn args [] ret fbody) tops ==>
    check_function_body am.layouts tx.target mods art src External mut nr args [] ret fbody` by
    (gen_tac >> strip_tac >>
     `External <> Deploy` by simp[NoAsms] >>
     drule_all_then ACCEPT_TAC check_contract_runtime_function_body_MEM) >>
  `ALL_DISTINCT (MAP FST args)` by
    (qpat_assum `params_ok _ args`
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [params_ok_def]));

val linked_positional_call_safe_tac =
  `call_evaluation_safe cx (int_calls_stmts body_code)` by
    (qpat_assum `int_calls_stmts body_code = int_calls_stmts fbody` SUBST1_TAC >>
     qpat_assum `Abbrev (cx = _)`
       (fn cx_eq => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] cx_eq]) >>
     asm "selected_decl" (DISJ_CASES_THEN strip_assume_tac)
     >- drule_all_then ACCEPT_TAC checked_explicit_external_body_call_evaluation_safe >>
     drule_all_then SUBST1_TAC selected_public_getter_body_int_calls_empty >>
     mp_tac (Q.INST [`cx` |-> `initial_evaluation_context am.sources am.layouts tx src`,
                     `owner` |-> `(src,tx.function_name)`, `art` |-> `art`,
                     `mods` |-> `mods`, `layouts` |-> `am.layouts`, `calls` |-> `[]`]
       (Q.INST_TYPE [`:'a` |-> `:num`] checked_contract_call_evaluation_safe_singleton)) >>
     impl_tac
     >- (qpat_assum `check_contract F am.layouts tx.target mods = SOME art`
           (fn checked => qpat_assum `ALOOKUP am.sources tx.target = SOME mods`
             (fn lookup => simp[NoAsms, initial_evaluation_context_def,
                calls_follow_call_graph_def, checked, lookup]))) >>
     simp[NoAsms, Abbr `cx`, initial_evaluation_context_def]);

val linked_positional_declared_typing_tac =
  `!f. MEM (FunctionDecl External mut nr raw f args [] ret fbody) tops ==>
       ?types_after. type_stmts entry_types ret body_code = SOME types_after` by
    (gen_tac >> strip_tac >>
     qpat_assum `!fn. MEM (FunctionDecl External _ _ _ _ _ _ _ _) tops ==> _`
       (drule_then mp_tac) >>
     simp[NoAsms, check_function_body_def, LET_THM, Abbr `entry_types`, Abbr `body_code`,
       optionTheory.IS_SOME_EXISTS]);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_accepted_guarded_execution]:
  linked_positional_checked_body_tac >>
  linked_positional_call_safe_tac >>
  linked_positional_declared_typing_tac >>
  suspend "linked_linear_accepted_guarded_typed_body"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_accepted_guarded_typed_body]:
  qpat_assum `compile_external_fn_bodies pre de = ((),before)`
    (fn real_bodies =>
     qspec_then `pre` (mp_tac o REWRITE_RULE [gas_shadow_compiles_def])
       gas_shadow_compiles_compile_external_fn_bodies >>
     disch_then (qspecl_then [`de`,`de`] mp_tac) >>
     simp[NoAsms, gas_shadow_state_refl, real_bodies]) >>
  Cases_on `compile_external_fn_bodies (MAP gas_shadow_external_package pre) de` >>
  rename1 `compile_external_fn_bodies _ de = (answer,shadow_before)` >>
  simp[] >> strip_tac >>
  `compile_external_fn_bodies (MAP gas_shadow_external_package pre) de =
    ((),shadow_before)` by simp[] >>
  Cases_on `new_block lbl shadow_before` >>
  rename1 `new_block lbl shadow_before = (old_label,shadow_opened)` >>
  `old_label = shadow_before.cs_current_bb` by
    (qpat_assum `new_block lbl shadow_before = (old_label,shadow_opened)`
      (mp_tac o AP_TERM ``FST:string # compile_state -> string``) >>
     simp[NoAsms, new_block_def, LET_THM]) >>
  `new_block lbl shadow_before = (shadow_before.cs_current_bb,shadow_opened)` by
    (qpat_assum `old_label = shadow_before.cs_current_bb`
      (fn label => qpat_assum `new_block lbl shadow_before = (old_label,shadow_opened)`
        (ACCEPT_TAC o PURE_REWRITE_RULE [label]))) >>
  `gas_shadow_state opened shadow_opened` by
    (qpat_assum `new_block lbl before = (before.cs_current_bb,opened)` (fn real_open =>
     qpat_assum `new_block lbl shadow_before = (old_label,shadow_opened)` (fn shadow_open =>
     qpat_assum `gas_shadow_state before shadow_before` (fn shadow =>
       mp_tac (Q.INST [`label` |-> `lbl`] gas_shadow_compiles_new_block) >>
       PURE_REWRITE_TAC [gas_shadow_compiles_def] >>
       disch_then (qspecl_then [`before`,`shadow_before`] mp_tac) >>
       simp[NoAsms, real_open, shadow_open, shadow]))) >>
     disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  Cases_on `compile_entry_checks mc pay shadow_opened` >>
  rename1 `compile_entry_checks mc pay shadow_opened = (shadow_answer,shadow_checked)` >>
  Cases_on `shadow_answer` >>
  `gas_shadow_state checked shadow_checked` by
    (qpat_assum `compile_entry_checks mc pay opened = ((),checked)` (fn real_checks =>
     qpat_assum `compile_entry_checks mc pay shadow_opened = ((),shadow_checked)` (fn shadow_checks =>
     qpat_assum `gas_shadow_state opened shadow_opened` (fn shadow =>
       mp_tac (Q.INST [`min_cds` |-> `mc`, `payable` |-> `pay`]
         gas_shadow_compiles_compile_entry_checks) >>
       PURE_REWRITE_TAC [gas_shadow_compiles_def] >>
       disch_then (qspecl_then [`opened`,`shadow_opened`] mp_tac) >>
       simp[NoAsms, real_checks, shadow_checks, shadow])))) >>
  Cases_on `compile_register_positional_args (gas_shadow_env T ce) pos 4 shadow_checked` >>
  rename1 `compile_register_positional_args _ pos 4 shadow_checked = (shadow_registered_env,shadow_registered)` >>
  `gas_shadow_env T registered_env = shadow_registered_env /\
    gas_shadow_state registered shadow_registered` by
    (qpat_assum `compile_register_positional_args ce pos 4 checked = (registered_env,registered)`
      (fn real_register =>
       qpat_assum `compile_register_positional_args (gas_shadow_env T ce) pos 4 shadow_checked =
          (shadow_registered_env,shadow_registered)` (fn shadow_register =>
       qpat_assum `gas_shadow_state checked shadow_checked` (fn shadow =>
         qspecl_then [`pos`,`ce`,`4`]
           (mp_tac o PURE_REWRITE_RULE [gas_shadow_compiles_env_def])
           (Q.INST [`sd` |-> `T`] gas_shadow_compiles_env_register_positional_args) >>
         disch_then (qspecl_then [`checked`,`shadow_checked`] mp_tac) >>
         simp[NoAsms, real_register, shadow_register, shadow])))) >>
  qpat_x_assum `gas_shadow_env T registered_env = shadow_registered_env`
    (SUBST_ALL_TAC o SYM) >>
  Cases_on `compile_guarded_body (gas_shadow_env T registered_env) nr key tr view
       (MAP gas_shadow_stmt body_code) rt shadow_registered` >>
  rename1 `compile_guarded_body _ _ _ _ _ _ _ shadow_registered = (shadow_answer,shadow_last)` >>
  Cases_on `shadow_answer` >>
  `gas_shadow_state last shadow_last` by
    (qpat_assum `compile_guarded_body registered_env nr key tr view body_code rt registered = ((),last)`
      (fn real_body =>
       qpat_assum `compile_guarded_body (gas_shadow_env T registered_env) nr key tr view
          (MAP gas_shadow_stmt body_code) rt shadow_registered = ((),shadow_last)` (fn shadow_body =>
       qpat_assum `gas_shadow_state registered shadow_registered` (fn shadow =>
         mp_tac (Q.INST [`sd` |-> `T`, `ce` |-> `registered_env`, `nr` |-> `nr`,
            `key` |-> `key`, `trans` |-> `tr`, `view` |-> `view`,
            `stmts` |-> `body_code`, `ret` |-> `rt`]
           gas_shadow_compiles_compile_guarded_body) >>
         PURE_REWRITE_TAC [gas_shadow_compiles_def] >>
         disch_then (qspecl_then [`registered`,`shadow_registered`] mp_tac) >>
         simp[NoAsms, real_body, shadow_body, shadow])))) >>
  suspend "linked_linear_accepted_shadow_body_code"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_accepted_shadow_body_code]:
  map_every (fn pattern => qpat_assum pattern
    (assume_tac o PURE_REWRITE_RULE [markerTheory.Abbrev_def]))
    [`Abbrev (packs = _)`, `Abbrev (ips = _)`, `Abbrev (sels = _)`] >>
  `EVERY (\(l,c,p,m,py,n,k,t,v,b,r). jump_label_ok l)
    (MAP gas_shadow_external_package packs)` by
    (qpat_assum `packs = MAP _ exts` SUBST1_TAC >>
     simp[EVERY_MAP, EVERY_MEM] >>
     qx_gen_tac `input` >> PairCases_on `input` >>
     simp[package_external_fn_unit_def, set_external_package_target_def,
          gas_shadow_external_package_def, jump_label_ok_def]) >>
  `EVERY (\d. internal_label_ok (FST d))
    (internal_fn_descriptors (MAP gas_shadow_internal_package ips))` by
    (PURE_REWRITE_TAC [gas_shadow_internal_fn_descriptors] >>
     qpat_assum `ips = MAP _ _` SUBST1_TAC >>
     simp[unit_package_internal_labels]) >>
  `packs = pre ++ (lbl,ce,pos,mc,pay,nr,key,tr,view,body_code,rt)::post` by
    (qpat_assum `packs = MAP _ exts` SUBST1_TAC >> FIRST_ASSUM ACCEPT_TAC) >>
  qpat_assum `packs = pre ++ _::post` (fn split =>
    qpat_assum `run_lowering sels (MAP gas_shadow_external_package packs) _ _ _ _ _ _ _ _ = SOME shadow_unit`
      (assume_tac o PURE_REWRITE_RULE [split, MAP_APPEND, MAP, gas_shadow_external_package_def]) >>
    qpat_assum `EVERY _ (MAP gas_shadow_external_package packs)`
      (assume_tac o PURE_REWRITE_RULE [split, MAP_APPEND, MAP, gas_shadow_external_package_def])) >>
  `compile_selector_dispatch_linear (MAP (\(sel,l,z). (sel,l)) sels) fl ds = ((),de)` by
    (qpat_assum `sels = build_selectors _ _` SUBST1_TAC >>
     qpat_assum `Abbrev (selectors = _)`
       (fn selectors => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] selectors)]) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  drule_all (Q.INST [`unit` |-> `shadow_unit`, `sa` |-> `shadow_registered`,
    `st'` |-> `shadow_last`] run_lowering_pinned_body_interval) >>
  disch_then (qx_choose_then `shadow_fn`
    (map_every assume_tac o CONJUNCTS)) >>
  `gas_shadow_function fn shadow_fn` by
    (qspecl_then [`unit.cu_context.ctx_functions`,
         `shadow_unit.cu_context.ctx_functions`,`"__entry"`] mp_tac
       gas_shadow_lookup_function >>
     impl_tac
     >- (qpat_assum `gas_shadow_context unit.cu_context shadow_unit.cu_context`
          (strip_assume_tac o PURE_REWRITE_RULE [gas_shadow_context_def]) >>
         FIRST_ASSUM ACCEPT_TAC) >>
     qpat_assum `lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn`
       (fn real => qpat_assum `lookup_function "__entry" shadow_unit.cu_context.ctx_functions =
          SOME shadow_fn` (fn shadow => simp[NoAsms, OPTREL_def, real, shadow]))) >>
  qpat_assum `compile_guarded_body _ nr key tr view (MAP _ _) rt shadow_registered = ((),shadow_last)`
    (fn shadow_body => qpat_assum `fn_has_code shadow_registered shadow_last shadow_fn`
      (mp_tac o MATCH_MP guarded_body_code_from_registration o CONJ shadow_body)) >>
  disch_then (qx_choosel_then [`shadow_locked`,`shadow_body_end`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "linked_linear_accepted_paired_intervals"
QED

val linked_positional_live_calls_tac =
  `EVERY (\k. MEM k (linked_live_functions mods exps))
    (int_calls_stmts body_code) /\ stmts_loop_calls_ok mods body_code` by
    (asm "selected_decl" (DISJ_CASES_THEN strip_assume_tac)
     >- (`MEM (src,tx.function_name)
              (linked_main_roots mods ++ linked_export_roots exps)` by
           (Cases_on `src` >>
            simp_tac bool_ss [MEM_APPEND]
            >- (disj1_tac >>
                `MEM (NONE:num option,tx.function_name)
                  (FLAT (MAP (external_name_keys_toplevel NONE) tops))` by
                  (simp[NoAsms, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
                   qexists_tac `FunctionDecl External mut nr raw tx.function_name args [] ret fbody` >>
                   simp[NoAsms, external_name_keys_toplevel_def] >>
                   first_assum ACCEPT_TAC) >>
                qpat_assum `ALOOKUP mods NONE = SOME tops` (fn main =>
                  simp[NoAsms, linked_main_roots_def, main, contract_keys_def, MEM_APPEND]) >>
                disj1_tac >> first_assum ACCEPT_TAC) >>
            disj2_tac >> simp[NoAsms, linked_export_roots_def, MEM_MAP, EXISTS_PROD] >>
            qpat_assum `SOME _ = ALOOKUP exps tx.function_name`
              (mp_tac o MATCH_MP ALOOKUP_MEM o SYM) >>
            disch_then ACCEPT_TAC) >>
         `MEM (src,tx.function_name) (linked_live_functions mods exps)` by
           (PURE_REWRITE_TAC [linked_live_functions_def, linked_live_functions_from_def, LET_THM] >>
            BETA_TAC >> irule (cj 1 call_closure_from_roots) >> FIRST_ASSUM ACCEPT_TAC) >>
         conj_tac
         >- (simp_tac bool_ss [Abbr `body_code`] >>
             drule_then assume_tac ALOOKUP_MEM >>
             drule_all_then ACCEPT_TAC checked_live_body_subst_calls_mods) >>
         qpat_assum `!sid ts vis mut nr raw name args dflts ret body.
             ALOOKUP mods sid = SOME ts /\ _ ==> _`
           (qspecl_then [`src`,`tops`,`External`,`mut`,`nr`,`raw`,
             `tx.function_name`,`args`,`[]`,`ret`,`fbody`] mp_tac) >>
         simp[Abbr `body_code`]) >>
     conj_tac
     >- (qpat_assum `int_calls_stmts body_code = int_calls_stmts fbody` SUBST1_TAC >>
         `int_calls_stmts fbody = []` by
           (drule_all_then ACCEPT_TAC selected_public_getter_body_int_calls_empty) >>
         qpat_assum `int_calls_stmts fbody = []`
           (fn empty => simp_tac bool_ss [empty, EVERY_DEF])) >>
     simp_tac bool_ss [Abbr `body_code`] >>
     drule_then MATCH_MP_TAC checked_subst_consts_loop_calls_ok_mods >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`external_getter_tuple src top = SOME (mut,nr,args,[],ret,fbody)`,
        `is_public_getter_decl tx.function_name top`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `top` >> simp[is_public_getter_decl_def, external_getter_tuple_def] >>
     Cases_on `v` >> gvs[is_public_getter_decl_def, external_getter_tuple_def,
       getter_def, AllCaseEqs(), stmt_loop_calls_ok_def] >>
     pairarg_tac >> gvs[] >> rpt strip_tac >> gvs[stmt_loop_calls_ok_def]);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_accepted_paired_intervals]:
  linked_positional_live_calls_tac >>
  suspend "linked_linear_selected_invariant"
QED

val linked_positional_runtime_ready_tac =
  `checked_contract_runtime_ready art mods am tx` by
    (drule_all source_typing_ok_runtime_ready_mods >>
     disch_then (qx_choose_then `ready_art` (map_every assume_tac o CONJUNCTS)) >>
     `ready_art = art` by
       (qpat_assum `check_contract F am.layouts tx.target mods = SOME ready_art` mp_tac >>
        qpat_assum `check_contract F am.layouts tx.target mods = SOME art`
          (fn checked => simp[NoAsms, checked])) >>
     qpat_assum `checked_contract_runtime_ready ready_art mods am tx` (fn ready =>
       qpat_assum `ready_art = art` (fn same =>
         ACCEPT_TAC (PURE_REWRITE_RULE [same] ready))));

val linked_positional_formals_tac =
  `!id ty. MEM (id,ty) args ==>
    FLOOKUP entry_types.var_types id = SOME ty /\
    IS_SOME (FLOOKUP entry_types.var_assignable id)` by
    (rpt strip_tac >>
     qpat_assum `ALL_DISTINCT (MAP FST args)` (fn distinct =>
       qpat_assum `MEM (id,ty) args` (fn member =>
         mp_tac (MATCH_MP
           (Q.SPECL [`args`,`artifact_env art mods src`,`id`,`ty`]
             (Q.INST [`asg` |-> `F`] FOLDL_extend_local_args_formal_lookup))
           (CONJ distinct member)))) >>
     simp[NoAsms, Abbr `entry_types`, function_entry_env_def]) >>
  `!n ty. FLOOKUP entry_types.var_types n = SOME ty ==>
    ?id. MEM (id,ty) args /\ n = id` by
    (rpt strip_tac >>
     `?id. MEM (id,ty) args /\ n = id` by
       (mp_tac (Q.SPECL [`args`,`artifact_env art mods src`,`n`,`ty`]
          (Q.INST [`asg` |-> `F`] FOLDL_extend_local_args_var_types_range)) >>
        qpat_assum `FLOOKUP entry_types.var_types n = SOME ty` mp_tac >>
        qpat_assum `ALL_DISTINCT (MAP FST args)` mp_tac >>
        simp[NoAsms, Abbr `entry_types`, function_entry_env_def, artifact_env_def]) >>
     qexists_tac `id` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `!n b. FLOOKUP entry_types.var_assignable n = SOME b ==>
    ?id ty. MEM (id,ty) args /\ n = id` by
    (rpt strip_tac >>
     (Q.SUBGOAL_THEN `?id ty. MEM (id,ty) args /\ n = id /\ b = F`
       (qx_choosel_then [`id`,`value_type`] strip_assume_tac)
     >- (mp_tac (Q.SPECL [`args`,`artifact_env art mods src`,`n`,`b`]
          (Q.INST [`asg` |-> `F`] FOLDL_extend_local_args_var_assignable_range)) >>
        qpat_assum `FLOOKUP entry_types.var_assignable n = SOME b` mp_tac >>
        qpat_assum `ALL_DISTINCT (MAP FST args)` mp_tac >>
        simp[NoAsms, Abbr `entry_types`, function_entry_env_def, artifact_env_def])) >>
     qexistsl_tac [`id`,`value_type`] >> conj_tac >> first_assum ACCEPT_TAC);

val linked_positional_scope_tac =
  `get_tenv cx = type_env_all_modules mods` by
    (qpat_assum `ALOOKUP am.sources tx.target = SOME mods` (fn source =>
       simp[NoAsms, Abbr `cx`, initial_evaluation_context_def, get_tenv_def, source])) >>
  `env_scopes_consistent entry_types cx es0` by
    (`es0 with scopes := [env] = es0` by
       simp[evaluation_state_component_equality] >>
     pop_assum (fn scopes => PURE_ONCE_REWRITE_TAC [GSYM scopes]) >>
     irule bind_arguments_env_scopes_consistent >>
     qexistsl_tac [`args`,`type_env_all_modules mods`,`tx.args`] >>
     asm_rewrite_tac[]) >>
  `env_context_consistent entry_types cx` by
    (irule env_context_consistent_same_static_maps >>
     qexists_tac `artifact_env art mods src` >>
     simp[NoAsms, Abbr `entry_types`, function_entry_env_def, FOLDL_extend_local_args_static] >>
     simp[NoAsms, Abbr `cx`] >>
     irule check_contract_env_context_consistent_initial_src >>
     qexists_tac `tx.target` >> rpt conj_tac >> (REFL_TAC ORELSE first_assum ACCEPT_TAC)) >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx am.immutables` by
    (qpat_assum `Abbrev (cx = _)`
       (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     irule immutables_ready_initial_evaluation_context_source >>
     qpat_assum `checked_contract_runtime_ready art mods am tx`
       (ACCEPT_TAC o cj 3 o REWRITE_RULE [checked_contract_runtime_ready_def])) >>
  `env_immutables_consistent entry_types cx es0` by
    (qpat_assum `es0.immutables = am.immutables` (fn imms =>
       simp[NoAsms, imms, Abbr `entry_types`, env_immutables_consistent_def,
            function_entry_env_def, artifact_env_def, FOLDL_extend_local_args_static]) >>
     qpat_assum `immutables_ready art.cta_bare_globals _ cx _`
       (ACCEPT_TAC o SIMP_RULE (srw_ss()) [immutables_ready_def])) >>
  `env_consistent entry_types cx es0` by
    asm_rewrite_tac [env_consistent_def];

val linked_positional_source_types_tac =
  `context_well_typed cx` by
    (qpat_assum `call_tx_well_typed tx` mp_tac >>
     simp[NoAsms, call_tx_well_typed_def, context_well_typed_def,
          Abbr `cx`, initial_evaluation_context_def, dimword_def]) >>
  `functions_well_typed cx` by
    (qpat_assum `Abbrev (cx = _)`
       (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     irule check_contract_functions_well_typed_initial >>
     qexistsl_tac [`tx.target`,`art`,`mods`] >>
     simp[NoAsms] >> conj_tac >> first_assum ACCEPT_TAC);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_selected_invariant]:
  linked_positional_runtime_ready_tac >>
  linked_positional_formals_tac >>
  linked_positional_scope_tac >>
  linked_positional_source_types_tac >>
  suspend "linked_linear_selected_body_resources"
QED

val linked_positional_static_maps_tac =
  `entry_types.bare_globals = art.cta_bare_globals /\
    entry_types.bare_global_assignable = art.cta_bare_global_assignable /\
    entry_types.toplevel_vtypes = art.cta_toplevel_vtypes /\
    entry_types.fn_sigs = art.cta_fn_sigs /\
    entry_types.type_defs = get_tenv cx /\ entry_types.current_src = src` by
    (qpat_assum `get_tenv cx = type_env_all_modules mods` (fn tenv =>
       simp[NoAsms, Abbr `entry_types`, function_entry_env_def, FOLDL_extend_local_args_static,
            artifact_env_def, tenv])) >>
  `check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art` by
    (qpat_assum `check_contract F am.layouts tx.target mods = SOME art` (fn checked =>
       simp[NoAsms, Abbr `cx`, initial_evaluation_context_def, checked])) >>
  `ALOOKUP cx.sources cx.txn.target = SOME mods` by
    (qpat_assum `ALOOKUP am.sources tx.target = SOME mods` (fn sources =>
       simp[NoAsms, Abbr `cx`, initial_evaluation_context_def, sources])) >>
  `linked_fn_sigs_declared mods cx entry_types.fn_sigs` by
    (qpat_assum `entry_types.fn_sigs = art.cta_fn_sigs` SUBST1_TAC >>
     drule_then ACCEPT_TAC check_contract_linked_fn_sigs_declared);

val linked_positional_const_cells_tac =
  `body_const_cells_agree_mods mods cx entry_types es0` by
    (`(case ALOOKUP es0.immutables cx.txn.target of
          NONE => empty_immutables | SOME cells => cells) =
         account_immutables am tx.target` by
       (qpat_assum `es0.immutables = am.immutables` (fn imms =>
          simp[NoAsms, imms, Abbr `cx`, initial_evaluation_context_def,
               account_immutables_def])) >>
     irule checked_body_const_cells_agree_mods >>
     pop_assum SUBST1_TAC >> rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       qexists_tac `account_immutables am tx.target` >>
         simp[NoAsms] >> first_assum ACCEPT_TAC,
       qexists_tac `art` >> PURE_REWRITE_TAC [frame_maps_def] >>
         rpt conj_tac >> first_assum ACCEPT_TAC]) >>
  `outcomes_accounts_typed es0.outcomes /\ IS_SOME es0.outcomes` by
    asm_rewrite_tac[optionTheory.IS_SOME_DEF];

val linked_positional_slot_witness_tac =
  `!id ty. FLOOKUP entry_types.var_types id = SOME ty ==>
    ?p sz. FLOOKUP registered_env.ce_vars id = SOME (PtrVar (Var p) sz)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!n ty. FLOOKUP entry_types.var_types n = SOME ty ==>
         ?id. MEM (id,ty) args /\ n = id`
       (drule_then strip_assume_tac) >>
     qpat_x_assum `id = id'` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `MEM (id,ty) args` (mp_tac o REWRITE_RULE [MEM_EL]) >>
     disch_then (qx_choose_then `j` strip_assume_tac) >>
     qpat_assum `!j. j < LENGTH args ==> ?aid q p n. _`
       (drule_then strip_assume_tac) >>
     qexistsl_tac [`q`,`n`] >>
     qpat_assum `(id,ty) = EL j args` (fn pair_eq =>
       qpat_assum `FLOOKUP registered_env.ce_vars (FST (EL j args)) = _`
         (fn lookup => mp_tac lookup >> simp[NoAsms, GSYM pair_eq])));

Resume linked_runtime_dispatched_readings_certificate[linked_linear_selected_body_resources]:
  linked_positional_static_maps_tac >>
  linked_positional_const_cells_tac >>
  linked_positional_slot_witness_tac >>
  suspend "linked_linear_selected_local_slots"
QED

val linked_positional_slot_metadata_tac =
  `ce_locals_declared registered_env entry_types` by
    (irule (Q.INST_TYPE [`:'a` |-> `:type`] ce_locals_declared_params) >>
     qexists_tac `args` >>
     conj_tac
     >- (qx_genl_tac [`n`,`loc`] >> strip_tac >>
         drule_all compile_register_positional_args_bound >>
         disch_then (qx_choose_then `slot` assume_tac) >>
         CCONTR_TAC >>
         qpat_assum `!k. ~MEM k (MAP FST args) ==> FLOOKUP ce.ce_vars k = NONE`
           (drule_then (fn missing =>
             qpat_assum `FLOOKUP ce.ce_vars n = SOME slot` mp_tac >>
             simp[NoAsms, missing]))) >>
     simp[NoAsms, Abbr `entry_types`, function_entry_env_var_types_fdom]) >>
  `registered_env.ce_struct_fields = make_struct_fields_map_mods mods /\
    registered_env.ce_var_type =
      (\n. ALOOKUP (REVERSE (args ++ collect_locals body_code)) n)` by
    (qpat_assum `registered_env = ce with ce_vars := registered_env.ce_vars`
       (fn installed => PURE_ONCE_REWRITE_TAC [installed]) >>
     qpat_assum `ce = _` SUBST1_TAC >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case =>
       simp[NoAsms, ret_case, Abbr `base_env`, build_compile_env_unit_def,
            pairTheory.ELIM_UNCURRY, update_cenv_nonreentrant_def,
            update_cenv_ret_abi_def])) >>
  qabbrev_tac `alloc_env = build_compile_env_unit mods src Internal mut name args ret body_code F` >>
  `type_memory_bytes registered_env = type_memory_bytes alloc_env` by
    (irule type_memory_bytes_frame >>
     qpat_assum `registered_env.ce_struct_fields = _` SUBST1_TAC >>
     simp[NoAsms, Abbr `alloc_env`, build_compile_env_unit_def, pairTheory.ELIM_UNCURRY]);

val linked_positional_slot_sizes_tac =
  `EVERY (\(_,ty). type_memory_bytes alloc_env ty < 2 ** 64) args` by
    (qpat_assum `fn_allocs_ok_unit mods (src,(mut,nr,raw,name,args,[],ret,body_code))`
       (mp_tac o REWRITE_RULE [fn_allocs_ok_unit_def, LET_THM]) >>
     simp[NoAsms, Abbr `alloc_env`]) >>
  `locals_alloc_ok registered_env entry_types` by
    (simp_tac std_ss [locals_alloc_ok_def] >> qx_genl_tac [`id`,`ty`] >> strip_tac >>
     qpat_assum `!n ty. FLOOKUP entry_types.var_types n = SOME ty ==>
         ?id. MEM (id,ty) args /\ n = id`
       (drule_then strip_assume_tac) >>
     qpat_assum `type_memory_bytes registered_env = type_memory_bytes alloc_env` SUBST1_TAC >>
     qpat_assum `EVERY (\(_,ty). type_memory_bytes alloc_env ty < 2 ** 64) args`
       (mp_tac o Q.SPEC `(id,ty)` o REWRITE_RULE [EVERY_MEM]) >>
     qpat_assum `id = id'` (fn same =>
       qpat_assum `MEM (id',ty) args`
         (fn member => simp[NoAsms, same, member])));

Resume linked_runtime_dispatched_readings_certificate[linked_linear_selected_local_slots]:
  linked_positional_slot_metadata_tac >>
  linked_positional_slot_sizes_tac >>
  suspend "linked_linear_selected_body_invariant"
QED

val linked_positional_locals_fresh_tac =
  `!id. MEM id (MAP FST args) ==> ~MEM id (MAP FST (collect_locals body_code))` by
    (gen_tac >> strip_tac >> asm "selected_decl" (DISJ_CASES_THEN strip_assume_tac)
     >- (qpat_assum `!f. MEM (FunctionDecl External _ _ _ f _ _ _ _) tops ==> _`
           (drule_then strip_assume_tac) >>
         drule (cj 2 type_stmt_bindings_fresh) >>
         qpat_assum `Abbrev (entry_types = _)` (fn abbrev =>
           simp[NoAsms, REWRITE_RULE [markerTheory.Abbrev_def] abbrev,
                function_entry_env_var_types_fdom, EVERY_MEM, MAP_APPEND, MEM_APPEND,
                collect_locals_supported_bindings_mem]) >>
         disch_then (qspec_then `id` mp_tac) >> simp[]) >>
     `collect_locals body_code = []` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`external_getter_tuple src top = SOME (mut,nr,args,[],ret,fbody)`,
           `is_public_getter_decl tx.function_name top`] >>
        qpat_assum `Abbrev (body_code = _)` (fn body =>
          POP_ASSUM_LIST (K ALL_TAC) >>
          PURE_ONCE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] body]) >>
        Cases_on `top` >> simp[is_public_getter_decl_def] >>
        Cases_on `v` >> simp[is_public_getter_decl_def, external_getter_tuple_def,
          getter_def, AllCaseEqs(), subst_consts_stmt_mods_def, collect_locals_def] >>
        pairarg_tac >> gvs[] >> rpt strip_tac >>
        gvs[subst_consts_stmt_mods_def, collect_locals_def]) >>
     pop_assum (fn empty => simp[NoAsms, empty]));

val linked_positional_local_types_tac =
  `!id ty. FLOOKUP entry_types.var_types id = SOME ty ==>
    registered_env.ce_var_type id = SOME ty` by
    (qx_genl_tac [`id`,`ty`] >> strip_tac >>
     qpat_assum `!n ty. FLOOKUP entry_types.var_types n = SOME ty ==>
         ?id. MEM (id,ty) args /\ n = id`
       (drule_then strip_assume_tac) >>
     qpat_x_assum `id = id'` (SUBST_ALL_TAC o SYM) >>
     `MEM id (MAP FST args)` by
       (simp[NoAsms, MEM_MAP] >> qexists_tac `(id,ty)` >>
        simp[NoAsms] >> first_assum ACCEPT_TAC) >>
     `ALOOKUP (REVERSE (collect_locals body_code)) id = NONE` by
       (qpat_assum `!id. MEM id (MAP FST args) ==> _` (drule_then mp_tac) >>
        simp[NoAsms, ALOOKUP_NONE, MAP_REVERSE]) >>
     `ALOOKUP (REVERSE args) id = SOME ty` by
       (irule ALOOKUP_ALL_DISTINCT_MEM >> simp[MAP_REVERSE, ALL_DISTINCT_REVERSE]) >>
     qpat_assum `registered_env.ce_var_type = _` SUBST1_TAC >>
     asm_simp_tac (srw_ss()) [REVERSE_APPEND, ALOOKUP_APPEND]);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_selected_body_invariant]:
  linked_positional_locals_fresh_tac >>
  linked_positional_local_types_tac >>
  suspend "linked_linear_selected_static_metadata"
QED
val linked_positional_expr_inv_tac =
  `~cx.in_deploy /\ check_contract F cx.layouts cx.txn.target mods = SOME art` by
    (qpat_assum `check_contract F am.layouts tx.target mods = SOME art` (fn checked =>
       simp[NoAsms, Abbr `cx`, initial_evaluation_context_def, checked])) >>
  `entry_types.bare_global_assignable = FEMPTY` by
    (qpat_assum `entry_types.bare_global_assignable = _` SUBST1_TAC >>
     drule_then ACCEPT_TAC check_contract_runtime_assignable) >>
  `imm_len_mods mods < 24576` by
    (PURE_ONCE_REWRITE_TAC [imm_len_mods_def] >> first_assum ACCEPT_TAC) >>
  `expr_sim_inv_mods mods registered_env cx entry_types es0` by
    drule_all_then ACCEPT_TAC linked_external_entry_expr_sim_inv_mods;

Resume linked_runtime_dispatched_readings_certificate[linked_linear_selected_static_metadata]:
  linked_positional_expr_inv_tac >>
  suspend "linked_linear_selected_body_support"
QED

val linked_positional_constants_tac =
  `!key r. ALOOKUP (consts_env_mods mods) key = SOME r ==>
      accesses_expr r = []` by
    (qpat_assum `body_const_cells_agree_mods mods cx entry_types es0`
       (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_mods_def]) >>
     qx_genl_tac [`const_key`,`rhs`] >> PairCases_on `const_key` >> strip_tac >>
     qpat_assum `!sid id r. ALOOKUP (consts_env_mods mods) (sid,id) = SOME r ==> _`
       (drule_then strip_assume_tac) >>
     first_assum ACCEPT_TAC) >>
  `~supported_stmts_expr_exists (const_name_root_mods mods) body_code` by
    (qpat_assum `Abbrev (body_code = _)`
       (fn code => PURE_ONCE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] code]) >>
     MATCH_MP_TAC (Q.INST [`mods` |-> `mods`, `ss` |-> `fbody`]
       linkedEntryImmutableGuardsTheory.substituted_stmts_const_name_free_mods) >>
     first_assum ACCEPT_TAC);

val linked_positional_typed_widths_tac =
  `!env_after. type_stmts entry_types ret body_code = SOME env_after ==>
      ~supported_stmts_expr_exists (\e. ~byte_widths_expr e) body_code` by
    (gen_tac >> strip_tac >>
     MATCH_MP_TAC (Q.INST [`args` |-> `args`, `cx` |-> `cx`,
       `env` |-> `entry_types`, `env'` |-> `env_after`, `ret` |-> `ret`,
       `ss` |-> `body_code`] (SPEC_ALL typed_parameter_body_excludes_bad_widths)) >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       qpat_assum `entry_types.type_defs = get_tenv cx` SUBST1_TAC >>
       qpat_assum `get_tenv cx = type_env_all_modules mods` SUBST1_TAC >>
       qpat_assum `params_ok (type_env_all_modules mods) args`
         (strip_assume_tac o REWRITE_RULE [params_ok_def]) >>
       first_assum ACCEPT_TAC,
       rpt strip_tac >>
       qpat_assum `!n ty. FLOOKUP entry_types.var_types n = SOME ty ==>
           ?id. MEM (id,ty) args /\ n = id` (drule_then strip_assume_tac) >>
       qpat_x_assum `n = id` SUBST_ALL_TAC >> first_assum ACCEPT_TAC]);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_selected_body_support]:
  linked_positional_constants_tac >>
  linked_positional_typed_widths_tac >>
  suspend "linked_linear_selected_decl_resolution"
QED

val linked_positional_decl_resolution_tac =
  `MEM (FunctionDecl External mut nr raw tx.function_name args [] ret fbody) tops ==>
    qualified_stmts_decls_ok mods body_code` by
    (strip_tac >>
     qpat_assum `!fn. MEM (FunctionDecl External _ _ _ _ _ _ _ _) tops ==>
       check_function_body am.layouts tx.target mods art src _ _ _ _ _ _ _`
       (drule_then assume_tac) >>
     simp_tac bool_ss [Abbr `body_code`] >>
     qpat_assum `check_contract F am.layouts tx.target mods = SOME art` (fn cc =>
       qpat_assum `check_function_body am.layouts tx.target mods art src
          External mut nr args [] ret fbody` (fn cb =>
           ACCEPT_TAC (MATCH_MP checked_qualified_body_decl_resolution (CONJ cc cb)))));

Resume linked_runtime_dispatched_readings_certificate[linked_linear_selected_decl_resolution]:
  linked_positional_decl_resolution_tac >>
  suspend "linked_linear_selected_body_allocation"
QED

val linked_positional_alloc_env_tac =
  `alloc_env_agree alloc_env base_env` by
    (map_every (fn pattern => qpat_assum pattern (fn def =>
       PURE_ONCE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] def]))
       [`Abbrev (alloc_env = _)`, `Abbrev (base_env = _)`] >>
     simp[NoAsms, alloc_env_agree_def, build_compile_env_unit_def,
          pairTheory.ELIM_UNCURRY]) >>
  `alloc_env_agree alloc_env registered_env` by
    (qpat_assum `registered_env = ce with ce_vars := registered_env.ce_vars`
       (fn installed => PURE_ONCE_REWRITE_TAC [installed]) >>
     qpat_assum `ce = _` SUBST1_TAC >>
     qpat_assum `alloc_env_agree alloc_env base_env` mp_tac >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case =>
       simp[NoAsms, ret_case, alloc_env_agree_def, update_cenv_nonreentrant_def,
            update_cenv_ret_abi_def]));

val linked_positional_alloc_limits_tac =
  `alloc_limits_stmts registered_env body_code` by
    (qspecl_then [`alloc_env`,`body_code`,`registered_env`] mp_tac
       (cj 2 alloc_limits_stmt_struct_fields) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then SUBST1_TAC >>
     qpat_assum `fn_allocs_ok_unit mods (src,(mut,nr,raw,name,args,[],ret,body_code))`
       (mp_tac o REWRITE_RULE [fn_allocs_ok_unit_def, LET_THM]) >>
     simp[NoAsms, Abbr `alloc_env`]);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_selected_body_allocation]:
  linked_positional_alloc_env_tac >>
  linked_positional_alloc_limits_tac >>
  suspend "linked_linear_selected_return_buffer"
QED

val linked_positional_return_buffer_tac =
  `stmts_valued_return body_code /\ ~registered_env.ce_raw_return ==>
     return_buffer_ok registered_env` by
    (qpat_assum `registered_env = ce with ce_vars := registered_env.ce_vars`
       (fn installed => PURE_ONCE_REWRITE_TAC [installed]) >>
     simp[NoAsms, return_buffer_ok_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     Cases_on `ret = NoneT`
     >- (qpat_assum `ce = _` SUBST1_TAC >>
         qpat_assum `ret = NoneT` (fn empty =>
           simp[NoAsms, empty, Abbr `base_env`, build_compile_env_unit_def,
                update_cenv_nonreentrant_def, pairTheory.ELIM_UNCURRY])) >>
     Cases_on `is_word_type ret`
     >- (qpat_assum `is_word_type ret`
           (mp_tac o Q.SPEC `base_env with ce_raw_return := raw` o
             MATCH_MP (ONCE_REWRITE_RULE [SWAP_FORALL_THM]
               update_cenv_ret_abi_word_return_buffer_ok)) >>
         qpat_assum `ce = _` SUBST1_TAC >>
         qpat_assum `ret <> NoneT` (fn nonempty =>
           simp[NoAsms, nonempty, return_buffer_ok_def,
                update_cenv_nonreentrant_def])) >>
     qpat_assum `external_return_buffer_ok _` mp_tac >>
     qpat_assum `rt = _` SUBST1_TAC >>
     simp[external_return_buffer_ok_def, return_buffer_ok_def]);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_selected_return_buffer]:
  `external_return_buffer_ok
     (lbl,ce,pos,mc,pay,nr,key,tr,view,body_code,rt)` by
    (qpat_assum `EVERY external_return_buffer_ok packs`
       (MATCH_MP_TAC o REWRITE_RULE [EVERY_MEM]) >>
     qpat_assum `Abbrev (packs = MAP _ exts)` (fn packs =>
       simp_tac bool_ss [REWRITE_RULE [markerTheory.Abbrev_def] packs,
         MEM_MAP, combinTheory.o_DEF]) >>
     qexists_tac `(src,(mut,nr,raw,name,args,[],ret,body_code))` >>
     conj_tac >- (sym_tac >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  linked_positional_return_buffer_tac >>
  suspend "linked_linear_selected_support_typing"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_selected_support_typing]:
  asm "selected_decl" (DISJ_CASES_THEN strip_assume_tac)
  >- suspend "linked_linear_declared_support_env" >>
  suspend "linked_linear_getter_support"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_support_env]:
  qpat_assum `!fn. MEM (FunctionDecl External _ _ _ _ _ _ _ _) tops ==>
    check_function_body am.layouts tx.target mods art src _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  `linked_body_type_facts tops src (type_env_all_modules mods)` by
    (qpat_assum `check_contract F am.layouts tx.target mods = SOME art` (fn check =>
      qpat_assum `ALOOKUP mods src = SOME tops` (fn owner =>
        ACCEPT_TAC (MATCH_MP linked_checked_body_type_facts (CONJ check owner))))) >>
  `src = NONE ==> layouts_agree tops am tx` by
    (strip_tac >>
     `MEM (NONE,tops) mods` by
       (qpat_assum `src = NONE` (fn main =>
          qpat_assum `ALOOKUP mods src = SOME tops`
            (ACCEPT_TAC o MATCH_MP ALOOKUP_MEM o REWRITE_RULE [main]))) >>
     qpat_assum `layouts_agree_mods mods exps am tx` mp_tac >>
     simp[NoAsms, layouts_agree_mods_def, layouts_agree_def, pairTheory.ELIM_UNCURRY] >>
     disch_then (qspecl_then [`NONE`,`tops`] mp_tac o
       CONJUNCT2 o CONJUNCT2 o CONJUNCT2) >>
     qpat_assum `MEM (NONE,tops) mods` (fn member => simp[NoAsms, member])) >>
  `entry_types.event_fields = art.cta_event_fields` by
    simp[NoAsms, Abbr `entry_types`, function_entry_env_def, artifact_env_def,
         FOLDL_extend_local_args_static] >>
  `linked_body_data_env tops src entry_types` by
    (MATCH_MP_TAC (Q.INST [`mode` |-> `F`, `am` |-> `am`, `tx` |-> `tx`,
      `mods` |-> `mods`, `art` |-> `art`] linked_checked_data_env) >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       qpat_assum `entry_types.type_defs = get_tenv cx` SUBST1_TAC >>
       first_assum ACCEPT_TAC,
       qpat_assum `entry_types.bare_global_assignable = FEMPTY` (fn empty =>
         simp[NoAsms, empty] >> NO_TAC),
       strip_tac >>
       qpat_assum `src = NONE` (fn main =>
         qpat_assum `linked_body_type_facts _ _ _`
           (mp_tac o CONJUNCT1 o REWRITE_RULE [linked_body_type_facts_def]) >>
         simp[NoAsms, main])]) >>
  Q.SUBGOAL_THEN
    `check_contract F am.layouts tx.target mods = SOME art /\
     ALOOKUP mods src = SOME tops /\
     MEM (FunctionDecl External mut nr raw tx.function_name args [] ret fbody) tops /\
     (F ==> External = Deploy) /\
     check_function_body am.layouts tx.target mods art src External mut nr args [] ret fbody`
    (mp_tac o MATCH_MP linked_checked_body_calls)
  >- (simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (entry_types = _)` (fn alias =>
    simp[NoAsms, GSYM (REWRITE_RULE [markerTheory.Abbrev_def] alias)]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "linked_linear_declared_body_supported"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_body_supported]:
  `!x ty. FLOOKUP entry_types.var_types x = SOME ty ==>
      assignable_type (type_env_all_modules mods) ty` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!x ty. FLOOKUP entry_types.var_types x = SOME ty ==>
       ?id. MEM (id,ty) args /\ x = id`
       (drule_then (qx_choose_then `param` strip_assume_tac)) >>
     qpat_assum `params_ok (type_env_all_modules mods) args`
       (strip_assume_tac o REWRITE_RULE [params_ok_def]) >>
     qpat_assum `EVERY _ args` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `(param,ty)` mp_tac) >>
     simp[NoAsms] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  `linked_body_env tops src (type_env_all_modules mods) entry_types` by
    (pure_rewrite_tac [linked_body_env_def] >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       qpat_assum `entry_types.type_defs = get_tenv cx` SUBST1_TAC >>
         first_assum ACCEPT_TAC,
       qpat_assum `entry_types.bare_global_assignable = FEMPTY`
         (fn empty => simp[NoAsms, empty])]) >>
  `FDOM entry_types.var_types = set (MAP FST args)` by
    simp[NoAsms, Abbr `entry_types`, function_entry_env_var_types_fdom] >>
  Q.SUBGOAL_THEN `src = NONE \/ imported_stmts_refs_ok body_code` assume_tac
  >- (Cases_on `src` >> simp[NoAsms] >>
     qpat_assum `ALOOKUP mods (SOME _) = SOME tops`
       (assume_tac o MATCH_MP ALOOKUP_MEM) >>
     simp_tac bool_ss [Abbr `body_code`] >>
     drule_all_then (ACCEPT_TAC o CONJUNCT2)
       check_contract_subst_imported_function_refs_ok) >>
  `!name. ~MEM (StructDecl name []) tops` by
    (qx_gen_tac `empty_struct` >> strip_tac >>
     qpat_assum `check_contract F am.layouts tx.target mods = SOME art` (fn cc =>
       qpat_assum `ALOOKUP mods src = SOME tops` (fn owner =>
         qpat_assum `MEM (StructDecl empty_struct []) tops`
           (mp_tac o MATCH_MP check_contract_toplevel_decl_MEM_checked o
            CONJ cc o CONJ owner))) >>
     simp[NoAsms, check_toplevel_decl_def]) >>
  qpat_assum `IS_SOME (type_stmts entry_types ret
                 (subst_consts_stmts_mods (consts_env_mods mods) fbody))`
    (fn typed => qpat_assum `Abbrev (body_code = _)` (fn code =>
      qx_choose_then `after_body` assume_tac
        (PURE_REWRITE_RULE
          [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] code), optionTheory.IS_SOME_EXISTS]
          typed))) >>
  `IS_SOME (check_contract F cx.layouts cx.txn.target mods)` by
    (qpat_assum `check_contract F am.layouts tx.target mods = SOME art`
       (fn cc => simp[NoAsms, Abbr `cx`, initial_evaluation_context_def, cc])) >>
  suspend "linked_linear_declared_body_guards"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_body_guards]:
  qpat_assum `body_const_cells_agree_mods mods cx entry_types es0`
    (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_mods_def]) >>
  `!key r. ALOOKUP (consts_env_mods mods) key = SOME r ==>
       subst_consts_expr_mods (consts_env_mods mods) r = r` by
    (qx_genl_tac [`const_key`, `rhs`] >> PairCases_on `const_key` >> strip_tac >>
     qpat_assum `!sid id r. ALOOKUP (consts_env_mods mods) (sid,id) = SOME r ==> _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     MATCH_MP_TAC (Q.INST [`mods` |-> `mods`]
       (SPEC_ALL (cj 1 subst_consts_expr_mods_closed))) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `subst_consts_stmts_mods (consts_env_mods mods) body_code = body_code` by
    (qpat_assum `Abbrev (body_code = _)` (fn code =>
       PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] code]) >>
     MATCH_MP_TAC subst_consts_stmts_mods_idempotent >> first_assum ACCEPT_TAC) >>
  `custom_errors_stmts_ok mods body_code` by
    (qpat_assum `Abbrev (body_code = _)` (fn code =>
       PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] code]) >>
     qpat_assum `check_contract F am.layouts tx.target mods = SOME art` (fn cc =>
       qpat_assum `check_function_body am.layouts tx.target mods art src
          External mut nr args [] ret fbody` (fn cb =>
           ACCEPT_TAC (MATCH_MP checked_linked_custom_errors_after_substitution
             (CONJ cc cb))))) >>
  `src = NONE ==> !name. ~MEM (StructDecl name []) tops` by
    (strip_tac >> first_assum ACCEPT_TAC) >>
  `IS_SOME (type_stmts entry_types ret
      (subst_consts_stmts_mods (consts_env_mods mods) body_code))` by
    (qpat_assum `subst_consts_stmts_mods _ body_code = body_code` (fn stable =>
       qpat_assum `type_stmts entry_types ret body_code = SOME after_body`
         (fn typed => simp[NoAsms, stable, typed]))) >>
  `supported_function_body tops External args body_code` by
    drule_all_then MATCH_ACCEPT_TAC checked_linked_typed_body_supported >>
  suspend "linked_linear_declared_exec"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_exec]:
  qabbrev_tac `bindings =
    args ++ supported_stmts_bindings T body_code ++ supported_stmts_bindings F body_code` >>
  `supported_stmts tops bindings body_code` by
    (qpat_assum `supported_function_body tops External args body_code`
       (strip_assume_tac o BETA_RULE o PURE_REWRITE_RULE [supported_function_body_def, LET_THM]) >>
     simp[NoAsms, Abbr `bindings`] >> first_assum ACCEPT_TAC) >>
  `check_linked_state_ownership am.layouts tx.target mods (linked_live_functions mods exps)` by
    (PURE_REWRITE_TAC [GSYM linked_state_ownership_ok_def] >>
     drule_all_then ACCEPT_TAC check_contract_linked_state_ownership_ok) >>
  `MEM (src,tx.function_name) (linked_main_roots mods ++ linked_export_roots exps)` by
    (Cases_on `src` >>
     simp_tac bool_ss [MEM_APPEND]
     >- (disj1_tac >>
         `MEM (NONE:num option,tx.function_name)
              (FLAT (MAP (external_name_keys_toplevel NONE) tops))` by
           (simp[NoAsms, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
            qexists_tac `FunctionDecl External mut nr raw tx.function_name args [] ret fbody` >>
            simp[NoAsms, external_name_keys_toplevel_def] >>
            first_assum ACCEPT_TAC) >>
         qpat_assum `ALOOKUP mods NONE = SOME tops` (fn main =>
           simp[NoAsms, linked_main_roots_def, main, contract_keys_def, MEM_APPEND]) >>
         disj1_tac >> first_assum ACCEPT_TAC) >>
     disj2_tac >> simp[NoAsms, linked_export_roots_def, MEM_MAP, EXISTS_PROD] >>
     qpat_assum `SOME _ = ALOOKUP exps tx.function_name`
       (mp_tac o MATCH_MP ALOOKUP_MEM o SYM) >> disch_then ACCEPT_TAC) >>
  `MEM (src,tx.function_name) (linked_live_functions mods exps)` by
    (PURE_REWRITE_TAC [linked_live_functions_def, linked_live_functions_from_def, LET_THM] >>
     BETA_TAC >> irule (cj 1 call_closure_from_roots) >> first_assum ACCEPT_TAC) >>
  `immutable_section_layout_mods mods registered_env` by
    drule_then ACCEPT_TAC contract_inv_immutable_section_layout >>
  `entry_types.bare_global_assignable = art.cta_bare_global_assignable` by
    simp[NoAsms, Abbr `entry_types`, function_entry_env_def, artifact_env_def,
         FOLDL_extend_local_args_static] >>
  `~supported_stmts_expr_exists (unallocated_bare_global_root registered_env entry_types) body_code /\
    (!key. MEM (WriteAcc (StateRef key)) (accesses_stmts body_code) /\
           IS_SOME (FLOOKUP entry_types.bare_global_assignable key) ==>
           IS_SOME (FLOOKUP registered_env.ce_module_vars key))` by
    (qpat_assum `Abbrev (body_code = _)`
       (PURE_ONCE_REWRITE_TAC o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     drule_all_then ACCEPT_TAC linkedEntryImmutableGuardsTheory.linked_checked_body_immutable_guards) >>
  suspend "linked_linear_declared_frame"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_frame]:
  `MEM (src,tops) mods` by drule_then ACCEPT_TAC ALOOKUP_MEM >>
  `function_header_ok External mut nr raw tx.function_name args [] ret` by
    drule_all_then ACCEPT_TAC check_contract_function_header >>
  `nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot /\
          is_view_mut mut = (mut = View)` by
    (strip_tac >>
     conj_tac
     >- (qpat_assum `Abbrev (cx = _)`
           (PURE_ONCE_REWRITE_TAC o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
         qpat_assum `nr` (ASSUME_TAC o EQT_INTRO) >>
         `MEM (FunctionDecl External mut T raw tx.function_name args [] ret fbody) tops` by
           (qpat_assum `nr = T` (fn enabled =>
              qpat_assum `MEM (FunctionDecl External mut nr raw tx.function_name args [] ret fbody) tops`
                (ACCEPT_TAC o PURE_REWRITE_RULE [enabled]))) >>
         Q.SUBGOAL_THEN
           `src = NONE \/ MEM (src,tx.function_name) (linked_live_functions mods exps)`
           assume_tac
         >- (disj2_tac >> first_assum ACCEPT_TAC) >>
         drule_all_then mp_tac check_contract_linked_lock_slot >>
         Cases_on `ALOOKUP am.layouts tx.target`
         >- (qpat_assum `ALOOKUP am.layouts tx.target = NONE` (fn layout =>
               simp[NoAsms, layout, initial_evaluation_context_def, lookup_nonreentrant_slot_def])) >>
         Cases_on `x` >>
         qpat_assum `ALOOKUP am.layouts tx.target = SOME _` (fn layout =>
           simp[NoAsms, layout, initial_evaluation_context_def, lookup_nonreentrant_slot_def])) >>
     qpat_assum `nr` (ASSUME_TAC o EQT_INTRO) >>
     qpat_assum `nr = T` (fn enabled =>
       qpat_assum `function_header_ok External mut nr raw tx.function_name args [] ret`
         (mp_tac o MATCH_MP function_header_nonreentrant_view o PURE_REWRITE_RULE [enabled])) >>
     simp[NoAsms, is_view_mut_def]) >>
  `raw ==> ?n. ret = BaseT (BytesT (Dynamic n))` by
    (qpat_assum `function_header_ok External mut nr raw tx.function_name args [] ret` mp_tac >>
     simp[NoAsms, function_header_ok_def]) >>
  `ret <> NoneT ==> assignable_type (get_tenv cx) ret` by
    (strip_tac >>
     drule_all_then mp_tac check_contract_function_return_type >>
     qpat_assum `get_tenv cx = type_env_all_modules mods` (fn tenv =>
       qpat_assum `ret <> NoneT` (fn nonempty => simp[NoAsms, tenv, nonempty]))) >>
  suspend "linked_linear_declared_frame_ready"
QED

(* Registered-body stages use registered/locked/body_end/last and their
   shadow counterparts for the paired intervals. The entry route supplies
   the path to (s0,G2,tn2), the binding env, and the selected source tuple
   at src in cx. Source-specific body facts are prepared by the caller. *)
val linked_registered_frame_tac =
  `type_memory_bytes registered_env ret < 2 ** 64` by
    (qpat_assum `type_memory_bytes registered_env = type_memory_bytes alloc_env` SUBST1_TAC >>
     qpat_assum `fn_allocs_ok_unit mods (src,(mut,nr,raw,name,args,[],ret,body_code))`
       (mp_tac o REWRITE_RULE [fn_allocs_ok_unit_def, LET_THM]) >>
     simp[NoAsms, Abbr `alloc_env`]) >>
  `base_env.ce_modules = mods /\ base_env.ce_is_external /\
   ~base_env.ce_is_ctor /\ base_env.ce_return_pc = NONE /\
   base_env.ce_return_buf = NONE /\ base_env.ce_ctor_exit_label = NONE /\
   base_env.ce_type_env = type_env_all_modules mods` by
    simp[NoAsms, Abbr `base_env`, build_compile_env_unit_def, pairTheory.ELIM_UNCURRY] >>
  `registered_env.ce_modules = mods /\ registered_env.ce_is_external /\
   ~registered_env.ce_is_ctor /\ registered_env.ce_return_pc = NONE /\
   registered_env.ce_return_buf = NONE /\ registered_env.ce_ctor_exit_label = NONE /\
   registered_env.ce_nonreentrant = (nr,global_nonreentrant_slot,T,mut = View) /\
   registered_env.ce_raw_return = raw /\
   registered_env.ce_type_env = type_env_all_modules mods` by
    (qpat_assum `registered_env = ce with ce_vars := registered_env.ce_vars`
       (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `ce = _` SUBST1_TAC >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case =>
       simp[NoAsms, ret_case, update_cenv_nonreentrant_def, update_cenv_ret_abi_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC);

val linked_registered_stmts_env_tac =
  `SND (stmts_env registered_env NoLoop ret body_code locked) = body_end` by
    (qpat_assum `compile_stmts registered_env NoLoop _ body_code locked = ((),body_end)`
       (mp_tac o ONCE_REWRITE_RULE [stmtSimPropsTheory.compile_stmts_env]) >>
     qpat_assum `rt = _` SUBST1_TAC >>
     Cases_on `ret = NoneT`
     >- (qpat_assum `ret = NoneT` SUBST_ALL_TAC >>
         drule_then assume_tac externalCallSelectedTheory.type_stmts_none_valued_return >>
         qspecl_then [`body_code`,`tops`,`bindings`,`registered_env`,`NoLoop`,`NoneT`,`BaseT BoolT`]
           mp_tac stmtsEnvRetTyTheory.stmts_env_ret_ty_no_valued_return >>
         impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
         disch_then (fn state => simp[NoAsms, state])) >>
     qpat_assum `ret <> NoneT` (fn nonempty => simp[NoAsms, nonempty])) >>
  qabbrev_tac `body_env = FST (stmts_env registered_env NoLoop ret body_code locked)` >>
  `stmts_env registered_env NoLoop ret body_code locked = (body_env,body_end)` by
    (simp[NoAsms, Abbr `body_env`] >> sym_tac >>
     qpat_assum `SND (stmts_env registered_env NoLoop ret body_code locked) = body_end`
       (SUBST1_TAC o SYM) >> simp[NoAsms, pairTheory.PAIR]);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_frame_ready]:
  linked_registered_frame_tac >>
  linked_registered_stmts_env_tac >>
  suspend "linked_linear_declared_lock"
QED

(* Linear callers establish the route cut in two small stages. Grouped
   callers provide the corresponding path and open block from their cut. *)
val linked_linear_registered_route_tac =
  qabbrev_tac `start =
    vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  qabbrev_tac `explicit = gas_explicit_sites unit.cu_context shadow_unit.cu_context` >>
  `!D. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
      (start,FEMPTY,entry_taint) [] (OK p,G0,tn0)` by
    (gen_tac >> qunabbrev_tac `start` >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (_,FEMPTY,entry_taint) [] (OK p,G0,tn0)`
       (qspecl_then [`D`,`explicit`] ACCEPT_TAC)) >>
  `!D. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
      (start,FEMPTY,entry_taint) [] (OK u,G1,tn1)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) [] (OK p,G0,tn0)`
       (qspec_then `D` (mp_tac o MATCH_MP (SPEC_ALL gas_origin_ptr_path_append))) >>
     disch_then (qspecl_then [`p`,`G0`,`tn0`,`[]`,`OK u`,`G1`,`tn1`] mp_tac) >>
     simp_tac bool_ss [APPEND] >> disch_then MATCH_MP_TAC >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (p,G0,tn0) [] (OK u,G1,tn1)`
       (qspecl_then [`D`,`explicit`] ACCEPT_TAC)) >>
  `!D. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
      (start,FEMPTY,entry_taint) [] (OK s0,G2,tn2)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) [] (OK u,G1,tn1)`
       (qspec_then `D` (mp_tac o MATCH_MP (SPEC_ALL gas_origin_ptr_path_append))) >>
     disch_then (qspecl_then [`u`,`G1`,`tn1`,`[]`,`OK s0`,`G2`,`tn2`] mp_tac) >>
     simp_tac bool_ss [APPEND] >> disch_then MATCH_MP_TAC >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (u,G1,tn1) [] (OK s0,G2,tn2)`
       (qspecl_then [`D`,`explicit`] ACCEPT_TAC));

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_lock]:
  linked_linear_registered_route_tac >>
  suspend "linked_linear_declared_path_ready"
QED

val linked_registered_path_tac =
  `gas_path_mem unit.cu_context fn start 0 (OK s0)` by
    qpat_assum `!D. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) [] (OK s0,G2,tn2)`
      (qspec_then `ARB` (ACCEPT_TAC o MATCH_MP selectedAcceptedInterfacesTheory.selected_zero_path_mem)) >>
  `s0.vs_gas_readings = start.vs_gas_readings` by
    (drule_then mp_tac fragGasPathMemTheory.gas_path_mem_ok_suffix >>
     simp[NoAsms, DROP_0]) >>
  `?bb. lookup_block "__entry" fn.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0` by
    (`?bb. lookup_block "__entry" fn.fn_blocks = SOME bb` by
       (qpat_assum `fn_entry_label fn = SOME "__entry"` mp_tac >>
        Cases_on `fn.fn_blocks` >>
        qpat_assum `fn.fn_blocks = _` (fn blocks =>
          simp[NoAsms, blocks, fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm])) >>
     rename1 `lookup_block "__entry" fn.fn_blocks = SOME found_bb` >>
     qexists_tac `found_bb` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     drule_all_then ACCEPT_TAC lowering_context_ok_block_phi) >>
  rename1 `phi_prefix_length entry_bb.bb_instructions = 0` >>
  `!D. (!fuel. ptr_safe_run D 0 fuel unit.cu_context fn [] G2 tn2 s0) ==>
      !fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn [] FEMPTY entry_taint start` by
    (gen_tac >> strip_tac >>
     `!fuel. ptr_safe_run D 0 fuel unit.cu_context fn [] FEMPTY entry_taint start` by
       (MATCH_MP_TAC (Q.INST [`explicit` |-> `explicit`, `t` |-> `s0`,
         `H` |-> `G2`, `u` |-> `tn2`]
         selectedAcceptedInterfacesTheory.selected_zero_path_ptr_pullback) >>
        conj_tac
        >- qpat_assum `!D. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) [] (OK s0,G2,tn2)`
             (qspec_then `D` ACCEPT_TAC) >>
        conj_tac
        >- (map_every qx_gen_tac [`phi_bb`,`phi_label`] >>
            qpat_assum `!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==> _`
              (qspecl_then [`phi_label`,`phi_bb`] ACCEPT_TAC)) >>
        first_assum ACCEPT_TAC) >>
     MATCH_MP_TAC (Q.INST [`bb` |-> `entry_bb`]
       entryDispatchPtrTheory.ptr_safe_blocks_from_phi_free_run) >>
     conj_tac >- (simp[NoAsms, Abbr `start`] >> first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[NoAsms, Abbr `start`] >>
     first_assum ACCEPT_TAC);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_path_ready]:
  linked_registered_path_tac >>
  suspend "linked_linear_declared_lock_result"
QED

val linked_linear_registered_open_tac =
  `~block_is_terminated registered` by
    (`~block_is_terminated checked` by
       (irule selectedEntryPrefixCodeTheory.compile_entry_checks_open >>
        qexistsl_tac [`mc`,`pay`,`opened`,`()`] >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `compile_register_positional_args ce pos 4 checked = _`
       (DISJ_CASES_THEN2 SUBST1_TAC ACCEPT_TAC o
        MATCH_MP (SPEC_ALL registration_noop_or_open)) >>
     first_assum ACCEPT_TAC);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_lock_result]:
  linked_linear_registered_open_tac >>
  suspend "linked_linear_declared_lock_ready"
QED

fun linked_registered_lock_cases_tac success_tac abort_tac =
  `return_buf_frame NONE registered_env registered s0` by
    (PURE_REWRITE_TAC [loweringPostsTheory.return_buf_frame_def] >>
     first_assum ACCEPT_TAC) >>
  `global_nonreentrant_slot < dimword (:256)` by
    simp[NoAsms, contextTheory.global_nonreentrant_slot_def, wordsTheory.dimword_def] >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) es0` >>
  rename1 `lock_if_nr cx nr (is_view_mut mut) es0 = (lock_answer,es_lock)` >>
  Cases_on `lock_answer` >- success_tac >> abort_tac;

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_lock_ready]:
  linked_registered_lock_cases_tac
    (suspend "linked_linear_declared_lock_success")
    (suspend "linked_linear_declared_lock_abort")
QED

val linked_registered_lock_success_tac =
  rename1 `lock_if_nr cx nr (is_view_mut mut) es0 = (INL lock_value,es_lock)` >>
  Cases_on `lock_value` >>
  `?s_b G_b tn_b.
    gas_path_mem unit.cu_context fn start 0 (OK s_b) /\
    (!D. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
      (start,FEMPTY,entry_taint) [] (OK s_b,G_b,tn_b)) /\
    (!D. (!fuel. ptr_safe_run D 0 fuel unit.cu_context fn [] G_b tn_b s_b) ==>
      !fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn [] FEMPTY entry_taint start) /\
    alloca_history fn s_b /\ return_buf_frame NONE registered_env locked s_b /\
    local_ptrs_reserved registered_env locked /\ fresh_vars_wrt locked s_b /\
    ~block_is_terminated locked /\ ~s_b.vs_halted /\
    s_b.vs_current_bb = locked.cs_current_bb /\
    s_b.vs_inst_idx = LENGTH locked.cs_current_insts /\
    s_b.vs_gas_readings = s0.vs_gas_readings /\
    s_b.vs_code = s0.vs_code /\ s_b.vs_labels = s0.vs_labels /\
    (nr /\ mut <> View ==> ~cx.txn.is_static) /\
    !st0 H. valid_horizon cx st0 H es_lock.storage_trace ==>
      stmt_state_rel H unit.cu_context fn registered_env cx es_lock s_b /\
      ghost_inv H NONE registered_env cx es_lock G_b tn_b s_b` by
    (Cases_on `nr`
     >- (qpat_assum `T ==> cx.nonreentrant_slot = _ /\ _`
            (strip_assume_tac o REWRITE_RULE []) >>
         `compile_nonreentrant_lock global_nonreentrant_slot T (mut = View) registered =
           ((),locked)` by
           (qpat_assum `(if T then _ else _) registered = ((),locked)` mp_tac >>
            qpat_assum `key = global_nonreentrant_slot` (fn key =>
              qpat_assum `tr` (fn transient =>
                qpat_assum `view <=> mut = View` (fn view =>
                  simp[NoAsms, key, transient, view])))) >>
         mp_tac (Q.INST [`ctx` |-> `unit.cu_context`, `ss` |-> `start`,
           `cenv` |-> `registered_env`, `explicit` |-> `explicit`,
           `nkey` |-> `global_nonreentrant_slot`, `marks0` |-> `[]:bool list`,
           `s0` |-> `s0`, `G0` |-> `G2`, `tn0` |-> `tn2`,
           `func` |-> `fn`, `cx` |-> `cx`, `mut` |-> `mut`,
           `es0` |-> `es0`, `es_lock` |-> `es_lock`,
           `sa` |-> `registered`, `sl` |-> `locked`]
             (SPEC_ALL externalEntryJointTheory.selected_entry_after_lock)) >>
         simp_tac bool_ss [LENGTH, AND_CLAUSES] >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
         disch_then ACCEPT_TAC) >>
     `es_lock = es0` by
       (qpat_assum `lock_if_nr cx F _ es0 = (INL (),es_lock)` mp_tac >>
        simp[NoAsms, lock_if_nr_def, return_def]) >>
     `locked = registered` by
       (qpat_assum `(if F then _ else _) registered = ((),locked)` mp_tac >>
        simp[NoAsms, comp_return_def]) >>
     qpat_assum `es_lock = es0` SUBST1_TAC >>
     qpat_assum `locked = registered` SUBST1_TAC >>
     qexistsl_tac [`s0`,`G2`,`tn2`] >>
     simp_tac bool_ss [] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!H. stmt_state_rel H unit.cu_context fn registered_env cx es0 s0 /\ _`
       (qspec_then `H` ACCEPT_TAC)) >>
  rename1 `alloca_history fn s_b` >>
  rename1 `ptr_safe_run _ _ _ _ _ _ G_b tn_b s_b` >>
  drule_all_then (map_every assume_tac o CONJUNCTS) external_body_lock_frame >>
  `expr_sim_inv_mods mods registered_env cx entry_types es_lock` by
    (qpat_assum `expr_sim_inv_mods mods registered_env cx entry_types es0` mp_tac >>
     qpat_assum `es_lock.scopes = es0.scopes` (fn scopes =>
       qpat_assum `es_lock.immutables = es0.immutables` (fn immutables =>
       qpat_assum `es_lock.accounts = es0.accounts` (fn accounts =>
       qpat_assum `es_lock.outcomes = es0.outcomes` (fn outcomes =>
         PURE_REWRITE_TAC [expr_sim_inv_mods_def, state_well_typed_def, env_consistent_def,
           env_scopes_consistent_def, env_immutables_consistent_def,
           scopes, immutables, accounts, outcomes])))) >>
     disch_then ACCEPT_TAC) >>
  `body_const_cells_agree_mods mods cx entry_types es_lock` by
    (qpat_assum `es_lock.immutables = es0.immutables` (fn immutables =>
       qpat_assum `body_const_cells_agree_mods mods cx entry_types es0`
         (mp_tac o PURE_REWRITE_RULE [body_const_cells_agree_mods_def, const_cells_agree_def]) >>
       PURE_REWRITE_TAC [body_const_cells_agree_mods_def, const_cells_agree_def, immutables] >>
       disch_then ACCEPT_TAC));

val linked_registered_locked_horizon_tac =
  `!H. valid_horizon cx (initial_state am []) H es_lock.storage_trace ==>
     storage_well_formed_on cx es_lock (FST H)` by
    (gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [vyperStorageFootprintTheory.valid_horizon_def]) >>
     `storage_well_formed_on cx es0 (FST H)` by
       (MATCH_MP_TAC (Q.INST [`st` |->
          `initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>`,
          `mut` |-> `mut`, `res` |-> `INL ()`]
          (SPEC_ALL vyperExternalEntryStorageFrameTheory.send_call_value_preserves_storage_well_formed_on)) >>
        conj_tac
        >- (`storage_well_formed_on cx
                (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>)
                (FST H) <=> storage_well_formed_on cx (initial_state am []) (FST H)` by
              (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >> simp[NoAsms, initial_state_def]) >>
            pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
        qpat_assum `Abbrev (cx = _)`
          (PURE_ONCE_REWRITE_TAC o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        first_assum ACCEPT_TAC) >>
     mp_tac (Q.INST [`H` |-> `H`, `st` |-> `es0`, `u` |-> `es_lock`,
       `cx` |-> `cx`, `nr` |-> `nr`, `res` |-> `INL ()`, `view` |-> `is_view_mut mut`]
       (SPEC_ALL vyperExternalEntryStorageFrameTheory.lock_if_nr_preserves_storage_well_formed_on)) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_lock_success]:
  linked_registered_lock_success_tac >>
  linked_registered_locked_horizon_tac >>
  suspend "linked_linear_declared_locked_body"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_locked_body]:
  `ALL_DISTINCT (MAP FST mods)` by
    (qpat_assum `contract_namespaces_ok F mods`
       (strip_assume_tac o PURE_REWRITE_RULE [contract_namespaces_ok_def]) >>
     first_assum ACCEPT_TAC) >>
  `IS_SOME (type_stmts entry_types ret fbody)` by
    (qpat_assum `!fn. MEM (FunctionDecl External mut nr raw fn args [] ret fbody) tops ==> _`
       (qspec_then `tx.function_name` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (mp_tac o PURE_REWRITE_RULE [check_function_body_def, LET_THM]) >>
     simp[NoAsms, Abbr `entry_types`] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `stmts_no_control_escape fbody` by
    (qpat_assum `check_function_body am.layouts tx.target mods art src
         External mut nr args [] ret fbody`
       (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss
         [check_function_body_def, LET_THM]) >>
     first_assum ACCEPT_TAC) >>
  `ret <> NoneT ==> stmts_no_fallthrough fbody` by
    (disch_then (fn nonempty =>
       qpat_assum `check_function_body am.layouts tx.target mods art src
         External mut nr args [] ret fbody`
         (strip_assume_tac o SIMP_RULE (srw_ss())
           [check_function_body_def, LET_THM, nonempty])) >>
     first_assum ACCEPT_TAC) >>
  suspend "linked_linear_declared_replay_ready"
QED

val linked_registered_replay_tac =
  `!gs. eval_stmts cx body_code (es_lock with gas_obs := gs) =
         eval_stmts cx fbody (es_lock with gas_obs := gs)` by
    (qpat_assum `Abbrev (body_code = _)`
       (PURE_ONCE_REWRITE_TAC o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     MATCH_MP_TAC (Q.INST [`env` |-> `entry_types`, `ret` |-> `ret`]
       (SPEC_ALL bodySelectedLockedReplayModsTheory.selected_locked_replay_mods_with_offset)) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt gen_tac >> strip_tac >>
     irule (Q.INST_TYPE [`:'a` |-> `:160 word`]
       constSubstModsCorrectTheory.const_subst_blueprint_literal_offset_mods) >>
     conj_tac
     >- (qexistsl_tac [`cx.txn.target`, `art`, `F`, `cx.layouts`] >>
         first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_replay_ready]:
  linked_registered_replay_tac >>
  suspend "linked_linear_declared_guarded_frag"
QED

(* Install the linked external Return frame. Only the selected source
   lookup needs route-specific normalization. *)
fun linked_return_frame_tac retq ce cx ret source_lookup_tac =
  simp_tac bool_ss [Abbr retq] >>
  irule linkedExternalFrameRetTheory.linked_external_frame_ret_ok_full >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
    qpat_assum (`(` @ ce @ `).ce_type_env = type_env_all_modules mods`) SUBST1_TAC >>
      first_assum (ACCEPT_TAC o SYM),
    qpat_assum (`get_tenv (` @ cx @ `) = type_env_all_modules mods`) (ACCEPT_TAC o SYM),
    strip_tac >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
      qpat_assum (`(` @ ret @ `) <> NoneT`) (fn nonempty =>
        first_assum (ACCEPT_TAC o C MATCH_MP nonempty))],
    source_lookup_tac];

val linked_registered_return_layout_tac =
  `registered_env.ce_struct_fields = (base_env with ce_raw_return := raw).ce_struct_fields` by
    (qpat_assum `registered_env.ce_struct_fields = make_struct_fields_map_mods mods` SUBST1_TAC >>
     simp[NoAsms, Abbr `base_env`, build_compile_env_unit_def, pairTheory.ELIM_UNCURRY]) >>
  `ret <> NoneT ==>
    registered_env.ce_ret_enc_info = (update_cenv_ret_abi registered_env ret).ce_ret_enc_info /\
    registered_env.ce_max_return_size = (update_cenv_ret_abi registered_env ret).ce_max_return_size /\
    assignable_type (get_tenv cx) ret /\
    (registered_env.ce_raw_return ==> ?n. ret = BaseT (BytesT (Dynamic n))) /\
    type_memory_bytes registered_env ret < 2 ** 64` by
    (strip_tac >>
     `type_memory_bytes registered_env = type_memory_bytes (base_env with ce_raw_return := raw)` by
       (irule type_memory_bytes_frame >> first_assum ACCEPT_TAC) >>
     `type_to_abi_enc_info (base_env with ce_raw_return := raw).ce_struct_fields registered_env ret =
       type_to_abi_enc_info (base_env with ce_raw_return := raw).ce_struct_fields
         (base_env with ce_raw_return := raw) ret` by
       (irule linkedReturnAbiLayoutTheory.type_to_abi_enc_info_struct_fields >>
        first_assum ACCEPT_TAC) >>
     `registered_env.ce_ret_enc_info =
          (update_cenv_ret_abi (base_env with ce_raw_return := raw) ret).ce_ret_enc_info /\
       registered_env.ce_max_return_size =
          (update_cenv_ret_abi (base_env with ce_raw_return := raw) ret).ce_max_return_size` by
       (qpat_assum `registered_env = ce with ce_vars := registered_env.ce_vars`
          (PURE_ONCE_REWRITE_TAC o single) >>
        qpat_assum `ce = _` SUBST1_TAC >>
        qpat_assum `ret <> NoneT` (fn nonempty =>
          simp[NoAsms, nonempty, update_cenv_nonreentrant_def, update_cenv_ret_abi_def, LET_THM])) >>
     qpat_assum `registered_env.ce_ret_enc_info = _` SUBST1_TAC >>
     qpat_assum `registered_env.ce_max_return_size = _` SUBST1_TAC >>
     qpat_assum `registered_env.ce_raw_return = raw` (fn raw_eq =>
       qpat_assum `registered_env.ce_struct_fields = (base_env with ce_raw_return := raw).ce_struct_fields`
         (fn fields =>
           qpat_assum `type_memory_bytes registered_env = type_memory_bytes (base_env with ce_raw_return := raw)`
             (fn size =>
               qpat_assum `type_to_abi_enc_info _ registered_env ret = _` (fn plan =>
                 qpat_assum `type_memory_bytes registered_env ret < 2 ** 64` (fn limit =>
                   let
                     val plan = SIMP_RULE (srw_ss()) [] plan
                     val limit = SIMP_RULE (srw_ss()) [AP_THM size ``ret:type``] limit
                   in
                     simp[NoAsms, raw_eq, fields, size, plan, limit,
                          update_cenv_ret_abi_def, LET_THM]
                   end))))) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       qpat_assum `ret <> NoneT` (fn nonempty =>
         first_assum (ACCEPT_TAC o C MATCH_MP nonempty))]) >>
  qpat_assum `Abbrev (name = tx.function_name)` (fn name =>
    map_every (fn pattern => qpat_assum pattern
      (assume_tac o PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] name]))
      [`ALOOKUP mods (ALOOKUP exps name) = SOME tops`,
       `external_return_type_mods mods exps name = ret`]) >>
  `src = ALOOKUP exps tx.function_name` by simp[NoAsms, Abbr `src`, Abbr `name`] >>
  `ret = NoneT ==> tx_return_bytes_mods mods exps cx.txn NoneV []` by
    (strip_tac >>
     `~raw` by
       (qpat_assum `raw ==> ?n. ret = BaseT (BytesT (Dynamic n))` mp_tac >>
        qpat_assum `ret = NoneT` (fn none => simp[NoAsms, none])) >>
     qpat_assum `cx.txn = tx` SUBST1_TAC >>
     qpat_assum `ALOOKUP mods (ALOOKUP exps tx.function_name) = SOME tops` (fn selected =>
       qpat_assum `lookup_raw_return_or_F src tx.function_name External tops = raw` (fn raw_eq =>
         qpat_assum `src = ALOOKUP exps tx.function_name` (fn src_eq =>
           qpat_assum `external_return_type_mods mods exps tx.function_name = ret` (fn ret_eq =>
             qpat_assum `ret = NoneT` (fn none =>
               qpat_assum `~raw` (fn not_raw =>
                 simp[NoAsms, selected, raw_eq, ret_eq, none, not_raw, tx_return_bytes_mods_def,
                   return_bytes_mods_def, LET_THM,
                   GSYM src_eq])))))) );

val linked_registered_return_frame_tac =
  qabbrev_tac `RetQ = \(H:(bool # bytes32 # type_value) list # num list) v ee
      (gt:(string |-> num # num) # taint) r. ?tv v' us.
    evaluate_type (get_tenv cx) ret = SOME tv /\ safe_cast tv v = SOME v' /\
    unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),us) /\
    external_call_result_rel_mods H mods exps ret cx.txn
      (INL v', finalize_pending_deletions
        (abstract_machine_from_state cx.sources am.exports cx.layouts us),
       us.requests) r` >>
  `nr ==> is_view_mut mut = (mut = View)` by
    (strip_tac >>
     qpat_assum `nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot /\ _`
       (fn guard => qpat_assum `nr` (ACCEPT_TAC o CONJUNCT2 o MATCH_MP guard))) >>
  `nr /\ mut <> View ==> ~cx.txn.is_static /\
     cx.nonreentrant_slot = SOME global_nonreentrant_slot` by
    (strip_tac >> conj_tac
     >- (qpat_assum `nr /\ mut <> View ==> ~cx.txn.is_static` MATCH_MP_TAC >>
         conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot /\ _`
       (fn guard => qpat_assum `nr` (ACCEPT_TAC o CONJUNCT1 o MATCH_MP guard))) >>
  `frame_ret_ok_full_mods mods
       ((\H. cx_dead H cx),0,NONE,unit.cu_context,shadow_unit.cu_context,[],fn,shadow_fn)
       cx RetQ registered_env ret` by
    linked_return_frame_tac `RetQ` `registered_env` `cx` `ret`
      (FIRST [qpat_assum `cx.txn = tx` SUBST1_TAC >> first_assum ACCEPT_TAC,
        qpat_assum `cx.txn = tx` SUBST1_TAC >>
         qpat_assum `src = ALOOKUP exps tx.function_name` (fn src_eq =>
           PURE_REWRITE_TAC [GSYM src_eq]) >>
         qpat_assum `registered_env.ce_raw_return = raw` SUBST1_TAC >>
         qexists_tac `tops` >>
         conj_tac >- first_assum (ACCEPT_TAC o SYM) >>
         first_assum ACCEPT_TAC]);

val linked_registered_structs_tac =
  `EVERY (struct_args_unique o SND) mods` by
    (simp[NoAsms, EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
     rename1 `MEM (owner,ts) mods` >>
     irule typedCopyProducerTheory.distinct_type_keys_struct_args_unique >>
     `ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel owner) ts))` by
       drule_all_then ACCEPT_TAC contract_namespaces_ok_module_type_def_keys >>
     `!decls. FLAT (MAP (type_def_keys_toplevel (NONE:num option)) decls) =
         MAP (\(_,n). (NONE:num option,n)) (FLAT (MAP (type_def_keys_toplevel owner) decls)) /\
       EVERY (\(s,_). s = owner) (FLAT (MAP (type_def_keys_toplevel owner) decls))` by
       (POP_ASSUM_LIST (K ALL_TAC) >> Induct >> simp[] >>
        Cases_on `h` >> simp[type_def_keys_toplevel_def]) >>
     pop_assum (qspec_then `ts` strip_assume_tac) >>
     qpat_assum `FLAT (MAP (type_def_keys_toplevel NONE) ts) = MAP _ _` SUBST1_TAC >>
     irule ALL_DISTINCT_MAP_INJ >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     simp[NoAsms, FORALL_PROD] >>
     qpat_assum `EVERY _ (FLAT (MAP (type_def_keys_toplevel owner) ts))` mp_tac >>
     simp[NoAsms, EVERY_MEM, FORALL_PROD] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `exports_ok cx.layouts cx.txn.target mods exps` by
    (simp[NoAsms, Abbr `cx`, initial_evaluation_context_def] >> first_assum ACCEPT_TAC);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_guarded_frag]:
  linked_registered_return_layout_tac >>
  linked_registered_return_frame_tac >>
  linked_registered_structs_tac >>
  `qualified_stmts_decls_ok mods body_code` by
    drule_then ACCEPT_TAC (ASSUME
      ``MEM (FunctionDecl External mut nr raw tx.function_name args [] ret fbody) tops ==>
        qualified_stmts_decls_ok mods body_code``) >>
  suspend "linked_linear_declared_body_abi_targets"
QED

(* Select a premise by its predicate (or the left-hand head of an equation). *)
fun linked_premise_head t = fst (strip_comb (if is_eq t then lhs t else t));
fun linked_select_premise head =
  valOf o List.find (fn t => same_const (linked_premise_head t) head) o strip_conj;

(* Infer the linked source witnesses from the caller's support, typing,
   contract and selected-module facts, not from the order of the binders. *)
fun linked_body_fragment_tac source_facts =
  let fun supply pat = qpat_assum pat (fn th =>
        part_match_exists_tac (linked_select_premise (linked_premise_head (concl th)))
          (concl th))
  in
    irule bodySimFullMainTheory.body_stmts_sim_full_mods >>
    rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC,
      map_every supply source_facts >> rpt conj_tac >> first_assum ACCEPT_TAC]
  end;

val linked_registered_abi_targets_tac =
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) body_code ==>
            EXISTS (occurs_abi_decode_target target o SND) mods` by
    (gen_tac >> strip_tac >>
     `supported_stmts_expr_exists (expr_abi_decode_target_root target) fbody` by
       (qpat_assum `Abbrev (body_code = _)` (fn code =>
          qpat_assum `supported_stmts_expr_exists (expr_abi_decode_target_root target) body_code`
            (assume_tac o PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] code])) >>
        drule_all_then ACCEPT_TAC
          linkedSubstitutionAbiTargetsTheory.checked_linked_const_substitution_abi_decode_target) >>
     simp[NoAsms, EXISTS_MEM] >>
     qexists_tac `(src,tops)` >>
     simp_tac bool_ss [SND] >> conj_tac >- first_assum ACCEPT_TAC >>
     drule_all_then ACCEPT_TAC bodyAbiDecodeTargetTheory.lookup_function_abi_decode_target_occurs);

val linked_registered_fragment_tac =
  `stmts_exprs_ok registered_env body_code` by
    (MATCH_MP_TAC stmt_exprs_ok_from_traversal_bounds >>
     qpat_assum `registered_env.ce_modules = mods` (fn eq =>
       REWRITE_TAC [eq]) >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       drule_all_then ACCEPT_TAC (ASSUME
         ``!env_after. type_stmts entry_types ret body_code = SOME env_after ==>
           ~supported_stmts_expr_exists (\e. ~byte_widths_expr e) body_code``),
       strip_tac >> drule_all_then ACCEPT_TAC (ASSUME
         ``stmts_valued_return body_code /\ ~registered_env.ce_raw_return ==>
           return_buffer_ok registered_env``)]) >>
  `stmt_frag_full_mods
      ((\H. cx_dead H cx),0,NONE,unit.cu_context,shadow_unit.cu_context,[],fn,shadow_fn)
      cx NoLoop RetQ registered_env
      (stmts_env registered_env NoLoop ret body_code)
      (stmts_env (gas_shadow_env T registered_env) NoLoop ret (MAP gas_shadow_stmt body_code))
      (eval_stmts cx body_code) es_lock` by
    linked_body_fragment_tac
      [`supported_stmts tops bindings body_code`,
       `type_stmts entry_types ret body_code = SOME after_body`,
       `contract_inv mods exps unit.cu_context registered_env cx`,
       `module_body_inv mods src tops registered_env cx`];

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_body_abi_targets]:
  linked_registered_abi_targets_tac >>
  linked_registered_fragment_tac >>
  suspend "linked_linear_declared_body_shadow"
QED

val linked_registered_shadow_tac =
  `gas_shadow_state locked shadow_locked` by
    (qpat_assum `key = global_nonreentrant_slot` (fn key =>
       qpat_assum `tr` (fn tr => qpat_assum `view = (mut = View)` (fn view =>
         `gas_shadow_compiles
           (if nr then compile_nonreentrant_lock key tr view else comp_return ())
           (if nr then compile_nonreentrant_lock key tr view else comp_return ())` by
           (Cases_on `nr` >>
            simp[NoAsms, key, tr, view,
              gasShadowModuleOpsTheory.gas_shadow_compiles_nonreentrant_lock,
              gas_shadow_compiles_return])))) >>
     qpat_assum `gas_shadow_compiles _ _`
       (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`registered`,`shadow_registered`] mp_tac) >>
     qpat_assum `gas_shadow_state registered shadow_registered`
       (fn paired => qpat_assum `(if nr then _ else _) registered = ((),locked)`
         (fn locked => qpat_assum `(if nr then _ else _) shadow_registered = ((),shadow_locked)`
           (fn shadow => simp_tac bool_ss [paired, locked, shadow, FST, SND])))) >>
  `stmts_env (gas_shadow_env T registered_env) NoLoop ret (MAP gas_shadow_stmt body_code)
      shadow_locked = (gas_shadow_env T body_env,shadow_body_end) /\
    gas_shadow_state body_end shadow_body_end` by
    (`SND (stmts_env (gas_shadow_env T registered_env) NoLoop ret
            (MAP gas_shadow_stmt body_code) shadow_locked) = shadow_body_end` by
       (qpat_assum `compile_stmts (gas_shadow_env T registered_env) NoLoop _
           (MAP gas_shadow_stmt body_code) shadow_locked = ((),shadow_body_end)`
          (mp_tac o REWRITE_RULE [stmtSimPropsTheory.compile_stmts_env]) >>
        qpat_assum `rt = _` SUBST1_TAC >>
        Cases_on `ret = NoneT`
        >- (`~stmts_valued_return body_code` by
              (qpat_assum `ret = NoneT` (fn none =>
                 qpat_assum `type_stmts entry_types ret body_code = SOME after_body`
                   (mp_tac o PURE_REWRITE_RULE [none])) >>
               disch_then (ACCEPT_TAC o MATCH_MP externalCallSelectedTheory.type_stmts_none_valued_return)) >>
            qspecl_then [`MAP gas_shadow_stmt body_code`,`tops`,`bindings`,
              `gas_shadow_env T registered_env`,`NoLoop`,`NoneT`,`BaseT BoolT`] mp_tac
               stmtsEnvRetTyTheory.stmts_env_ret_ty_no_valued_return >>
            impl_tac
            >- (conj_tac
                >- (qpat_assum `supported_stmts tops bindings body_code`
                      (ACCEPT_TAC o MATCH_MP gasShadowStmtEnvTheory.gas_shadow_supported_stmts)) >>
                PURE_REWRITE_TAC [gasShadowStmtEnvTheory.gas_shadow_valued_return] >>
                first_assum ACCEPT_TAC) >>
            qpat_assum `ret = NoneT` (fn none => disch_then (fn state =>
              simp[NoAsms, state, none]))) >>
        qpat_assum `ret <> NoneT` (fn nonempty => simp[NoAsms, nonempty])) >>
     qspecl_then [`body_code`,`registered_env`,`NoLoop`,`ret`] mp_tac
       (Q.INST [`sd` |-> `T`] gasShadowStmtEnvTheory.gas_shadow_stmts_env_env) >>
     PURE_REWRITE_TAC [gas_shadow_compiles_env_def] >>
     disch_then (qspecl_then [`locked`,`shadow_locked`] mp_tac) >>
     qpat_assum `gas_shadow_state locked shadow_locked` (fn pair =>
       qpat_assum `stmts_env registered_env NoLoop ret body_code locked = (body_env,body_end)`
         (fn raw => qpat_assum `SND (stmts_env (gas_shadow_env T registered_env) NoLoop ret
               (MAP gas_shadow_stmt body_code) shadow_locked) = shadow_body_end`
           (fn shadow => simp_tac bool_ss [pair, raw, shadow, FST, SND]))) >>
     disch_then (CONJUNCTS_THEN2 (assume_tac o SYM) assume_tac) >>
     simp_tac bool_ss [pairTheory.PAIR_FST_SND_EQ,FST,SND] >>
     rpt conj_tac >> first_assum ACCEPT_TAC);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_body_shadow]:
  linked_registered_shadow_tac >>
  suspend "linked_linear_declared_body_execute"
QED

val linked_registered_admissible_tac =
  `gas_admissible (eval_stmts cx body_code) (stmt_res_ok NoLoop) es_lock` by
    (PURE_REWRITE_TAC [gasContextTheory.gas_admissible_def] >>
     qx_genl_tac [`gs`,`res`,`ee`] >> strip_tac >>
     `no_type_error_eval
        (eval_stmts cx body_code (es_lock with gas_obs := gs))` by
       (qpat_assum `expr_sim_inv_mods mods registered_env cx entry_types es_lock`
          (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [expr_sim_inv_mods_def]) >>
        MATCH_MP_TAC (Q.INST [`env` |-> `entry_types`,`env'` |-> `after_body`,`ret_ty` |-> `ret`]
             (SPEC_ALL vyperTypeStmtSoundnessTheory.eval_stmts_no_type_error)) >>
        simp_tac (srw_ss()) [NoAsms, gas_obs_type_invariants] >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     Cases_on `res` >- simp[NoAsms, stmtSimDefsTheory.stmt_res_ok_def] >>
     rename1 `eval_stmts _ _ _ = (INR exc,ee)` >>
     `exc <> BreakException /\ exc <> ContinueException` by
       (qpat_assum `!gas. eval_stmts cx body_code _ = eval_stmts cx fbody _`
          (qspec_then `gs` (fn replay =>
            qpat_assum `eval_stmts cx body_code _ = (INR exc,ee)`
              (assume_tac o PURE_REWRITE_RULE [replay]))) >>
        drule_all_then ACCEPT_TAC
          vyperTypeEvalProofsTheory.stmts_no_control_escape_eval_stmts_no_loop_control) >>
     qpat_assum `no_type_error_eval (eval_stmts cx body_code _)` mp_tac >>
     qpat_assum `eval_stmts cx body_code _ = (INR exc,ee)` (fn ev =>
       simp_tac bool_ss [ev, vyperTypeExprSoundnessTheory.no_type_error_eval_def,
         vyperTypeExprSoundnessTheory.no_type_error_result_def, FST]) >>
     qpat_assum `exc <> BreakException` mp_tac >>
     qpat_assum `exc <> ContinueException` mp_tac >>
     Cases_on `exc` >> simp[NoAsms, stmtSimDefsTheory.stmt_res_ok_def] >>
     rename1 `(!msg. err <> TypeError msg) ==> _` >>
     Cases_on `err` >> simp[NoAsms]);

val linked_registered_reachability_tac =
  `ctx_inst_ids_distinct unit.cu_context` by
    (drule lowering_context_ok_static_integrity >> strip_tac >> first_assum ACCEPT_TAC) >>
  `MEM fn unit.cu_context.ctx_functions /\
    MEM shadow_fn shadow_unit.cu_context.ctx_functions` by
    (conj_tac >> drule_then ACCEPT_TAC venomInstTheory.lookup_function_MEM) >>
  `!i. contextCodegenRel$active_inst fn i s_b ==> raw_reachable vs unit.cu_context fn i s_b` by
    (gen_tac >> strip_tac >>
     `gas_path unit.cu_context fn start 0 (OK s_b)` by
       (qpat_assum `gas_path_mem unit.cu_context fn start 0 (OK s_b)`
          (ACCEPT_TAC o CONJUNCT1 o MATCH_MP fragGasPathMemTheory.gas_path_mem_exec)) >>
     mp_tac (Q.INST [`ctx` |-> `unit.cu_context`,`n` |-> `0`,
       `s` |-> `start`,`w` |-> `s_b`,`inst` |-> `i`]
       callRejectMemoryTheory.raw_reachable_from_entry_path) >>
     impl_tac
     >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[Abbr `start`]]) >>
     disch_then ACCEPT_TAC) >>
  `!callee inst w. frag_reachable unit.cu_context fn s_b callee inst w ==>
    dalloca_fmp_headroom inst w` by
    (Cases_on `ctx_has_dalloca unit.cu_context`
     >- (rpt strip_tac >>
         qpat_assum `ctx_has_dalloca unit.cu_context ==>
            !fn inst s. raw_reachable vs _ fn inst s ==> _` (drule_then irule) >>
         qexists_tac `callee` >>
         drule_then (qspec_then `vs` irule) deployBodyReachabilityTheory.raw_reachable_through_fragment >>
         first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     qpat_assum `frag_reachable unit.cu_context fn s_b callee inst w`
       (fn reached => qpat_assum `MEM fn unit.cu_context.ctx_functions`
         (map_every assume_tac o CONJUNCTS o MATCH_MP (MATCH_MP
           contextRawReachableTheory.frag_reachable_members reached))) >>
     qpat_assum `~ctx_has_dalloca unit.cu_context` mp_tac >>
     simp[NoAsms, ctx_has_dalloca_def, EXISTS_MEM, unitTransformDefsTheory.dalloca_fmp_headroom_def] >>
     disch_then (qspec_then `callee` mp_tac) >>
     qpat_assum `MEM callee unit.cu_context.ctx_functions` (fn mem => simp[NoAsms, mem]) >>
     disch_then (qspec_then `inst` mp_tac) >>
     qpat_assum `MEM inst (fn_insts callee)` (fn mem => simp[NoAsms, mem]));

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_body_execute]:
  linked_registered_admissible_tac >>
  linked_registered_reachability_tac >>
  suspend "linked_linear_declared_body_frame"
QED

val linked_registered_immutable_frame_tac =
  `fn_inst_ids_distinct fn` by
    (drule_all ctx_inst_ids_distinct_fn >>
     simp[NoAsms, fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_map_id]) >>
  `s_b.vs_data_section = vs.vs_data_section` by
    (`gas_path unit.cu_context fn start 0 (OK s_b)` by
       (qpat_assum `gas_path_mem unit.cu_context fn start 0 (OK s_b)`
          (ACCEPT_TAC o CONJUNCT1 o MATCH_MP fragGasPathMemTheory.gas_path_mem_exec)) >>
     qpat_assum `gas_path unit.cu_context fn start 0 (OK s_b)`
       (mp_tac o MATCH_MP gasPathDataSectionTheory.gas_path_data_section) >>
     simp[NoAsms, Abbr `start`]) >>
  `immutable_frame_mods fn registered_env cx es_lock s_b` by
    (qpat_assum `~registered_env.ce_is_ctor` (fn runtime =>
       simp[NoAsms, runtime, immutable_frame_mods_def, immutables_rel_mods_def,
            immutable_alloca_sep_mods_def, immutable_alloca_sep_def, immutable_decl_sep_def]) >>
     rpt gen_tac >> strip_tac >>
     irule linked_section_runtime_relation >> qexists_tac `mods` >>
     qpat_assum `es_lock.immutables = es0.immutables` (fn locked_imms =>
       qpat_assum `es0.immutables = am.immutables` (fn imms =>
         qpat_assum `s_b.vs_data_section = vs.vs_data_section` (fn section =>
           simp[NoAsms, locked_imms, imms, section, Abbr `cx`, initial_evaluation_context_def,
                GSYM account_immutables_def]))) >>
     rpt conj_tac >> first_assum ACCEPT_TAC);

val linked_registered_storage_prefix_tac =
  `es0.storage_trace = []` by
    (qpat_assum `send_call_value mut (initial_evaluation_context am.sources am.layouts tx src)
         (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
         (INL (),es0)` (mp_tac o MATCH_MP (SPEC_ALL send_call_value_accounts)) >>
     simp[NoAsms, initial_state_def]) >>
  `es_lock.storage_trace = if nr then [StorageLock global_nonreentrant_slot] else []` by
    (Cases_on `nr`
     >- (qpat_assum `T ==> cx.nonreentrant_slot = _ /\ _`
           (map_every assume_tac o CONJUNCTS o REWRITE_RULE []) >>
         drule_all externalCallSelectedTheory.lock_if_nr_success_trace >>
         qpat_assum `es0.storage_trace = []` (fn empty => simp[NoAsms, empty])) >>
     qpat_assum `lock_if_nr cx F _ es0 = (INL (),es_lock)` mp_tac >>
     qpat_assum `es0.storage_trace = []` (fn empty =>
       simp[NoAsms, lock_if_nr_def, return_def] >> disch_then (SUBST1_TAC o SYM) >>
       simp[NoAsms, empty])) >>
  `storage_trace_domain cx (initial_state am []) es_lock.storage_trace` by
    (qpat_assum `es_lock.storage_trace = _` SUBST1_TAC >>
     Cases_on `nr` >>
     simp[NoAsms, vyperStorageFootprintTheory.storage_trace_domain_def,
       vyperStorageFootprintTheory.valid_horizon_def,
       vyperStorageFootprintTheory.storage_trace_horizon_def,
       vyperStorageFootprintTheory.storage_trace_regions_def,
       vyperStorageFootprintTheory.storage_trace_locks_def, regions_consistent_def,
       vyperStorageFootprintTheory.storage_locks_separated_def,
       vyperStorageFootprintTheory.storage_well_formed_on_def,
       vyperStorageFootprintTheory.storage_observations_ok_def,
       vyperStorageFootprintTheory.storage_roots_fit_def,
       vyperStorageFootprintTheory.storage_trace_backends_well_formed_def,
       arithmeticTheory.ADD1, contextTheory.global_nonreentrant_slot_def,
       wordsTheory.dimword_def]) >>
  `ctx_has_dalloca unit.cu_context ==> allocas_below_fmp s_b` by
    (qpat_assum `storage_trace_domain cx (initial_state am []) es_lock.storage_trace`
       (assume_tac o PURE_REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def]) >>
     qpat_assum `!st0 H. valid_horizon cx st0 H es_lock.storage_trace ==> _`
       (qspecl_then [`initial_state am []`,`storage_trace_horizon es_lock.storage_trace`]
         mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (CONJUNCTS_THEN2
       (MATCH_ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)
       kall_tac));

val linked_registered_run_tac =
  qpat_assum `stmt_frag_full_mods _ cx NoLoop RetQ registered_env _ _ _ es_lock`
    (mp_tac o REWRITE_RULE [stmt_frag_full_mods_def]) >>
  disch_then (qspecl_then [`initial_state am []`,`locked`,`body_end`,
    `shadow_locked`,`shadow_body_end`,`s_b`,`G_b`,`tn_b`,`body_env`] mp_tac) >>
  impl_tac
  >- (qpat_assum `~registered_env.ce_is_ctor` (fn runtime =>
       qpat_assum `registered_env.ce_return_pc = NONE` (fn retpc =>
         qpat_assum `registered_env.ce_return_buf = NONE` (fn retbuf =>
           simp_tac (srw_ss()) [NoAsms, runtime, retpc, retbuf,
             bodyFullShadowBodyInvTheory.dead_lo_ok_mods_def, dead_sub_def, loweringPostsTheory.ret_pc_ok_def,
             bodySimFullTheory.return_buf_sep_def]))) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      gen_tac >> strip_tac >>
      qpat_assum `!st0 H. valid_horizon cx st0 H es_lock.storage_trace ==> _`
         (drule_then (map_every assume_tac o CONJUNCTS)) >>
      qpat_assum `!H. valid_horizon cx (initial_state am []) H es_lock.storage_trace ==> _`
         (drule_then assume_tac) >>
      qpat_assum `ghost_inv H NONE registered_env cx es_lock G_b tn_b s_b`
         (mp_tac o PURE_REWRITE_RULE [ghost_inv_def]) >>
      simp_tac (srw_ss()) [NoAsms, bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def, ghost_inv_at_def] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      simp[NoAsms, ptrDisciplineTheory.allocas_from_def, GSYM stor_taint_ok_cx_dead] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `registered_env.ce_modules = mods` (fn linked =>
    qpat_assum `Abbrev (explicit = _)` (fn exp =>
      PURE_REWRITE_TAC [linked, GSYM (REWRITE_RULE [markerTheory.Abbrev_def] exp)])) >>
  disch_then assume_tac;

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_body_frame]:
  linked_registered_immutable_frame_tac >>
  linked_registered_storage_prefix_tac >>
  linked_registered_run_tac >>
  suspend "linked_linear_declared_body_compose"
QED

val linked_registered_trace_inputs_tac =
  `cx = initial_evaluation_context am.sources am.layouts tx src` by
    simp[NoAsms, Abbr `cx`] >>
  drule_all linkedRuntimeSourceLookupTheory.linked_runtime_source_lookup >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_exported_function cx am tx.function_name =
      SOME (mut,nr,args,[],ret,fbody)` by
    (qpat_assum `lookup_exported_function cx am tx.function_name = _` (fn exported =>
       qpat_assum `vyperInterpreter$lookup_function src tx.function_name External tops = _`
         (fn declared => simp[NoAsms, exported, declared]))) >>
  `LENGTH args = LENGTH tx.args` by
    drule_then ACCEPT_TAC vyperCallTheory.bind_arguments_length >>
  `!gobs. send_call_value mut cx
     (initial_state am [FEMPTY] with
       <|outcomes := SOME vs.vs_outcomes; requests := []; gas_obs := gobs; storage_trace := []|>) =
     (INL (),es0 with <|scopes := [FEMPTY]; gas_obs := gobs|>)` by
    (`send_call_value mut cx
        (initial_state am [FEMPTY] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
        (INL (),es0 with scopes := [FEMPTY])` by
       (qpat_assum `send_call_value mut (initial_evaluation_context am.sources am.layouts tx src)
          (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
          (INL (),es0)` (fn paid =>
          qpat_assum `cx = initial_evaluation_context am.sources am.layouts tx src` (fn cx =>
            mp_tac (MATCH_MP (SPEC_ALL externalEntryBoundTheory.send_call_value_with_scopes)
              (PURE_REWRITE_RULE [GSYM cx] paid)))) >>
        disch_then (qspec_then `[FEMPTY]` mp_tac o CONJUNCT2) >>
        simp[NoAsms, initial_state_def]) >>
     qpat_assum `send_call_value mut cx _ = (INL (),es0 with scopes := [FEMPTY])`
       (mp_tac o CONJUNCT2 o
        MATCH_MP (SPEC_ALL externalEntryBoundTheory.send_call_value_with_gas_obs)) >>
     simp[NoAsms, initial_state_def]) >>
  `!gobs. lock_if_nr cx nr (is_view_mut mut)
     ((es0 with <|scopes := [FEMPTY]; gas_obs := gobs|>) with scopes := [env]) =
     (INL (),es_lock with gas_obs := gobs)` by
    (gen_tac >>
     `((es0 with <|scopes := [FEMPTY]; gas_obs := gobs|>) with scopes := [env]) =
         es0 with gas_obs := gobs` by
       (qpat_assum `es0.scopes = [env]` (fn scopes =>
          simp[NoAsms, evaluation_state_component_equality, scopes])) >>
     pop_assum SUBST1_TAC >>
     qpat_assum `lock_if_nr cx nr (is_view_mut mut) es0 = (INL (),es_lock)`
       (MATCH_ACCEPT_TAC o MATCH_MP (SPEC_ALL externalCallSelectedTheory.lock_if_nr_with_gas_obs))) >>
  `!ee. ?eu. unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),eu)` by
    (gen_tac >> Cases_on `nr`
     >- (qpat_assum `T ==> cx.nonreentrant_slot = _ /\ _`
           (map_every assume_tac o CONJUNCTS o REWRITE_RULE []) >>
         mp_tac (Q.INST [`nr` |-> `T`, `iv` |-> `is_view_mut mut`, `es` |-> `ee`,
           `key` |-> `global_nonreentrant_slot`]
           (SPEC_ALL externalCallSelectedTheory.unlock_if_nr_success_trace)) >>
         impl_tac >- first_assum ACCEPT_TAC >>
         disch_then (qx_choose_then `eu` strip_assume_tac) >>
         qexists_tac `eu` >> first_assum ACCEPT_TAC) >>
     simp[NoAsms, unlock_if_nr_def, return_def]);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_body_compose]:
  linked_registered_trace_inputs_tac >>
  suspend "linked_linear_declared_compose_result"
QED

(* Match the body's outcome before specializing the remaining call boundary.
   Thus the caller proves the horizon transfers and all-tail replay for its
   selected entry, including any marks already consumed on the entry path. *)
fun linked_compose_result_tac {outcome, property, start, trace, relation, exempt, prefix} =
  qpat_assum outcome (fn body_outcome =>
    PART_MATCH
      (linked_select_premise ``gas_outcome_full_mods`` o fst o dest_imp)
      (Q.ISPEC property unitExecutionComposeResultTheory.unit_execution_compose_result_horizon_mods)
      (concl body_outcome) |>
    Q.GENL [`vs0`,`CT`,`REL`,`EX`,`marks0`] |>
    Q.ISPECL [start, trace, relation, exempt, prefix] |>
    BETA_RULE |> PURE_REWRITE_RULE [APPEND] |> mp_tac);

fun linked_registered_compose_tac {horizon_tac, tails_tac, exempt_tac,
    fallthrough_tac, exit_tac, readings_tac, finish_tac} =
  `!gobs. eval_external_defaults cx [] (es0 with
       <|scopes := [FEMPTY]; gas_obs := gobs|>) =
       (INL [],es0 with <|scopes := [FEMPTY]; gas_obs := gobs|>)` by
    simp[NoAsms, eval_external_defaults_def, return_def] >>
  linked_compose_result_tac
    {outcome = `gas_outcome_full_mods _ _ _ _ _ _ _ _`,
     property = `\(cr : value + exception).
       cr <> INR (Error (RuntimeError "msg.gas: no gas reading"))`,
     start = `start:venom_state`,
     trace = `\gs. call_external_trace (SOME vs.vs_outcomes) gs am tx`,
     relation = `\(H:(bool # bytes32 # type_value) list # num list) c r.
       external_call_result_rel_mods H mods exps ret tx c r`,
     exempt = `source_exempt_mods mods`, prefix = `[]:bool list`} >>
  impl_tac
  >- (conj_tac >- simp[NoAsms, vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac
      >- (gen_tac >> strip_tac >> BETA_TAC >>
          qpat_assum `!D. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) [] (OK s_b,G_b,tn_b)`
            (qspec_then `cx_dead H cx` (fn start_path =>
              qpat_assum `!D. (!fuel. ptr_safe_run _ _ _ _ _ _ G_b tn_b s_b) ==> _`
                (qspec_then `cx_dead H cx` (fn ptr => ACCEPT_TAC (CONJ start_path ptr)))))) >>
      conj_tac >- (BETA_TAC >>
        qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
          (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND] o BETA_RULE)) >>
      conj_tac
      >- horizon_tac >>
      conj_tac
      >- tails_tac >>
      conj_tac
      >- exempt_tac >>
      conj_tac
      >- fallthrough_tac >>
      conj_tac
      >- exit_tac >>
      readings_tac) >>
  finish_tac;

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_compose_result]:
  linked_registered_compose_tac
    {horizon_tac = suspend "linked_linear_trace_horizon",
     tails_tac = suspend "linked_linear_trace_gas_tail",
     exempt_tac = suspend "linked_linear_trace_exempt",
     fallthrough_tac = suspend "linked_linear_trace_fallthrough",
     exit_tac = suspend "linked_linear_trace_exit",
     readings_tac = suspend "linked_linear_trace_readings",
     finish_tac = suspend "linked_linear_body_compose_finish"}
QED

val linked_registered_trace_horizon_tac =
  qx_genl_tac [`gobs`,`res`,`ee`] >> BETA_TAC >> strip_tac >>
  qpat_assum `!gas. eval_stmts cx body_code _ = eval_stmts cx fbody _`
    (qspec_then `gobs` (fn replay =>
      qpat_assum `eval_stmts cx body_code _ = (res,ee)`
        (assume_tac o PURE_REWRITE_RULE [replay]))) >>
  qpat_assum `!ee. ?eu. unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),eu)`
    (qspec_then `ee` (qx_choose_then `eu` assume_tac)) >>
  linked_selected_trace_tac `gobs` `res` `ee` `eu` >>
  qpat_assum `call_external_trace _ gobs am tx = (_,_,_,call_obs)`
    (fn trace => PURE_REWRITE_TAC [trace, SND]) >>
  Cases_on `res = INL () \/ (?v. res = INR (ReturnException v))`
  >- (qpat_assum `_ ==> call_obs = eu.storage_trace` (fn out =>
        first_assum (SUBST1_TAC o MATCH_MP out)) >>
      reverse (Cases_on `nr`)
      >- (qpat_assum `unlock_if_nr cx F _ ee = (INL (),eu)` mp_tac >>
          simp[NoAsms, unlock_if_nr_def, return_def] >> disch_then SUBST1_TAC >>
          simp[NoAsms]) >>
      qpat_assum `T ==> cx.nonreentrant_slot = _ /\ _`
        (map_every assume_tac o CONJUNCTS o REWRITE_RULE []) >>
      mp_tac (Q.INST [`key` |-> `global_nonreentrant_slot`,
        `iv` |-> `is_view_mut mut`, `gs` |-> `gobs`, `st` |-> `initial_state am []`]
        (SPEC_ALL externalCallSelectedTheory.selected_unlock_trace_horizons)) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  qpat_assum `_ ==> call_obs = ee.storage_trace` (fn out =>
    first_assum (SUBST1_TAC o MATCH_MP out)) >>
  simp[NoAsms];

Resume linked_runtime_dispatched_readings_certificate[linked_linear_trace_horizon]:
  linked_registered_trace_horizon_tac
QED

val linked_registered_trace_exempt_tac =
  qx_genl_tac [`gx`,`err`,`ee`,`cr`,`am'`,`rqs`,`obs`] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `res = (INR (Error err) : unit + exception)` >>
  `!tail. eval_stmts cx body_code (es_lock with gas_obs := gx ++ tail) =
      (res,ee with gas_obs := tail)` by
    (simp[NoAsms, Abbr `res`] >> first_assum ACCEPT_TAC) >>
  linked_body_eval_tac >>
  linked_unlock_at_empty_gas_tac >>
  linked_selected_trace_tac `gx` `res` `ee with gas_obs := []` `eu` >>
  qpat_assum `call_external_trace _ gx am tx = (cr,am',rqs,obs)` (fn trace =>
    qpat_assum `call_external_trace _ gx am tx = (call_res,_,_,_)`
      (mp_tac o PURE_REWRITE_RULE [trace])) >>
  simp[NoAsms, source_exempt_mods_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!e. res = INR e /\ _ ==> call_res = _ /\ _`
    (qspec_then `Error err` mp_tac) >>
  simp[NoAsms, Abbr `res`] >> strip_tac >>
  qpat_assum `call_res = INR (Error err)` SUBST1_TAC >>
  simp[];

Resume linked_runtime_dispatched_readings_certificate[linked_linear_trace_exempt]:
  linked_registered_trace_exempt_tac
QED

val linked_registered_trace_tails_tac =
  qx_genl_tac [`gx`,`res`,`ee`] >> BETA_TAC >> strip_tac >>
  linked_body_eval_tac >>
  linked_unlock_at_empty_gas_tac >>
  linked_selected_trace_tac `gx` `res` `ee with gas_obs := []` `eu` >>
  qx_gen_tac `tail` >>
  `unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := tail) =
    (INL (),eu with gas_obs := tail)` by
    (qpat_assum `unlock_if_nr cx nr _ (ee with gas_obs := []) = _`
       (mp_tac o Q.INST [`obs` |-> `tail`] o
        MATCH_MP (SPEC_ALL externalCallSelectedTheory.unlock_if_nr_with_gas_obs)) >>
     simp[NoAsms]) >>
  qpat_assum `!tail. eval_stmts cx fbody _ = (res,ee with gas_obs := tail)`
    (qspec_then `tail` assume_tac) >>
  linked_selected_trace_as_tac [`tail_res`,`tail_am`,`tail_rqs`,`tail_obs`]
    `gx ++ tail` `res` `ee with gas_obs := tail` `eu with gas_obs := tail` >>
  qpat_assum `call_external_trace _ (gx ++ tail) am tx = (tail_res,_,_,_)` SUBST1_TAC >>
  qpat_assum `call_external_trace _ gx am tx = (call_res,_,_,_)` SUBST1_TAC >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`(res = INL () \/ (?v. res = INR (ReturnException v))) ==> call_obs = _`,
     `~(res = INL () \/ (?v. res = INR (ReturnException v))) ==> call_obs = _`,
     `res = INL () ==> call_res = _ /\ _`,
     `!v. res = INR (ReturnException v) ==> call_rqs = _ /\ _`,
     `res = INR HaltException ==> call_res = _ /\ _`,
     `!e. res = INR e /\ _ ==> call_res = _ /\ _`,
     `(res = INL () \/ (?v. res = INR (ReturnException v))) ==> tail_obs = _`,
     `~(res = INL () \/ (?v. res = INR (ReturnException v))) ==> tail_obs = _`,
     `res = INL () ==> tail_res = _ /\ _`,
     `!v. res = INR (ReturnException v) ==> tail_rqs = _ /\ _`,
     `res = INR HaltException ==> tail_res = _ /\ _`,
     `!e. res = INR e /\ _ ==> tail_res = _ /\ _`] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  namedCases_on `res` ["u","exc"]
  >- (Cases_on `u` >> simp[abstract_machine_from_state_def] >> strip_tac >> simp[]) >>
  Cases_on `exc` >> simp[abstract_machine_from_state_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[PAIR_EQ];

Resume linked_runtime_dispatched_readings_certificate[linked_linear_trace_gas_tail]:
  linked_registered_trace_tails_tac
QED

val linked_registered_trace_readings_tac =
  qx_genl_tac [`gx`,`res`,`ee`,`cr`,`am'`,`rqs`,`obs`] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  linked_body_eval_tac >>
  `res <> INR (Error (RuntimeError "msg.gas: no gas reading"))` by
    (disch_tac >>
     qpat_assum `!tail. eval_stmts cx fbody _ = (res,ee with gas_obs := tail)`
       (qspec_then `[0w:bytes32]` (fn result =>
         qpat_assum `res = INR (Error (RuntimeError "msg.gas: no gas reading"))`
           (fn missing =>
             mp_tac (MATCH_MP (cj 2 vyperEvalReadingErrorsTheory.evaluate_missing_reading_state)
               (PURE_REWRITE_RULE [missing] result))))) >>
     simp[NoAsms]) >>
  linked_unlock_at_empty_gas_tac >>
  linked_selected_trace_tac `gx` `res` `ee with gas_obs := []` `eu` >>
  qpat_assum `call_external_trace _ gx am tx = (cr,am',rqs,obs)` (fn trace =>
    qpat_assum `call_external_trace _ gx am tx = (call_res,_,_,_)`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [trace])) >>
  qpat_assum `cr = call_res` SUBST1_TAC >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`res <> INR (Error (RuntimeError "msg.gas: no gas reading"))`,
     `res = INL () ==> call_res = _ /\ _`,
     `!v. res = INR (ReturnException v) ==> _`,
     `res = INR HaltException ==> call_res = _ /\ _`,
     `!e. res = INR e /\ _ ==> call_res = _ /\ _`] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  namedCases_on `res` ["u","exc"]
  >- (Cases_on `u` >> simp[] >> rpt strip_tac >> simp[]) >>
  Cases_on `exc` >> simp[AllCaseEqs()] >> rpt strip_tac >> gvs[];

Resume linked_runtime_dispatched_readings_certificate[linked_linear_trace_readings]:
  linked_registered_trace_readings_tac
QED

fun linked_registered_trace_exit_tac abort_or_halt_tac =
  qx_genl_tac [`gx`,`res`,`ee`,`H`,`gt`,`r`,`cr`,`am'`,`rqs`,`obs`] >>
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  linked_body_eval_tac >>
  linked_unlock_at_empty_gas_tac >>
  linked_selected_trace_tac `gx` `res` `ee with gas_obs := []` `eu` >>
  qpat_assum `call_external_trace _ gx am tx = (cr,am',rqs,obs)` (fn trace =>
    qpat_assum `call_external_trace _ gx am tx = (call_res,_,_,_)`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [trace])) >>
  `cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn = tx` by
    simp[NoAsms, Abbr `cx`, initial_evaluation_context_def] >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!tail. stmt_exit_ptr (RetQ H) _ res gt r`
    (qspec_then `[]` mp_tac) >>
  PURE_REWRITE_TAC [stmt_exit_ptr_def] >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (qx_choose_then `v` (map_every assume_tac o CONJUNCTS)))
  >- abort_or_halt_tac >>
  qpat_assum `Abbrev (RetQ = _)` (fn retq =>
    qpat_assum `RetQ H _ _ _ _` (strip_assume_tac o
      SIMP_RULE (srw_ss()) [Excl "unlock_if_nr_def", Excl "is_view_mut_def"] o
      BETA_RULE o PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] retq])) >>
  `unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := []) = (INL (),eu)` by
    first_assum ACCEPT_TAC >>
  qpat_assum `unlock_if_nr cx nr _ (ee with gas_obs := []) = (INL (),eu)`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [Excl "unlock_if_nr_def"] o
      Q.INST [`sc` |-> `[]`] o
      MATCH_MP (SPEC_ALL externalCallSelectedTheory.unlock_if_nr_with_scopes)) >>
  `us = eu with scopes := []` by
    (qpat_assum `unlock_if_nr cx nr (is_view_mut mut) _ = (INL (),us)` mp_tac >>
     qpat_assum `unlock_if_nr cx nr (mut = View \/ mut = Pure) _ = (INL (),eu with scopes := [])`
       (fn step => simp[NoAsms, is_view_mut_def, step, Excl "unlock_if_nr_def"])) >>
  qpat_assum `res = INR (ReturnException v)` (fn returned =>
    qpat_assum `get_tenv cx = type_env_all_modules mods` (fn tenv =>
      qpat_assum `!v. res = INR (ReturnException v) ==> call_rqs = _ /\ _`
        (qspec_then `v` (strip_assume_tac o SIMP_RULE (srw_ss()) [GSYM tenv] o
          C MATCH_MP returned)))) >>
  qpat_assum `evaluate_type (get_tenv cx) ret = SOME tv` (fn ty =>
    qpat_assum `safe_cast tv v = SOME v'` (fn cast =>
      qpat_assum `(call_res,call_am) = _`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [ty, cast]))) >>
  qpat_x_assum `external_call_result_rel_mods H mods exps ret cx.txn _ r` mp_tac >>
  asm_simp_tac (srw_ss()) [abstract_machine_from_state_def];

Resume linked_runtime_dispatched_readings_certificate[linked_linear_trace_exit]:
  linked_registered_trace_exit_tac (suspend "linked_linear_trace_abort_or_halt")
QED

val linked_registered_abort_or_halt_tac =
  `stmt_res_ok NoLoop res` by
    (qpat_assum `gas_admissible (eval_stmts cx body_code) (stmt_res_ok NoLoop) es_lock`
       (mp_tac o PURE_REWRITE_RULE [gasContextTheory.gas_admissible_def]) >>
     disch_then (qspecl_then [`gx`,`res`,`ee with gas_obs := []`] mp_tac) >>
     qpat_assum `!tail. eval_stmts cx body_code _ = (res,ee with gas_obs := tail)`
       (qspec_then `[]` (fn eval =>
          assume_tac (PURE_REWRITE_RULE [APPEND_NIL] eval))) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then ACCEPT_TAC) >>
  qpat_assum `cr = call_res` SUBST1_TAC >>
  qpat_assum `am' = call_am` SUBST1_TAC >>
  qpat_assum `rqs = call_rqs` SUBST1_TAC >>
  Cases_on `res = INR HaltException`
  >- (qpat_assum `halt_exit H cx (ee with gas_obs := []) res r` mp_tac >>
      qpat_assum `res = INR HaltException` (fn ex =>
        simp[NoAsms, ex, exprSimDefsTheory.halt_exit_def]) >>
      disch_then (qx_choose_then `ss` strip_assume_tac) >>
      qpat_assum `r = Halt ss` SUBST_ALL_TAC >>
      qpat_assum `res = INR HaltException` (fn ex =>
        qpat_assum `expr_exit res (Halt ss)`
          (assume_tac o SIMP_RULE (srw_ss()) [exprSimDefsTheory.expr_exit_def, ex]) >>
        qpat_assum `res = INR HaltException ==> call_res = _ /\ _`
          (strip_assume_tac o C MATCH_MP ex)) >>
      mp_tac (Q.SPECL [`H`,`cx`,`ee with gas_obs := []`,`ss`,`[]`,`tx`,
          `am.sources`,`am.exports`,`am.layouts`]
        (INST_TYPE [alpha |-> ``:256``] loweringHaltTheory.external_halt_rel_success)) >>
      impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
        qpat_assum `cx.txn = tx` (fn txn => simp[NoAsms, txn])]) >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`ss.vs_returndata = []`, `call_res = INR HaltException`,
         `call_am = finalize_pending_deletions _`, `call_rqs = _`] >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[external_call_result_rel_mods_def, LET_THM, logs_correspond_def] >>
      rpt strip_tac >> simp[LET_THM] >>
      qpat_x_assum `LIST_REL (log_entry_corresponds _ _ _) _ _` mp_tac >>
      simp[LIST_REL_EL_EQN, log_entry_corresponds_concrete_event, LET_THM]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`expr_exit res r`, `stmt_res_ok NoLoop res`, `res <> INR HaltException`,
     `!e. res = INR e /\ _ ==> call_res = _ /\ _`] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `r` >>
  simp[exprSimDefsTheory.expr_exit_def, stmtSimDefsTheory.stmt_res_ok_def] >>
  rpt strip_tac >> gvs[exprSimDefsTheory.expr_exit_def] >>
  simp[external_call_result_rel_mods_def, LET_THM];

Resume linked_runtime_dispatched_readings_certificate[linked_linear_trace_abort_or_halt]:
  linked_registered_abort_or_halt_tac
QED

fun linked_registered_fallthrough_tac ghost_tac result_tac =
  qx_genl_tac [`gx`,`res`,`ee`,`t`] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `res = INL () /\ ~block_is_terminated body_end /\ ~t.vs_halted /\
    t.vs_current_bb = body_end.cs_current_bb /\
    t.vs_inst_idx = LENGTH body_end.cs_current_insts` by
    (qpat_assum `?H G tn. valid_horizon _ _ H _ /\
       ?ce'. stmt_lands NoLoop body_end res t /\ _`
       (qx_choosel_then [`H`,`G`,`tn`] (CONJUNCTS_THEN2 assume_tac
          (qx_choose_then `final_env` (map_every assume_tac o CONJUNCTS)))) >>
     qpat_assum `stmt_lands NoLoop body_end res t`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [loweringPostsTheory.stmt_lands_def]) >>
     qpat_assum `res = INL () ==> ~block_is_terminated body_end /\ _`
       (drule_then (assume_tac o CONJUNCT1)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  linked_body_eval_tac >>
  `ret = NoneT` by
    (CCONTR_TAC >>
     `stmts_no_fallthrough fbody` by
       (qpat_assum `ret <> NoneT ==> stmts_no_fallthrough fbody` drule >>
        disch_then ACCEPT_TAC) >>
     qpat_assum `stmts_no_fallthrough fbody` (fn nofall =>
       qspecl_then [`fbody`,`cx`,`es_lock with gas_obs := gx`,`ee with gas_obs := []`]
         (mp_tac o C MATCH_MP nofall)
         (cj 2 vyperTypeEvalProofsTheory.no_fallthrough_eval_no_success)) >>
     qpat_assum `res = INL ()` (fn success =>
       qpat_assum `eval_stmts cx fbody (es_lock with gas_obs := gx) = _`
         (fn eval => simp[NoAsms, eval, success]))) >>
  qpat_x_assum `ret = NoneT` SUBST_ALL_TAC >>
  `compile_guarded_body registered_env nr global_nonreentrant_slot T (mut = View)
       body_code NONE registered = ((),last) /\
    (if nr then compile_nonreentrant_lock global_nonreentrant_slot T (mut = View)
     else comp_return ()) registered = ((),locked) /\
    compile_stmts registered_env NoLoop (BaseT BoolT) body_code locked = ((),body_end)` by
    (qpat_assum `key = global_nonreentrant_slot` (fn key =>
       qpat_assum `view = (mut = View)` (fn view =>
         qpat_assum `tr` (fn tr =>
           qpat_assum `rt = _` (fn rt =>
             rpt conj_tac >> first_assum
               (ACCEPT_TAC o SIMP_RULE (srw_ss()) [key, view, tr, rt])))))) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`nkey` |-> `global_nonreentrant_slot`, `iv` |-> `mut = View`,
      `st` |-> `registered`, `sl` |-> `locked`, `se` |-> `body_end`,
      `sb` |-> `last`, `cenv` |-> `registered_env`, `stmts` |-> `body_code`]
      (SPEC_ALL nonreentrantExitTheory.compile_guarded_body_stop_unlock_parts)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `su` (map_every assume_tac o CONJUNCTS)) >>
  `fn_has_code body_end su fn /\ fn_has_code su last fn` by
    (drule_all_then ACCEPT_TAC fn_has_code_split) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `ss = halt_state ((if nr /\ mut <> View then
      tstore (n2w global_nonreentrant_slot) 0w t else t)
      with <|vs_inst_idx := LENGTH su.cs_current_insts; vs_returndata := []|>)` >>
  qexists_tac `Halt ss` >>
  simp_tac (srw_ss()) [NoAsms, exit_result_def] >>
  qx_genl_tac [`H`,`G`,`tn`] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `final_env` (map_every assume_tac o CONJUNCTS))) >>
  `allocas_from 0 t /\ (nr /\ mut <> View ==> ~t.vs_call_ctx.cc_static)` by
    (qpat_assum `stmt_state_rel H unit.cu_context fn final_env cx _ t` mp_tac >>
     qpat_assum `nr /\ mut <> View ==> ~cx.txn.is_static` (fn static =>
       simp_tac (srw_ss()) [NoAsms, ptrDisciplineTheory.allocas_from_def,
         stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def,
         loweringStateRelDefsTheory.call_ctx_rel_def, static]) >>
     rpt strip_tac >> gvs[]) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`iv` |-> `mut = View`, `nkey` |-> `global_nonreentrant_slot`,
      `st` |-> `body_end`, `sb` |-> `last`, `s` |-> `t`,
      `ctx` |-> `unit.cu_context`, `func` |-> `fn`, `lo` |-> `0`, `PG` |-> `[]`,
      `DF` |-> `\H. cx_dead H cx`, `cenv` |-> `final_env`]
      (INST_TYPE [alpha |-> ``:256``
        ] (SPEC_ALL nonreentrantExitTheory.optional_transient_unlock_stop_joint_at))) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`ss_out`,`tn_out`]
    (map_every assume_tac o CONJUNCTS)) >>
  `ss_out = ss` by
    (qpat_assum `ss_out = halt_state _` (fn out => simp[NoAsms, out, Abbr `ss`])) >>
  qpat_x_assum `ss_out = ss` SUBST_ALL_TAC >>
  qexistsl_tac [`G`,`tn_out`] >>
  conj_tac
  >- (qpat_assum `!H explicit. _ ==> gas_origin_ptr_path _ _ [] (Halt ss,G,tn_out)`
        (qspecl_then [`H`,`explicit`] mp_tac) >>
      BETA_TAC >> disch_then irule >>
      ghost_tac) >>
  result_tac;

Resume linked_runtime_dispatched_readings_certificate[linked_linear_trace_fallthrough]:
  linked_registered_fallthrough_tac
    (suspend "linked_linear_fallthrough_ghost")
    (suspend "linked_linear_fallthrough_result")
QED

val linked_registered_fallthrough_ghost_tac =
  `~final_env.ce_is_ctor` by
    (qpat_assum `cenv_top_ext registered_env final_env _`
       (mp_tac o MATCH_MP stmtFragPtrTheory.cenv_top_ext_is_ctor) >>
     qpat_assum `~registered_env.ce_is_ctor` (fn runtime => simp[NoAsms, runtime])) >>
  conj_tac >>
  FIRST [qmatch_goalsub_abbrev_tac `dead_lo_ok _ _ _ _ _` >>
    qpat_assum `~final_env.ce_is_ctor`
      (fn runtime => simp[NoAsms, dead_lo_ok_def, runtime]),
    qpat_assum `ghost_inv_at_mods (cx_dead H cx) 0 NONE final_env cx _ G tn t`
      (strip_assume_tac o PURE_REWRITE_RULE [bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >>
    first_assum ACCEPT_TAC];

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallthrough_ghost]:
  linked_registered_fallthrough_ghost_tac
QED

val linked_registered_fallthrough_result_tac =
  qx_genl_tac [`cr`,`am'`,`rqs`,`obs`] >> strip_tac >>
  linked_unlock_at_empty_gas_tac >>
  linked_selected_trace_ret_tac `NoneT` [`call_res`,`call_am`,`call_rqs`,`call_obs`]
    `gx` `res` `ee with gas_obs := []` `eu` >>
  qpat_assum `call_external_trace _ gx am tx = (cr,am',rqs,obs)` (fn trace =>
    qpat_assum `call_external_trace _ gx am tx = (call_res,_,_,_)`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [trace])) >>
  qpat_assum `res = INL () ==> call_res = _ /\ _`
    (fn success => qpat_assum `res = INL ()`
      (map_every assume_tac o CONJUNCTS o MATCH_MP success)) >>
  `cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn = tx` by
    simp[NoAsms, Abbr `cx`, initial_evaluation_context_def] >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  `unlock_if_nr cx nr (is_view_mut mut) =
    if nr /\ mut <> View then
      release_nonreentrant_lock cx.txn.target global_nonreentrant_slot
    else vyperState$return ()` by
    (Cases_on `nr`
     >- (qpat_assum `T ==> cx.nonreentrant_slot = _ /\ _`
           (map_every assume_tac o CONJUNCTS o REWRITE_RULE []) >>
         qpat_assum `cx.nonreentrant_slot = SOME global_nonreentrant_slot` (fn slot =>
           qpat_assum `is_view_mut mut = (mut = View)` (fn view =>
             simp[NoAsms, unlock_if_nr_def, slot, view, Excl "is_view_mut_def"]))) >>
     simp[NoAsms, unlock_if_nr_def]) >>
  qspecl_then [`H`,`fn`,`final_env`,`cx`,`ee with gas_obs := []`,`eu`,`t`,`ss`,
    `nr`,`global_nonreentrant_slot`,`mut = View`,`[]`,`tx`,`am.sources`,
    `am.exports`,`am.layouts`] mp_tac
    (INST_TYPE [alpha |-> ``:256``] loweringHaltTheory.external_halt_success_unlock) >>
  impl_tac
  >- (qpat_assum `stmt_state_rel H unit.cu_context fn final_env cx _ t`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [stmt_state_rel_def]) >>
      qpat_assum `unlock_if_nr cx nr (is_view_mut mut) = _` (fn norm =>
        qpat_assum `unlock_if_nr cx nr (is_view_mut mut) _ = (INL (),eu)`
          (assume_tac o PURE_REWRITE_RULE [norm])) >>
      rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
        qmatch_goalsub_rename_tac `state_rel H fn final_env cx _ t` >>
          PURE_REWRITE_TAC [loweringStateRelDefsTheory.state_rel_gas_obs] >>
          first_assum ACCEPT_TAC,
        qpat_assum `cx.txn = tx` (fn txn => simp[NoAsms, txn])]) >>
  qpat_assum `cx.txn = tx` (fn txn =>
    qpat_assum `NoneT = NoneT ==> tx_return_bytes_mods mods exps cx.txn NoneV []`
      (mp_tac o SIMP_RULE (srw_ss()) [txn])) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`ss.vs_returndata = []`, `external_return_type_mods mods exps tx.function_name = NoneT`,
     `cr = call_res`, `am' = call_am`, `rqs = call_rqs`,
     `call_res = INL NoneV`, `call_am = finalize_pending_deletions _`, `call_rqs = eu.requests`] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[external_call_result_rel_mods_def, tx_return_bytes_mods_def, LET_THM,
    logs_correspond_def, LIST_REL_EL_EQN, log_entry_corresponds_concrete_event] >>
  rpt strip_tac >> simp[LET_THM];

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallthrough_result]:
  linked_registered_fallthrough_result_tac
QED

val linked_registered_finish_tac =
  disch_then (qx_choose_then `body_marks` assume_tac) >>
  `s_b.vs_gas_readings = vs.vs_gas_readings` by
    (qpat_assum `s_b.vs_gas_readings = s0.vs_gas_readings` SUBST1_TAC >>
     qpat_assum `s0.vs_gas_readings = start.vs_gas_readings` SUBST1_TAC >>
     simp[NoAsms, Abbr `start`]) >>
  `!H obs. valid_horizon cx (initial_state am []) H obs <=>
    valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am []) H obs` by
    (qsuff_tac `cx.txn.target =
        (initial_evaluation_context am.sources am.layouts tx NONE).txn.target`
     >- (disch_then (fn target =>
           simp[NoAsms, valid_horizon_def,
             GEN_ALL (MATCH_MP vyperCallFiniteStorageSupportTheory.storage_well_formed_on_target target),
             GEN_ALL (MATCH_MP vyperCallFiniteStorageSupportTheory.storage_observations_ok_target target)])) >>
     simp[NoAsms, Abbr `cx`, initial_evaluation_context_def]) >>
  `!(H:(bool # bytes32 # type_value) list # num list). cx_dead H cx =
    cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE)` by
    simp[NoAsms, sourceUnitExecutionTheory.cx_dead_def, Abbr `cx`, initial_evaluation_context_def] >>
  `!obs. storage_trace_domain cx (initial_state am []) obs <=>
    storage_trace_domain
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am []) obs` by
    (PURE_REWRITE_TAC [storage_trace_domain_def] >> gen_tac >>
     qpat_assum `!H obs. valid_horizon cx (initial_state am []) H obs <=> _`
       (qspecl_then [`storage_trace_horizon obs`, `obs`] ACCEPT_TAC)) >>
  `!os gas. SND (SND (SND (call_external_trace (SOME os) gas am tx))) =
      source_storage_trace am tx os gas` by
    (rpt gen_tac >> Cases_on `call_external_trace (SOME os) gas am tx` >>
     PairCases_on `r` >> simp[NoAsms, source_storage_trace_def] >>
     first_assum (fn trace => simp[NoAsms, trace])) >>
  qexists_tac `body_marks` >>
  qpat_x_assum `_ \/ ?res am' rqs obs. _` mp_tac >>
  qpat_assum `s_b.vs_gas_readings = vs.vs_gas_readings` (fn readings =>
    qpat_assum `!os gas. SND (SND (SND (call_external_trace (SOME os) gas am tx))) = _`
      (fn observations => simp[NoAsms, readings, APPEND, observations])) >>
  disch_then (DISJ_CASES_THEN2 (map_every assume_tac o CONJUNCTS)
    (qx_choosel_then [`out`,`out_am`,`out_rqs`,`out_obs`]
      (map_every assume_tac o CONJUNCTS)))
  >- (`!tail. ~call_storage_ok am tx vs.vs_outcomes
          (gas_explicit body_marks vs.vs_gas_readings ++ tail)` by
        (qx_gen_tac `tail` >> disch_tac >>
         drule_then mp_tac sourceUnitExecutionTheory.source_storage_guards_domain >>
         qpat_assum `!obs. storage_trace_domain cx (initial_state am []) obs <=> _`
           (fn domain => PURE_REWRITE_TAC [GSYM domain]) >>
         qpat_assum `!tail. ~storage_trace_domain cx _ _`
           (qspec_then `tail` (fn bad => simp[NoAsms, bad]))) >>
      conj_tac
      >- (PURE_REWRITE_TAC [source_unit_execution_correct_with_mods_def] >>
          qexistsl_tac [`fn`,`shadow_fn`] >>
          rpt (conj_tac >- first_assum ACCEPT_TAC) >>
          disj1_tac >> conj_tac >- first_assum ACCEPT_TAC >>
          qpat_assum `!H. cx_dead H cx = _` (fn dead =>
            qpat_assum `Abbrev (start = _)` (fn start =>
              qpat_assum `Abbrev (explicit = _)` (fn sites =>
                PURE_REWRITE_TAC (GSYM dead :: map (GSYM o PURE_REWRITE_RULE
                  [markerTheory.Abbrev_def]) [start, sites])))) >>
          first_assum ACCEPT_TAC) >>
      disch_then (qx_choose_then `tail` assume_tac) >>
      qpat_assum `!tail. ~call_storage_ok _ _ _ _`
        (qspec_then `tail` (fn bad => first_assum (CONTR_TAC o MATCH_MP (NOT_ELIM bad))))) >>
  conj_tac
  >- (PURE_REWRITE_TAC [source_unit_execution_correct_with_mods_def] >>
      qexistsl_tac [`fn`,`shadow_fn`] >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      disj2_tac >> qexistsl_tac [`out`,`out_am`,`out_rqs`,`out_obs`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `!H obs. valid_horizon cx (initial_state am []) H obs <=> _` (fn horizon =>
        qpat_assum `!obs. storage_trace_domain cx (initial_state am []) obs <=> _` (fn domain =>
          qpat_assum `!H. cx_dead H cx = _` (fn dead =>
            qpat_assum `Abbrev (start = _)` (fn start =>
              qpat_assum `Abbrev (explicit = _)` (fn sites =>
                PURE_REWRITE_TAC (map GSYM [horizon,domain,dead] @
                  map (GSYM o PURE_REWRITE_RULE
                    [markerTheory.Abbrev_def]) [start, sites])))))) >>
      first_assum ACCEPT_TAC) >>
  disch_tac >> qx_gen_tac `tail` >>
  qpat_assum `!tail. call_external_trace (SOME vs.vs_outcomes) _ am tx =
    (out,out_am,out_rqs,out_obs)`
    (qspec_then `tail` (strip_assume_tac o MATCH_MP call_external_trace_result)) >>
  qpat_assum `call_external _ _ _ _ = (out,out_am,out_rqs)`
    (fn call => simp[NoAsms, call]) >>
  first_assum ACCEPT_TAC;

Resume linked_runtime_dispatched_readings_certificate[linked_linear_body_compose_finish]:
  linked_registered_finish_tac
QED

val linked_registered_lock_abort_tac =
  rename1 `lock_if_nr cx nr (is_view_mut mut) es0 = (INR lock_err,es_lock)` >>
  `nr = T` by
    (Cases_on `nr` >> simp[NoAsms] >>
     qpat_assum `lock_if_nr cx F _ es0 = (INR lock_err,es_lock)` mp_tac >>
     simp[NoAsms, lock_if_nr_def, return_def]) >>
  qpat_x_assum `nr = T` SUBST_ALL_TAC >>
  qpat_assum `T ==> cx.nonreentrant_slot = _ /\ _`
    (strip_assume_tac o REWRITE_RULE []) >>
  `compile_guarded_body registered_env T global_nonreentrant_slot T (mut = View)
       body_code rt registered = ((),last)` by
    (qpat_assum `compile_guarded_body registered_env T key tr view body_code rt registered = _`
       mp_tac >>
     qpat_assum `key = global_nonreentrant_slot` (fn key =>
       qpat_assum `tr` (fn transient =>
         qpat_assum `view <=> mut = View` (fn view =>
           simp[NoAsms, key, transient, view])))) >>
  mp_tac (Q.INST [`ctx` |-> `unit.cu_context`, `cx` |-> `cx`,
    `ss` |-> `start`, `func` |-> `fn`, `cenv` |-> `registered_env`,
    `fbody` |-> `body_code`, `rt` |-> `rt`, `sa` |-> `registered`,
    `st'` |-> `last`, `es0` |-> `es0`, `es_abort` |-> `es_lock`,
    `exc` |-> `lock_err`, `mut` |-> `mut`,
    `explicit` |-> `explicit`, `marks0` |-> `[]:bool list`,
    `s0` |-> `s0`, `G0` |-> `G2`, `tn0` |-> `tn2`]
      (SPEC_ALL externalEntryJointTheory.external_entry_abort_from_registration)) >>
  simp_tac bool_ss [LENGTH, DROP_0] >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`abort`,`s_abort`,`G_abort`,`tn_abort`]
    (map_every assume_tac o CONJUNCTS));

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_lock_abort]:
  linked_registered_lock_abort_tac >>
  suspend "linked_linear_declared_lock_abort_source"
QED

val linked_registered_lock_abort_source_tac =
  `cx.txn.target = tx.target /\ ~cx.in_deploy` by
    simp[NoAsms, Abbr `cx`, initial_evaluation_context_def] >>
  `find_function_module am tx.target tx.function_name = src /\
    lookup_exported_function cx am tx.function_name =
      SOME (mut,T,args,[],ret,fbody)` by
    (`cx = initial_evaluation_context am.sources am.layouts tx src` by
       simp[NoAsms, Abbr `cx`] >>
     drule_all linkedRuntimeSourceLookupTheory.linked_runtime_source_lookup >>
     qpat_assum `vyperInterpreter$lookup_function src tx.function_name External tops = _`
       (fn lookup => simp[NoAsms, lookup])) >>
  `LENGTH args = LENGTH tx.args` by
    drule_then ACCEPT_TAC vyperCallTheory.bind_arguments_length >>
  `send_call_value mut cx
      (initial_state am [FEMPTY] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
      (INL (),es0 with scopes := [FEMPTY])` by
    (qpat_assum `send_call_value mut (initial_evaluation_context am.sources am.layouts tx src)
        (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
        (INL (),es0)` (fn paid =>
       qpat_assum `Abbrev (cx = _)` (fn cx =>
         mp_tac (MATCH_MP (SPEC_ALL externalEntryBoundTheory.send_call_value_with_scopes)
           (PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] cx)] paid)))) >>
     disch_then (qspec_then `[FEMPTY]` mp_tac o CONJUNCT2) >>
     simp[NoAsms, initial_state_def]) >>
  `!tail. call_external_function_trace (SOME vs.vs_outcomes) tail am cx
      T mut tops mods args [] tx.args fbody ret =
      (INR lock_err,am,es_lock.requests,es_lock.storage_trace)` by
    (gen_tac >>
     qpat_assum `send_call_value mut cx _ = (INL (),es0 with scopes := [FEMPTY])`
       (qspec_then `tail` assume_tac o CONJUNCT2 o
        MATCH_MP (SPEC_ALL externalEntryBoundTheory.send_call_value_with_gas_obs)) >>
     qpat_assum `lock_if_nr cx T (is_view_mut mut) es0 = (INR lock_err,es_lock)`
       (assume_tac o Q.INST [`obs` |-> `tail`] o
        MATCH_MP (SPEC_ALL externalCallSelectedTheory.lock_if_nr_with_gas_obs)) >>
     `initial_state am [FEMPTY] with
        <|outcomes := SOME vs.vs_outcomes; requests := []; gas_obs := tail;
          storage_trace := []|> =
       (initial_state am [FEMPTY] with <|outcomes := SOME vs.vs_outcomes; requests := []|>)
         with gas_obs := tail` by
       simp[NoAsms, initial_state_def] >>
     `set_scopes [env] ((es0 with scopes := [FEMPTY]) with gas_obs := tail) =
       (INL (),es0 with gas_obs := tail)` by
       (qpat_assum `es0.scopes = [env]` (fn scopes =>
          simp[NoAsms, scopes, vyperStateTheory.set_scopes_def,
                vyperStateTheory.return_def, evaluation_state_component_equality])) >>
     qpat_assum `~cx.in_deploy` (fn not_deploy =>
       qpat_assum `LENGTH args = LENGTH tx.args` (fn argc =>
         qpat_assum `bind_arguments (type_env_all_modules mods) args tx.args = SOME env`
           (fn bound =>
             simp_tac (srw_ss()) [NoAsms, call_external_function_trace_def, LET_THM,
               not_deploy, argc, bound, vyperStateTheory.ignore_bind_def,
               vyperStateTheory.bind_def, vyperStateTheory.return_def,
               Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"]))) >>
     qpat_assum `initial_state am [FEMPTY] with <|outcomes := _; requests := [];
         gas_obs := tail; storage_trace := []|> = _` (fn init =>
       qpat_assum `send_call_value mut cx (_ with gas_obs := tail) = _` (fn paid =>
         qpat_assum `set_scopes [env] _ = (INL (),es0 with gas_obs := tail)` (fn scopes =>
           qpat_assum `lock_if_nr cx T (is_view_mut mut) (es0 with gas_obs := tail) = _`
             (fn locked => PURE_REWRITE_TAC [init, paid] >>
               simp[NoAsms, scopes, locked, Excl "lock_if_nr_def",
                 Excl "unlock_if_nr_def", Excl "is_view_mut_def"])))) >>
     qpat_assum `lock_err = _ \/ lock_err = _` (DISJ_CASES_THEN SUBST1_TAC) >>
     simp[NoAsms, Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"]) >>
  `!tail. call_external_trace (SOME vs.vs_outcomes) tail am tx =
    (INR lock_err,am,es_lock.requests,es_lock.storage_trace)` by
    (gen_tac >>
     qpat_assum `find_function_module am tx.target tx.function_name = src` (fn find_src =>
       qpat_assum `Abbrev (cx = _)` (fn cx =>
          PURE_REWRITE_TAC [call_external_trace_def, LET_THM, find_src,
            GSYM (REWRITE_RULE [markerTheory.Abbrev_def] cx)])) >>
     `(case src of NONE => get_self_code cx
                  | SOME src_id => get_module_code cx (SOME src_id)) = SOME tops` by
       (Cases_on `src` >> simp_tac (srw_ss()) [get_self_code_def] >>
        first_assum ACCEPT_TAC) >>
     CONV_TAC (DEPTH_CONV BETA_CONV) >>
     qpat_assum `Abbrev (cx = _)` (fn cx =>
       PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] cx)]) >>
     qpat_assum `ALOOKUP am.sources tx.target = SOME mods` (fn mods_eq =>
       qpat_assum `(case src of NONE => get_self_code cx | SOME i => _) = SOME tops`
         (fn tops_eq =>
           qpat_assum `lookup_exported_function cx am tx.function_name = _` (fn lookup =>
             qpat_assum `!tail. call_external_function_trace _ tail am cx _ _ _ _ _ _ _ _ _ = _`
               (qspec_then `tail` (fn trace => simp[NoAsms, mods_eq, tops_eq, lookup, trace]))))) >>
     qpat_assum `lock_err = _ \/ lock_err = _` (DISJ_CASES_THEN SUBST1_TAC) >>
     simp[NoAsms]);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_lock_abort_source]:
  linked_registered_lock_abort_source_tac >>
  suspend "linked_linear_declared_lock_abort_certificate"
QED

(* Terminal paths determine the erased execution and safety at every fuel. *)
fun linked_terminal_abort_path_tac marks result =
  `gas_origin_path T explicit unit.cu_context fn start ^marks ^result` by
    (qpat_assum `!D. gas_origin_ptr_path _ (start,_,_) ^marks (^result,_,_)`
      (qspec_then `ARB` (ACCEPT_TAC o CONJUNCT1 o
        MATCH_MP (SPEC_ALL gas_origin_ptr_path_projections)))) >>
  `!D fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn [] FEMPTY entry_taint start` by
    (rpt gen_tac >> irule entryDispatchPtrTheory.ptr_safe_blocks_from_phi_free_run >>
     (reverse conj_tac >-
       (simp[NoAsms, Abbr `start`] >> qexists_tac `entry_bb` >>
        conj_tac >> first_assum ACCEPT_TAC)) >>
     qpat_assum `!D. gas_origin_ptr_path _ (start,_,_) ^marks (^result,_,_)`
       (qspec_then `D` (mp_tac o MATCH_MP fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec)) >>
     simp[NoAsms, exit_result_def] >>
     disch_then (qx_choose_then `run_fuel` strip_assume_tac) >>
     irule fragExecPtrTheory.ptr_safe_run_all_fuel >> qexists_tac `run_fuel` >>
     qpat_assum `run_from run_fuel _ _ start = ^result` (fn ran => simp[NoAsms, ran]) >>
     first_assum ACCEPT_TAC);

(* Package a terminal path and an exact source trace in the matched-result case. *)
fun linked_terminal_execution_tac shadow result trace_witnesses result_rel_tac =
  rewrite_tac [source_unit_execution_correct_with_mods_def] >>
  qexistsl_tac [`fn`,shadow] >>
  qpat_assum `lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn`
    (assume_tac o MATCH_MP lookup_function_MEM) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  disj2_tac >> qexistsl_tac trace_witnesses >>
  simp[NoAsms] >> (conj_tac >- first_assum ACCEPT_TAC) >>
  disj2_tac >> qexists_tac result >>
  qpat_assum `Abbrev (start = _)` (fn start =>
    qpat_assum `Abbrev (explicit = _)` (fn sites =>
      PURE_REWRITE_TAC (map (GSYM o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) [start, sites]))) >>
  simp[NoAsms, exit_result_def] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_tac >> (conj_tac >- result_rel_tac) >>
  first_assum (fn th => MATCH_ACCEPT_TAC (SPEC_ALL th));

val linked_registered_lock_abort_domain_tac =
  `es0.storage_trace = []` by
    (qpat_assum `send_call_value mut (initial_evaluation_context am.sources am.layouts tx src)
       _ = (INL (),es0)` (mp_tac o MATCH_MP (SPEC_ALL send_call_value_accounts)) >>
     simp[NoAsms, initial_state_def]) >>
  `es_lock.storage_trace = [StorageLock global_nonreentrant_slot]` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`lock_if_nr cx T (is_view_mut mut) es0 = _`,
        `cx.nonreentrant_slot = SOME global_nonreentrant_slot`, `es0.storage_trace = []`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     qpat_x_assum `lock_if_nr _ _ _ _ = _` mp_tac >>
     simp[lock_if_nr_def, vyperTypeEvalStoragePreservationTheory.acquire_nonreentrant_lock_eq] >>
     Cases_on `lookup_storage (n2w global_nonreentrant_slot)
       (lookup_transient_storage cx.txn.target es0.tStorage) = 1w` >>
     Cases_on `is_view_mut mut` >> Cases_on `cx.txn.is_static` >>
     simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperTypeEvalStoragePreservationTheory.acquire_nonreentrant_lock_eq,
       vyperStateTheory.return_def, vyperStateTheory.check_not_static_def,
       vyperStateTheory.check_def, vyperStateTheory.assert_def, vyperStateTheory.raise_def] >>
     strip_tac >> gvs[vyperStateTheory.assert_def, vyperStateTheory.raise_def]) >>
  `storage_trace_domain (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am []) es_lock.storage_trace` by
    (qpat_assum `es_lock.storage_trace = _` SUBST1_TAC >>
     simp[NoAsms, storage_trace_domain_def, valid_horizon_def, storage_trace_horizon_def,
       storage_trace_regions_def, storage_trace_locks_def, regions_consistent_def,
       storage_locks_separated_def, storage_well_formed_on_def, storage_observations_ok_def,
       storage_roots_fit_def, storage_trace_backends_well_formed_def, arithmeticTheory.ADD1] >>
     qpat_assum `global_nonreentrant_slot < dimword (:256)` mp_tac >> decide_tac);

val linked_registered_lock_abort_finish_tac =
  linked_terminal_abort_path_tac ``[]:bool list`` ``Abort abort s_abort`` >>
  qexists_tac `[]` >> reverse conj_tac
  >- (disch_tac >> qx_gen_tac `tail` >>
      qpat_assum `!tail. call_external_trace _ tail am tx = (INR lock_err,_,_,_)`
        (qspec_then `tail` (fn trace =>
          simp[NoAsms, CONJUNCT1 (MATCH_MP call_external_trace_result trace)])) >>
      qpat_assum `lock_err = _ \/ lock_err = _` (DISJ_CASES_THEN SUBST1_TAC) >>
      simp[NoAsms]) >>
  linked_terminal_execution_tac `shadow_fn` `Abort abort s_abort`
    [`INR lock_err`,`am`,`es_lock.requests`,`es_lock.storage_trace`]
    (qpat_assum `lock_err = _ \/ lock_err = _` (DISJ_CASES_THEN SUBST1_TAC) >>
     simp[NoAsms, external_call_result_rel_mods_def, LET_THM]);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_declared_lock_abort_certificate]:
  linked_registered_lock_abort_domain_tac >>
  linked_registered_lock_abort_finish_tac
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_getter_support]:
  `?env_after. type_stmts entry_types ret fbody = SOME env_after` by
    (drule_all checked_public_getter_body_typing_package >>
     simp[NoAsms, Abbr `entry_types`] >>
     disch_then (ACCEPT_TAC o cj 2)) >>
  `?e. fbody = [Return (SOME e)]` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`external_getter_tuple src top = SOME _`,`is_public_getter_decl tx.function_name top`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `top` >> simp[external_getter_tuple_def, is_public_getter_decl_def] >>
     Cases_on `v` >> simp[external_getter_tuple_def, is_public_getter_decl_def,
       getter_def, AllCaseEqs()] >>
     rpt (pairarg_tac >> gvs[]) >>
     rpt strip_tac >> gvs[]) >>
  rename1 `fbody = [Return (SOME getter_value)]` >>
  `body_code = [Return (SOME
      (subst_consts_expr_mods (consts_env_mods mods) getter_value))]` by
    (qpat_assum `fbody = [Return (SOME getter_value)]` (fn body =>
       simp[NoAsms, Abbr `body_code`, body,
            subst_consts_stmt_mods_def, subst_consts_expr_mods_def])) >>
  suspend "linked_linear_getter_value"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_getter_value]:
  `(?after_body. type_stmts entry_types ret body_code = SOME after_body) /\
   IS_SOME (type_stmts entry_types ret fbody) /\
   ret <> NoneT /\
   stmts_no_control_escape fbody /\
   qualified_stmts_decls_ok mods body_code /\
   (raw ==> ?n. ret = BaseT (BytesT (Dynamic n))) /\
   (nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot /\
           is_view_mut mut = (mut = View)) /\
   (ret <> NoneT ==> assignable_type (get_tenv cx) ret) /\
   ~supported_stmts_expr_exists (unallocated_bare_global_root registered_env entry_types) body_code /\
   (!key. MEM (WriteAcc (StateRef key)) (accesses_stmts body_code) /\
          IS_SOME (FLOOKUP entry_types.bare_global_assignable key) ==>
          IS_SOME (FLOOKUP registered_env.ce_module_vars key)) /\
   supported_stmts tops
     (args ++ supported_stmts_bindings T body_code ++ supported_stmts_bindings F body_code) body_code`
    suffices_by
    (disch_then (CONJUNCTS_THEN2 (qx_choose_then `after_body` assume_tac)
        (map_every assume_tac o CONJUNCTS)) >>
     suspend "linked_linear_getter_registered") >>
  Cases_on `ALOOKUP (consts_env_mods mods) (src,tx.function_name)`
  >- suspend "linked_linear_getter_no_replacement" >>
  rename1 `ALOOKUP (consts_env_mods mods) (src,tx.function_name) = SOME replacement` >>
  `well_typed_expr (artifact_env art mods src) replacement` by
    (drule_all checked_linked_constant_replacements_typed >>
     disch_then (qspec_then `src` ACCEPT_TAC)) >>
  drule_all checked_linked_constant_replacement_value >>
  disch_then (qx_choosel_then [`owner_tops`,`const_visibility`,`initializer`,
    `const_ty`,`slot`,`const_tv`,`const_value`]
      (map_every assume_tac o CONJUNCTS)) >>
  `owner_tops = tops` by
    (qpat_assum `ALOOKUP mods src = SOME tops` (fn owner =>
       qpat_assum `ALOOKUP mods src = SOME owner_tops`
         (ACCEPT_TAC o SYM o REWRITE_RULE [owner,optionTheory.SOME_11]))) >>
  qpat_x_assum `owner_tops = tops` SUBST_ALL_TAC >>
  `top = VariableDecl const_visibility (Constant initializer) tx.function_name const_ty slot` by
    (`ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) tops))` by
       (qpat_assum `ALOOKUP mods src = SOME tops`
          (assume_tac o MATCH_MP ALOOKUP_MEM) >>
        drule_then assume_tac check_contract_runtime_namespaces >>
        drule_all_then ACCEPT_TAC contract_namespaces_ok_module_toplevel_vtype_keys) >>
     qpat_assum `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) tops))`
       (mp_then Any mp_tac all_distinct_flat_map_unique) >>
     disch_then irule >>
     conj_tac
     >- (qexists_tac `(src,tx.function_name)` >>
         simp[NoAsms, toplevel_vtype_keys_toplevel_def] >>
         qpat_assum `is_public_getter_decl tx.function_name top` mp_tac >>
         Cases_on `top` >>
         simp[NoAsms, is_public_getter_decl_def, toplevel_vtype_keys_toplevel_def] >>
         Cases_on `v` >>
         simp[NoAsms, is_public_getter_decl_def, toplevel_vtype_keys_toplevel_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  Q.SUBGOAL_THEN `?vis. const_visibility = Public vis`
    (qx_choose_then `getter_guard` SUBST_ALL_TAC)
  >- (qpat_assum `top = VariableDecl _ _ _ _ _` (fn decl =>
      qpat_assum `is_public_getter_decl tx.function_name top`
        (mp_tac o REWRITE_RULE [decl])) >>
     Cases_on `const_visibility` >> simp[NoAsms, is_public_getter_decl_def]) >>
  `well_typed_expr entry_types replacement` by
    (qpat_assum `Abbrev (entry_types = _)` (fn env_def =>
       simp_tac bool_ss [REWRITE_RULE [markerTheory.Abbrev_def] env_def]) >>
     MATCH_MP_TAC constant_expr_function_entry_typing >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `well_formed_type entry_types.type_defs const_ty` by
    (qpat_assum `expr_type replacement = const_ty` (SUBST1_TAC o SYM) >>
     `entry_types.type_defs = (artifact_env art mods src).type_defs` by
       (qpat_assum `entry_types.type_defs = get_tenv cx` SUBST1_TAC >>
        qpat_assum `get_tenv cx = type_env_all_modules mods`
          (fn tenv => simp[NoAsms, tenv, artifact_env_def])) >>
     qpat_assum `entry_types.type_defs = (artifact_env art mods src).type_defs`
       SUBST1_TAC >>
     MATCH_MP_TAC well_typed_expr_type_well_formed >>
     conj_tac >- first_assum ACCEPT_TAC >>
     simp[NoAsms, artifact_env_def]) >>
  `!id ty. MEM (id,ty) args ==> FLOOKUP entry_types.var_types id = SOME ty` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!id ty. MEM (id,ty) args ==> _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `?env_after. type_stmts entry_types ret body_code = SOME env_after` by
    (qpat_assum `Abbrev (body_code = _)` (fn body =>
      PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] body]) >>
     qpat_assum `top = VariableDecl _ _ _ _ _` (fn decl =>
       qpat_assum `external_getter_tuple src top = SOME _`
         (assume_tac o PURE_REWRITE_RULE [decl])) >>
     qexists_tac `env_after` >>
     drule_all_then ACCEPT_TAC constant_public_getter_typing_mods) >>
  suspend "linked_linear_getter_substituted_typed"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_getter_no_replacement]:
  `body_code = fbody` by
    (qpat_assum `Abbrev (body_code = _)`
       (fn body => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] body]) >>
     qpat_assum `ALOOKUP (consts_env_mods mods) (src,tx.function_name) = NONE` (fn absent =>
       map_every (fn pat => qpat_assum pat mp_tac)
         [`external_getter_tuple src top = SOME _`,`is_public_getter_decl tx.function_name top`] >>
       POP_ASSUM_LIST (K ALL_TAC) >>
       Cases_on `top` >> simp[external_getter_tuple_def, is_public_getter_decl_def] >>
       Cases_on `v` >>
       simp[external_getter_tuple_def, is_public_getter_decl_def, getter_def,
         AllCaseEqs(), subst_consts_stmt_mods_def, subst_consts_expr_mods_def, absent] >>
       rpt (pairarg_tac >> gvs[]) >>
       rpt strip_tac >> gvs[] >>
       drule_then (qspec_then `consts_env_mods mods` mp_tac) build_getter_subst_mods >>
       simp[subst_consts_expr_mods_def, subst_consts_stmt_mods_def, absent] >>
       strip_tac >> gvs[])) >>
  `?env_after. type_stmts entry_types ret body_code = SOME env_after` by
    (qpat_assum `body_code = fbody` SUBST1_TAC >>
     qexists_tac `env_after` >> first_assum ACCEPT_TAC) >>
  suspend "linked_linear_getter_unsubstituted_typed"
QED

(* Common source facts at either typed getter cut. *)
val linked_positional_getter_type_tac =
  `IS_SOME (type_stmts entry_types ret fbody)` by
    (qpat_assum `type_stmts entry_types ret fbody = SOME _`
       (fn typed => simp[NoAsms, typed])) >>
  Q.SUBGOAL_THEN `?out. type_stmts entry_types ret body_code = SOME out`
    (qx_choose_then `after_body` assume_tac)
  >- (qpat_assum `type_stmts entry_types ret body_code = SOME _` (irule_at Any)) >>
  `ret <> NoneT` by
    (qpat_assum `fbody = [Return (SOME getter_value)]` (fn shape =>
       qpat_assum `type_stmts entry_types ret fbody = SOME env_after`
         (mp_tac o PURE_REWRITE_RULE [shape])) >>
     simp[NoAsms, type_stmt_def, AllCaseEqs()]) >>
  `stmts_no_control_escape fbody` by
    (qpat_assum `fbody = [Return (SOME getter_value)]` (fn shape =>
       simp[NoAsms, shape, stmt_no_control_escape_def])) >>
  `qualified_stmts_decls_ok mods body_code` by
    (qpat_assum `body_code = [Return (SOME _)]` (fn shape => simp[NoAsms, shape]));

val linked_positional_getter_lock_tac =
  `mut = View` by
    (qpat_assum `external_getter_tuple src top = SOME _` mp_tac >>
     qpat_assum `is_public_getter_decl tx.function_name top` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `top` >> simp[external_getter_tuple_def, is_public_getter_decl_def] >>
     Cases_on `v` >> simp[external_getter_tuple_def, is_public_getter_decl_def,
       getter_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[]) >>
  `~raw` by
    (qspecl_then [`tops`,`src`,`tx.function_name`,`top`] mp_tac public_getter_raw_return_none >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then (fn no_raw =>
       qpat_assum `lookup_raw_return_or_F src tx.function_name External tops = raw`
         (mp_tac o REWRITE_RULE [lookup_raw_return_or_F_def, no_raw])) >>
     simp[NoAsms]) >>
  `raw ==> ?n. ret = BaseT (BytesT (Dynamic n))` by
    (qpat_assum `~raw` (fn r => simp[NoAsms, r])) >>
  `nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot /\
          is_view_mut mut = (mut = View)` by
    (strip_tac >>
     `lookup_nonreentrant_slot am.layouts tx.target = SOME 0` by
       drule_all_then ACCEPT_TAC checked_selected_getter_lock_slot >>
     qpat_assum `mut = View` (fn view =>
       qpat_assum `lookup_nonreentrant_slot am.layouts tx.target = SOME 0` (fn lock =>
         simp[NoAsms, Abbr `cx`, initial_evaluation_context_def, lock, view,
           contextTheory.global_nonreentrant_slot_def, is_view_mut_def])));

val linked_positional_getter_return_tac =
  `assignable_type (get_tenv cx) ret` by
    (`check_toplevel_decl mods art src top` by
       drule_all_then ACCEPT_TAC check_contract_toplevel_decl_MEM_checked >>
     `check_value_type (type_env_all_modules mods) (Type ret)` by
       (map_every (fn p => qpat_assum p mp_tac)
          [`check_toplevel_decl mods art src top`, `external_getter_tuple src top = SOME _`,
           `is_public_getter_decl tx.function_name top`] >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        Cases_on `top` >> simp[is_public_getter_decl_def, external_getter_tuple_def] >>
        Cases_on `v` >> simp[is_public_getter_decl_def, external_getter_tuple_def,
          getter_def, AllCaseEqs()] >>
        rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[check_toplevel_decl_def] >>
        TRY (rename1 `is_ArrayT ty` >> Cases_on `v0` >> fs[check_toplevel_decl_def, check_value_type_def]) >>
        TRY (rename1 `check_toplevel_decl _ _ _ (VariableDecl _ var_kind _ _ _)` >>
          Cases_on `var_kind` >> fs[check_toplevel_decl_def, check_value_type_def]) >>
        metis_tac[check_value_type_ArrayT_type, build_getter_ret_checked, check_value_type_def]) >>
     qpat_assum `get_tenv cx = type_env_all_modules mods` (fn tenv =>
       qpat_assum `check_value_type (type_env_all_modules mods) (Type ret)`
         (ACCEPT_TAC o REWRITE_RULE [GSYM tenv, check_value_type_def]))) >>
  `ret <> NoneT ==> assignable_type (get_tenv cx) ret` by
    (strip_tac >> first_assum ACCEPT_TAC);

val linked_positional_getter_env_tac =
  `linked_body_type_facts tops src (type_env_all_modules mods)` by
    drule_all_then ACCEPT_TAC linked_checked_body_type_facts >>
  `src = NONE ==> layouts_agree tops am tx` by
    (strip_tac >>
     `MEM (NONE,tops) mods` by
       (qpat_assum `src = NONE` (fn main =>
          qpat_assum `ALOOKUP mods src = SOME tops`
            (ACCEPT_TAC o MATCH_MP ALOOKUP_MEM o REWRITE_RULE [main]))) >>
     qpat_assum `layouts_agree_mods mods exps am tx` mp_tac >>
     simp[NoAsms, layouts_agree_mods_def, layouts_agree_def, pairTheory.ELIM_UNCURRY] >>
     disch_then (qspecl_then [`NONE`,`tops`] mp_tac o
       CONJUNCT2 o CONJUNCT2 o CONJUNCT2) >>
     qpat_assum `MEM (NONE,tops) mods` (fn member => simp[NoAsms, member])) >>
  `entry_types.event_fields = art.cta_event_fields` by
    simp[NoAsms, Abbr `entry_types`, function_entry_env_def, artifact_env_def,
         FOLDL_extend_local_args_static] >>
  `linked_body_data_env tops src entry_types` by
    (MATCH_MP_TAC (Q.INST [`mode` |-> `F`, `am` |-> `am`, `tx` |-> `tx`,
      `mods` |-> `mods`, `art` |-> `art`] linked_checked_data_env) >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       qpat_assum `entry_types.type_defs = get_tenv cx` SUBST1_TAC >> first_assum ACCEPT_TAC,
       qpat_assum `entry_types.bare_global_assignable = FEMPTY` (fn empty => simp[NoAsms, empty] >> NO_TAC),
       strip_tac >>
       qpat_assum `src = NONE` (fn main =>
         qpat_assum `linked_body_type_facts _ _ _` (mp_tac o REWRITE_RULE [linked_body_type_facts_def]) >>
         simp[NoAsms, main] >> strip_tac >> first_assum ACCEPT_TAC)]) >>
  `!x ty. FLOOKUP entry_types.var_types x = SOME ty ==>
      assignable_type (type_env_all_modules mods) ty` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!x ty. FLOOKUP entry_types.var_types x = SOME ty ==>
       ?id. MEM (id,ty) args /\ x = id`
       (drule_then (qx_choose_then `param` strip_assume_tac)) >>
     qpat_assum `params_ok (type_env_all_modules mods) args`
       (strip_assume_tac o REWRITE_RULE [params_ok_def]) >>
     qpat_assum `EVERY _ args` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `(param,ty)` mp_tac) >>
     simp[NoAsms] >> disch_then irule >> first_assum ACCEPT_TAC);

(* Imported declarations give the path annotations; qualified constants
   preserve the same reference discipline when a getter root is inlined. *)
val linked_getter_path_refs_tac =
  Q.SUBGOAL_THEN
    `!e kt vt n. imported_expr_refs_ok e /\ imported_type_refs_ok kt /\
       imported_value_type_refs_ok vt ==>
       imported_expr_refs_ok (SND (SND (build_getter e kt vt n)))`
    assume_tac
  >- (POP_ASSUM_LIST (K ALL_TAC) >> ho_match_mp_tac build_getter_ind >>
      rpt conj_tac >> rpt gen_tac >> disch_tac >> strip_tac >>
      simp[Once build_getter_def] >>
      TRY (Cases_on `is_ArrayT vt` >> fs[]) >>
      simp[pairTheory.UNCURRY, imported_expr_refs_ok_def,
        imported_type_refs_ok_def, imported_value_type_refs_ok_def,
        getter_vtype_annotation_def] >>
      gvs[imported_value_type_refs_ok_def, AllCaseEqs()] >>
      TRY (rename1 `is_ArrayT arr` >> Cases_on `arr` >>
           gvs[is_ArrayT_def, ArrayT_type_def, imported_type_refs_ok_def]) >>
      rpt (pairarg_tac >> gvs[]) >>
      gvs[imported_expr_refs_ok_def, imported_type_refs_ok_def] >>
      fs[getter_vtype_annotation_def, imported_type_refs_ok_def]);


(* Only lookups at qualified keys are needed for inlining an imported
   getter.  The main module's unqualified expressions are not restricted. *)
val linked_getter_import_fold_tac =
  `!ty bi es. imported_type_refs_ok ty /\ imported_builtin_refs_ok bi /\
    imported_exprs_refs_ok es ==> imported_expr_refs_ok (fold_const_builtin ty bi es)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >> strip_tac >>
     Cases_on `bi` >> simp[fold_const_builtin_def, imported_expr_refs_ok_def] >>
     Cases_on `es` >> simp[imported_expr_refs_ok_def] >>
     Cases_on `t` >> simp[imported_expr_refs_ok_def] >>
     Cases_on `h` >> simp[imported_expr_refs_ok_def] >>
     rename1 `Literal _ lit` >> Cases_on `lit` >> simp[imported_expr_refs_ok_def]) >>
  `(!e. imported_expr_refs_ok e ==> imported_expr_refs_ok (fold_const_expr e)) /\
   (!t. imported_base_target_refs_ok t ==> imported_base_target_refs_ok (fold_const_btarget t)) /\
   (!es. imported_exprs_refs_ok es ==> imported_exprs_refs_ok (fold_const_exprs es)) /\
   (!o'. imported_optional_expr_refs_ok o' ==> imported_optional_expr_refs_ok (fold_const_opt o')) /\
   (!fs. imported_field_refs_ok fs ==> imported_field_refs_ok (fold_const_fields fs))` by
    (qpat_assum `!ty bi es. _ ==> imported_expr_refs_ok (fold_const_builtin ty bi es)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >> ho_match_mp_tac fold_const_expr_ind >>
     simp[fold_const_expr_def, imported_expr_refs_ok_def] >> metis_tac[]);

val linked_getter_import_subst_tac =
  `(!E e. (!k r. FST k <> NONE /\ ALOOKUP E k = SOME r ==> imported_expr_refs_ok r) ==>
      imported_expr_refs_ok e ==> imported_expr_refs_ok (subst_consts_expr_mods E e)) /\
   (!E t. (!k r. FST k <> NONE /\ ALOOKUP E k = SOME r ==> imported_expr_refs_ok r) ==>
      imported_base_target_refs_ok t ==> imported_base_target_refs_ok (subst_consts_btarget_mods E t)) /\
   (!E es. (!k r. FST k <> NONE /\ ALOOKUP E k = SOME r ==> imported_expr_refs_ok r) ==>
      imported_exprs_refs_ok es ==> imported_exprs_refs_ok (subst_consts_exprs_mods E es)) /\
   (!E o'. (!k r. FST k <> NONE /\ ALOOKUP E k = SOME r ==> imported_expr_refs_ok r) ==>
      imported_optional_expr_refs_ok o' ==> imported_optional_expr_refs_ok (subst_consts_opt_mods E o')) /\
   (!E fs. (!k r. FST k <> NONE /\ ALOOKUP E k = SOME r ==> imported_expr_refs_ok r) ==>
      imported_field_refs_ok fs ==> imported_field_refs_ok (subst_consts_fields_mods E fs))` by
    (POP_ASSUM_LIST (K ALL_TAC) >> ho_match_mp_tac subst_consts_expr_mods_ind >>
     simp[subst_consts_expr_mods_def, imported_expr_refs_ok_def] >> rpt strip_tac
     >~ [`ALOOKUP _ (_,_)`]
     >- (rename1 `ALOOKUP constants (source,key)` >>
         Cases_on `ALOOKUP constants (source,key)` >> simp[imported_expr_refs_ok_def] >>
         qpat_assum `!key replacement. _` (qspec_then `(source,key)` mp_tac) >> simp[]) >>
     qpat_assum `!key replacement. _` (fn ok => fs[EQT_INTRO ok]));

val linked_getter_import_acc_tac =
  `!(E:(nsid # expr) list) k r. EVERY (\(key,rhs). FST key <> NONE ==> imported_expr_refs_ok rhs) E /\
      FST k <> NONE /\ ALOOKUP E k = SOME r ==> imported_expr_refs_ok r` by
    (POP_ASSUM_LIST (K ALL_TAC) >>
     rpt gen_tac >> PairCases_on `k` >> simp[EVERY_MEM, FORALL_PROD] >>
     rpt strip_tac >> drule_then assume_tac ALOOKUP_MEM >>
     qpat_assum `!s name value. MEM ((s,name),value) E ==> _` drule >> simp[]);

val linked_getter_import_module_goal_tac =
  Q.SUBGOAL_THEN
    `!ts owner E. (owner <> NONE ==> EVERY imported_toplevel_refs_ok ts) /\
       EVERY (\(k,r). FST k <> NONE ==> imported_expr_refs_ok r) E ==>
       EVERY (\(k,r). FST k <> NONE ==> imported_expr_refs_ok r)
         (module_consts_env_mods owner ts E)` assume_tac;

val linked_getter_import_module_setup_tac =
  map_every (fn p => qpat_assum p mp_tac)
    [`!E k r. EVERY _ E /\ _ ==> _`,
     `!E e. _ ==> _ ==> imported_expr_refs_ok (subst_consts_expr_mods E e)`,
     `!e. imported_expr_refs_ok e ==> imported_expr_refs_ok (fold_const_expr e)`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> ntac 3 strip_tac;

val linked_getter_import_module_induct_tac =
  Induct >> simp[module_consts_env_mods_def] >>
  Cases_on `h` >> simp[module_consts_env_mods_def] >>
  rename1 `VariableDecl vis mut key ty slot` >>
  Cases_on `mut` >> simp[module_consts_env_mods_def] >> rpt strip_tac >>
  qpat_assum `!owner E. _ ==> EVERY _ (module_consts_env_mods owner _ E)` irule >>
  simp[EVERY_APPEND] >> rpt strip_tac;

val linked_getter_import_module_finish_tac =
  qpat_assum `!e. imported_expr_refs_ok e ==> imported_expr_refs_ok (fold_const_expr e)` irule >>
  qpat_assum `!E e. _ ==> _ ==> imported_expr_refs_ok (subst_consts_expr_mods E e)` irule >>
  fs[imported_toplevel_refs_ok_def] >> rpt strip_tac;

val linked_getter_import_all_goal_tac =
  Q.SUBGOAL_THEN
    `!owners E. EVERY (\(owner,ts). owner <> NONE ==> EVERY imported_toplevel_refs_ok ts) owners /\
      EVERY (\(k,r). FST k <> NONE ==> imported_expr_refs_ok r) E ==>
      EVERY (\(k,r). FST k <> NONE ==> imported_expr_refs_ok r) (consts_env_mods_acc owners E)`
    assume_tac;

val linked_getter_import_all_induct_tac =
  qpat_assum `!ts owner E. _ ==> EVERY _ (module_consts_env_mods owner ts E)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
  Induct >> simp[consts_env_mods_acc_def] >> Cases_on `h` >>
  simp[consts_env_mods_acc_def] >> rpt strip_tac >>
  qpat_assum `!E. _ ==> EVERY _ (consts_env_mods_acc _ E)` irule >> simp[];

val linked_getter_import_all_modules_tac =
  `EVERY (\(k,r). FST k <> NONE ==> imported_expr_refs_ok r) (consts_env_mods mods)` by
    (simp[NoAsms, consts_env_mods_def, consts_env_modules_order_eq] >>
     qpat_assum `!owners E. _ ==> EVERY _ (consts_env_mods_acc owners E)` irule >>
     simp[] >> once_rewrite_tac[EVERY_MEM] >> simp[FORALL_PROD, MEM_constants_order] >>
     Cases >> simp[] >> rpt strip_tac >>
     drule_all_then ACCEPT_TAC check_contract_imported_toplevel_refs_ok);

val linked_getter_import_decl_tac =
  `src <> NONE ==> imported_toplevel_refs_ok top` by
    (map_every (fn p => qpat_assum p mp_tac)
       [`MEM top tops`,`ALOOKUP mods src = SOME tops`,
        `check_contract F am.layouts tx.target mods = SOME art`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule_then assume_tac ALOOKUP_MEM >> Cases_on `src` >> fs[] >>
     drule_all check_contract_imported_toplevel_refs_ok >>
     simp[EVERY_MEM]);

val linked_getter_import_original_goal_tac =
  Q.SUBGOAL_THEN `src <> NONE ==> imported_expr_refs_ok getter_value` assume_tac;

val linked_getter_import_original_shape_tac =
  map_every (fn pat => qpat_assum pat mp_tac)
    [`external_getter_tuple src top = SOME _`,
     `is_public_getter_decl tx.function_name top`,
     `fbody = [Return (SOME getter_value)]`,
     `src <> NONE ==> imported_toplevel_refs_ok top`,
     `!e kt vt n. _ ==> imported_expr_refs_ok (SND (SND (build_getter e kt vt n)))`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
  Cases_on `top` >> simp[external_getter_tuple_def, is_public_getter_decl_def] >>
  Cases_on `v` >> simp[external_getter_tuple_def, is_public_getter_decl_def,
    getter_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[imported_toplevel_refs_ok_def, imported_expr_refs_ok_def];

val linked_getter_import_path_finish_tac =
  qpat_assum `build_getter _ _ _ _ = _`
    (mp_tac o AP_TERM ``\x : (string # type) list # type # expr. SND (SND x)``) >>
  simp[NoAsms] >> disch_then (SUBST1_TAC o SYM) >>
  first_x_assum irule >>
  simp[imported_expr_refs_ok_def, imported_type_refs_ok_def,
       imported_value_type_refs_ok_def] >>
  rename1 `imported_type_refs_ok (ArrayT_type arr)` >> Cases_on `arr` >>
  gvs[is_ArrayT_def, ArrayT_type_def, imported_type_refs_ok_def];
(* A getter can be checked with no function signatures: its expression has
   no internal calls before or after the checked constant substitution. *)
val linked_positional_getter_restrict_tac =
  `int_calls_stmts fbody = []` by
    drule_all_then ACCEPT_TAC selected_public_getter_body_int_calls_empty >>
  `int_calls_stmts body_code = []` by
    (qpat_assum `Abbrev (body_code = _)`
       (fn body => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] body]) >>
     drule_then (strip_assume_tac o SPEC_ALL) checked_subst_consts_int_calls_mods >>
     simp[]) >>
  Q.SUBGOAL_THEN `type_stmts (entry_types with fn_sigs := FEMPTY) ret body_code =
     SOME (after_body with fn_sigs := FEMPTY)` assume_tac
  >- (mp_tac (Q.INST [`ks` |-> `{}`] (SPEC_ALL whitelistCheckerFnSigsTheory.type_stmt_fn_sigs_restrict)) >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `!env ret ss. set (int_calls_stmts ss) SUBSET {} ==> _`
        (qspecl_then [`entry_types`,`ret`,`body_code`] mp_tac) >>
      (impl_tac >-
        (qpat_assum `int_calls_stmts body_code = []` (fn calls => simp[NoAsms, calls]))) >>
      qpat_assum `type_stmts entry_types ret body_code = SOME after_body`
        (fn typed => simp[NoAsms, DRESTRICT_IS_FEMPTY, typed]));

val linked_positional_getter_support_env_tac =
  (Q.SUBGOAL_THEN `linked_body_data_env tops (src:num option)
       (entry_types with fn_sigs := FEMPTY)` assume_tac
   >- (simp[NoAsms, linked_body_data_env_def] >>
       qpat_assum `linked_body_data_env tops src entry_types`
         (ACCEPT_TAC o SIMP_RULE (srw_ss()) [linked_body_data_env_def]))) >>
  `linked_body_env tops (src:num option) (type_env_all_modules mods)
      (entry_types with fn_sigs := FEMPTY)` by
    (simp[NoAsms, linked_body_env_def, linked_body_calls_env_def] >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       qpat_assum `entry_types.type_defs = get_tenv cx` SUBST1_TAC >> first_assum ACCEPT_TAC,
       qpat_assum `entry_types.bare_global_assignable = FEMPTY` (fn empty => simp[NoAsms, empty])]) >>
  `!name. ~MEM (StructDecl name []) tops` by
    (qx_gen_tac `empty_struct` >> strip_tac >>
     drule_all check_contract_toplevel_decl_MEM_checked >>
     simp[NoAsms, check_toplevel_decl_def]);

val linked_positional_getter_support_tac =
  Q.SUBGOAL_THEN `((src:num option) = NONE \/ imported_stmts_refs_ok body_code) ==>
     supported_stmts tops
       (args ++ supported_stmts_bindings T body_code ++ supported_stmts_bindings F body_code)
       body_code` assume_tac
  >- (disch_tac >>
     linked_positional_getter_restrict_tac >>
     linked_positional_getter_support_env_tac >>
     (Q.SUBGOAL_THEN `?e. body_code = [Return (SOME e)]`
        (qx_choose_then `getter_code` assume_tac)
      >- qpat_assum `body_code = [Return (SOME _)]` (irule_at Any)) >>
     `well_typed_expr (entry_types with fn_sigs := FEMPTY) getter_code` by
       (qpat_assum `body_code = [Return (SOME getter_code)]` (fn body =>
          qpat_assum `type_stmts (entry_types with fn_sigs := FEMPTY) ret body_code = SOME _`
            (mp_tac o PURE_REWRITE_RULE [body])) >>
        simp[NoAsms, type_stmt_def, AllCaseEqs()]) >>
     (Q.SUBGOAL_THEN `(src:num option) = NONE \/ imported_expr_refs_ok getter_code` assume_tac
      >- (qpat_assum `body_code = [Return (SOME getter_code)]` (fn body =>
            qpat_assum `src = NONE \/ imported_stmts_refs_ok body_code`
              (mp_tac o PURE_REWRITE_RULE [body])) >>
          simp[NoAsms, imported_stmt_refs_ok_def, imported_expr_refs_ok_def])) >>
     mp_tac (Q.INST [`tenv` |-> `type_env_all_modules mods`]
               (Q.ISPEC `(src:num option)` (Q.GEN `src`
                 whitelistLinkedBodyExprsTheory.linked_well_typed_expr_supported))) >>
     (impl_tac >- (disch_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!env e. well_typed_expr env e ==> _`
       (qspecl_then [`entry_types with fn_sigs := FEMPTY`,`getter_code`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     strip_tac >>
     qpat_assum `body_code = [Return (SOME getter_code)]` SUBST1_TAC >>
     simp[supportedStmtsTheory.supported_stmt_def, supportedExprsTheory.supported_expr_def]);

(* Descending a synthesized getter adds only Subscripts and local Names. *)
val linked_getter_guard_path_tac =
  `!e kt vt n.
     ~supportedExprTraverse$supported_expr_exists
        (unallocated_bare_global_root registered_env entry_types) e ==>
     ~supportedExprTraverse$supported_expr_exists
        (unallocated_bare_global_root registered_env entry_types)
        (SND (SND (build_getter e kt vt n)))` by
    (POP_ASSUM_LIST (K ALL_TAC) >>
     recInduct build_getter_ind >> rpt conj_tac >> rpt gen_tac >>
     disch_tac >> disch_tac >> simp[Once build_getter_def] >>
     Cases_on `is_ArrayT vt` >>
     gvs[supportedExprTraverseTheory.supported_expr_exists_def,
         unallocated_bare_global_root_def] >>
     pairarg_tac >> gvs[] >> metis_tac[pairTheory.SND]);

val linked_getter_guard_replacement_tac =
  `(!e. supportedExprTraverse$supported_expr_exists
          (unallocated_bare_global_root registered_env entry_types) e ==>
        ?key. MEM (ReadAcc (StateRef key)) (accesses_expr e)) /\
   (!t. supportedExprTraverse$supported_target_exists
          (unallocated_bare_global_root registered_env entry_types) t ==>
        ?key. MEM (ReadAcc (StateRef key)) (accesses_target t)) /\
   (!es. supportedExprTraverse$supported_exprs_exists
          (unallocated_bare_global_root registered_env entry_types) es ==>
         ?key. MEM (ReadAcc (StateRef key)) (accesses_exprs es)) /\
   (!opt. supportedExprTraverse$supported_opt_exists
          (unallocated_bare_global_root registered_env entry_types) opt ==>
          ?key. MEM (ReadAcc (StateRef key)) (accesses_opt opt)) /\
   (!fields. supportedExprTraverse$supported_fields_exists
          (unallocated_bare_global_root registered_env entry_types) fields ==>
          ?key. MEM (ReadAcc (StateRef key)) (accesses_named_exprs fields))` by
    (POP_ASSUM_LIST (K ALL_TAC) >> ho_match_mp_tac accesses_expr_ind >>
     simp[supportedExprTraverseTheory.supported_expr_exists_def,
          unallocated_bare_global_root_def, accesses_expr_def, MEM_APPEND] >>
     rpt strip_tac >> metis_tac[]);

val linked_getter_guard_replacement_base_tac =
  linked_getter_guard_replacement_tac >>
  `~supportedExprTraverse$supported_expr_exists
      (unallocated_bare_global_root registered_env entry_types) replacement` by
    (strip_tac >>
     qpat_assum `!e. supportedExprTraverse$supported_expr_exists _ e ==> _`
       (qspec_then `replacement` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (qx_choose_then `read_key` assume_tac) >>
     qpat_assum `!a. MEM a (accesses_expr replacement) ==> a = RiskyAcc`
       (qspec_then `ReadAcc (StateRef read_key)` mp_tac) >>
     simp[var_access_distinct]) >>
  `!ty. ~supportedExprTraverse$supported_expr_exists
      (unallocated_bare_global_root registered_env entry_types)
      (subst_consts_expr_mods (consts_env_mods mods)
        (TopLevelName ty (src,tx.function_name)))` by
    (gen_tac >>
     qpat_assum `ALOOKUP (consts_env_mods mods) (src,tx.function_name) = SOME replacement`
       (fn found => simp[NoAsms, subst_consts_expr_mods_def, found]) >>
     first_assum ACCEPT_TAC);

(* The selected public declaration is a closure root in its actual module. *)
val linked_getter_guard_live_tac =
  `MEM (src,tx.function_name) (linked_main_roots mods ++ linked_export_roots exps)` by
    (Cases_on `src` >> simp_tac bool_ss [MEM_APPEND]
     >- (disj1_tac >>
         qpat_assum `ALOOKUP mods NONE = SOME tops` (fn main =>
           simp[NoAsms, linked_main_roots_def, main, contract_keys_def, MEM_APPEND]) >>
         disj1_tac >> simp[NoAsms, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
         qexists_tac `top` >> conj_tac >- first_assum ACCEPT_TAC >>
         qpat_assum `is_public_getter_decl _ top` mp_tac >>
         Cases_on `top` >> simp[NoAsms, is_public_getter_decl_def] >>
         Cases_on `v` >> simp[NoAsms, is_public_getter_decl_def,
           external_name_keys_toplevel_def]) >>
     disj2_tac >> simp[NoAsms, linked_export_roots_def, MEM_MAP, EXISTS_PROD] >>
     qpat_assum `SOME _ = ALOOKUP exps tx.function_name`
       (mp_tac o MATCH_MP ALOOKUP_MEM o SYM) >> disch_then ACCEPT_TAC) >>
  `MEM (src,tx.function_name) (linked_live_functions mods exps)` by
    (PURE_REWRITE_TAC [linked_live_functions_def, linked_live_functions_from_def, LET_THM] >>
     BETA_TAC >> irule (cj 1 call_closure_from_roots) >> first_assum ACCEPT_TAC);

val linked_getter_guard_owned_tac =
  linked_getter_guard_live_tac >>
  `check_linked_state_ownership am.layouts tx.target mods (linked_live_functions mods exps)` by
    (PURE_REWRITE_TAC [GSYM linked_state_ownership_ok_def] >>
     drule_all_then ACCEPT_TAC check_contract_linked_state_ownership_ok) >>
  `MEM (src,tops) mods` by drule_then ACCEPT_TAC ALOOKUP_MEM >>
  Q.SUBGOAL_THEN
    `mods = [(NONE,tops)] \/ linked_state_ref_allocated am.layouts tx.target mods (src,tx.function_name)`
    assume_tac
  >- (qpat_assum `check_linked_state_ownership _ _ _ _` mp_tac >>
     PURE_REWRITE_TAC [check_linked_state_ownership_def] >>
     disch_then (DISJ_CASES_THEN2 mp_tac assume_tac)
     >- (qpat_assum `ALOOKUP mods src = SOME tops` mp_tac >>
         Cases_on `mods` >> simp[NoAsms] >> PairCases_on `h` >>
         Cases_on `h0` >> Cases_on `t` >> simp[NoAsms, AllCaseEqs()]) >>
     qpat_assum `EVERY _ mods` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `(src,tops)` mp_tac) >>
     qpat_assum `MEM (src,tops) mods` (fn member => simp[NoAsms, member, Once EVERY_MEM]) >>
     disch_then (qspec_then `top` mp_tac) >>
     qpat_assum `MEM top tops` (fn member => simp[NoAsms, member]) >>
     qpat_assum `is_public_getter_decl tx.function_name top` mp_tac >>
     qpat_assum `MEM (src,tx.function_name) (linked_live_functions mods exps)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `top` >> simp[is_public_getter_decl_def] >>
     Cases_on `v` >> simp[is_public_getter_decl_def] >> rpt strip_tac >> gvs[]) >>
  `immutable_section_layout_mods mods registered_env` by
    drule_then ACCEPT_TAC contract_inv_immutable_section_layout;

(* A matching constant declaration would have contributed its qualified key. *)
val linked_getter_guard_const_keys_tac =
  `!src tops E key.
     MEM key (MAP FST E) \/
     (?vis e id ty slot. key = (src,id) /\ MEM (VariableDecl vis (Constant e) id ty slot) tops) ==>
     MEM key (MAP FST (module_consts_env_mods src tops E))` by
    (POP_ASSUM_LIST (K ALL_TAC) >> ho_match_mp_tac module_consts_env_mods_ind >>
     simp[module_consts_env_mods_def, MEM_APPEND] >> metis_tac[]) >>
  `!ms E key.
     MEM key (MAP FST E) \/
     (?s ts vis e id ty slot. key = (s,id) /\ MEM (s,ts) ms /\
       MEM (VariableDecl vis (Constant e) id ty slot) ts) ==>
     MEM key (MAP FST (consts_env_mods_acc ms E))` by
    (qpat_assum `!s ts E key. _ ==> MEM key (MAP FST (module_consts_env_mods s ts E))` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     Induct >> simp[consts_env_mods_acc_def, FORALL_PROD] >>
     rpt strip_tac >> first_x_assum irule >> metis_tac[]);

val linked_getter_allocation_guards_tac =
  linked_getter_guard_path_tac >>
  `~supported_stmts_expr_exists (unallocated_bare_global_root registered_env entry_types) body_code /\
   (!key. MEM (WriteAcc (StateRef key)) (accesses_stmts body_code) /\
          IS_SOME (FLOOKUP entry_types.bare_global_assignable key) ==>
          IS_SOME (FLOOKUP registered_env.ce_module_vars key))` by
    (reverse conj_tac
     >- (qpat_assum `entry_types.bare_global_assignable = FEMPTY`
           (fn empty => simp[NoAsms, empty])) >>
     qpat_assum `body_code = [Return (SOME _)]` SUBST1_TAC >>
     simp[NoAsms, supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
          supportedExprTraverseTheory.supported_expr_exists_def] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`external_getter_tuple src top = SOME _`, `is_public_getter_decl tx.function_name top`,
        `fbody = [Return (SOME getter_value)]`] >>
     qpat_assum `!ty. ~supportedExprTraverse$supported_expr_exists _ (subst_consts_expr_mods _ _)`
       mp_tac >>
     qpat_assum `!e kt vt n. _ ==> ~supportedExprTraverse$supported_expr_exists _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `top` >> simp[external_getter_tuple_def, is_public_getter_decl_def] >>
     Cases_on `v` >> simp[external_getter_tuple_def, is_public_getter_decl_def,
       getter_def, AllCaseEqs()] >>
     rpt (pairarg_tac >> gvs[]) >>
     rpt strip_tac >> gvs[] >>
     metis_tac[build_getter_subst_mods, pairTheory.SND]);

Resume linked_runtime_dispatched_readings_certificate[linked_linear_getter_substituted_typed]:
  linked_getter_guard_replacement_base_tac >>
  linked_getter_allocation_guards_tac >>
  linked_positional_getter_type_tac >>
  linked_positional_getter_lock_tac >>
  linked_positional_getter_return_tac >>
  linked_positional_getter_env_tac >>
  linked_getter_path_refs_tac >>
  linked_getter_import_decl_tac >>
  linked_getter_import_original_goal_tac
  >- (linked_getter_import_original_shape_tac >> linked_getter_import_path_finish_tac) >>
  linked_getter_import_fold_tac >>
  linked_getter_import_subst_tac >>
  linked_getter_import_acc_tac >>
  linked_getter_import_module_goal_tac
  >- (linked_getter_import_module_setup_tac >>
      linked_getter_import_module_induct_tac >>
      linked_getter_import_module_finish_tac >>
      qpat_assum `!E k r. _ ==> imported_expr_refs_ok r`
        (qspecl_then [`E`,`k`,`r`] mp_tac) >> simp[]) >>
  linked_getter_import_all_goal_tac
  >- (linked_getter_import_all_induct_tac >>
      qpat_assum `!ts owner E. _ ==> EVERY _ (module_consts_env_mods owner ts E)` irule >>
      simp[]) >>
  linked_getter_import_all_modules_tac >>
  Q.SUBGOAL_THEN `src = NONE \/ imported_stmts_refs_ok body_code` assume_tac
  >- (map_every (fn p => qpat_assum p mp_tac)
       [`body_code = [Return (SOME (subst_consts_expr_mods (consts_env_mods mods) getter_value))]`,
        `src <> NONE ==> imported_expr_refs_ok getter_value`,
        `!E e. _ ==> _ ==> imported_expr_refs_ok (subst_consts_expr_mods E e)`,
        `!E k r. EVERY _ E /\ _ ==> _`,
        `EVERY _ (consts_env_mods mods)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     Cases_on `src` >> fs[imported_stmt_refs_ok_def, imported_expr_refs_ok_def] >>
     qpat_assum `!E e. _ ==> _ ==> imported_expr_refs_ok (subst_consts_expr_mods E e)` irule >>
     simp[] >> rpt strip_tac >>
     qpat_assum `!E k r. EVERY _ E /\ _ ==> _` irule >>
     map_every qexists_tac [`consts_env_mods mods`,`k`] >> simp[]) >>
  linked_positional_getter_support_tac >>
  `supported_stmts tops
     (args ++ supported_stmts_bindings T body_code ++ supported_stmts_bindings F body_code) body_code` by
    (qpat_assum `(src = NONE \/ imported_stmts_refs_ok body_code) ==> supported_stmts _ _ body_code`
       (drule_then ACCEPT_TAC)) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    qexists_tac `after_body` >> first_assum ACCEPT_TAC]
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_getter_unsubstituted_typed]:
  linked_getter_guard_owned_tac >>
  linked_getter_guard_const_keys_tac >>
  Q.SUBGOAL_THEN `!ty. ~supportedExprTraverse$supported_expr_exists
      (unallocated_bare_global_root registered_env entry_types)
      (subst_consts_expr_mods (consts_env_mods mods)
        (TopLevelName ty (src,tx.function_name)))` assume_tac
  >- (gen_tac >>
      qpat_assum `ALOOKUP (consts_env_mods mods) (src,tx.function_name) = NONE`
        (fn absent => simp[NoAsms, subst_consts_expr_mods_def, absent,
          supportedExprTraverseTheory.supported_expr_exists_def, unallocated_bare_global_root_def]) >>
      strip_tac >>
      Cases_on `FLOOKUP entry_types.bare_globals (src,tx.function_name)` >> simp[NoAsms] >>
      rename1 `FLOOKUP entry_types.bare_globals (src,tx.function_name) = SOME bare_type` >>
      `FLOOKUP (build_contract_type_artifact F mods).cta_bare_globals (src,tx.function_name) = SOME bare_type` by
        (qpat_assum `entry_types.bare_globals = art.cta_bare_globals` (fn static =>
           qpat_assum `FLOOKUP entry_types.bare_globals (src,tx.function_name) = SOME bare_type`
             (mp_tac o PURE_REWRITE_RULE [static])) >>
         qpat_assum `check_contract F am.layouts tx.target mods = SOME art`
           (fn checked => simp[NoAsms, MATCH_MP check_contract_nonsig_maps checked])) >>
      drule_all_then (DISJ_CASES_THEN2
        (qx_choosel_then [`origin_tops`,`imm_vis`,`imm_id`,`imm_slot`]
          (map_every assume_tac o CONJUNCTS))
        (qx_choosel_then [`origin_tops`,`const_vis`,`const_init`,`const_id`,`const_slot`]
          (map_every assume_tac o CONJUNCTS))) build_contract_type_artifact_bare_globals_sound
      >- (`origin_tops = tops` by
            (qpat_assum `ALOOKUP mods src = SOME tops` (fn selected =>
               qpat_assum `ALOOKUP mods src = SOME origin_tops` (mp_tac o PURE_REWRITE_RULE [selected])) >>
             simp[NoAsms]) >>
          qpat_x_assum `origin_tops = tops` SUBST_ALL_TAC >>
          qpat_x_assum `tx.function_name = imm_id` (SUBST_ALL_TAC o SYM) >>
          `?off. FLOOKUP registered_env.ce_module_vars (src,tx.function_name) = SOME (ImmutableLoc off)` by
            drule_all_then ACCEPT_TAC linkedOwnedImmutableLocationTheory.linked_owned_immutable_location >>
          qpat_assum `FLOOKUP registered_env.ce_module_vars (src,tx.function_name) = NONE`
            (fn absent =>
              qpat_assum `FLOOKUP registered_env.ce_module_vars (src,tx.function_name) = SOME _`
                (CONTR_TAC o REWRITE_RULE [absent, optionTheory.NOT_NONE_SOME]))) >>
      `MEM (src,tx.function_name) (MAP FST (consts_env_mods mods))` by
        (qpat_x_assum `tx.function_name = const_id` (SUBST_ALL_TAC o SYM) >>
         simp[NoAsms, consts_env_mods_def, consts_env_modules_order_eq] >>
         qpat_assum `!ms E key. _ ==> MEM key (MAP FST (consts_env_mods_acc ms E))` irule >>
         simp[NoAsms, MEM_constants_order] >>
         qexistsl_tac [`origin_tops`,`const_vis`,`const_init`,`bare_type`,`const_slot`] >>
         conj_tac >- drule_then ACCEPT_TAC ALOOKUP_MEM >> first_assum ACCEPT_TAC) >>
      qpat_assum `ALOOKUP (consts_env_mods mods) (src,tx.function_name) = NONE`
        (mp_tac o REWRITE_RULE [ALOOKUP_NONE]) >> simp[]) >>
  linked_getter_allocation_guards_tac >>
  linked_positional_getter_type_tac >>
  linked_positional_getter_lock_tac >>
  linked_positional_getter_return_tac >>
  linked_positional_getter_env_tac >>
  linked_getter_path_refs_tac >>
  linked_getter_import_decl_tac >>
  linked_getter_import_original_goal_tac
  >- (linked_getter_import_original_shape_tac >> linked_getter_import_path_finish_tac) >>
  Q.SUBGOAL_THEN `src = NONE \/ imported_stmts_refs_ok body_code` assume_tac
  >- (map_every (fn p => qpat_assum p mp_tac)
       [`body_code = fbody`, `fbody = [Return (SOME getter_value)]`,
        `src <> NONE ==> imported_expr_refs_ok getter_value`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> Cases_on `src` >>
     fs[imported_stmt_refs_ok_def, imported_expr_refs_ok_def]) >>
  linked_positional_getter_support_tac >>
  `supported_stmts tops
     (args ++ supported_stmts_bindings T body_code ++ supported_stmts_bindings F body_code) body_code` by
    (qpat_assum `(src = NONE \/ imported_stmts_refs_ok body_code) ==> supported_stmts _ _ body_code`
       (drule_then ACCEPT_TAC)) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    qexists_tac `after_body` >> first_assum ACCEPT_TAC]
QED

(* The selected getter has a single Return regardless of whether its root
   was replaced. The route supplies the registered code and path. *)
val linked_positional_getter_registered_tac =
  qabbrev_tac `bindings =
    args ++ supported_stmts_bindings T body_code ++ supported_stmts_bindings F body_code` >>
  `supported_stmts tops bindings body_code` by
    (simp[NoAsms, Abbr `bindings`] >> first_assum ACCEPT_TAC) >>
  `MEM (src,tops) mods` by drule_then ACCEPT_TAC ALOOKUP_MEM >>
  `IS_SOME (check_contract F cx.layouts cx.txn.target mods)` by
    (qpat_assum `check_contract F cx.layouts cx.txn.target mods = SOME art`
      (fn checked => simp[NoAsms, checked])) >>
  `ALL_DISTINCT (MAP FST mods)` by
    (qpat_assum `contract_namespaces_ok F mods`
      (strip_assume_tac o PURE_REWRITE_RULE [contract_namespaces_ok_def]) >>
     first_assum ACCEPT_TAC) >>
  `ret <> NoneT ==> stmts_no_fallthrough fbody` by
    (qpat_assum `fbody = [Return (SOME getter_value)]` (fn body =>
       simp[NoAsms, body, stmt_no_fallthrough_def]));

Resume linked_runtime_dispatched_readings_certificate[linked_linear_getter_registered]:
  linked_positional_getter_registered_tac >>
  linked_registered_frame_tac >>
  linked_registered_stmts_env_tac >>
  linked_linear_registered_route_tac >>
  linked_registered_path_tac >>
  linked_linear_registered_open_tac >>
  linked_registered_lock_cases_tac
    (suspend "linked_linear_getter_lock_success")
    (suspend "linked_linear_getter_lock_abort")
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_getter_lock_abort]:
  linked_registered_lock_abort_tac >>
  linked_registered_lock_abort_source_tac >>
  linked_registered_lock_abort_domain_tac >>
  linked_registered_lock_abort_finish_tac
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_getter_lock_success]:
  linked_registered_lock_success_tac >>
  linked_registered_locked_horizon_tac >>
  linked_registered_replay_tac >>
  linked_registered_return_layout_tac >>
  linked_registered_return_frame_tac >>
  linked_registered_structs_tac >>
  linked_registered_abi_targets_tac >>
  linked_registered_fragment_tac >>
  linked_registered_shadow_tac >>
  linked_registered_admissible_tac >>
  linked_registered_reachability_tac >>
  `immutable_section_layout_mods mods registered_env` by
    drule_then ACCEPT_TAC contract_inv_immutable_section_layout >>
  linked_registered_immutable_frame_tac >>
  linked_registered_storage_prefix_tac >>
  linked_registered_run_tac >>
  linked_registered_trace_inputs_tac >>
  linked_registered_compose_tac
    {horizon_tac = suspend "linked_linear_getter_trace_horizon",
     tails_tac = suspend "linked_linear_getter_trace_tails",
     exempt_tac = suspend "linked_linear_getter_trace_exempt",
     fallthrough_tac = suspend "linked_linear_getter_fallthrough",
     exit_tac = suspend "linked_linear_getter_exit",
     readings_tac = suspend "linked_linear_getter_trace_readings",
     finish_tac = suspend "linked_linear_getter_finish"}
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_getter_trace_horizon]:
  linked_registered_trace_horizon_tac
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_getter_trace_tails]:
  linked_registered_trace_tails_tac
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_getter_trace_exempt]:
  linked_registered_trace_exempt_tac
QED

val linked_positional_getter_no_fallthrough_tac =
  qx_genl_tac [`gx`,`res`,`ee`,`t`] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `?H G tn. valid_horizon _ _ H _ /\
     ?ce'. stmt_lands NoLoop body_end res t /\ _`
    (qx_choosel_then [`H`,`G`,`tn`] (CONJUNCTS_THEN2 kall_tac
       (qx_choose_then `final_env` (assume_tac o CONJUNCT1)))) >>
  `res = INL ()` by
    (qpat_assum `stmt_lands NoLoop body_end res t` mp_tac >>
     simp[NoAsms, loweringPostsTheory.stmt_lands_def]) >>
  linked_body_eval_tac >>
  `stmts_no_fallthrough fbody` by
    (qpat_assum `ret <> NoneT ==> stmts_no_fallthrough fbody`
       (drule_then ACCEPT_TAC)) >>
  drule_then mp_tac (cj 2 vyperTypeEvalProofsTheory.no_fallthrough_eval_no_success) >>
  disch_then (qspecl_then [`cx`,`es_lock with gas_obs := gx`,`ee with gas_obs := []`] mp_tac) >>
  qpat_assum `res = INL ()` (fn success =>
    qpat_assum `eval_stmts cx fbody (es_lock with gas_obs := gx) = _`
      (fn eval => simp[NoAsms, eval, success]));

Resume linked_runtime_dispatched_readings_certificate[linked_linear_getter_fallthrough]:
  linked_positional_getter_no_fallthrough_tac
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_getter_exit]:
  linked_registered_trace_exit_tac (suspend "linked_linear_getter_abort_or_halt")
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_getter_abort_or_halt]:
  linked_registered_abort_or_halt_tac
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_getter_trace_readings]:
  linked_registered_trace_readings_tac
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_getter_finish]:
  linked_registered_finish_tac
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_accepted_fallback]:
  `tx.function_name = "__default__" /\ tx.args = [] /\
    (list$EXISTS is_default_decl (main_module mods) \/ IS_SOME (exported_fallback mods exps))`
    suffices_by (disch_then (map_every assume_tac o CONJUNCTS) >>
      suspend "linked_linear_fallback_body")
  >> qpat_assum `calldata_dispatch_mods _ _ cd = SOME _` mp_tac >>
  qpat_assum `(if LENGTH cd < 4 then NONE else _) = NONE` (fn miss =>
    simp[NoAsms, calldata_dispatch_mods_def, LET_THM, miss, AllCaseEqs()])
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_body]:
  drule_then assume_tac (Q.INST [`name` |-> `"__default__"`] export_excludes_main_external) >>
  mp_tac (Q.INST [`guarded` |-> `nr`, `imp_ctors` |-> `imp_ctors`]
    (INST_TYPE [``:'a`` |-> ``:num``] default_miss_classified)) >>
  qpat_assum `tx.function_name = "__default__"` (fn name =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [name]) >> PURE_REWRITE_TAC [name] >>
    assume_tac name) >>
  simp_tac (srw_ss()) [GSYM markerTheory.Abbrev_def] >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE pure_ss [LET_THM] default_unit_linear_run) >>
  disch_then (qx_choose_then `actual_internals` strip_assume_tac) >>
  drule run_lowering_entry >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `fn` assume_tac)) >>
  `fn_entry_label fn = SOME "__entry"` by (drule_all_then ACCEPT_TAC run_lowering_entry_label) >>
  suspend "linked_linear_fallback_code"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_code]:
  `?ce pay key tr view rt.
    set_fallback_package_target rpolicy.rpol_target
      (package_fallback_fn_unit mods T (K global_nonreentrant_slot) fb) =
    SOME (ce,pay,nr,key,tr,view,
      subst_consts_stmts_mods (consts_env_mods mods) fbody,rt)` by
    (qpat_assum `fb = SOME (ALOOKUP exps "__default__",_)` SUBST1_TAC >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case =>
       simp[NoAsms, ret_case, package_fallback_fn_unit_def,
            set_fallback_package_target_def, LET_THM])) >>
  qpat_assum `set_fallback_package_target _ _ = SOME _` (fn fallback =>
    qpat_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _`
      (assume_tac o PURE_REWRITE_RULE [fallback])) >>
  drule_all run_lowering_fallback_interval_code >>
  disch_then (qx_choosel_then [`fl`,`ds`,`de`,`opened`,`check_start`,`body_start`,`body_last`]
    (map_every assume_tac o CONJUNCTS)) >>
  drule_all linked_classified_linear_routes >>
  disch_then (qspec_then `cd` (CONJUNCTS_THEN assume_tac)) >>
  `!fl. linear_dispatch_target cd (MAP (\(sel,lbl,z). (sel,lbl))
       (build_selectors (type_env_all_modules mods) (MAP SND exts))) fl = fl` by
    (qpat_assum `LENGTH cd < 4 \/ FIND _ _ = NONE ==> _` irule >>
     Cases_on `LENGTH cd < 4`
     >- (disj1_tac >> first_assum ACCEPT_TAC) >>
     disj2_tac >>
     qpat_assum `(if LENGTH cd < 4 then NONE else _) = NONE` mp_tac >>
     qpat_assum `~(LENGTH cd < 4)` (fn long => simp[NoAsms, long])) >>
  suspend "linked_linear_fallback_entry"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_entry]:
  `EVERY (\(sel,lbl). sel < 2 ** 32)
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env_all_modules mods) (MAP SND exts)))` by
    simp[NoAsms, linear_selectors_lt] >>
  drule_then strip_assume_tac lower_vyper_runtime_unit_raw_shape_mods >>
  drule_all linked_linear_dispatch_entry_path >>
  disch_then (qx_choosel_then [`hit`,`Gh`,`tnh`]
    (map_every assume_tac o CONJUNCTS)) >>
  `hit.vs_current_bb = fl` by
    (qpat_assum `hit.vs_current_bb = _` SUBST1_TAC >>
     qpat_assum `Abbrev (cd = _)`
       (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `!fl. linear_dispatch_target cd _ fl = fl`
       (qspec_then `fl` ACCEPT_TAC)) >>
  `check_start.cs_current_bb = fl` by
    (qpat_assum `new_block fl opened = (_,check_start)`
       (mp_tac o AP_TERM ``\p:string # compile_state. (SND p).cs_current_bb``) >>
     simp[NoAsms, new_block_def, LET_THM]) >>
  `hit.vs_call_ctx.cc_callvalue = n2w tx.value` by
    (qpat_assum `hit.vs_call_ctx = vs.vs_call_ctx` SUBST1_TAC >>
     qpat_assum `initial_venom_state_rel_mods mods am tx vs` mp_tac >>
     simp[NoAsms, initial_venom_state_rel_mods_def, venom_env_rel_def,
          call_ctx_rel_def]) >>
  suspend "linked_linear_fallback_value_guard"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_value_guard]:
  `pay = (mut = Payable)` by
    (qpat_assum `set_fallback_package_target _ _ = SOME _` mp_tac >>
     qpat_assum `fb = SOME (ALOOKUP exps "__default__",_)` SUBST1_TAC >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case =>
       simp[NoAsms, ret_case, package_fallback_fn_unit_def,
            set_fallback_package_target_def, LET_THM])) >>
  Q.SUBGOAL_THEN `pay \/ hit.vs_call_ctx.cc_callvalue = 0w` ASSUME_TAC
  >- (qpat_assum `pay = (mut = Payable)` SUBST1_TAC >>
      qpat_assum `hit.vs_call_ctx.cc_callvalue = n2w tx.value` SUBST1_TAC >>
      qpat_assum `mut = Payable \/ cx.txn.value = 0` mp_tac >>
      simp[NoAsms, Abbr `cx`, initial_evaluation_context_def] >>
      disch_then (DISJ_CASES_THEN (fn accepted => simp[NoAsms, accepted]))) >>
  `fresh_vars_wrt check_start hit` by
    (MATCH_MP_TAC (Q.SPECL [`de`,`check_start`,`hit`] fresh_vars_wrt_mono) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     `ci_mono de opened /\ ci_mono opened check_start` by
       (conj_tac
        >- (qpat_assum `compile_external_fn_bodies _ de = ((),opened)` (fn opened =>
              mp_tac (PART_MATCH (rand o rand) entry_legacy_jobs_ci_mono
                        (lhs (concl opened))) >>
              simp[NoAsms, opened])) >>
        qpat_assum `new_block fl opened = (_,check_start)` (fn check =>
          mp_tac (Q.SPECL [`fl`,`opened`] ci_mono_new_block) >>
          simp[NoAsms, check])) >>
     qpat_assum `ci_mono de opened` (fn left =>
       qpat_assum `ci_mono opened check_start`
         (mp_tac o MATCH_MP ci_mono_trans o CONJ left)) >>
     simp[NoAsms, ci_mono_def, arithmeticTheory.GREATER_EQ]) >>
  mp_tac (Q.INST [`PG` |-> `[]`, `lo` |-> `0`, `ctx` |-> `unit.cu_context`,
    `fn` |-> `fn`, `s` |-> `hit`, `pay` |-> `pay`, `st` |-> `check_start`,
    `st'` |-> `body_start`, `tn` |-> `tnh`, `G` |-> `Gh`]
      (SPEC_ALL compile_entry_value_check_ptr_endpoint)) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    strip_tac >> first_assum ACCEPT_TAC, asm_rewrite_tac[] >> simp[NoAsms]]) >>
  disch_then (qx_choosel_then [`fallback_body_vs`,`fallback_body_G`,`fallback_body_taint`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `compile_guarded_body ce nr key tr view _ rt body_start = ((),body_last)`
    (fn guarded => qpat_assum `fn_has_code body_start body_last fn`
      (mp_tac o MATCH_MP guarded_body_code_from_registration o CONJ guarded)) >>
  disch_then (qx_choosel_then [`fallback_locked`,`fallback_body_end`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "linked_linear_fallback_guarded_body"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_guarded_body]:
  qabbrev_tac `fallback_code = subst_consts_stmts_mods (consts_env_mods mods) fbody` >>
  `fall = SOME (ce,pay,nr,key,tr,view,fallback_code,rt)` by
    (qpat_assum `Abbrev (fall = _)`
       (fn alias => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] alias]) >>
     simp_tac bool_ss [Abbr `fallback_code`] >> first_assum ACCEPT_TAC) >>
  Q.SUBGOAL_THEN `?fallback_shadow_fn.
     lookup_function "__entry" shadow_unit.cu_context.ctx_functions =
       SOME fallback_shadow_fn /\ gas_shadow_function fn fallback_shadow_fn`
    (qx_choose_then `fallback_shadow_fn` (map_every assume_tac o CONJUNCTS))
  >- (qspecl_then [`unit.cu_context.ctx_functions`,
         `shadow_unit.cu_context.ctx_functions`,`"__entry"`] mp_tac
       gas_shadow_lookup_function >>
     impl_tac
     >- (qpat_assum `gas_shadow_context unit.cu_context shadow_unit.cu_context`
           (map_every assume_tac o CONJUNCTS o REWRITE_RULE [gas_shadow_context_def]) >>
         first_assum ACCEPT_TAC) >>
     qpat_assum `lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn`
       (fn found => simp[NoAsms, OPTREL_def, found, AllCaseEqs()])) >>
  `EVERY (\(l,c,p,m,py,n,k,t,v,b,r). jump_label_ok l)
     (MAP gas_shadow_external_package packs)` by
    (qpat_assum `Abbrev (packs = MAP _ exts)`
       (fn alias => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] alias]) >>
     simp[NoAsms, EVERY_MAP, EVERY_MEM] >>
     qx_gen_tac `external_decl` >> PairCases_on `external_decl` >>
     simp[NoAsms, package_external_fn_unit_def, set_external_package_target_def,
          gas_shadow_external_package_def, jump_label_ok_def]) >>
  `EVERY (\d. internal_label_ok (FST d))
      (internal_fn_descriptors (MAP gas_shadow_internal_package ips))` by
    (PURE_REWRITE_TAC [gas_shadow_internal_fn_descriptors] >>
     qpat_assum `Abbrev (ips = _)`
       (fn alias => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] alias]) >>
     simp[NoAsms, unit_package_internal_labels]) >>
  qpat_assum `fall = SOME (ce,pay,nr,key,tr,view,fallback_code,rt)` (fn fallback =>
    qpat_assum `run_lowering sels (MAP gas_shadow_external_package packs) _
      (OPTION_MAP gas_shadow_fallback_package fall) _ _ _ _ _ _ = SOME shadow_unit`
      (assume_tac o REWRITE_RULE [fallback, optionTheory.OPTION_MAP_DEF,
                                  gas_shadow_fallback_package_def])) >>
  drule_all (Q.INST [`u` |-> `shadow_unit`, `efn` |-> `fallback_shadow_fn`]
    run_lowering_fallback_interval_code) >>
  disch_then (qx_choosel_then [`shadow_fl`,`shadow_ds`,`shadow_de`,`shadow_opened`,
      `shadow_check_start`,`shadow_body_start`,`shadow_body_last`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "linked_linear_fallback_shadow_pair"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_shadow_pair]:
  `shadow_fl = fl /\ shadow_ds = ds` by
    (qpat_assum `fresh_label "fallback" (initial_compile_state "__entry") = (shadow_fl,shadow_ds)` mp_tac >>
     qpat_assum `fresh_label "fallback" (initial_compile_state "__entry") = (fl,ds)`
       (fn label => simp[NoAsms, label])) >>
  `shadow_de = de` by
    (qpat_assum `compile_selector_dispatch_linear (MAP _ sels) shadow_fl shadow_ds = ((),shadow_de)`
       mp_tac >>
     qpat_assum `Abbrev (sels = _)` (fn sels =>
       qpat_assum `shadow_fl = fl` (fn label =>
         qpat_assum `shadow_ds = ds` (fn start =>
           qpat_assum `compile_selector_dispatch_linear _ fl ds = ((),de)` (fn real =>
             simp[NoAsms, REWRITE_RULE [markerTheory.Abbrev_def] sels, label, start, real]))))) >>
  `gas_shadow_state opened shadow_opened` by
    (qspec_then `packs` (mp_tac o REWRITE_RULE [gas_shadow_compiles_def])
       gas_shadow_compiles_compile_external_fn_bodies >>
     disch_then (qspecl_then [`de`,`shadow_de`] mp_tac) >>
     qpat_assum `Abbrev (packs = MAP _ exts)` (fn packs =>
       qpat_assum `shadow_de = de` (fn same =>
         qpat_assum `compile_external_fn_bodies _ de = ((),opened)` (fn real =>
           qpat_assum `compile_external_fn_bodies (MAP gas_shadow_external_package packs) shadow_de =
                ((),shadow_opened)` (fn shadow =>
             simp[NoAsms, real, same, gas_shadow_state_refl,
               REWRITE_RULE [markerTheory.Abbrev_def, same] packs,
               PURE_REWRITE_RULE [same, REWRITE_RULE [markerTheory.Abbrev_def] packs] shadow]))))) >>
  `gas_shadow_state check_start shadow_check_start` by
    (mp_tac (Q.INST [`label` |-> `fl`] gas_shadow_compiles_new_block) >>
     PURE_REWRITE_TAC [gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`opened`,`shadow_opened`] mp_tac) >>
     qpat_assum `shadow_fl = fl` (fn label =>
       qpat_assum `new_block shadow_fl shadow_opened = _` (fn shadow =>
         qpat_assum `new_block fl opened = _` (fn real =>
           qpat_assum `gas_shadow_state opened shadow_opened` (fn pair =>
             simp[NoAsms, real, PURE_REWRITE_RULE [label] shadow, pair])))) >>
     disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  `gas_shadow_state body_start shadow_body_start` by
    (mp_tac (Q.INST [`min_cds` |-> `4`, `payable` |-> `pay`]
       gas_shadow_compiles_compile_entry_checks) >>
     PURE_REWRITE_TAC [gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`check_start`,`shadow_check_start`] mp_tac) >>
     qpat_assum `compile_entry_checks 4 pay check_start = ((),body_start)` (fn real =>
       qpat_assum `compile_entry_checks 4 pay shadow_check_start = ((),shadow_body_start)` (fn shadow =>
         qpat_assum `gas_shadow_state check_start shadow_check_start` (fn pair =>
           simp[NoAsms, real, shadow, pair])))) >>
  qpat_assum `compile_guarded_body (gas_shadow_env T ce) nr key tr view
       (MAP gas_shadow_stmt fallback_code) rt shadow_body_start = ((),shadow_body_last)`
    (fn guarded => qpat_assum `fn_has_code shadow_body_start shadow_body_last fallback_shadow_fn`
      (mp_tac o MATCH_MP guarded_body_code_from_registration o CONJ guarded)) >>
  disch_then (qx_choosel_then [`shadow_fallback_locked`,`shadow_fallback_body_end`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "linked_linear_fallback_paired_guard_execution"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_paired_guard_execution]:
  `vars_pc_only vs fallback_body_vs` by
    (irule vars_pc_only_trans >> qexists_tac `hit` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `fallback_body_taint.t_mem = {} /\ fallback_body_taint.t_stor = {} /\
    fallback_body_taint.t_trans = {} /\ fallback_body_taint.t_imm = {}` by
    (rpt conj_tac >> first_assum (fn eq => SUBST1_TAC eq >> first_assum ACCEPT_TAC)) >>
  qabbrev_tac `fallback_site = ARB:instruction` >>
  mp_tac (Q.INST [`ctx` |-> `unit.cu_context`, `initial` |-> `vs`,
       `s` |-> `fallback_body_vs`, `mc` |-> `4`, `opened` |-> `check_start`,
       `checked` |-> `body_start`, `tn` |-> `fallback_body_taint`, `site` |-> `fallback_site`]
       linked_post_checks_resources) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "linked_linear_fallback_empty_register"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_empty_register]:
  `bind_arguments (type_env_all_modules mods) args tx.args = SOME FEMPTY` by
    (qpat_assum `args = []` SUBST1_TAC >>
     qpat_assum `tx.args = []` SUBST1_TAC >>
     simp[NoAsms, bind_arguments_def]) >>
  `env = FEMPTY` by
    (qpat_assum `bind_arguments _ args tx.args = SOME FEMPTY`
       (fn bind => qpat_assum `bind_arguments _ args tx.args = SOME env`
         (ACCEPT_TAC o GSYM o PURE_REWRITE_RULE [bind, optionTheory.SOME_11]))) >>
  `ce.ce_vars = FEMPTY` by
    (qpat_assum `set_fallback_package_target _ _ = SOME _` mp_tac >>
     qpat_assum `fb = SOME (ALOOKUP exps "__default__",_)` SUBST1_TAC >>
     qpat_assum `args = []` (fn args =>
       Cases_on `ret = NoneT` >>
       pop_assum (fn ret_case =>
         simp[NoAsms, args, ret_case, package_fallback_fn_unit_def,
              set_fallback_package_target_def, LET_THM, build_compile_env_unit_def,
              update_cenv_ret_abi_def, update_cenv_nonreentrant_def, allocate_args_def,
              pairTheory.ELIM_UNCURRY])) >>
     strip_tac >>
     qpat_assum `_ = ce` (SUBST1_TAC o SYM) >> simp[NoAsms]) >>
  `local_ptrs_rel fn ce [env] fallback_body_vs` by
    (qpat_assum `ce.ce_vars = FEMPTY` (fn vars =>
       simp[NoAsms, vars, local_ptrs_rel_def, local_region_def])) >>
  suspend "linked_linear_fallback_state_relation"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_state_relation]:
  `set_external_package_target rpolicy.rpol_target
    (package_external_fn_unit mods T (K global_nonreentrant_slot)
      (src,subst_consts_fn_mods (consts_env_mods mods)
        (mut,nr,lookup_raw_return_or_F src "__default__" External tops,
         "__default__",args,[],ret,fbody))) =
    ("fn___default__",ce,[],4,pay,nr,key,tr,view,fallback_code,rt)` by
    (qpat_assum `set_fallback_package_target _ _ = SOME _` mp_tac >>
     qpat_assum `fb = SOME (ALOOKUP exps "__default__",_)` SUBST1_TAC >>
     qpat_assum `args = []` (fn args =>
       simp[NoAsms, Abbr `src`, Abbr `fallback_code`, args,
            package_fallback_fn_unit_def, set_fallback_package_target_def,
            package_external_fn_unit_def, set_external_package_target_def,
            subst_consts_fn_mods_def, subst_consts_expr_mods_def,
            build_positional_args_def, min_calldata_size_def, LET_THM]) >>
     strip_tac >>
     qpat_assum `mut = View <=> view` (SUBST1_TAC o SYM) >> asm_rewrite_tac[]) >>
  `compile_register_positional_args ce [] 4 body_start = (ce,body_start)` by
    simp[NoAsms, compile_register_positional_args_def, comp_return_def] >>
  `vars_pc_only (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                vs_inst_idx := 0|>) fallback_body_vs` by
    (qpat_assum `vars_pc_only vs fallback_body_vs` mp_tac >>
     simp[NoAsms, vars_pc_only_def, venomStateTheory.venom_state_component_equality]) >>
  qpat_assum `default_registration_resources _ _ _ _ body_start fallback_body_vs _`
    (strip_assume_tac o REWRITE_RULE [default_registration_resources_def]) >>
  qpat_assum `default_registration_entry_frame vs fallback_body_vs`
    (strip_assume_tac o REWRITE_RULE [default_registration_entry_frame_def]) >>
  `alloca_frontier_inv unit.cu_context fn fallback_site fallback_body_vs` by
    (qpat_assum `alloca_frontier_inv_from 0 _ _ _ _` mp_tac >>
     simp[NoAsms, alloca_frontier_inv_def, alloca_frontier_inv_from_def]) >>
  `fallback_body_vs.vs_allocas = FEMPTY` by
    (qpat_assum `vars_pc_only vs fallback_body_vs`
       (assume_tac o MATCH_MP (SPEC_ALL vars_pc_only_allocas)) >>
     qpat_assum `initial_venom_state_rel_mods _ _ _ vs` mp_tac >>
     simp[NoAsms, initial_venom_state_rel_mods_def] >> rpt strip_tac >> asm_rewrite_tac[]) >>
  qpat_assum `initial_venom_state_rel_mods _ _ _ vs`
    (strip_assume_tac o PURE_REWRITE_RULE [initial_venom_state_rel_mods_def]) >>
  `send_call_value mut (initial_evaluation_context am.sources am.layouts tx src)
      (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
      (INL (),es0)` by
    (qpat_assum `Abbrev (cx = _)` (fn cx =>
       PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] cx)]) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `!H:(bool # 256 word # type_value) list # num list.
    stmt_state_rel H unit.cu_context fn ce cx es0 fallback_body_vs /\
    ghost_inv H NONE ce cx es0 fallback_body_G fallback_body_taint fallback_body_vs` by
    (gen_tac >>
     qpat_assum `Abbrev (cx = _)` (fn cx =>
       PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] cx]) >>
     mp_tac (Q.INST [`efn` |-> `fn`, `cenv0` |-> `ce`, `cenv` |-> `ce`,
       `pos_args` |-> `[]`, `mincd` |-> `4`, `ut'` |-> `tr`, `iv` |-> `view`,
       `lowered_body` |-> `fallback_code`, `st` |-> `body_start`, `sa` |-> `body_start`,
       `elbl` |-> `"__entry"`, `lbl` |-> `"fn___default__"`,
       `s0` |-> `fallback_body_vs`, `s1` |-> `fallback_body_vs`, `tvs` |-> `[]`,
       `site` |-> `fallback_site`, `G0` |-> `fallback_body_G`,
       `tn0` |-> `fallback_body_taint`]
        (Q.INST_TYPE [`:'a` |-> `:256`]
          registration_actual_endpoint_relations_from_prefix_mods)) >>
     impl_tac
     >- (qpat_assum `args = []` (fn noargs =>
          qpat_assum `fallback_body_vs.vs_allocas = FEMPTY` (fn empty =>
          qpat_assum `tx.function_name = "__default__"` (fn name =>
            simp[noargs, empty, name, Abbr `src`]))) >>
         rpt conj_tac >>
         FIRST [first_assum ACCEPT_TAC,
           qpat_assum `set_external_package_target _ _ = ("fn___default__",ce,[],4,pay,nr,key,tr,view,fallback_code,rt)`
             mp_tac >>
           qpat_assum `args = []` (fn noargs =>
             qpat_assum `pay = (mut = Payable)` (fn payment =>
               simp[NoAsms, noargs, payment]))]) >>
     disch_then ACCEPT_TAC) >>
  suspend "linked_linear_fallback_body_invariant"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_body_invariant]:
  qabbrev_tac `fallback_base =
    build_compile_env_unit mods src External mut "__default__" args ret fallback_code T` >>
  `contract_inv mods exps unit.cu_context
    (fallback_base with ce_target := rpolicy.rpol_target) cx` by
    (qpat_assum `!mut args ret ss. contract_inv _ _ _ _ _`
       (qspecl_then [`mut`,`args`,`ret`,`fallback_code`] mp_tac) >>
     qpat_assum `tx.function_name = "__default__"` (fn name =>
       simp[NoAsms, name, Abbr `fallback_base`])) >>
  `ce =
    update_cenv_nonreentrant
      (if ret = NoneT then fallback_base with ce_raw_return :=
        lookup_raw_return_or_F src "__default__" External tops
       else update_cenv_ret_abi
         (fallback_base with ce_raw_return :=
           lookup_raw_return_or_F src "__default__" External tops) ret)
      nr global_nonreentrant_slot T (mut = View)
    with ce_target := rpolicy.rpol_target /\
    key = global_nonreentrant_slot /\ tr /\ view = (mut = View) /\
    rt = (if ret = NoneT then NONE else SOME ret)` by
    (qpat_assum `set_fallback_package_target _ _ = SOME _` mp_tac >>
     qpat_assum `fb = SOME (ALOOKUP exps "__default__",_)` SUBST1_TAC >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case =>
       simp[NoAsms, ret_case, Abbr `fallback_base`, Abbr `src`,
            Abbr `fallback_code`, LET_THM, combinTheory.K_THM,
            package_fallback_fn_unit_def, set_fallback_package_target_def]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `mut = View <=> view` (fn view_eq => PURE_REWRITE_TAC [GSYM view_eq]) >>
     rpt conj_tac >> first_assum (fn eq =>
       FIRST [ACCEPT_TAC eq, ACCEPT_TAC (SYM eq)])) >>
  `module_body_inv mods src tops ce cx` by
    (qpat_assum `ce = _` SUBST1_TAC >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case =>
       simp[NoAsms, ret_case, module_body_inv_def, Abbr `fallback_base`,
            Abbr `src`, build_compile_env_unit_def, pairTheory.ELIM_UNCURRY,
            update_cenv_nonreentrant_def, update_cenv_ret_abi_def]) >>
     first_assum ACCEPT_TAC) >>
  `contract_inv mods exps unit.cu_context ce cx` by
    (qpat_assum `contract_inv mods exps _ (fallback_base with ce_target := _) cx` mp_tac >>
     qpat_assum `ce = _` SUBST1_TAC >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case =>
       simp[NoAsms, ret_case, contract_inv_def, cenv_module_pins_mods_def,
            immutable_section_layout_mods_def,
            update_cenv_nonreentrant_def, update_cenv_ret_abi_def]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     asm_rewrite_tac[] >> rpt conj_tac >>
     FIRST [
       qpat_assum `fallback_base.ce_struct_fields = _`
         (fn fields => PURE_REWRITE_TAC [GSYM fields] >> first_assum ACCEPT_TAC),
       qpat_assum `fallback_base.ce_module_vars = _`
         (fn locations => PURE_REWRITE_TAC [GSYM locations] >> first_assum ACCEPT_TAC),
       rpt gen_tac >> strip_tac >>
       qpat_assum `!sid ts. ALOOKUP mods sid = SOME ts ==> supported_module_headers ts /\ _`
         (drule_then (fn headers => simp[NoAsms, headers]))]) >>
  suspend "linked_linear_fallback_source_frame"
QED

val linked_empty_source_frame_tac =
  `get_module_code cx src = SOME tops` by
    drule_all_then ACCEPT_TAC contract_inv_module_code >>
  `es0.scopes = [env] /\ es0.immutables = am.immutables /\
    es0.outcomes = SOME vs.vs_outcomes /\ es0.requests = [] /\
    state_well_typed es0 /\ accounts_well_typed es0.accounts` by
    drule_all_then ACCEPT_TAC external_body_prefix_state >>
  `popped_keys_indexed es0.scopes` by
    (qpat_assum `es0.scopes = [env]` SUBST1_TAC >>
     qpat_assum `env = FEMPTY` SUBST1_TAC >>
     simp[NoAsms, popped_keys_indexed_def]) >>
  `module_allocated am.layouts tx.target src tops` by
    (qpat_assum `module_body_inv mods src tops ce cx`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [module_body_inv_def]) >>
     Cases_on `src`
     >- drule_all_then ACCEPT_TAC check_contract_main_module_allocated >>
     rename1 `ALOOKUP mods (SOME sid) = SOME tops` >>
     `MEM ("__default__",sid) exps` by
       (irule ALOOKUP_MEM >>
        qpat_assum `Abbrev (SOME sid = _)` mp_tac >>
        qpat_assum `tx.function_name = "__default__"`
          (fn name => simp[NoAsms, name, markerTheory.Abbrev_def])) >>
     qpat_assum `exports_ok _ _ mods exps`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [exports_ok_def]) >>
     simp[NoAsms, EVERY_MEM, FORALL_PROD] >>
     disch_then (qspecl_then [`"__default__"`,`sid`] mp_tac) >>
     qpat_assum `ALOOKUP mods (SOME sid) = SOME tops` (fn lookup =>
       qpat_assum `MEM ("__default__",sid) exps` (fn exported =>
         simp[NoAsms, lookup, exported]))) >>
  `int_calls_stmts fallback_code = int_calls_stmts fbody` by
    (qpat_assum `check_contract F _ _ mods = SOME art`
       (fn checked => qpat_assum `Abbrev (fallback_code = _)` (fn body =>
          PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] body,
            CONJUNCT2 (MATCH_MP checked_subst_consts_int_calls_mods checked)])) >>
     REFL_TAC);

val linked_empty_source_declaration_tac =
  `ALL_DISTINCT (MAP FST exps)` by
    drule_then (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2) exports_ok_names >>
  Q.SUBGOAL_THEN
    `?fm fg fr fargs fdefaults frt fstmts.
      MEM (FunctionDecl External fm fg fr "__default__" fargs fdefaults frt fstmts) tops`
    (qx_choosel_then [`fm`,`fg`,`fr`,`fargs`,`fdefaults`,`frt`,`fstmts`] assume_tac)
  >- (map_every (fn pat => qpat_assum pat mp_tac)
        [`list$EXISTS is_default_decl (main_module mods) \/ _`,
         `ALOOKUP mods (ALOOKUP exps "__default__") = SOME tops`,
         `ALL_DISTINCT (MAP FST exps)`,
         `MEM "__default__" (MAP FST exps) ==> ~MEM (NONE,"__default__") _`] >>
      POP_ASSUM_LIST (K ALL_TAC) >> ntac 3 (disch_then assume_tac) >>
      disch_then (DISJ_CASES_THEN assume_tac)
      >- (Cases_on `ALOOKUP mods NONE` >> fs[main_module_def] >>
          rename1 `ALOOKUP mods NONE = SOME main` >>
          qpat_x_assum `list$EXISTS is_default_decl main`
            (strip_assume_tac o REWRITE_RULE [EXISTS_MEM]) >>
          rename1 `is_default_decl decl` >> Cases_on `decl` >>
          fs[is_default_decl_def] >> Cases_on `f` >> fs[is_default_decl_def] >>
          `ALOOKUP exps "__default__" = NONE` by
            (simp[ALOOKUP_NONE] >> disch_tac >>
             qpat_x_assum `MEM "__default__" (MAP FST exps) ==> _` drule >>
             simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
             goal_assum (drule_at Any) >> simp[external_name_keys_toplevel_def]) >>
          gvs[] >> goal_assum (drule_at Any) >> simp[]) >>
      Cases_on `exported_fallback mods exps` >> fs[] >>
      PairCases_on `x` >>
      rename1 `exported_fallback mods exps = SOME (owner,decl)` >>
      drule_then (qx_choosel_then [`n`,`owner_tops`] strip_assume_tac) exported_fallback_slot >>
      qpat_x_assum `owner = SOME n` SUBST_ALL_TAC >>
      `ALOOKUP exps "__default__" = SOME n` by
        drule_all_then ACCEPT_TAC ALOOKUP_ALL_DISTINCT_MEM >>
      `owner_tops = tops` by gvs[] >>
      qpat_x_assum `owner_tops = tops` SUBST_ALL_TAC >>
      PairCases_on `decl` >>
      rename1 `FST (SND (SND (FOLDR classify_function _ tops))) =
        SOME (m,g,r,name,aa,ds,rty,ss)` >>
      `name = "__default__"` by
        (`FST (SND (SND (classify_functions tops))) =
            SOME (m,g,r,name,aa,subst_consts_exprs (module_consts_env tops []) ds,
              rty,subst_consts_stmts (module_consts_env tops []) ss)` by
           (Cases_on `FOLDR classify_function ([],[],NONE,NONE) tops` >>
            PairCases_on `r'` >> gvs[classify_functions_def, subst_consts_fn_def]) >>
         drule_then ACCEPT_TAC runtimeFallbackSourceAlignmentTheory.classified_fallback_name) >>
      qpat_x_assum `name = "__default__"` SUBST_ALL_TAC >>
      drule_then assume_tac loweringShapePropsTheory.classify_fold_fallback_mem >>
      goal_assum (drule_at Any) >> simp[]) >>
  `ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (ALOOKUP exps "__default__")) tops))` by
    drule_all_then ACCEPT_TAC source_typing_ok_mods_external_names_distinct >>
  `MEM (FunctionDecl External mut nr
      (lookup_raw_return_or_F (ALOOKUP exps "__default__") "__default__" External tops)
      "__default__" args [] ret fbody) tops` by
    (qpat_assum `vyperInterpreter$lookup_function (ALOOKUP exps "__default__") "__default__" External tops = SOME _`
       (mp_tac o MATCH_MP lookup_function_external_raw_cases) >>
     disch_then (DISJ_CASES_THEN strip_assume_tac)
     >- (qpat_assum `lookup_raw_return (ALOOKUP exps "__default__") "__default__" External tops = SOME _`
           (fn raw => simp[NoAsms, lookup_raw_return_or_F_def, raw]) >>
         first_assum ACCEPT_TAC) >>
     `MEM (ALOOKUP exps "__default__","__default__")
       (external_name_keys_toplevel (ALOOKUP exps "__default__") decl)` by
       (qpat_assum `is_public_getter_decl "__default__" decl` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        Cases_on `decl` >> simp[is_public_getter_decl_def] >>
        Cases_on `v` >> simp[is_public_getter_decl_def, external_name_keys_toplevel_def]) >>
     `decl = FunctionDecl External fm fg fr "__default__" fargs fdefaults frt fstmts` by
       (drule all_distinct_flat_map_unique >>
        disch_then irule >>
        map_every (fn pat => qpat_assum pat mp_tac)
          [`MEM decl tops`,
           `MEM (FunctionDecl External fm fg fr "__default__" fargs fdefaults frt fstmts) tops`,
           `MEM (ALOOKUP exps "__default__","__default__")
             (external_name_keys_toplevel (ALOOKUP exps "__default__") decl)`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[external_name_keys_toplevel_def]) >>
     qpat_x_assum `decl = FunctionDecl External fm fg fr "__default__" fargs fdefaults frt fstmts` SUBST_ALL_TAC >>
     qpat_assum `is_public_getter_decl "__default__" _` mp_tac >>
     simp[NoAsms,is_public_getter_decl_def]) >>
  `MEM (FunctionDecl External mut nr
      (lookup_raw_return_or_F src tx.function_name External tops)
      tx.function_name args [] ret fbody) tops` by
    (qpat_assum `tx.function_name = "__default__"` (fn name =>
       simp[NoAsms, name, Abbr `src`]) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `module_body_inv mods src tops ce cx`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [module_body_inv_def]) >>
  `call_evaluation_safe cx (int_calls_stmts fallback_code)` by
    (qpat_assum `int_calls_stmts fallback_code = int_calls_stmts fbody` SUBST1_TAC >>
     qpat_assum `Abbrev (cx = _)`
       (fn cx_eq => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] cx_eq]) >>
     drule_all_then ACCEPT_TAC checked_explicit_external_body_call_evaluation_safe);

val linked_empty_source_checked_tac =
  `check_function_body am.layouts tx.target mods art src External mut nr args [] ret fbody` by
    (`External <> Deploy` by simp[NoAsms] >>
     drule_all_then ACCEPT_TAC check_contract_runtime_function_body_MEM) >>
  `stmts_loop_calls_ok mods fallback_code` by
    (qpat_assum `!sid ts vis mut nr raw name args dflts ret body.
         ALOOKUP mods sid = SOME ts /\ _ ==> _`
       (qspecl_then [`src`,`tops`,`External`,`mut`,`nr`,
          `lookup_raw_return_or_F src tx.function_name External tops`,
          `tx.function_name`,`args`,`[]`,`ret`,`fbody`] mp_tac) >>
     qpat_assum `Abbrev (fallback_code = _)` (fn body =>
       PURE_ONCE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] body)]) >>
     disch_then match_mp_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  `checked_contract_runtime_ready art mods am tx` by
    (drule_all source_typing_ok_runtime_ready_mods >>
     qpat_assum `check_contract F am.layouts tx.target mods = SOME art` (fn checked =>
       simp[NoAsms, checked])) >>
  `context_well_typed cx` by
    (qpat_assum `call_tx_well_typed tx` mp_tac >>
     simp[NoAsms, call_tx_well_typed_def, context_well_typed_def,
          Abbr `cx`, initial_evaluation_context_def]) >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx es0.immutables` by
    (qpat_assum `checked_contract_runtime_ready art mods am tx`
       (mp_tac o REWRITE_RULE [checked_contract_runtime_ready_def]) >>
     qpat_assum `es0.immutables = am.immutables` SUBST1_TAC >>
     strip_tac >>
     qpat_assum `Abbrev (cx = _)` (fn context_eq =>
       PURE_ONCE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] context_eq]) >>
     qpat_assum `immutables_ready _ _ (initial_evaluation_context _ _ _ NONE) _`
       (fn ready => ACCEPT_TAC (MATCH_MP immutables_ready_initial_evaluation_context_source ready))) >>
  `env_consistent (artifact_env art mods src) cx es0 /\ functions_well_typed cx` by
    (mp_tac (Q.INST [`st` |-> `es0`] (SPEC_ALL checked_external_empty_frame_ready)) >>
     impl_tac
     >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[NoAsms, Abbr `cx`]]) >>
     `es0 with scopes := [FEMPTY] = es0` by
       (qpat_assum `es0.scopes = [env]` (fn scopes =>
         qpat_assum `env = FEMPTY` (fn empty =>
           simp[NoAsms, evaluation_state_component_equality, scopes, empty]))) >>
     pop_assum (fn scopes => PURE_REWRITE_TAC [scopes]) >>
     disch_then (fn frame => CONJ_TAC >- ACCEPT_TAC (cj 1 frame) >> ACCEPT_TAC (cj 3 frame)));

val linked_empty_source_static_env_tac =
  qabbrev_tac `fallback_types = artifact_env art mods src` >>
  `~cx.in_deploy /\ check_contract F cx.layouts cx.txn.target mods = SOME art` by
    (qpat_assum `check_contract F am.layouts tx.target mods = SOME art` (fn checked =>
       simp[NoAsms, Abbr `cx`, initial_evaluation_context_def, checked])) >>
  `get_tenv cx = type_env_all_modules mods /\ ALOOKUP cx.sources cx.txn.target = SOME mods` by
    (qpat_assum `ALOOKUP am.sources tx.target = SOME mods` (fn sources =>
       simp[NoAsms, Abbr `cx`, initial_evaluation_context_def, get_tenv_def, sources])) >>
  `art.cta_bare_global_assignable = FEMPTY` by
    drule_then ACCEPT_TAC check_contract_runtime_assignable >>
  `frame_maps fallback_types art /\
   fallback_types.current_src = src /\
   fallback_types.fn_sigs = art.cta_fn_sigs /\
   fallback_types.toplevel_vtypes = art.cta_toplevel_vtypes /\
   fallback_types.bare_globals = art.cta_bare_globals /\
   fallback_types.bare_global_assignable = FEMPTY /\
   fallback_types.var_types = FEMPTY` by
    (qpat_assum `art.cta_bare_global_assignable = FEMPTY` (fn writable =>
       simp[NoAsms, Abbr `fallback_types`, frame_maps_def, artifact_env_def, writable])) >>
  `fallback_types.type_defs = get_tenv cx` by
    (qpat_assum `get_tenv cx = type_env_all_modules mods` (fn tenv =>
       simp[NoAsms, Abbr `fallback_types`, artifact_env_def, tenv])) >>
  `imm_len_mods mods < 24576` by
    (PURE_ONCE_REWRITE_TAC [imm_len_mods_def] >> first_assum ACCEPT_TAC) >>
  `IS_SOME es0.outcomes /\ outcomes_accounts_typed es0.outcomes` by
    (qpat_assum `es0.outcomes = SOME vs.vs_outcomes` (fn out => simp[NoAsms, out]) >>
     first_assum ACCEPT_TAC) >>
  `(!id ty. FLOOKUP fallback_types.var_types id = SOME ty ==>
      ?p sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)) /\
   (!id ty. FLOOKUP fallback_types.var_types id = SOME ty ==> ce.ce_var_type id = SOME ty)` by
    (qpat_assum `fallback_types.var_types = FEMPTY` (fn vars => simp[NoAsms, vars])) >>
  `expr_sim_inv_mods mods ce cx fallback_types es0` by
    drule_all_then ACCEPT_TAC linked_external_entry_expr_sim_inv_mods >>
  `body_const_cells_agree_mods mods cx fallback_types es0` by
    (`(case ALOOKUP es0.immutables cx.txn.target of
          NONE => empty_immutables | SOME cells => cells) =
         account_immutables am tx.target` by
       (qpat_assum `es0.immutables = am.immutables` (fn imms =>
          simp[NoAsms, imms, Abbr `cx`, initial_evaluation_context_def,
               account_immutables_def])) >>
     MATCH_MP_TAC (Q.INST [`art` |-> `art`,`imms` |-> `account_immutables am tx.target`]
       checked_body_const_cells_agree_mods) >>
     qpat_assum `~cx.in_deploy` (fn runtime => simp[NoAsms, runtime]) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, first_assum (ACCEPT_TAC o SYM)]);

val linked_empty_source_typed_tac =
  `function_entry_env art mods src External args = fallback_types` by
    (qpat_assum `args = []` (fn noargs =>
       simp[NoAsms, noargs, Abbr `fallback_types`, function_entry_env_def])) >>
  Q.SUBGOAL_THEN
    `check_contract F am.layouts tx.target mods = SOME art /\
     ALOOKUP mods src = SOME tops /\
     MEM (FunctionDecl External mut nr
       (lookup_raw_return_or_F src tx.function_name External tops)
       tx.function_name args [] ret fbody) tops /\
     (F ==> External = Deploy) /\
     check_function_body am.layouts tx.target mods art src External mut nr args [] ret fbody`
    (mp_tac o MATCH_MP linked_checked_body_calls)
  >- (simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `function_entry_env art mods src External args = fallback_types` (fn entry =>
    qpat_assum `Abbrev (fallback_code = _)` (fn code =>
      simp[NoAsms, entry, GSYM (REWRITE_RULE [markerTheory.Abbrev_def] code)])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `qualified_stmts_decls_ok mods fallback_code` by
    (qpat_assum `check_contract F am.layouts tx.target mods = SOME art` (fn checked =>
       qpat_assum `check_function_body am.layouts tx.target mods art src External mut nr args [] ret fbody`
         (fn body => qpat_assum `Abbrev (fallback_code = _)`
           (fn code => ACCEPT_TAC (PURE_REWRITE_RULE
             [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] code)]
             (MATCH_MP checked_qualified_body_decl_resolution (CONJ checked body)))))));

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_source_frame]:
  linked_empty_source_frame_tac >>
  linked_empty_source_declaration_tac >>
  linked_empty_source_checked_tac >>
  linked_empty_source_static_env_tac >>
  linked_empty_source_typed_tac >>
  suspend "linked_linear_fallback_body_guards"
QED

(* The allocation facts above the fallback cut may come from either
   dispatcher. The source-body prerequisites below use the selected
   declaration, not the selector program. *)
val linked_empty_body_types_tac =
  `linked_body_type_facts tops src (type_env_all_modules mods)` by
    drule_all_then ACCEPT_TAC linked_checked_body_type_facts >>
  `src = NONE ==> layouts_agree tops am tx` by
    (strip_tac >>
     `MEM (NONE,tops) mods` by
       (qpat_assum `src = NONE` (fn main =>
          qpat_assum `ALOOKUP mods src = SOME tops`
            (ACCEPT_TAC o MATCH_MP ALOOKUP_MEM o PURE_REWRITE_RULE [main]))) >>
     qpat_assum `layouts_agree_mods mods exps am tx` mp_tac >>
     simp[NoAsms, layouts_agree_mods_def, layouts_agree_def, pairTheory.ELIM_UNCURRY] >>
     disch_then (qspecl_then [`NONE`,`tops`] mp_tac o
       CONJUNCT2 o CONJUNCT2 o CONJUNCT2) >>
     qpat_assum `MEM (NONE,tops) mods` (fn member => simp[NoAsms, member])) >>
  `fallback_types.type_defs = type_env_all_modules mods /\
    fallback_types.event_fields = art.cta_event_fields` by
    simp[NoAsms, Abbr `fallback_types`, artifact_env_def] >>
  `linked_body_data_env tops src fallback_types` by
    (MATCH_MP_TAC (Q.INST [`mode` |-> `F`, `am` |-> `am`, `tx` |-> `tx`,
      `mods` |-> `mods`, `art` |-> `art`] linked_checked_data_env) >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       qpat_assum `fallback_types.bare_global_assignable = FEMPTY`
         (fn empty => simp[NoAsms, empty] >> NO_TAC),
       strip_tac >>
       qpat_assum `src = NONE` (fn main =>
         qpat_assum `linked_body_type_facts _ _ _`
           (mp_tac o CONJUNCT1 o REWRITE_RULE [linked_body_type_facts_def]) >>
         simp[NoAsms, main])]) >>
  `linked_body_env tops src (type_env_all_modules mods) fallback_types` by
    (PURE_REWRITE_TAC [linked_body_env_def] >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       qpat_assum `fallback_types.var_types = FEMPTY`
         (fn empty => simp[NoAsms, empty] >> NO_TAC),
       qpat_assum `fallback_types.bare_global_assignable = FEMPTY`
         (fn empty => simp[NoAsms, empty])]) >>
  `ce_locals_declared ce fallback_types /\ locals_alloc_ok ce fallback_types /\
    FDOM fallback_types.var_types = set (MAP FST (args:(string # type) list)) /\
    ALL_DISTINCT (MAP FST args)` by
    (PURE_REWRITE_TAC [ce_locals_declared_def, locals_alloc_ok_def] >>
     map_every (fn pat => qpat_assum pat SUBST1_TAC)
       [`ce.ce_vars = FEMPTY`,`fallback_types.var_types = FEMPTY`,`(args:(string # type) list) = []`] >>
     simp[NoAsms]);

val linked_empty_body_support_tac =
  Q.SUBGOAL_THEN `src = NONE \/ imported_stmts_refs_ok fallback_code` assume_tac
  >- (Cases_on `src` >> simp[NoAsms] >>
      qpat_assum `ALOOKUP mods (SOME _) = SOME tops`
        (assume_tac o MATCH_MP ALOOKUP_MEM) >>
      simp_tac bool_ss [Abbr `fallback_code`] >>
      drule_all_then (ACCEPT_TAC o CONJUNCT2)
        check_contract_subst_imported_function_refs_ok) >>
  `src = NONE ==> !name. ~MEM (StructDecl name []) tops` by
    (strip_tac >> qx_gen_tac `empty_struct` >> strip_tac >>
     drule_all_then mp_tac check_contract_toplevel_decl_MEM_checked >>
     simp[NoAsms, check_toplevel_decl_def]) >>
  qpat_assum `IS_SOME (type_stmts fallback_types ret fallback_code)`
    (qx_choose_then `after_body` assume_tac o
       PURE_REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  qpat_assum `body_const_cells_agree_mods mods cx fallback_types es0`
    (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_mods_def]) >>
  `!key r. ALOOKUP (consts_env_mods mods) key = SOME r ==>
       subst_consts_expr_mods (consts_env_mods mods) r = r` by
    (qx_genl_tac [`const_key`, `rhs`] >> PairCases_on `const_key` >> strip_tac >>
     qpat_assum `!sid id r. ALOOKUP (consts_env_mods mods) (sid,id) = SOME r ==> _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     MATCH_MP_TAC (Q.INST [`mods` |-> `mods`]
       (SPEC_ALL (cj 1 subst_consts_expr_mods_closed))) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `custom_errors_stmts_ok mods fallback_code` by
    (simp_tac bool_ss [Abbr `fallback_code`] >>
     drule_all_then ACCEPT_TAC checked_linked_custom_errors_after_substitution) >>
  `IS_SOME (type_stmts fallback_types ret
      (subst_consts_stmts_mods (consts_env_mods mods) fallback_code))` by
    (`subst_consts_stmts_mods (consts_env_mods mods) fallback_code = fallback_code` by
       (simp_tac bool_ss [Abbr `fallback_code`] >>
        MATCH_MP_TAC subst_consts_stmts_mods_idempotent >> first_assum ACCEPT_TAC) >>
     pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `supported_function_body tops External args fallback_code` by
    drule_all_then MATCH_ACCEPT_TAC checked_linked_typed_body_supported >>
  qabbrev_tac `bindings =
    args ++ supported_stmts_bindings T fallback_code ++ supported_stmts_bindings F fallback_code` >>
  `supported_stmts tops bindings fallback_code` by
    (qpat_assum `supported_function_body tops External args fallback_code`
       (strip_assume_tac o BETA_RULE o PURE_REWRITE_RULE [supported_function_body_def, LET_THM]) >>
     simp[NoAsms, Abbr `bindings`] >> first_assum ACCEPT_TAC);

val linked_empty_body_live_tac =
  `src = ALOOKUP exps tx.function_name` by
    (qpat_assum `tx.function_name = "__default__"` (fn name =>
       simp[NoAsms, Abbr `src`, name])) >>
  `cx = initial_evaluation_context am.sources am.layouts tx src /\
    cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn = tx` by
    simp[NoAsms, Abbr `cx`, initial_evaluation_context_def] >>
  `vyperInterpreter$lookup_function src tx.function_name External tops =
      SOME (mut,nr,args,[],ret,fbody) /\
    external_return_type_mods mods exps tx.function_name = ret` by
    (conj_tac >> FIRST [first_assum ACCEPT_TAC,
       qpat_assum `tx.function_name = "__default__"` (fn name =>
         simp[NoAsms, name, Abbr `src`]) >> first_assum ACCEPT_TAC]) >>
  drule_all linkedRuntimeSourceLookupTheory.linked_runtime_source_lookup >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_exported_function cx am tx.function_name = SOME (mut,nr,args,[],ret,fbody)` by
    (qpat_assum `lookup_exported_function cx am tx.function_name = _` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  `MEM (src,tops) mods` by drule_then ACCEPT_TAC ALOOKUP_MEM >>
  `MEM (src,tx.function_name) (linked_main_roots mods ++ linked_export_roots exps)` by
    (Cases_on `src` >> simp_tac bool_ss [MEM_APPEND]
     >- (disj1_tac >>
         qpat_assum `ALOOKUP mods NONE = SOME tops` (fn main =>
           simp[NoAsms, main, linked_main_roots_def, contract_keys_def, MEM_APPEND]) >>
         disj1_tac >> simp[NoAsms, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
         qpat_assum `MEM (FunctionDecl External mut nr _ tx.function_name args [] ret fbody) tops`
           (fn decl => exists_tac (rand (rator (concl decl))) >>
             simp[NoAsms, external_name_keys_toplevel_def, decl])) >>
     disj2_tac >> simp[NoAsms, linked_export_roots_def, MEM_MAP, EXISTS_PROD] >>
     FIRST [qpat_assum `SOME _ = ALOOKUP exps tx.function_name`
       (ACCEPT_TAC o MATCH_MP ALOOKUP_MEM o SYM),
       qpat_assum `ALOOKUP exps tx.function_name = SOME _`
         (ACCEPT_TAC o MATCH_MP ALOOKUP_MEM)]) >>
  `MEM (src,tx.function_name) (linked_live_functions mods exps)` by
    (PURE_REWRITE_TAC [linked_live_functions_def, linked_live_functions_from_def, LET_THM] >>
     BETA_TAC >> irule (cj 1 call_closure_from_roots) >> first_assum ACCEPT_TAC) >>
  `EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_stmts fallback_code)` by
    (simp_tac bool_ss [Abbr `fallback_code`] >>
     drule_all_then ACCEPT_TAC checked_live_body_subst_calls_mods);

val linked_empty_body_immutable_tac =
  `check_linked_state_ownership am.layouts tx.target mods (linked_live_functions mods exps)` by
    (PURE_REWRITE_TAC [GSYM linked_state_ownership_ok_def] >>
     drule_all_then ACCEPT_TAC check_contract_linked_state_ownership_ok) >>
  `immutable_section_layout_mods mods ce` by
    drule_then ACCEPT_TAC contract_inv_immutable_section_layout >>
  `fallback_types.bare_global_assignable = art.cta_bare_global_assignable` by
    simp[NoAsms, Abbr `fallback_types`, artifact_env_def] >>
  `!key r. ALOOKUP (consts_env_mods mods) key = SOME r ==> accesses_expr r = []` by
    (qx_genl_tac [`const_key`,`rhs`] >> PairCases_on `const_key` >> strip_tac >>
     qpat_assum `!sid id r. ALOOKUP (consts_env_mods mods) (sid,id) = SOME r ==> _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `~supported_stmts_expr_exists (unallocated_bare_global_root ce fallback_types) fallback_code /\
    (!key. MEM (WriteAcc (StateRef key)) (accesses_stmts fallback_code) /\
           IS_SOME (FLOOKUP fallback_types.bare_global_assignable key) ==>
           IS_SOME (FLOOKUP ce.ce_module_vars key))` by
    (simp_tac bool_ss [Abbr `fallback_code`] >>
     drule_all_then ACCEPT_TAC linkedEntryImmutableGuardsTheory.linked_checked_body_immutable_guards) >>
  `stmts_no_control_escape fbody` by
    (qpat_assum `check_function_body am.layouts tx.target mods art src
         External mut nr args [] ret fbody`
       (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss
         [check_function_body_def, LET_THM]) >> first_assum ACCEPT_TAC);

val linked_empty_body_lock_tac =
  qabbrev_tac `raw = lookup_raw_return_or_F src tx.function_name External tops` >>
  `MEM (FunctionDecl External mut nr raw tx.function_name args [] ret fbody) tops` by
    (simp_tac bool_ss [Abbr `raw`] >> first_assum ACCEPT_TAC) >>
  `function_header_ok External mut nr raw tx.function_name args [] ret` by
    drule_all_then ACCEPT_TAC check_contract_function_header >>
  `nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot /\
          is_view_mut mut = (mut = View)` by
    (strip_tac >>
     conj_tac
     >- (qpat_assum `cx = initial_evaluation_context am.sources am.layouts tx src` SUBST1_TAC >>
         qpat_assum `nr` (ASSUME_TAC o EQT_INTRO) >>
         `MEM (FunctionDecl External mut T raw tx.function_name args [] ret fbody) tops` by
           (qpat_assum `nr = T` (fn enabled =>
              qpat_assum `MEM (FunctionDecl External mut nr raw tx.function_name args [] ret fbody) tops`
                (ACCEPT_TAC o PURE_REWRITE_RULE [enabled]))) >>
         Q.SUBGOAL_THEN `src = NONE \/ MEM (src,tx.function_name) (linked_live_functions mods exps)`
           assume_tac >- (disj2_tac >> first_assum ACCEPT_TAC) >>
         drule_all_then mp_tac check_contract_linked_lock_slot >>
         Cases_on `ALOOKUP am.layouts tx.target`
         >- (qpat_assum `ALOOKUP am.layouts tx.target = NONE` (fn layout =>
               simp[NoAsms, layout, initial_evaluation_context_def, lookup_nonreentrant_slot_def])) >>
         Cases_on `x` >>
         qpat_assum `ALOOKUP am.layouts tx.target = SOME _` (fn layout =>
           simp[NoAsms, layout, initial_evaluation_context_def, lookup_nonreentrant_slot_def])) >>
     qpat_assum `nr` (ASSUME_TAC o EQT_INTRO) >>
     qpat_assum `nr = T` (fn enabled =>
       qpat_assum `function_header_ok External mut nr raw tx.function_name args [] ret`
         (mp_tac o MATCH_MP function_header_nonreentrant_view o PURE_REWRITE_RULE [enabled])) >>
     simp[NoAsms, is_view_mut_def]) >>
  `raw ==> ?n. ret = BaseT (BytesT (Dynamic n))` by
    (qpat_assum `function_header_ok External mut nr raw tx.function_name args [] ret`
       mp_tac >> simp[NoAsms, function_header_ok_def]) >>
  `ret <> NoneT ==> assignable_type (get_tenv cx) ret` by
    (strip_tac >> drule_all_then mp_tac check_contract_function_return_type >>
     qpat_assum `get_tenv cx = type_env_all_modules mods` (fn tenv =>
       qpat_assum `ret <> NoneT` (fn nonempty => simp[NoAsms, tenv, nonempty]))) >>
  `global_nonreentrant_slot < dimword (:256)` by
    simp[NoAsms, contextTheory.global_nonreentrant_slot_def, wordsTheory.dimword_def];

val linked_empty_body_base_tac =
  `fallback_base.ce_modules = mods /\ fallback_base.ce_is_external /\ ~fallback_base.ce_is_ctor /\
   fallback_base.ce_return_pc = NONE /\ fallback_base.ce_return_buf = NONE /\
   fallback_base.ce_imm_alloca = NONE /\ fallback_base.ce_ctor_exit_label = NONE /\
   fallback_base.ce_type_env = type_env_all_modules mods /\
   fallback_base.ce_struct_fields = make_struct_fields_map_mods mods` by
    simp[NoAsms, Abbr `fallback_base`, build_compile_env_unit_def, pairTheory.ELIM_UNCURRY];

val linked_empty_body_package_tac =
  `ce.ce_modules = mods /\ ce.ce_is_external /\ ~ce.ce_is_ctor /\
   ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\ ce.ce_imm_alloca = NONE /\
   ce.ce_ctor_exit_label = NONE /\ ce.ce_nonreentrant = (nr,global_nonreentrant_slot,T,mut = View) /\
   ce.ce_raw_return = raw /\ ce.ce_type_env = type_env_all_modules mods /\
   ce.ce_struct_fields = make_struct_fields_map_mods mods` by
    (qpat_assum `ce = _` SUBST1_TAC >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case => qpat_assum `tx.function_name = "__default__"` (fn name =>
       simp[NoAsms, ret_case, name, Abbr `raw`,
         update_cenv_nonreentrant_def, update_cenv_ret_abi_def])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC);

val linked_empty_body_context_tac =
  `local_ptrs_reserved ce body_start /\ return_buf_frame NONE ce body_start fallback_body_vs` by
    (PURE_REWRITE_TAC [local_ptrs_reserved_def, loweringPostsTheory.return_buf_frame_def] >>
     map_every (fn pat => qpat_assum pat SUBST1_TAC)
       [`ce.ce_vars = FEMPTY`,`ce.ce_imm_alloca = NONE`,`ce.ce_return_buf = NONE`] >>
     simp[NoAsms]) >>
  `IS_SOME (check_contract F cx.layouts cx.txn.target mods)` by
    (qpat_assum `check_contract F cx.layouts cx.txn.target mods = SOME art`
       (fn check => simp[NoAsms, check])) >>
  `exports_ok cx.layouts cx.txn.target mods exps` by
    (simp[NoAsms, Abbr `cx`, initial_evaluation_context_def] >> first_assum ACCEPT_TAC) >>
  `contract_namespaces_ok F mods` by drule_then ACCEPT_TAC check_contract_namespaces_ok >>
  `env_context_consistent fallback_types cx` by
    (qpat_assum `env_consistent fallback_types cx es0` (mp_tac o REWRITE_RULE [env_consistent_def]) >>
     strip_tac >> first_assum ACCEPT_TAC);

val linked_empty_body_alloc_tac =
  qabbrev_tac `alloc_env = build_compile_env_unit mods src Internal mut "__default__" args ret fallback_code F` >>
  `alloc_env_agree alloc_env fallback_base` by
    simp[NoAsms, alloc_env_agree_def, Abbr `alloc_env`, Abbr `fallback_base`,
         build_compile_env_unit_def, pairTheory.ELIM_UNCURRY] >>
  `alloc_env_agree alloc_env ce` by
    (qpat_assum `ce = _` SUBST1_TAC >>
     qpat_assum `alloc_env_agree alloc_env fallback_base` mp_tac >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case => simp[NoAsms, ret_case, alloc_env_agree_def,
       update_cenv_nonreentrant_def, update_cenv_ret_abi_def]));

val linked_empty_body_alloc_bounds_tac =
  `alloc_limits_stmts ce fallback_code /\ type_memory_bytes ce ret < 2 ** 64` by
    (`type_memory_bytes ce = type_memory_bytes alloc_env` by
       (irule type_memory_bytes_frame >>
        qpat_assum `alloc_env_agree alloc_env ce`
          (strip_assume_tac o REWRITE_RULE [alloc_env_agree_def]) >> first_assum ACCEPT_TAC) >>
     pop_assum SUBST1_TAC >>
     qspecl_then [`alloc_env`,`fallback_code`,`ce`] mp_tac
       (cj 2 alloc_limits_stmt_struct_fields) >>
     impl_tac >- first_assum ACCEPT_TAC >> disch_then SUBST1_TAC >>
     qpat_assum `EVERY (fn_allocs_ok_unit mods) (case fb of NONE => [] | SOME picked => [picked])` mp_tac >>
     qpat_assum `fb = SOME _` (fn fallback =>
       qpat_assum `tx.function_name = "__default__"` (fn name =>
         qpat_assum `args = []` (fn args =>
           simp[NoAsms, fallback, name, args, fn_allocs_ok_unit_def,
             Abbr `alloc_env`, Abbr `src`]))));

val linked_empty_body_widths_tac =
  `~supported_stmts_expr_exists (const_name_root_mods mods) fallback_code` by
    (simp_tac bool_ss [Abbr `fallback_code`] >>
     MATCH_MP_TAC (Q.INST [`mods` |-> `mods`, `ss` |-> `fbody`]
       linkedEntryImmutableGuardsTheory.substituted_stmts_const_name_free_mods) >>
     first_assum ACCEPT_TAC) >>
  `~supported_stmts_expr_exists (\e. ~byte_widths_expr e) fallback_code` by
    (MATCH_MP_TAC (Q.INST [`args` |-> `args`, `cx` |-> `cx`,
       `env` |-> `fallback_types`, `env'` |-> `after_body`, `ret` |-> `ret`,
       `ss` |-> `fallback_code`] (SPEC_ALL typed_parameter_body_excludes_bad_widths)) >>
     qpat_assum `fallback_types.var_types = FEMPTY` (fn empty =>
       qpat_assum `(args:(string # type) list) = []` (fn args => simp[NoAsms, empty, args])) >>
     conj_tac >> first_assum ACCEPT_TAC);

val linked_empty_body_stmts_exprs_tac =
  `stmts_exprs_ok ce fallback_code` by
    (MATCH_MP_TAC stmt_exprs_ok_from_traversal_bounds >>
     qpat_assum `ce.ce_modules = mods` SUBST1_TAC >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       strip_tac >>
       qpat_assum `stmts_valued_return fallback_code /\ ~ce.ce_raw_return ==> return_buffer_ok ce`
         (drule_all_then ACCEPT_TAC)]) >>
  `ret <> NoneT ==> stmts_no_fallthrough fbody` by
    (strip_tac >>
     qpat_assum `ret <> NoneT` (fn nonempty =>
       qpat_assum `check_function_body am.layouts tx.target mods art src External mut nr args [] ret fbody`
         (strip_assume_tac o SIMP_RULE (srw_ss()) [check_function_body_def, LET_THM, nonempty])) >>
     first_assum ACCEPT_TAC);

val linked_empty_body_return_buffer_tac =
  `stmts_valued_return fallback_code /\ ~ce.ce_raw_return ==> return_buffer_ok ce` by
    (strip_tac >> Cases_on `ret = NoneT`
     >- (qpat_assum `type_stmts fallback_types ret fallback_code = SOME after_body`
           (mp_tac o MATCH_MP externalCallSelectedTheory.type_stmts_none_valued_return o
             REWRITE_RULE [ASSUME ``ret = NoneT``]) >>
         qpat_assum `stmts_valued_return fallback_code` (fn valued => simp[NoAsms, valued])) >>
     Cases_on `is_word_type ret`
     >- (qpat_assum `is_word_type ret`
           (mp_tac o Q.SPEC `fallback_base with ce_raw_return := raw` o
             MATCH_MP (ONCE_REWRITE_RULE [SWAP_FORALL_THM]
               update_cenv_ret_abi_word_return_buffer_ok)) >>
         qpat_assum `ce = _` SUBST1_TAC >>
         qpat_assum `tx.function_name = "__default__"` (fn name =>
           qpat_assum `ret <> NoneT` (fn nonempty =>
             simp[NoAsms, nonempty, name, Abbr `raw`, return_buffer_ok_def,
               update_cenv_nonreentrant_def]))) >>
     qpat_assum `OPTION_ALL _ fall` mp_tac >>
     map_every (fn pat => qpat_assum pat SUBST1_TAC)
       [`fall = SOME (ce,pay,nr,key,tr,view,fallback_code,rt)`,`rt = _`] >>
     qpat_assum `~ce.ce_raw_return` (fn raw_off =>
       qpat_assum `~is_word_type ret` (fn not_word =>
         qpat_assum `stmts_valued_return fallback_code` (fn valued =>
           qpat_assum `ret <> NoneT` (fn ty =>
             simp[NoAsms, external_return_buffer_ok_def, raw_off, not_word, valued, ty])))));

(* The linear caller has two zero-reading path segments; the grouped
   caller supplies its own path and does not use this tactic. *)
val linked_linear_empty_path_tac =
  qabbrev_tac `start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  qabbrev_tac `explicit = gas_explicit_sites unit.cu_context shadow_unit.cu_context` >>
  `!D. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
      (start,FEMPTY,entry_taint) [] (OK fallback_body_vs,fallback_body_G,fallback_body_taint)` by
    (gen_tac >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (_ ,FEMPTY,entry_taint) [] (OK hit,Gh,tnh)`
       (qspecl_then [`D`,`explicit`] (mp_tac o MATCH_MP (SPEC_ALL gas_origin_ptr_path_append))) >>
     disch_then (qspecl_then [`hit`,`Gh`,`tnh`,`[]`,`OK fallback_body_vs`,
         `fallback_body_G`,`fallback_body_taint`] mp_tac) >>
     simp_tac bool_ss [APPEND, Abbr `start`] >>
     disch_then MATCH_MP_TAC >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (hit,Gh,tnh) []
          (OK fallback_body_vs,fallback_body_G,fallback_body_taint)`
       (qspecl_then [`D`,`explicit`] ACCEPT_TAC)) >>
  `gas_path_mem unit.cu_context fn start 0 (OK fallback_body_vs)` by
    qpat_assum `!D. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) [] (OK fallback_body_vs,_,_)`
      (qspec_then `ARB` (ACCEPT_TAC o MATCH_MP selectedAcceptedInterfacesTheory.selected_zero_path_mem));

val linked_empty_entry_open_tac =
  `~block_is_terminated body_start` by
    (irule selectedEntryPrefixCodeTheory.compile_entry_checks_open >>
     qexistsl_tac [`4`,`pay`,`check_start`,`()`] >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `check_start.cs_current_insts = []` (fn empty =>
       simp[NoAsms, block_is_terminated_def, empty])) >>
  `!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt gen_tac >> strip_tac >> drule_all_then ACCEPT_TAC lowering_context_ok_block_phi) >>
  `?bb. lookup_block "__entry" fn.fn_blocks = SOME bb /\ phi_prefix_length bb.bb_instructions = 0` by
    (`?bb. lookup_block "__entry" fn.fn_blocks = SOME bb` by
       (qpat_assum `fn_entry_label fn = SOME "__entry"` mp_tac >>
        Cases_on `fn.fn_blocks` >>
        qpat_assum `fn.fn_blocks = _` (fn blocks =>
          simp[NoAsms, blocks, fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm])) >>
     rename1 `lookup_block "__entry" fn.fn_blocks = SOME found_bb` >>
     qexists_tac `found_bb` >> conj_tac >- first_assum ACCEPT_TAC >>
     drule_all_then ACCEPT_TAC lowering_context_ok_block_phi) >>
  rename1 `phi_prefix_length entry_bb.bb_instructions = 0`;

val linked_empty_entry_ptr_tac =
  `!D. (!fuel. ptr_safe_run D 0 fuel unit.cu_context fn []
            fallback_body_G fallback_body_taint fallback_body_vs) ==>
       !fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn [] FEMPTY entry_taint start` by
    (gen_tac >> strip_tac >>
     `!fuel. ptr_safe_run D 0 fuel unit.cu_context fn [] FEMPTY entry_taint start` by
       (MATCH_MP_TAC (Q.INST [`explicit` |-> `explicit`, `t` |-> `fallback_body_vs`,
         `H` |-> `fallback_body_G`, `u` |-> `fallback_body_taint`]
         selectedAcceptedInterfacesTheory.selected_zero_path_ptr_pullback) >>
        conj_tac
        >- qpat_assum `!D. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) [] (OK fallback_body_vs,_,_)`
             (qspec_then `D` ACCEPT_TAC) >>
        conj_tac
        >- (map_every qx_gen_tac [`phi_bb`,`phi_label`] >>
            qpat_assum `!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==> _`
              (qspecl_then [`phi_label`,`phi_bb`] ACCEPT_TAC)) >>
        first_assum ACCEPT_TAC) >>
     MATCH_MP_TAC (Q.INST [`bb` |-> `entry_bb`]
       entryDispatchPtrTheory.ptr_safe_blocks_from_phi_free_run) >>
     conj_tac >- (simp[NoAsms, Abbr `start`] >> first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[NoAsms, Abbr `start`] >>
     first_assum ACCEPT_TAC);

val linked_empty_return_plan_tac =
  `ret <> NoneT ==>
    ce.ce_ret_enc_info = (update_cenv_ret_abi ce ret).ce_ret_enc_info /\
    ce.ce_max_return_size = (update_cenv_ret_abi ce ret).ce_max_return_size /\
    assignable_type (get_tenv cx) ret /\
    (ce.ce_raw_return ==> ?n. ret = BaseT (BytesT (Dynamic n))) /\
    type_memory_bytes ce ret < 2 ** 64` by
    (strip_tac >>
     `ce.ce_struct_fields = (fallback_base with ce_raw_return := raw).ce_struct_fields` by
       (qpat_assum `fallback_base.ce_struct_fields = _` (fn fields => simp[NoAsms, fields]) >>
        first_assum ACCEPT_TAC) >>
     `type_memory_bytes ce = type_memory_bytes (fallback_base with ce_raw_return := raw)` by
       (irule type_memory_bytes_frame >> first_assum ACCEPT_TAC) >>
     `type_to_abi_enc_info (fallback_base with ce_raw_return := raw).ce_struct_fields ce ret =
      type_to_abi_enc_info (fallback_base with ce_raw_return := raw).ce_struct_fields
        (fallback_base with ce_raw_return := raw) ret` by
       (irule linkedReturnAbiLayoutTheory.type_to_abi_enc_info_struct_fields >> first_assum ACCEPT_TAC) >>
     `ce.ce_ret_enc_info = (update_cenv_ret_abi (fallback_base with ce_raw_return := raw) ret).ce_ret_enc_info /\
      ce.ce_max_return_size = (update_cenv_ret_abi (fallback_base with ce_raw_return := raw) ret).ce_max_return_size` by
       (qpat_assum `ce = _` SUBST1_TAC >>
        qpat_assum `tx.function_name = "__default__"` (fn name =>
          qpat_assum `ret <> NoneT` (fn nonempty =>
            simp[NoAsms, name, Abbr `raw`, nonempty, update_cenv_nonreentrant_def, update_cenv_ret_abi_def, LET_THM]))) >>
     qpat_assum `ce.ce_ret_enc_info = _` SUBST1_TAC >>
     qpat_assum `ce.ce_max_return_size = _` SUBST1_TAC >>
     qpat_assum `ce.ce_raw_return = raw` (fn raw_eq =>
       qpat_assum `ce.ce_struct_fields = (fallback_base with ce_raw_return := raw).ce_struct_fields` (fn fields =>
         qpat_assum `type_memory_bytes ce = type_memory_bytes (fallback_base with ce_raw_return := raw)` (fn size =>
           qpat_assum `type_to_abi_enc_info _ ce ret = _` (fn plan =>
             qpat_assum `type_memory_bytes ce ret < 2 ** 64` (fn limit =>
               let val plan = SIMP_RULE (srw_ss()) [] plan
                   val limit = SIMP_RULE (srw_ss()) [AP_THM size ``ret:type``] limit
               in simp[NoAsms, raw_eq, fields, size, plan, limit, update_cenv_ret_abi_def, LET_THM]
               end))))) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       qpat_assum `ret <> NoneT` (fn nonempty => first_assum (ACCEPT_TAC o C MATCH_MP nonempty))]);

val linked_empty_return_none_tac =
  `lookup_raw_return_or_F src tx.function_name External tops = raw` by
    simp[NoAsms, Abbr `raw`] >>
  `ret = NoneT ==> tx_return_bytes_mods mods exps cx.txn NoneV []` by
    (strip_tac >>
     `~raw` by
       (qpat_assum `raw ==> ?n. ret = BaseT (BytesT (Dynamic n))` mp_tac >>
        qpat_assum `ret = NoneT` (fn none => simp[NoAsms, none])) >>
     qpat_assum `cx.txn = tx` SUBST1_TAC >>
     qpat_assum `src = ALOOKUP exps tx.function_name` (fn src_eq =>
       qpat_assum `ALOOKUP mods src = SOME tops` (fn selected =>
         qpat_assum `lookup_raw_return_or_F src tx.function_name External tops = raw` (fn raw_eq =>
           qpat_assum `external_return_type_mods mods exps tx.function_name = ret` (fn ret_eq =>
             qpat_assum `ret = NoneT` (fn none =>
               qpat_assum `~raw` (fn not_raw =>
                 simp[NoAsms, GSYM src_eq, selected, raw_eq, ret_eq, none, not_raw,
                   tx_return_bytes_mods_def, return_bytes_mods_def, LET_THM])))))));

val linked_empty_entry_static_tac =
  `MEM fn unit.cu_context.ctx_functions /\ MEM fallback_shadow_fn shadow_unit.cu_context.ctx_functions` by
    (conj_tac >> drule_then ACCEPT_TAC venomInstTheory.lookup_function_MEM) >>
  `ctx_inst_ids_distinct unit.cu_context` by
    (drule lowering_context_ok_static_integrity >> strip_tac >> first_assum ACCEPT_TAC) >>
  `fn_inst_ids_distinct fn` by
    (drule_all ctx_inst_ids_distinct_fn >>
     simp[NoAsms, fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_map_id]) >>
  `LENGTH args = LENGTH tx.args` by
    drule_then ACCEPT_TAC vyperCallTheory.bind_arguments_length >>
  `ALL_DISTINCT (MAP FST mods)` by
    (qpat_assum `contract_namespaces_ok F mods`
       (strip_assume_tac o PURE_REWRITE_RULE [contract_namespaces_ok_def]) >>
     first_assum ACCEPT_TAC);

(* Normalize an empty registration cut for the common execution stages.
   The caller supplies its own start, explicit sites, path, and resources. *)
val linked_empty_registered_cut_tac =
  rename1 `return_buf_frame NONE registered_env registered s0` >>
  rename1 `gas_shadow_state registered shadow_registered` >>
  rename1 `compile_guarded_body (gas_shadow_env T registered_env) nr key tr view
    (MAP gas_shadow_stmt _) _ shadow_registered = ((),shadow_last)` >>
  rename1 `fn_has_code shadow_registered shadow_last shadow_fn` >>
  rename1 `compile_guarded_body registered_env nr key tr view body_code rt registered = ((),last)` >>
  rename1 `compile_stmts registered_env NoLoop _ body_code locked = ((),body_end)` >>
  rename1 `compile_stmts (gas_shadow_env T registered_env) NoLoop _
    (MAP gas_shadow_stmt body_code) shadow_locked = ((),shadow_body_end)` >>
  rename1 `type_stmts entry_types ret body_code = SOME after_body` >>
  rename1 `!D. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
      (start,FEMPTY,entry_taint) [] (OK s0,G2,tn2)`;

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_body_guards]:
  linked_empty_body_types_tac >>
  linked_empty_body_support_tac >>
  linked_empty_body_live_tac >>
  linked_empty_body_immutable_tac >>
  linked_empty_body_lock_tac >>
  linked_empty_body_base_tac >>
  linked_empty_body_package_tac >>
  linked_empty_body_context_tac >>
  linked_empty_body_alloc_tac >>
  linked_empty_body_alloc_bounds_tac >>
  linked_empty_body_widths_tac >>
  linked_empty_body_return_buffer_tac >>
  linked_empty_body_stmts_exprs_tac >>
  linked_linear_empty_path_tac >>
  linked_empty_entry_open_tac >>
  linked_empty_entry_ptr_tac >>
  linked_empty_return_plan_tac >>
  linked_empty_return_none_tac >>
  linked_empty_entry_static_tac >>
  linked_empty_registered_cut_tac >>
  linked_registered_stmts_env_tac >>
  linked_registered_path_tac >>
  linked_registered_lock_cases_tac
    (suspend "linked_linear_fallback_lock_success")
    (suspend "linked_linear_fallback_lock_abort")
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_lock_abort]:
  linked_registered_lock_abort_tac >>
  linked_registered_lock_abort_source_tac >>
  linked_registered_lock_abort_domain_tac >>
  linked_registered_lock_abort_finish_tac
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_lock_success]:
  linked_registered_lock_success_tac >>
  linked_registered_locked_horizon_tac >>
  linked_registered_replay_tac >>
  linked_registered_return_frame_tac >>
  linked_registered_structs_tac >>
  linked_registered_abi_targets_tac >>
  linked_registered_fragment_tac >>
  linked_registered_shadow_tac >>
  linked_registered_admissible_tac >>
  linked_registered_reachability_tac >>
  linked_registered_immutable_frame_tac >>
  linked_registered_storage_prefix_tac >>
  linked_registered_run_tac >>
  linked_registered_trace_inputs_tac >>
  linked_registered_compose_tac
    {horizon_tac = suspend "linked_linear_fallback_trace_horizon",
     tails_tac = suspend "linked_linear_fallback_trace_tails",
     exempt_tac = suspend "linked_linear_fallback_trace_exempt",
     fallthrough_tac = suspend "linked_linear_fallback_fallthrough",
     exit_tac = suspend "linked_linear_fallback_exit",
     readings_tac = suspend "linked_linear_fallback_trace_readings",
     finish_tac = suspend "linked_linear_fallback_finish"}
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_trace_horizon]:
  linked_registered_trace_horizon_tac
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_trace_tails]:
  linked_registered_trace_tails_tac
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_trace_exempt]:
  linked_registered_trace_exempt_tac
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_fallthrough]:
  linked_registered_fallthrough_tac
    (suspend "linked_linear_fallback_fallthrough_ghost")
    (suspend "linked_linear_fallback_fallthrough_result")
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_fallthrough_ghost]:
  linked_registered_fallthrough_ghost_tac
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_fallthrough_result]:
  linked_registered_fallthrough_result_tac
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_exit]:
  linked_registered_trace_exit_tac (suspend "linked_linear_fallback_abort_or_halt")
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_abort_or_halt]:
  linked_registered_abort_or_halt_tac
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_trace_readings]:
  linked_registered_trace_readings_tac
QED

Resume linked_runtime_dispatched_readings_certificate[linked_linear_fallback_finish]:
  linked_registered_finish_tac
QED


Resume linked_runtime_dispatched_readings_certificate[linked_grouped_active_body]:
  `EVERY group_entry_labels_ok groups` by
    simp[Abbr `groups`, EVERY_MAP, package_external_group_unit_labels] >>
  `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips)` by
    (qpat_assum `Abbrev (ips = _)`
      (fn ips => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] ips]) >>
     MATCH_ACCEPT_TAC unit_package_internal_labels) >>
  drule_all grouped_internal_run_labels >>
  disch_then (qx_choosel_then [`compiled`,`final`,`data`]
    (map_every assume_tac o CONJUNCTS)) >>
  `unit.cu_context.ctx_entry = SOME "__entry" /\
   ?fn. venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn` by
    (qpat_assum `extract_context_with_internals _ _ _ = _` mp_tac >>
     simp[NoAsms, extract_context_with_internals_def] >> CASE_TAC >> simp[] >>
     rename1 `package_internal_blocks _ _ = SOME packed` >> PairCases_on `packed` >>
     simp[mk_venom_context_def, lookup_function_def, mk_raw_function_def, FIND_thm] >>
     disch_then (SUBST1_TAC o SYM o CONJUNCT1) >> simp[FIND_thm]) >>
  `fn_entry_label fn = SOME "__entry"` by
    (drule_all run_grouped_lowering_retained_entry_prefix >>
     disch_then (qx_choosel_then [`se`,`rest`] strip_assume_tac) >>
     `cs_extends (initial_compile_state "__entry") se` by
       (irule compile_grouped_runtime_extends >> qexistsl_tac [`fall`,`groups`,`[]`] >> simp[]) >>
     `MAP (\bb. bb.bb_label) (all_blocks (initial_compile_state "__entry")) =
      ["__entry"]` by simp[initial_compile_state_def, all_blocks_def] >>
     qpat_assum `cs_extends (initial_compile_state "__entry") se`
       (mp_tac o MATCH_MP block_labels_cs_extends) >>
     simp[] >> strip_tac >>
     Cases_on `all_blocks se` >>
     gvs[fn_entry_label_def, entry_block_def]) >>
  drule_all grouped_shadow_entry_dispatch >>
  disch_then (qx_choosel_then
    [`shunit`,`shfn`,`sf`,`fall_lbl`,`jobs`,`sd`,`shd`,`sx`,`shx`,`sn`,`shn`,`se`,`she`]
    (map_every assume_tac o CONJUNCTS)) >>
  `shunit = shadow_unit` by
    (qpat_assum `run_grouped_lowering (MAP _ groups) _ _ _ _ = SOME shunit` mp_tac >>
     qpat_assum `run_grouped_lowering (MAP _ groups) _ _ _ _ = SOME shadow_unit`
       (fn actual => simp[NoAsms, actual])) >>
  qpat_x_assum `shunit = shadow_unit` SUBST_ALL_TAC >>
  suspend "linked_grouped_selector"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_selector]:
  qabbrev_tac `cd = vs.vs_call_ctx.cc_calldata` >>
  Cases_on `if LENGTH cd < 4 then NONE else
    FIND (\(name,tys). abi_method_id (type_env_all_modules mods) name tys = cd_selector cd)
      (abi_deployed_signatures mods exps)`
  >- suspend "linked_grouped_fallback" >>
  PairCases_on `x` >>
  rename1 `(if LENGTH cd < 4 then NONE else _) = SOME (name,tys)` >>
  `4 <= LENGTH cd /\
    FIND (\(name,tys). abi_method_id (type_env_all_modules mods) name tys = cd_selector cd)
      (abi_deployed_signatures mods exps) = SOME (name,tys)` by
    (Cases_on `LENGTH cd < 4` >> fs[arithmeticTheory.NOT_LESS]) >>
  `?decoded_tys.
    name = tx.function_name /\
    OPT_MMAP (evaluate_type (type_env_all_modules mods)) tys = SOME decoded_tys /\
    4 + SUM (MAP tv_abi_size decoded_tys) <= LENGTH cd /\
    calldata_decode_args cd decoded_tys 0 = SOME tx.args` by
    (qpat_assum `calldata_dispatch_mods _ _ cd = SOME _` mp_tac >>
     qpat_assum `(if LENGTH cd < 4 then NONE else _) = SOME (name,tys)`
       (fn hit => simp[NoAsms, calldata_dispatch_mods_def, LET_THM, hit, AllCaseEqs()]) >>
     strip_tac >> goal_assum (drule_at Any) >> simp[]) >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `name = tx.function_name` SUBST_ALL_TAC >>
  `MEM (tx.function_name,tys) (abi_deployed_signatures mods exps)` by
    drule_then ACCEPT_TAC FIND_MEM >>
  suspend "linked_grouped_signature"
QED

(* A miss here selects the linked fallback, because source dispatch succeeded. *)
val linked_grouped_fallback_source_tac =
  (Q.SUBGOAL_THEN `tx.function_name = "__default__" /\ tx.args = [] /\
    (list$EXISTS is_default_decl (main_module mods) \/ IS_SOME (exported_fallback mods exps))`
    (map_every assume_tac o CONJUNCTS)
    >- (qpat_assum `calldata_dispatch_mods _ _ cd = SOME _` mp_tac >>
        qpat_assum `(if LENGTH cd < 4 then NONE else _) = NONE` (fn miss =>
          simp[NoAsms, calldata_dispatch_mods_def, LET_THM, miss, AllCaseEqs()]))) >>
  drule_all_then (qx_choosel_then [`tops`,`mut`,`nr`,`ret`,`fbody`]
    (map_every assume_tac o CONJUNCTS)) linked_fallback_source_entry_mods;

val linked_grouped_fallback_classified_tac =
  drule_then assume_tac (Q.INST [`name` |-> `"__default__"`] export_excludes_main_external) >>
  drule_all_then (map_every assume_tac o CONJUNCTS)
    (INST_TYPE [``:'a`` |-> ``:num``] default_miss_classified);

val linked_grouped_fallback_lookup_tac =
  `ALOOKUP mods src = SOME tops /\
   vyperInterpreter$lookup_function src tx.function_name External tops =
     SOME (mut,nr,[],[],ret,fbody)` by
    (qpat_assum `tx.function_name = _` (fn name => simp[Abbr `src`, name])) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  `external_return_type_mods mods exps tx.function_name = ret` by
    (qpat_assum `ALOOKUP mods src = SOME tops` mp_tac >>
     qpat_assum `vyperInterpreter$lookup_function src tx.function_name External tops = _` mp_tac >>
     simp[NoAsms, Abbr `src`, external_return_type_mods_def, LET_THM] >> simp[LET_THM]) >>
  qpat_assum `external_return_type_mods _ _ _ = _` (fn rt => PURE_REWRITE_TAC [rt]);

val linked_grouped_fallback_code_tac =
  qabbrev_tac `fallback_code = subst_consts_stmts_mods (consts_env_mods mods) fbody` >>
  qabbrev_tac `fallback_rt = if ret = NoneT then NONE else SOME ret` >>
  (Q.SUBGOAL_THEN `?ce. fall = SOME (ce,mut = Payable,nr,global_nonreentrant_slot,T,
       mut = View,fallback_code,fallback_rt)` (qx_choose_then `ce` assume_tac)
   >- (qpat_assum `Abbrev (fall = _)`
         (fn alias => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] alias]) >>
       qpat_assum `fb = SOME (ALOOKUP exps "__default__",_)` SUBST1_TAC >>
       Cases_on `ret = NoneT` >> pop_assum (fn none =>
         simp[NoAsms, Abbr `fallback_rt`, none,
           package_fallback_fn_unit_def, set_fallback_package_target_def, LET_THM]))) >>
  (Q.SUBGOAL_THEN
    `compile_fallback_body ce (mut = Payable) nr global_nonreentrant_slot T
       (mut = View) fallback_code fallback_rt sn = ((),se) /\
     compile_fallback_body (gas_shadow_env T ce) (mut = Payable) nr global_nonreentrant_slot T
       (mut = View) (MAP gas_shadow_stmt fallback_code) fallback_rt shn = ((),she)`
    (map_every assume_tac o CONJUNCTS)
    >- (qpat_assum `(case fall of NONE => _ | SOME (_,_,_,_,_,_,_,_) => _) sn = _` mp_tac >>
        qpat_assum `(case OPTION_MAP gas_shadow_fallback_package fall of NONE => _
             | SOME (_,_,_,_,_,_,_,_) => _) shn = _` mp_tac >>
        qpat_assum `fall = SOME (_,_,_,_,_,_,_,_)`
          (fn fall => simp[NoAsms, fall, gas_shadow_fallback_package_def]))) >>
  qpat_assum `compile_fallback_body (gas_shadow_env T ce) _ _ _ _ _ _ _ shn = _`
    (fn compile => qpat_assum `fn_has_code shn she shfn`
      (mp_tac o MATCH_MP grouped_fallback_guarded_code o CONJ compile)) >>
  disch_then (qx_choose_then `shadow_body_start` (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `compile_fallback_body ce _ _ _ _ _ _ _ sn = _`
    (fn compile => qpat_assum `fn_has_code sn se fn`
      (mp_tac o MATCH_MP grouped_fallback_guarded_code o CONJ compile)) >>
  disch_then (qx_choose_then `body_start` (map_every assume_tac o CONJUNCTS)) >>
  `gas_shadow_state body_start shadow_body_start` by
    (mp_tac (Q.INST [`min_cds` |-> `4`, `payable` |-> `mut = Payable`]
       gas_shadow_compiles_compile_entry_checks) >>
     simp_tac bool_ss [gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sn`,`shn`] mp_tac) >> asm_rewrite_tac[SND]);

val linked_grouped_fallback_start_tac =
  qabbrev_tac `start = vs with <|vs_prev_bb := NONE;
    vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  `!label bb. venomInst$lookup_block label fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule acceptedContextPhiTheory.lowering_context_ok_block_phi >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  `start.vs_current_bb = "__entry" /\ start.vs_inst_idx = 0 /\
   start.vs_allocas = FEMPTY /\ start.vs_alloca_next = 0 /\
   allocas_below_fmp start /\ allocas_from 0 start /\
   ~start.vs_halted /\ fresh_vars_wrt sf start /\
   start.vs_call_ctx = vs.vs_call_ctx` by
    (qpat_assum `initial_venom_state_rel_mods mods am tx vs` mp_tac >>
     qpat_assum `sf.cs_next_var = 0` (fn var =>
       simp[NoAsms, Abbr `start`, initial_venom_state_rel_mods_def, allocas_below_fmp_def,
            allocas_from_def, fresh_vars_wrt_def, var])) >>
  `alloca_frontier_inv unit.cu_context fn ARB start /\
   unit_alloca_budget unit.cu_context < dimword (:256)` by
    (irule (Q.INST [`name` |-> `"__entry"`] registration_empty_frontier) >>
     asm_rewrite_tac[]) >>
  `alloca_inv start` by simp[alloca_inv_empty] >>
  `selected_registration_resources unit.cu_context fn ARB 0 sf start` by
    (PURE_REWRITE_TAC [selected_registration_resources_def] >>
     asm_rewrite_tac [FLOOKUP_EMPTY, arithmeticTheory.ZERO_LESS_EQ] >> simp[NoAsms]) >>
  `fn_inst_ids_distinct fn` by
    (`MEM fn unit.cu_context.ctx_functions` by drule_then ACCEPT_TAC lookup_function_MEM >>
     drule lowering_context_ok_static_integrity >> strip_tac >>
     drule_all ctx_inst_ids_distinct_fn >>
     simp[NoAsms, fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_map_id]) >>
  `LENGTH start.vs_call_ctx.cc_calldata < dimword (:256)` by simp[Abbr `cd`, dimword_def] >>
  `ctx_has_dalloca unit.cu_context ==>
     allocas_below_fmp start /\
     start.vs_alloca_next + pending_alloca_size fn start <= w2n start.vs_initial_fmp` by
    (strip_tac >>
     `start.vs_alloca_next + pending_alloca_size fn start <= unit_alloca_budget unit.cu_context` by
       (qpat_assum `alloca_frontier_inv _ _ _ _`
          (mp_tac o REWRITE_RULE [alloca_frontier_inv_def]) >>
        simp[NoAsms, deploy_ctor_pending_alloca_eq] >> decide_tac) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `unit_alloca_budget unit.cu_context` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `ctx_has_dalloca unit.cu_context ==>
       unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\ _`
       (drule_then (mp_tac o CONJUNCT1)) >> simp[NoAsms, Abbr `start`]);

val linked_grouped_fallback_span_tac =
  `ci_mono sd sx` by
    (qpat_assum `compile_external_jobs jobs sd = ((),sx)` (fn done =>
       simp[NoAsms, compile_external_jobs_ci_mono, GSYM (REWRITE_RULE [] (AP_TERM ``SND:unit # compile_state -> compile_state`` done))])) >>
  `ci_mono sx sn` by
    (qspecl_then [`fall_lbl`,`sx`] mp_tac ci_mono_new_block >> simp[]) >>
  `ci_mono sd sn` by metis_tac[ci_mono_trans] >>
  (Q.SUBGOAL_THEN `?target. lookup_block fall_lbl fn.fn_blocks = SOME target`
    (qx_choose_then `target` assume_tac)
   >- (`cs_extends sn se` by metis_tac[cs_appends_def, entryCompileIntervalsTheory.cs_appends_fallback_body] >>
       drule_all fn_has_code_start >> simp[]));

val linked_grouped_fallback_widths_tac =
  `!common entries specs off. MEM (ExternalDefaults common entries specs off) groups ==>
    EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs` by
    (rpt gen_tac >> simp[NoAsms, Abbr `groups`, MEM_MAP] >>
     disch_then (qx_choose_then `other` strip_assume_tac) >> PairCases_on `other` >>
     rename1 `MEM (other_src,m,n,r,nm,aa,ds,rt,code) exts` >>
     qpat_assum `ExternalDefaults _ _ _ _ = _` (assume_tac o SYM) >>
     drule_all classified_grouped_default_compile_inputs_mods >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     drule_all classified_external_default_source_mods >>
     disch_then (qx_choosel_then [`declarations`,`raw_ds`,`raw_code`] strip_assume_tac) >>
     `module_allocated am.layouts tx.target other_src declarations` by
       drule_all_then ACCEPT_TAC classified_external_owner_allocated_mods >>
     `LENGTH ds <= LENGTH aa` by
       (`ds = subst_consts_exprs_mods (consts_env_mods mods) raw_ds` by
          (qpat_assum `subst_consts_fn_mods _ (_,_,_,_,_,raw_ds,_,_) = _` mp_tac >>
           simp[NoAsms, subst_consts_fn_mods_def]) >>
        drule_all grouped_checked_default_syntax_mods >> simp[]) >>
     qabbrev_tac `alloc_env = build_compile_env_unit mods other_src Internal m nm aa rt code F` >>
     `common.ec_env.ce_struct_fields = alloc_env.ce_struct_fields` by
       (qunabbrev_tac `alloc_env` >>
        qpat_assum `ExternalDefaults _ _ _ _ = package_external_group_unit _ _ _ _ _` mp_tac >>
        qpat_assum `ds <> []` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
        Cases_on `rt = NoneT` >>
        simp[package_external_group_unit_def, package_external_fn_unit_def,
             set_external_package_target_def, update_cenv_ret_abi_def,
             update_cenv_nonreentrant_def, NULL_EQ] >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        qpat_assum `common = _` SUBST1_TAC >>
        simp[build_compile_env_unit_def, ELIM_UNCURRY]) >>
     `type_memory_bytes common.ec_env = type_memory_bytes alloc_env` by
       (irule type_memory_bytes_frame >> first_assum ACCEPT_TAC) >>
     `EVERY (\(_,ty). type_memory_bytes alloc_env ty < 2 ** 64) aa` by
       (qpat_assum `fn_allocs_ok_unit mods (other_src,(m,n,r,nm,aa,ds,rt,code))` mp_tac >>
        simp[NoAsms, fn_allocs_ok_unit_def, Abbr `alloc_env`]) >>
     simp[NoAsms, EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
     rename1 `MEM (param,ty,x) specs` >>
     `MEM (param,ty) aa` by
       (irule rich_listTheory.MEM_DROP_IMP >>
        qexists_tac `LENGTH aa - LENGTH ds` >>
        qpat_x_assum `MEM (param,ty,x) specs` mp_tac >>
        qpat_assum `specs = MAP _ _` SUBST1_TAC >>
        pure_rewrite_tac [MEM_MAP] >> simp[NoAsms, EXISTS_PROD] >>
        rpt strip_tac >>
        `LENGTH (DROP (LENGTH aa - LENGTH ds) aa) = LENGTH ds` by simp[LENGTH_DROP] >>
        qpat_x_assum `MEM _ (ZIP _)` mp_tac >>
        simp[MEM_ZIP] >> disch_then (qx_choose_then `idx` strip_assume_tac) >>
        simp[MEM_EL] >> qexists_tac `idx` >> simp[]) >>
     qpat_assum `EVERY (\(_,ty). _) aa`
       (mp_tac o Q.SPEC `(param,ty)` o REWRITE_RULE [EVERY_MEM]) >>
     simp[dimword_def]);

val linked_grouped_fallback_selectors_tac =
  `!src mut nr rr name args ds ret code.
     MAP FST (external_group_selectors
       (package_external_group_unit mods rpolicy.rpol_target T
         (K global_nonreentrant_slot) (src,(mut,nr,rr,name,args,ds,ret,code)))) =
     MAP (\(nm,tys). abi_method_id (type_env_all_modules mods) nm tys)
       (abi_function_signatures name args ds)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >> Cases_on `ds` >>
     simp[package_external_group_unit_def, package_external_fn_unit_def,
          set_external_package_target_def, external_group_selectors_def,
          compute_selector_method_id, abi_function_signatures_def, abi_entries_no_defaults,
          MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f, FORALL_PROD]) >>
  `!id. MEM id (MAP FST (grouped_selectors groups)) ==>
     ?nm ts. MEM (nm,ts) (abi_deployed_signatures mods exps) /\
       id = abi_method_id (type_env_all_modules mods) nm ts` by
    (gen_tac >> simp[NoAsms, Abbr `groups`, grouped_selectors_def, MAP_FLAT, MEM_FLAT, MEM_MAP] >>
     strip_tac >> rename1 `MEM key exts` >> PairCases_on `key` >>
     `MEM id (MAP FST (external_group_selectors
        (package_external_group_unit mods rpolicy.rpol_target T (K global_nonreentrant_slot)
          (key0,key1,key2,key3,key4,key5,key6,key7,key8))))` by
       (simp[MEM_MAP] >> metis_tac[]) >>
     qpat_x_assum `MEM id (MAP FST (external_group_selectors _))` mp_tac >>
     qpat_assum `!src mut nr rr name args ds ret code. MAP FST _ = _`
       (fn origin => pure_rewrite_tac[origin, abi_function_signatures_def, MAP_MAP_o,
                                  combinTheory.o_DEF] >> simp[NoAsms, MEM_MAP, EXISTS_PROD]) >>
     disch_then (qx_choosel_then [`sig_args`,`j`] strip_assume_tac) >>
     qexistsl_tac [`key4`,`MAP SND sig_args`] >>
     conj_tac >- drule_all_then ACCEPT_TAC classified_grouped_member_signature_mods >>
     first_assum ACCEPT_TAC) >>
  `EVERY (\(sel,_,_). sel < dimword (:256)) (grouped_selectors groups)` by
    (simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
     rename1 `MEM (sel,lbl,tz) _` >>
     `MEM sel (MAP FST (grouped_selectors groups))` by
       (simp[MEM_MAP] >> qexists_tac `(sel,lbl,tz)` >> simp[]) >>
     qpat_assum `!id. MEM id _ ==> _` drule >>
     disch_then (qx_choosel_then [`nm`,`ts`] strip_assume_tac) >>
     simp[abi_method_id_def, GSYM calldata_method_id_four_bytes, wordsTheory.w2n_lt]);

val linked_grouped_fallback_miss_tac =
  (Q.SUBGOAL_THEN `4 <= LENGTH start.vs_call_ctx.cc_calldata ==>
   EVERY (\g. case g of ExternalSingle (sel,_,_) _ =>
      calldata_method_id start.vs_call_ctx.cc_calldata <> n2w sel
    | ExternalDefaults common entries specs _ =>
        FIND (\(sel,_,_,_). calldata_method_id start.vs_call_ctx.cc_calldata = n2w sel) entries = NONE /\
        EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs) groups` assume_tac
    >- (`start.vs_call_ctx.cc_calldata = cd` by simp[Abbr `cd`] >>
     qpat_assum `start.vs_call_ctx.cc_calldata = cd` SUBST1_TAC >> strip_tac >>
     `~(LENGTH cd < 4)` by decide_tac >>
     `FIND (\(nm,ts). abi_method_id (type_env_all_modules mods) nm ts = cd_selector cd)
       (abi_deployed_signatures mods exps) = NONE` by
       (qpat_assum `(if LENGTH cd < 4 then NONE else _) = NONE` (fn miss =>
          qpat_assum `~(LENGTH cd < 4)` (fn long =>
            ACCEPT_TAC (SIMP_RULE bool_ss [long] miss)))) >>
     `~MEM (cd_selector cd) (MAP FST (grouped_selectors groups))` by
       (strip_tac >> qpat_assum `!id. MEM id _ ==> _` drule >>
        disch_then (qx_choosel_then [`nm`,`ts`] strip_assume_tac) >>
        qpat_assum `FIND _ (abi_deployed_signatures mods exps) = NONE`
          (mp_tac o SIMP_RULE (srw_ss())
            [mem2varBlockSimHelpersTheory.FIND_NONE_EVERY, EVERY_MEM, combinTheory.o_DEF, FORALL_PROD]) >>
        disch_then (qspecl_then [`nm`,`ts`] mp_tac) >> simp[]) >>
     `EVERY (\g. case g of ExternalSingle (sel,_,_) _ => calldata_method_id cd <> n2w sel
        | ExternalDefaults _ entries _ _ =>
           FIND (\(sel,_,_,_). calldata_method_id cd = n2w sel) entries = NONE) groups` by
       (irule grouped_selector_misses >> simp[GSYM calldataSelectorPropsTheory.cd_selector_method_id]) >>
     simp[EVERY_MEM] >> qx_gen_tac `g` >> strip_tac >>
     qpat_assum `EVERY (\g. case g of ExternalSingle _ _ => _ | ExternalDefaults _ _ _ _ => _) groups`
       (mp_tac o Q.SPEC `g` o REWRITE_RULE [EVERY_MEM]) >>
     Cases_on `g` >> simp[] >>
     qpat_assum `!common entries specs off. MEM (ExternalDefaults _ _ _ _) groups ==> _`
       drule >> simp[EVERY_MEM]));

val linked_grouped_fallback_hit_tac =
  `compile_entry_checks 4 T sn = ((),sn)` by
    simp[NoAsms, compile_entry_checks_def, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  `fn_has_code sn sn fn` by
    (simp[NoAsms, fn_has_code_def, emitted_blocks_def] >>
     qexists_tac `target` >> simp[]) >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`pay` |-> `T`] grouped_fallback_checks_pass)) >>
  disch_then (qspecl_then [`entry_taint`,`[]`,`FEMPTY`]
    (qx_choosel_then [`hit`,`Gh`,`tnh`] (map_every assume_tac o CONJUNCTS))) >>
  `hit.vs_call_ctx = vs.vs_call_ctx` by
    (qpat_assum `selected_registration_frame start entry_taint hit tnh` mp_tac >>
     qpat_assum `start.vs_call_ctx = vs.vs_call_ctx` (fn call_ctx =>
       simp[NoAsms, selected_registration_frame_def, call_ctx])) >>
  `hit.vs_call_ctx.cc_callvalue = n2w tx.value` by
    (qpat_assum `hit.vs_call_ctx = vs.vs_call_ctx` SUBST1_TAC >>
     qpat_assum `initial_venom_state_rel_mods mods am tx vs` mp_tac >>
     simp[NoAsms, initial_venom_state_rel_mods_def, venom_env_rel_def, call_ctx_rel_def]) >>
  `LENGTH hit.vs_call_ctx.cc_calldata < dimword (:256)` by simp[Abbr `cd`, dimword_def];

val linked_grouped_fallback_entry_ghost_tac =
  `entry_prov fn start FEMPTY = FEMPTY /\
   entry_taint_vars fn start entry_taint = entry_taint` by
    (`?bb. venomInst$lookup_block "__entry" fn.fn_blocks = SOME bb` by
       (qpat_assum `fn_entry_label fn = SOME "__entry"` mp_tac >>
        Cases_on `fn.fn_blocks`
        >- (qpat_assum `fn.fn_blocks = []` (fn blocks =>
             simp[NoAsms, blocks, fn_entry_label_def, entry_block_def])) >>
        qpat_assum `fn.fn_blocks = _::_` (fn blocks =>
          simp[NoAsms, blocks, fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm])) >>
     irule typedCopyArrayPtrTheory.entry_ghost_no_phi >>
     qexists_tac `bb` >> simp[] >>
     qpat_assum `!label bb. venomInst$lookup_block label _ = SOME bb ==> _`
       (qspecl_then [`"__entry"`,`bb`] mp_tac) >> simp[]);

val linked_grouped_fallback_abort_path_tac =
  `tx.value < dimword (:256)` by
    (qpat_assum `call_tx_well_typed tx` mp_tac >>
     simp[NoAsms, call_tx_well_typed_def, dimword_def]) >>
  `mut <> Payable /\ tx.value <> 0` by fs[] >>
  `hit.vs_call_ctx.cc_callvalue <> 0w` by
    (qpat_assum `hit.vs_call_ctx.cc_callvalue = _` SUBST1_TAC >>
     qpat_assum `tx.value <> 0` (fn nz =>
       qpat_assum `tx.value < dimword (:256)` (fn bound =>
         simp[NoAsms, wordsTheory.n2w_11, nz, bound]))) >>
  `compile_entry_checks 4 F sn = ((),body_start)` by
    (qpat_assum `compile_entry_checks 4 (mut = Payable) sn = ((),body_start)` mp_tac >>
     qpat_assum `mut <> Payable` (fn no => simp[NoAsms, no])) >>
  qpat_assum `selected_registration_resources _ _ _ _ sn hit`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [selected_registration_resources_def]) >>
  `ctx_has_dalloca unit.cu_context ==> allocas_below_fmp hit` by
    (strip_tac >> qpat_assum `ctx_has_dalloca _ ==> allocas_below_fmp hit /\ _`
      (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  (fn goal =>
    mp_tac (SIMP_RULE (srw_ss()) []
      (Q.INST [`m` |-> `4`, `pay` |-> `F`, `st` |-> `sn`, `last` |-> `body_start`,
        `s` |-> `hit`, `lo` |-> `0`, `ctx` |-> `unit.cu_context`,
        `PG` |-> `[]`,`G` |-> `Gh`,`tn` |-> `tnh`]
        (SPEC_ALL entryChecksRejectJointTheory.compile_entry_checks_reject_joint))) goal) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[dimword_def]])) >>
  disch_then (qx_choosel_then [`abort_state`,`abort_prov`,`abort_taint`]
     (map_every assume_tac o CONJUNCTS)) >>
  `!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
    (start,FEMPTY,entry_taint) [] (Abort Revert_abort abort_state,abort_prov,abort_taint)` by
    (rpt gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gh`,`hit`,`tnh`] >> asm_rewrite_tac[]);

val linked_grouped_fallback_reject_tac =
  linked_grouped_fallback_abort_path_tac >>
  `!gobs. call_external_trace (SOME vs.vs_outcomes) gobs am tx =
    (INR (Error (RuntimeError "not Payable")),am,[],[])` by
    (qpat_assum `Abbrev (src = ALOOKUP exps tx.function_name)` (fn owner =>
       let val source = REWRITE_RULE [markerTheory.Abbrev_def] owner in
         qpat_assum `ALOOKUP mods src = SOME tops` (assume_tac o REWRITE_RULE [source]) >>
         qpat_assum `vyperInterpreter$lookup_function src tx.function_name External tops = _`
           (assume_tac o REWRITE_RULE [source])
       end) >>
     `LENGTH tx.args <= LENGTH ([]: (string # type) list) /\
      LENGTH ([]: (string # type) list) - LENGTH tx.args <= LENGTH ([]:expr list)` by simp[] >>
     drule_all (SIMP_RULE (srw_ss()) []
       (Q.INST [`args` |-> `[]`,`dflts` |-> `[]`] linked_external_value_reject_trace)) >>
     disch_then (qspec_then `SOME vs.vs_outcomes` ACCEPT_TAC)) >>
  `!D fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn [] FEMPTY entry_taint start` by
    (qspecl_then [`unit.cu_context`,`fn`,`vs`,`abort_state`,`abort_prov`,`abort_taint`,`[]`]
       mp_tac entry_joint_revert_exit >>
     qpat_assum `Abbrev (start = _)`
       (fn initial => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] initial)]) >>
     impl_tac >- (rpt conj_tac >> asm_rewrite_tac[]) >>
     strip_tac >> asm_rewrite_tac[]) >>
  `gas_origin_path T (gas_explicit_sites unit.cu_context shadow_unit.cu_context)
    unit.cu_context fn start [] (Abort Revert_abort abort_state)` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ (start,_,_) [] (Abort Revert_abort abort_state,_,_)`
       (qspecl_then [`ARB`,`gas_explicit_sites unit.cu_context shadow_unit.cu_context`]
        (ACCEPT_TAC o CONJUNCT1 o MATCH_MP (SPEC_ALL gas_origin_ptr_path_projections)))) >>
  qpat_assum `lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn`
    (assume_tac o MATCH_MP lookup_function_MEM) >>
  qpat_assum `lookup_function "__entry" shadow_unit.cu_context.ctx_functions = SOME shfn`
    (assume_tac o MATCH_MP lookup_function_MEM) >>
  `storage_trace_domain (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am []) []` by
    simp[NoAsms, storage_trace_domain_def, valid_horizon_def,
         storage_observations_ok_def, storage_trace_horizon_def,
         storage_trace_regions_def, storage_trace_locks_def, regions_consistent_def,
         storage_locks_separated_def, storage_well_formed_on_def, storage_roots_fit_def,
         storage_trace_backends_well_formed_def] >>
  qexists_tac `[]` >> conj_tac
  >- (rewrite_tac [source_unit_execution_correct_with_mods_def] >>
      qexistsl_tac [`fn`,`shfn`] >> asm_rewrite_tac[] >> disj2_tac >>
      qexistsl_tac [`INR (Error (RuntimeError "not Payable"))`,`am`,`[]`,`[]`] >>
      asm_rewrite_tac[] >> disj2_tac >> qexists_tac `Abort Revert_abort abort_state` >>
      qpat_assum `Abbrev (start = _)` (fn initial =>
        PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] initial)]) >>
      simp[exit_result_def, external_call_result_rel_mods_def]) >>
  disch_tac >> qx_gen_tac `tail` >>
  qpat_assum `!gobs. call_external_trace _ _ _ _ = _`
    (qspec_then `gas_explicit [] vs.vs_gas_readings ++ tail`
      (fn trace => simp[NoAsms, CONJUNCT1 (MATCH_MP call_external_trace_result trace)]));

val linked_grouped_fallback_pass_tac =
  (Q.SUBGOAL_THEN `mut = Payable \/ hit.vs_call_ctx.cc_callvalue = 0w` assume_tac
   >- (qpat_assum `hit.vs_call_ctx.cc_callvalue = n2w tx.value` SUBST1_TAC >>
       qpat_assum `mut = Payable \/ tx.value = 0`
         (DISJ_CASES_THEN (fn accepted => simp[NoAsms, accepted])))) >>
  (fn goal => mp_tac (SIMP_RULE (srw_ss()) []
      (Q.INST [`m` |-> `4`, `pay` |-> `mut = Payable`, `sa` |-> `sn`, `sb` |-> `body_start`,
        `s` |-> `hit`, `lo` |-> `0`, `site` |-> `ARB`, `ctx` |-> `unit.cu_context`,
        `PG` |-> `[]`, `G` |-> `Gh`, `tn` |-> `tnh`]
        (SPEC_ALL grouped_default_checks_pass_origin))) goal) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[dimword_def]])) >>
  disch_then (qx_choosel_then [`fallback_body_vs`,`fallback_body_G`,`fallback_body_taint`]
    (map_every assume_tac o CONJUNCTS)) >>
  `!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
    (start,FEMPTY,entry_taint) [] (OK fallback_body_vs,fallback_body_G,fallback_body_taint)` by
    (rpt gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gh`,`hit`,`tnh`] >> asm_rewrite_tac[]) >>
  `selected_registration_frame vs entry_taint fallback_body_vs fallback_body_taint` by
    (qpat_assum `selected_registration_frame start entry_taint hit tnh` mp_tac >>
     qpat_assum `selected_registration_frame hit tnh fallback_body_vs fallback_body_taint` mp_tac >>
     simp[NoAsms, selected_registration_frame_def, Abbr `start`] >>
     rpt strip_tac >> asm_rewrite_tac[]);

val linked_grouped_fallback_empty_register_tac =
  `bind_arguments (type_env_all_modules mods) [] tx.args = SOME FEMPTY` by
    (qpat_assum `tx.args = []` (fn args => simp[NoAsms, args, bind_arguments_def])) >>
  `compile_register_positional_args ce [] 4 body_start = (ce,body_start) /\
   compile_register_positional_args (gas_shadow_env T ce) [] 4 shadow_body_start =
     (gas_shadow_env T ce,shadow_body_start)` by
    simp[NoAsms, compile_register_positional_args_def, comp_return_def] >>
  `ce.ce_vars = FEMPTY` by
    (qpat_assum `fall = SOME (_,_,_,_,_,_,_,_)` mp_tac >>
     qpat_assum `Abbrev (fall = _)`
       (fn alias => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] alias]) >>
     qpat_assum `fb = SOME (ALOOKUP exps "__default__",_)` SUBST1_TAC >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `ret = NoneT` >> pop_assum (fn none =>
       simp[NoAsms, none, package_fallback_fn_unit_def, set_fallback_package_target_def,
           LET_THM, build_compile_env_unit_def, update_cenv_ret_abi_def,
           update_cenv_nonreentrant_def, allocate_args_def, pairTheory.ELIM_UNCURRY]) >>
     strip_tac >> qpat_assum `_ = ce` (SUBST1_TAC o SYM) >> simp[NoAsms]) >>
  `local_ptrs_rel fn ce [FEMPTY] fallback_body_vs` by
    (qpat_assum `ce.ce_vars = FEMPTY` (fn vars => simp[NoAsms, vars, local_ptrs_rel_def, local_region_def]));

val linked_grouped_fallback_transfer_tac =
  `cx.txn = tx` by simp[NoAsms, Abbr `cx`, initial_evaluation_context_def] >>
  `value_transfer_ok cx.txn (initial_state am [FEMPTY] with
       <|outcomes := SOME vs.vs_outcomes; requests := []|>).accounts` by
    (qpat_assum `initial_venom_state_rel_mods mods am tx vs` mp_tac >>
     qpat_assum `cx.txn = tx` SUBST1_TAC >>
     simp[NoAsms, initial_state_def, initial_venom_state_rel_mods_def]);

val linked_grouped_fallback_send_tac =
  (Q.SUBGOAL_THEN `?es0. send_call_value mut cx (initial_state am [FEMPTY] with
        <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es0)`
     (qx_choose_then `es0` assume_tac)
   >- (Cases_on `send_call_value mut cx (initial_state am [FEMPTY] with
        <|outcomes := SOME vs.vs_outcomes; requests := []|>)` >>
       rename1 `_ = (res,es)` >> Cases_on `res` >> simp[NoAsms] >>
       drule_all_then strip_assume_tac send_call_value_reject_condition >>
       qpat_assum `mut = Payable \/ tx.value = 0` mp_tac >>
       qpat_assum `cx.txn = tx` (fn txn =>
         qpat_assum `cx.txn.value <> 0` (fn nz =>
           qpat_assum `mut <> Payable` (fn np =>
             simp[NoAsms, REWRITE_RULE [txn] nz, np])))));

(* A long miss may allocate keyword buffers. Preserve their history; only the
   source locals and positional registration are empty at this cut. *)
val linked_grouped_fallback_resources_tac =
  qpat_assum `selected_registration_resources _ _ _ _ body_start fallback_body_vs`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [selected_registration_resources_def]) >>
  qpat_assum `selected_registration_frame vs entry_taint fallback_body_vs fallback_body_taint`
    (map_every assume_tac o CONJUNCTS o SIMP_RULE (srw_ss())
      [selected_registration_frame_def, entry_taint_def]) >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) []
                (OK fallback_body_vs,fallback_body_G,fallback_body_taint)`
    (qspecl_then [`ARB`,`{}`] assume_tac) >>
  `fallback_body_vs.vs_initial_fmp = vs.vs_initial_fmp` by
    (drule_all decoder_origin_path_allocation_frame >> simp[NoAsms, Abbr `start`]) >>
  `fallback_body_vs.vs_fmp = fallback_body_vs.vs_initial_fmp` by
    (qpat_assum `fallback_body_vs.vs_fmp = vs.vs_fmp` SUBST1_TAC >>
     qpat_assum `fallback_body_vs.vs_initial_fmp = vs.vs_initial_fmp` SUBST1_TAC >>
     qpat_assum `initial_venom_state_rel_mods mods am tx vs` mp_tac >>
     simp[NoAsms, initial_venom_state_rel_mods_def]) >>
  `fmp_room unit.cu_context fn fallback_body_vs` by
    (MATCH_MP_TAC (Q.INST [`site` |-> `ARB`] entry_frontier_fmp_room) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       qpat_assum `fallback_body_vs.vs_initial_fmp = vs.vs_initial_fmp` SUBST1_TAC >>
       simp[]]) >>
  `abi_alloca_history (fn_insts fn) start` by
    (MATCH_MP_TAC abi_alloca_history_empty >> first_assum ACCEPT_TAC) >>
  `abi_alloca_history (fn_insts fn) fallback_body_vs` by
    drule_all_then ACCEPT_TAC groupedEntryAllocationTheory.grouped_entry_path_abi_history;

val linked_grouped_fallback_env_tac =
  `set_external_package_target rpolicy.rpol_target
    (package_external_fn_unit mods T (K global_nonreentrant_slot)
      (src,subst_consts_fn_mods (consts_env_mods mods)
        (mut,nr,lookup_raw_return_or_F src tx.function_name External tops,
         tx.function_name,[],[],ret,fbody))) =
    ("fn___default__",ce,[],4,mut = Payable,nr,global_nonreentrant_slot,T,
       mut = View,fallback_code,fallback_rt)` by
    (qpat_assum `fall = SOME (_,_,_,_,_,_,_,_)` mp_tac >>
     qpat_assum `Abbrev (fall = _)`
       (fn alias => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] alias]) >>
     qpat_assum `fb = SOME (ALOOKUP exps "__default__",_)` SUBST1_TAC >>
     qpat_assum `tx.function_name = "__default__"` (fn name =>
       simp[NoAsms, Abbr `src`, Abbr `fallback_code`, name,
            package_fallback_fn_unit_def, set_fallback_package_target_def,
            package_external_fn_unit_def, set_external_package_target_def,
            subst_consts_fn_mods_def, subst_consts_expr_mods_def,
            build_positional_args_def, min_calldata_size_def, LET_THM])) >>
  qabbrev_tac `fallback_shadow_env = gas_shadow_env T ce`;

(* Name the common guarded-body inputs without rewriting the grouped
   dispatcher, whose package uses literal lock settings. *)
val linked_grouped_fallback_bindings_tac =
  (Q.SUBGOAL_THEN `?args env. args = ([]:(string # type) list) /\ env = FEMPTY /\
     bind_arguments (type_env_all_modules mods) args tx.args = SOME env /\
     vyperInterpreter$lookup_function src tx.function_name External tops =
       SOME (mut,nr,args,[],ret,fbody) /\
     vyperInterpreter$lookup_function (ALOOKUP exps "__default__") "__default__" External tops =
       SOME (mut,nr,args,[],ret,fbody) /\
     send_call_value mut cx (initial_state am [env] with
       <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es0)`
     (qx_choosel_then [`args`,`env`] (map_every assume_tac o CONJUNCTS))
   >- (qexistsl_tac [`[]`,`FEMPTY`] >> simp_tac bool_ss [] >>
       rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  `src = ALOOKUP exps tx.function_name` by simp[NoAsms, Abbr `src`] >>
  `ce.ce_module = src` by
    (qpat_assum `set_external_package_target _ _ = _` mp_tac >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn none => simp[NoAsms, none, package_external_fn_unit_def,
       set_external_package_target_def, subst_consts_fn_mods_def,
       update_cenv_nonreentrant_def, update_cenv_ret_abi_def, LET_THM]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `_ = ce` (SUBST1_TAC o SYM) >>
     simp[NoAsms, build_compile_env_unit_def, pairTheory.ELIM_UNCURRY]);

val linked_grouped_fallback_invariant_tac =
  qabbrev_tac `fallback_base =
    build_compile_env_unit mods src External mut "__default__" args ret fallback_code T` >>
  `contract_inv mods exps unit.cu_context
      (fallback_base with ce_target := rpolicy.rpol_target) cx` by
    (qpat_assum `!mut args ret ss. contract_inv _ _ _ _ _`
       (qspecl_then [`mut`,`args`,`ret`,`fallback_code`] mp_tac) >>
     qpat_assum `tx.function_name = "__default__"` (fn name =>
       simp[NoAsms, name, Abbr `fallback_base`])) >>
  `ce = update_cenv_nonreentrant
      (if ret = NoneT then fallback_base with ce_raw_return :=
        lookup_raw_return_or_F src "__default__" External tops
       else update_cenv_ret_abi (fallback_base with ce_raw_return :=
        lookup_raw_return_or_F src "__default__" External tops) ret)
      nr global_nonreentrant_slot T (mut = View)
    with ce_target := rpolicy.rpol_target` by
    (qpat_assum `fall = SOME (_,_,_,_,_,_,_,_)` mp_tac >>
     qpat_assum `Abbrev (fall = _)`
       (fn alias => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] alias]) >>
     qpat_assum `fb = SOME (ALOOKUP exps "__default__",_)` SUBST1_TAC >>
     Cases_on `ret = NoneT` >> pop_assum (fn none =>
       qpat_assum `args = []` (fn empty =>
         qpat_assum `tx.function_name = "__default__"` (fn name =>
           simp[NoAsms, none, empty, name, Abbr `fallback_base`, Abbr `src`,
             package_fallback_fn_unit_def, set_fallback_package_target_def,
             combinTheory.K_THM, LET_THM]))) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     first_assum (ACCEPT_TAC o SYM)) >>
  `module_body_inv mods src tops ce cx` by
    (qpat_assum `ce = _` SUBST1_TAC >> Cases_on `ret = NoneT` >>
     pop_assum (fn none => simp[NoAsms, none, module_body_inv_def,
       Abbr `fallback_base`, Abbr `src`, build_compile_env_unit_def, pairTheory.ELIM_UNCURRY,
       update_cenv_nonreentrant_def, update_cenv_ret_abi_def]) >>
     first_assum ACCEPT_TAC) >>
  `contract_inv mods exps unit.cu_context ce cx` by
    (qpat_assum `contract_inv mods exps _ (fallback_base with ce_target := _) cx` mp_tac >>
     qpat_assum `ce = _` SUBST1_TAC >> Cases_on `ret = NoneT` >>
     pop_assum (fn none => simp[NoAsms, none, contract_inv_def, cenv_module_pins_mods_def,
       immutable_section_layout_mods_def, update_cenv_nonreentrant_def, update_cenv_ret_abi_def]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     asm_rewrite_tac[] >> rpt conj_tac >>
     FIRST [qpat_assum `fallback_base.ce_struct_fields = _`
       (fn fields => PURE_REWRITE_TAC [GSYM fields] >> first_assum ACCEPT_TAC),
       qpat_assum `fallback_base.ce_module_vars = _`
       (fn locations => PURE_REWRITE_TAC [GSYM locations] >> first_assum ACCEPT_TAC),
       rpt gen_tac >> strip_tac >>
       qpat_assum `!sid ts. ALOOKUP mods sid = SOME ts ==> supported_module_headers ts /\ _`
         (drule_then (fn headers => simp[NoAsms, headers]))]);

fun linked_grouped_fallback_state_tac premises_tac =
  `vars_pc_only (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
     vs_inst_idx := 0|>) vs` by
    simp[NoAsms, vars_pc_only_def, venomStateTheory.venom_state_component_equality] >>
  qpat_assum `initial_venom_state_rel_mods _ _ _ vs`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [initial_venom_state_rel_mods_def]) >>
  `send_call_value mut (initial_evaluation_context am.sources am.layouts tx src)
      (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
      (INL (),es0)` by
    (qpat_assum `Abbrev (cx = _)` (fn cx =>
       PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] cx)]) >>
     first_assum ACCEPT_TAC) >>
  `!H:(bool # 256 word # type_value) list # num list.
    stmt_state_rel H unit.cu_context fn ce cx es0 fallback_body_vs /\
    ghost_inv H NONE ce cx es0 fallback_body_G fallback_body_taint fallback_body_vs` by
    (gen_tac >>
     qpat_assum `Abbrev (cx = _)` (fn cx =>
       PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] cx]) >>
     mp_tac (Q.INST [`efn` |-> `fn`, `cenv0` |-> `ce`, `cenv` |-> `ce`,
       `pos_args` |-> `[]`, `mincd` |-> `4`, `ut'` |-> `T`, `iv` |-> `mut = View`,
       `args` |-> `[]`, `env` |-> `FEMPTY`, `pay` |-> `mut = Payable`,
       `key` |-> `global_nonreentrant_slot`,
       `lowered_body` |-> `fallback_code`, `rt` |-> `fallback_rt`,
       `st` |-> `body_start`, `sa` |-> `body_start`,
       `elbl` |-> `"__entry"`, `lbl` |-> `"fn___default__"`,
       `s0` |-> `fallback_body_vs`, `s1` |-> `vs`, `tvs` |-> `[]`,
       `site` |-> `ARB`, `G0` |-> `fallback_body_G`, `tn0` |-> `fallback_body_taint`]
        (Q.INST_TYPE [`:'a` |-> `:256`]
          registration_actual_endpoint_relations_from_prefix_mods)) >>
     (impl_tac >- premises_tac) >> disch_then ACCEPT_TAC);

val linked_grouped_fallback_guard_code_tac =
  rename1 `Abbrev (rt = if ret = NoneT then NONE else SOME ret)` >>
  `rt = if ret = NoneT then NONE else SOME ret` by simp[NoAsms, Abbr `rt`] >>
  (Q.SUBGOAL_THEN `?pay key tr view.
    pay = (mut = Payable) /\ key = global_nonreentrant_slot /\ tr /\ view = (mut = View) /\
    fall = SOME (ce,pay,nr,key,tr,view,fallback_code,rt) /\
    compile_guarded_body ce nr key tr view fallback_code rt body_start = ((),se) /\
    compile_guarded_body (gas_shadow_env T ce) nr key tr view
      (MAP gas_shadow_stmt fallback_code) rt shadow_body_start = ((),she)`
    (qx_choosel_then [`pay`,`key`,`tr`,`view`] (map_every assume_tac o CONJUNCTS))
   >- (qexistsl_tac [`mut = Payable`,`global_nonreentrant_slot`,`T`,`mut = View`] >>
       simp_tac bool_ss [] >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
         qpat_assum `Abbrev (fallback_shadow_env = _)`
           (fn env => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] env)] >>
              first_assum ACCEPT_TAC)])) >>
  qpat_assum `compile_guarded_body ce nr key tr view _ rt body_start = ((),se)`
    (fn guarded => qpat_assum `fn_has_code body_start se fn`
      (mp_tac o MATCH_MP guarded_body_code_from_registration o CONJ guarded)) >>
  disch_then (qx_choosel_then [`fallback_locked`,`fallback_body_end`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `compile_guarded_body (gas_shadow_env T ce) nr key tr view
     (MAP gas_shadow_stmt fallback_code) rt shadow_body_start = ((),she)`
    (fn guarded => qpat_assum `fn_has_code shadow_body_start she shfn`
      (mp_tac o MATCH_MP guarded_body_code_from_registration o CONJ guarded)) >>
  disch_then (qx_choosel_then [`shadow_fallback_locked`,`shadow_fallback_body_end`]
    (map_every assume_tac o CONJUNCTS));

val linked_grouped_fallback_path_tac =
  qabbrev_tac `explicit = gas_explicit_sites unit.cu_context shadow_unit.cu_context` >>
  `!D. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
      (start,FEMPTY,entry_taint) [] (OK fallback_body_vs,fallback_body_G,fallback_body_taint)` by
    (qx_gen_tac `D` >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) []
       (OK fallback_body_vs,_,_)` (qspecl_then [`D`,`explicit`] ACCEPT_TAC)) >>
  `alloca_history fn start` by (irule alloca_history_empty >> asm_rewrite_tac[]) >>
  `alloca_history fn fallback_body_vs` by drule_all_then ACCEPT_TAC body_full_path_alloca_history >>
  `~block_is_terminated body_start` by
    (irule selectedEntryPrefixCodeTheory.compile_entry_checks_open >>
     qexistsl_tac [`4`,`mut = Payable`,`sn`,`()`] >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `sn.cs_current_insts = []` (fn empty =>
       simp[NoAsms, block_is_terminated_def, empty])) >>
  `fallback_body_vs.vs_labels = vs.vs_labels` by
    (qpat_assum `gas_origin_ptr_path _ (start,FEMPTY,entry_taint) []
       (OK fallback_body_vs,_,_)`
       (mp_tac o MATCH_MP gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels) >>
     simp[NoAsms, Abbr `start`]);

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_fallback]:
  linked_grouped_fallback_source_tac >> linked_grouped_fallback_classified_tac >>
  linked_grouped_fallback_lookup_tac >> linked_grouped_fallback_code_tac >>
  linked_grouped_fallback_start_tac >> linked_grouped_fallback_span_tac >>
  linked_grouped_fallback_widths_tac >> linked_grouped_fallback_selectors_tac >>
  linked_grouped_fallback_miss_tac >> linked_grouped_fallback_hit_tac >>
  linked_grouped_fallback_entry_ghost_tac >>
  reverse (DISJ_CASES_THEN assume_tac
    (Q.SPEC `mut = Payable \/ (tx:call_txn).value = 0` EXCLUDED_MIDDLE))
  >- linked_grouped_fallback_reject_tac >>
  linked_grouped_fallback_pass_tac >> linked_grouped_fallback_empty_register_tac >>
  linked_grouped_fallback_transfer_tac >> linked_grouped_fallback_send_tac >>
  linked_grouped_fallback_resources_tac >>
  linked_grouped_fallback_env_tac >>
  linked_grouped_fallback_bindings_tac >> linked_grouped_fallback_invariant_tac >>
  linked_empty_source_frame_tac >> linked_empty_source_declaration_tac >>
  linked_empty_source_checked_tac >> linked_empty_source_static_env_tac >>
  linked_empty_source_typed_tac >> linked_empty_body_types_tac >>
  linked_empty_body_support_tac >> linked_empty_body_live_tac >>
  linked_empty_body_immutable_tac >> linked_empty_body_lock_tac >>
  linked_empty_body_base_tac >> linked_empty_body_package_tac >>
  linked_empty_body_context_tac >> linked_empty_body_alloc_tac >>
  linked_empty_body_alloc_bounds_tac >> linked_empty_body_widths_tac >>
  linked_grouped_fallback_state_tac (suspend "linked_grouped_fallback_state_premises") >>
  suspend "linked_grouped_fallback_guarded"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_fallback_state_premises]:
  rpt disch_tac >> simp[NoAsms] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `Abbrev (cx = _)` (fn cx =>
        PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] cx)]) >>
      first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (raw = _)`
    (fn raw => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] raw)]) >>
  first_assum ACCEPT_TAC
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_fallback_guarded]:
  linked_grouped_fallback_guard_code_tac >>
  linked_empty_body_return_buffer_tac >> linked_empty_body_stmts_exprs_tac >>
  linked_empty_return_plan_tac >> linked_empty_return_none_tac >>
  linked_grouped_fallback_path_tac >>
  `shadow_body_inv_mods mods exps unit.cu_context shadow_unit.cu_context` by
    (map_every (fn pattern =>
       qpat_assum pattern (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]))
       [`Abbrev (groups = _)`,`Abbrev (ips = _)`,`Abbrev (fall = _)`] >>
     qmatch_asmsub_abbrev_tac
       `run_grouped_lowering grouped_shadow_groups
         (MAP gas_shadow_internal_package ips) (OPTION_MAP gas_shadow_fallback_package fall)
         rpolicy "__entry" = SOME shadow_unit` >>
     qpat_assum `check_contract F am.layouts tx.target mods = SOME art`
       (mp_then Any mp_tac (Q.INST [`shadow_groups` |-> `grouped_shadow_groups`,
          `rp` |-> `rpolicy`] grouped_runtime_shadow_body_inv_mods)) >>
     disch_then (qspecl_then [`unit`,`rpolicy`,`ips`,`ints`,`imp_ctors`,
       `groups`,`grouped_shadow_groups`,`fb`,`fall`,`exts`,`exps`,`ctor`] mp_tac) >>
     impl_tac
     >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       qpat_assum `Abbrev (grouped_shadow_groups = _)`
         (ACCEPT_TAC o REWRITE_RULE [markerTheory.Abbrev_def])]) >>
     qpat_assum `run_grouped_lowering grouped_shadow_groups _ _ _ _ = SOME shadow_unit`
       (fn compiled => simp[NoAsms, compiled, optionTheory.SOME_11])) >>
  rename1 `gas_shadow_function fn fallback_shadow_fn` >>
  linked_empty_entry_static_tac >>
  linked_empty_registered_cut_tac >> linked_registered_stmts_env_tac >>
  linked_registered_path_tac >>
  linked_registered_lock_cases_tac
    (suspend "linked_grouped_fallback_lock_success")
    (suspend "linked_grouped_fallback_lock_abort")
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_fallback_lock_abort]:
  linked_registered_lock_abort_tac >> linked_registered_lock_abort_source_tac >>
  linked_registered_lock_abort_domain_tac >> linked_registered_lock_abort_finish_tac
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_fallback_lock_success]:
  linked_registered_lock_success_tac >> linked_registered_locked_horizon_tac >>
  linked_registered_replay_tac >> linked_registered_return_frame_tac >>
  rename1 `lookup_block fall_lbl fn.fn_blocks = SOME fallback_start_block` >>
  linked_registered_structs_tac >> linked_registered_abi_targets_tac >>
  linked_registered_fragment_tac >> linked_registered_shadow_tac >>
  linked_registered_admissible_tac >> linked_registered_reachability_tac >>
  linked_registered_immutable_frame_tac >> linked_registered_storage_prefix_tac >>
  linked_registered_run_tac >> linked_registered_trace_inputs_tac >>
  linked_registered_compose_tac
    {horizon_tac = linked_registered_trace_horizon_tac,
     tails_tac = linked_registered_trace_tails_tac,
     exempt_tac = linked_registered_trace_exempt_tac,
     fallthrough_tac = linked_registered_fallthrough_tac
       linked_registered_fallthrough_ghost_tac linked_registered_fallthrough_result_tac,
     exit_tac = linked_registered_trace_exit_tac linked_registered_abort_or_halt_tac,
     readings_tac = linked_registered_trace_readings_tac,
     finish_tac = linked_registered_finish_tac}
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_signature]:
  drule_all_then (qx_choosel_then
    [`selected_tops`,`top`,`mut`,`nr`,`selected_raw`,`args`,`dflts`,`ret`,
     `selected_body`,`prefix`,`k`] (map_every assume_tac o CONJUNCTS))
    deployed_grouped_signature_member_mods >>
  `ALOOKUP mods src = SOME selected_tops` by simp[Abbr `src`] >>
  `MEM (tx.function_name,tys) (abi_decl_signatures top)` by
    (qpat_assum `abi_decl_signatures top = _` SUBST1_TAC >>
     simp_tac (srw_ss()) [abi_function_signatures_def,MEM_MAP,pairTheory.EXISTS_PROD] >>
     qexistsl_tac [`prefix`,`k`] >> asm_rewrite_tac[]) >>
  drule_all_then assume_tac source_typing_ok_mods_external_names_distinct >>
  `vyperInterpreter$lookup_function src tx.function_name External selected_tops =
    SOME (mut,nr,args,dflts,ret,selected_body)` by
    (irule lookup_function_external_unique_tagged_decl >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `top` >> asm_rewrite_tac[] >>
     reverse conj_tac
     >- (irule abi_decl_signature_external_key >>
         qexists_tac `tys` >> first_assum ACCEPT_TAC) >>
     qpat_assum `(tx.function_name <> "__default__" /\ _) \/ _`
       (DISJ_CASES_THEN2 strip_assume_tac
         (strip_assume_tac o REWRITE_RULE [tagged_getter_source_tuple]))
     >- (qpat_assum `top = FunctionDecl External _ _ _ _ _ _ _ _` SUBST1_TAC >>
         simp[NoAsms, vyperInterpreterTheory.lookup_function_def]) >>
     qpat_assum `is_public_getter_decl tx.function_name top` mp_tac >>
     qpat_assum `Abbrev (src = ALOOKUP exps tx.function_name)` (fn owner =>
       qpat_assum `external_getter_tuple (ALOOKUP exps tx.function_name) top = _`
         (mp_tac o REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] owner)])) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `top` >> simp[is_public_getter_decl_def] >>
     Cases_on `v` >> simp[is_public_getter_decl_def, external_getter_tuple_def,
       vyperInterpreterTheory.lookup_function_def] >>
     rpt strip_tac >> gvs[]) >>
  `external_return_type_mods mods exps tx.function_name = ret` by
    (qpat_assum `Abbrev (src = ALOOKUP exps tx.function_name)` (fn owner_src =>
      qpat_assum `ALOOKUP mods src = SOME selected_tops` (fn owner =>
        qpat_assum `vyperInterpreter$lookup_function src tx.function_name External selected_tops =
           SOME (mut,nr,args,dflts,ret,selected_body)` (fn selected =>
          simp_tac std_ss [external_return_type_mods_def, LET_THM,
            GSYM (REWRITE_RULE [markerTheory.Abbrev_def] owner_src), owner, selected,
            optionTheory.option_case_def, pairTheory.pair_case_thm])))) >>
  qpat_assum `external_return_type_mods _ _ _ = _`
    (fn return_type => PURE_REWRITE_TAC [return_type]) >>
  `params_ok (type_env_all_modules mods) args` by
    (irule checked_external_parameter_types_mods >>
     rpt (goal_assum (drule_at Any)) >> metis_tac[]) >>
  `k <= LENGTH dflts /\ prefix = TAKE (LENGTH args - LENGTH dflts + k) args` by
    fs[abi_entries_member] >>
  `abi_method_id (type_env_all_modules mods) tx.function_name tys = cd_selector cd` by
    drule_then (ACCEPT_TAC o SIMP_RULE (srw_ss()) [pairTheory.UNCURRY]) venomInstTheory.FIND_P >>
  qabbrev_tac `entry_key = (src,subst_consts_fn_mods (consts_env_mods mods)
    (mut,nr,selected_raw,tx.function_name,args,dflts,ret,selected_body))` >>
  `MEM entry_key exts` by simp[Abbr `entry_key`, Abbr `src`] >>
  qabbrev_tac `group = package_external_group_unit mods rpolicy.rpol_target T
    (K global_nonreentrant_slot) entry_key` >>
  `?pkeys skeys. exts = pkeys ++ entry_key::skeys` by
    (pure_rewrite_tac[GSYM MEM_SPLIT] >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `pre = MAP (package_external_group_unit mods rpolicy.rpol_target T
      (K global_nonreentrant_slot)) pkeys` >>
  qabbrev_tac `post = MAP (package_external_group_unit mods rpolicy.rpol_target T
      (K global_nonreentrant_slot)) skeys` >>
  `groups = pre ++ group::post` by
    simp[Abbr `groups`, Abbr `pre`, Abbr `post`, Abbr `group`] >>
  suspend "linked_grouped_retained_route"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_retained_route]:
  `!src mut nr rr name args ds ret code.
     MAP FST (external_group_selectors
       (package_external_group_unit mods rpolicy.rpol_target T
         (K global_nonreentrant_slot) (src,(mut,nr,rr,name,args,ds,ret,code)))) =
     MAP (\(nm,tys). abi_method_id (type_env_all_modules mods) nm tys)
       (abi_function_signatures name args ds)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >> Cases_on `ds` >>
     simp[package_external_group_unit_def, package_external_fn_unit_def,
          set_external_package_target_def, external_group_selectors_def,
          compute_selector_method_id, abi_function_signatures_def, abi_entries_no_defaults,
          MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f, FORALL_PROD]) >>
  `!keys id. MEM id (MAP FST (grouped_selectors
       (MAP (package_external_group_unit mods rpolicy.rpol_target T
          (K global_nonreentrant_slot)) keys))) ==>
     ?key nm ts pref j. MEM key keys /\ fn_decl_name (SND key) = nm /\ ts = MAP SND pref /\
        (?sid m n r aa ds rt code. key = (sid,(m,n,r,nm,aa,ds,rt,code)) /\
          MEM (pref,j) (abi_entries aa ds)) /\
        id = abi_method_id (type_env_all_modules mods) nm ts` by
    (rpt gen_tac >> simp[grouped_selectors_def, MAP_FLAT, MEM_FLAT, MEM_MAP] >>
     strip_tac >> rename1 `MEM key keys` >> PairCases_on `key` >>
     `MEM id (MAP FST (external_group_selectors
        (package_external_group_unit mods rpolicy.rpol_target T
          (K global_nonreentrant_slot)
          (key0,key1,key2,key3,key4,key5,key6,key7,key8))))` by
       (simp[MEM_MAP] >> metis_tac[]) >>
     qpat_x_assum `MEM id (MAP FST (external_group_selectors _))` mp_tac >>
     qpat_assum `!src mut nr rr name args ds ret code. MAP FST _ = _`
       (fn eq => pure_rewrite_tac[eq, abi_function_signatures_def, MAP_MAP_o,
                                  combinTheory.o_DEF] >> simp[NoAsms, MEM_MAP, EXISTS_PROD]) >>
     disch_then (qx_choosel_then [`sig_args`,`j`] strip_assume_tac) >>
     qexistsl_tac [`key0`,`key1`,`key2`,`key3`,`key4`,`key5`,`key6`,`key7`,`key8`,
                   `sig_args`,`j`] >>
     simp[NoAsms, fn_decl_name_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!nm ts. MEM (nm,ts) (abi_deployed_signatures mods exps) /\
     abi_method_id (type_env_all_modules mods) nm ts = cd_selector cd ==>
     nm = tx.function_name /\ ts = tys` by
    (rpt gen_tac >> strip_tac >>
     `ALL_DISTINCT (MAP (\(nm,ts). abi_method_id (type_env_all_modules mods) nm ts)
        (abi_deployed_signatures mods exps))` by
       (qpat_assum `exports_ok am.layouts tx.target mods exps` mp_tac >>
        simp[NoAsms, vyperTypeContractTheory.exports_ok_def]) >>
     `(nm,ts) = (tx.function_name,tys)` by
       (drule mem2varProofsTheory.ALL_DISTINCT_MAP_IMP >>
        disch_then (qspecl_then [`(nm,ts)`,`(tx.function_name,tys)`] mp_tac) >> simp[]) >>
     pop_assum mp_tac >> simp[NoAsms]) >>
  `ALL_DISTINCT (MAP (fn_decl_name o SND) exts)` by
    (drule_all defaultDispatchModsNamesTheory.linked_package_labels_distinct >>
     disch_then (qspec_then `rpolicy.rpol_target` mp_tac) >>
     `!entry. FST (set_external_package_target rpolicy.rpol_target
         (package_external_fn_unit mods T (K global_nonreentrant_slot) entry)) =
       "fn_" ++ fn_decl_name (SND entry)` by
       (POP_ASSUM_LIST (K ALL_TAC) >> Cases >>
        rename1 `FST (_ (_ (_,funrec))) = _` >> PairCases_on `funrec` >>
        simp[package_external_fn_unit_def, set_external_package_target_def, fn_decl_name_def]) >>
     simp[MAP_MAP_o, combinTheory.o_DEF] >> strip_tac >>
     irule (Q.ISPEC `STRCAT "fn_"` ALL_DISTINCT_MAP) >>
     simp[MAP_MAP_o, combinTheory.o_DEF]) >>
  `fn_decl_name (SND entry_key) = tx.function_name` by
    simp[Abbr `entry_key`, subst_consts_fn_mods_def, fn_decl_name_def] >>
  `!x. MEM x pkeys ==> MEM x exts` by
    (qpat_assum `exts = pkeys ++ _` SUBST1_TAC >> simp[NoAsms, MEM_APPEND]) >>
  `~MEM (cd_selector cd) (MAP FST (grouped_selectors pre))` by
    (simp[NoAsms, Abbr `pre`] >> strip_tac >>
     qpat_assum `!keys id. MEM id _ ==> _` drule >>
     disch_then (qx_choosel_then [`other`,`nm`,`ts`,`pf`,`j`] strip_assume_tac) >>
     `MEM other exts` by
       (qpat_assum `!x. MEM x pkeys ==> MEM x exts` (drule_then ACCEPT_TAC)) >>
     `MEM (nm,ts) (abi_deployed_signatures mods exps)` by
       (qpat_assum `other = _` SUBST_ALL_TAC >>
        qpat_assum `ts = MAP SND pf` SUBST1_TAC >>
        irule classified_grouped_member_signature_mods >>
        rpt (goal_assum (drule_at Any))) >>
     `nm = tx.function_name` by
       (qpat_assum `!nm ts. MEM _ (abi_deployed_signatures _ _) /\ _ ==> _`
         (qspecl_then [`nm`,`ts`] mp_tac) >> simp[]) >>
     `MEM tx.function_name (MAP (fn_decl_name o SND) pkeys)` by
       (simp[NoAsms, MEM_MAP] >> qexists_tac `other` >> simp[]) >>
     qpat_x_assum `ALL_DISTINCT (MAP (fn_decl_name o SND) exts)` mp_tac >>
     simp[ALL_DISTINCT_APPEND] >> disj2_tac >> disj2_tac >>
     qexists_tac `tx.function_name` >> simp[]) >>
  `cd_selector cd = w2n (calldata_method_id cd)` by
    drule_then ACCEPT_TAC calldataSelectorPropsTheory.cd_selector_method_id >>
  `!keys. EVERY (\(sel,_,_). sel < dimword (:256))
      (grouped_selectors (MAP (package_external_group_unit mods rpolicy.rpol_target T
        (K global_nonreentrant_slot)) keys))` by
    (gen_tac >> simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
     rename1 `MEM (sel,lbl,tz) _` >>
     `MEM sel (MAP FST (grouped_selectors
       (MAP (package_external_group_unit mods rpolicy.rpol_target T
         (K global_nonreentrant_slot)) keys)))` by
       (simp[MEM_MAP] >> qexists_tac `(sel,lbl,tz)` >> simp[]) >>
     qpat_assum `!keys id. MEM id _ ==> _` drule >>
     disch_then (qx_choosel_then [`other`,`nm`,`ts`,`pref`,`j`] strip_assume_tac) >>
     simp[abi_method_id_def, GSYM calldata_method_id_four_bytes, wordsTheory.w2n_lt]) >>
  `EVERY (\g. case g of ExternalSingle (sel,_,_) _ =>
      calldata_method_id cd <> n2w sel
    | ExternalDefaults _ entries _ _ =>
        FIND (\(sel,_,_,_). calldata_method_id cd = n2w sel) entries = NONE) pre` by
    (irule grouped_selector_misses >>
     qpat_assum `cd_selector cd = w2n (calldata_method_id cd)`
       (fn selector => PURE_REWRITE_TAC [GSYM selector]) >>
     simp[Abbr `pre`]) >>
  suspend "linked_grouped_selected_package"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_selected_package]:
  qabbrev_tac `start = vs with <|vs_prev_bb := NONE;
    vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  `!label bb. venomInst$lookup_block label fn.fn_blocks = SOME bb ==>
               phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule acceptedContextPhiTheory.lowering_context_ok_block_phi >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     first_assum ACCEPT_TAC) >>
  `start.vs_current_bb = "__entry" /\ start.vs_inst_idx = 0 /\
   start.vs_allocas = FEMPTY /\ start.vs_alloca_next = 0 /\
   allocas_below_fmp start /\ allocas_from 0 start /\
   ~start.vs_halted /\ fresh_vars_wrt sf start /\
   start.vs_call_ctx = vs.vs_call_ctx` by
    (qpat_assum `initial_venom_state_rel_mods mods am tx vs` mp_tac >>
     qpat_assum `sf.cs_next_var = 0` (fn var =>
       simp[NoAsms, Abbr `start`, initial_venom_state_rel_mods_def, allocas_below_fmp_def,
            allocas_from_def, fresh_vars_wrt_def, var])) >>
  `entry_prov fn start FEMPTY = FEMPTY /\
   entry_taint_vars fn start entry_taint = entry_taint` by
    (`?bb. venomInst$lookup_block "__entry" fn.fn_blocks = SOME bb` by
       (qpat_assum `fn_entry_label fn = SOME "__entry"` mp_tac >>
        Cases_on `fn.fn_blocks`
        >- (qpat_assum `fn.fn_blocks = []` (fn blocks =>
             simp[NoAsms, blocks, fn_entry_label_def, entry_block_def])) >>
        qpat_assum `fn.fn_blocks = _::_` (fn blocks =>
          simp[NoAsms, blocks, fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm])) >>
     irule typedCopyArrayPtrTheory.entry_ghost_no_phi >>
     qexists_tac `bb` >> simp[] >>
     qpat_assum `!label bb. venomInst$lookup_block label _ = SOME bb ==> _`
       (qspecl_then [`"__entry"`,`bb`] mp_tac) >> simp[]) >>
  `alloca_frontier_inv unit.cu_context fn ARB start /\
   unit_alloca_budget unit.cu_context < dimword (:256)` by
    (irule (Q.INST [`name` |-> `"__entry"`] registration_empty_frontier) >>
     asm_rewrite_tac[]) >>
  `alloca_inv start` by simp[alloca_inv_empty] >>
  `selected_registration_resources unit.cu_context fn ARB 0 sf start` by
    (PURE_REWRITE_TAC [selected_registration_resources_def] >>
     asm_rewrite_tac [FLOOKUP_EMPTY, arithmeticTheory.ZERO_LESS_EQ] >>
     simp[NoAsms]) >>
  `fn_inst_ids_distinct fn` by
    (`MEM fn unit.cu_context.ctx_functions` by drule_then ACCEPT_TAC lookup_function_MEM >>
     drule lowering_context_ok_static_integrity >> strip_tac >>
     drule_all ctx_inst_ids_distinct_fn >>
     simp[NoAsms, fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_map_id]) >>
  `4 <= LENGTH start.vs_call_ctx.cc_calldata /\
    LENGTH start.vs_call_ctx.cc_calldata < dimword (:256)` by
    simp[Abbr `cd`, dimword_def] >>
  `ctx_has_dalloca unit.cu_context ==>
     allocas_below_fmp start /\
     start.vs_alloca_next + pending_alloca_size fn start <= w2n start.vs_initial_fmp` by
    (strip_tac >>
     `start.vs_alloca_next + pending_alloca_size fn start <= unit_alloca_budget unit.cu_context` by
       (qpat_assum `alloca_frontier_inv _ _ _ _`
          (mp_tac o REWRITE_RULE [alloca_frontier_inv_def]) >>
        simp[NoAsms, deploy_ctor_pending_alloca_eq] >> decide_tac) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists_tac `unit_alloca_budget unit.cu_context` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `ctx_has_dalloca unit.cu_context ==>
       unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\ _`
       (drule_then (mp_tac o CONJUNCT1)) >>
     simp[NoAsms, Abbr `start`]) >>
  drule_all grouped_dispatch_long_prelude_with_frame >>
  disch_then (qspecl_then [`entry_taint`,`[]`,`FEMPTY`]
    (qx_choosel_then [`mid`,`prelude`,`dispatch_end`,`br`,`u`,`Gu`,`tnu`]
      (map_every assume_tac o CONJUNCTS))) >>
  suspend "linked_grouped_picked_entry"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_picked_entry]:
  `!common entries specs off. MEM (ExternalDefaults common entries specs off) groups ==>
    EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs` by
    (rpt gen_tac >> simp[NoAsms, Abbr `groups`, MEM_MAP] >>
     disch_then (qx_choose_then `other` strip_assume_tac) >> PairCases_on `other` >>
     rename1 `MEM (other_src,m,n,r,nm,aa,ds,rt,code) exts` >>
     qpat_assum `ExternalDefaults _ _ _ _ = _` (assume_tac o SYM) >>
     drule_all classified_grouped_default_compile_inputs_mods >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     drule_all classified_external_default_source_mods >>
     disch_then (qx_choosel_then [`declarations`,`raw_ds`,`raw_code`] strip_assume_tac) >>
     `module_allocated am.layouts tx.target other_src declarations` by
       drule_all_then ACCEPT_TAC classified_external_owner_allocated_mods >>
     `LENGTH ds <= LENGTH aa` by
       (`ds = subst_consts_exprs_mods (consts_env_mods mods) raw_ds` by
          (qpat_assum `subst_consts_fn_mods _ (_,_,_,_,_,raw_ds,_,_) = _` mp_tac >>
           simp[NoAsms, subst_consts_fn_mods_def]) >>
        drule_all grouped_checked_default_syntax_mods >> simp[]) >>
     qabbrev_tac `alloc_env = build_compile_env_unit mods other_src Internal m nm aa rt code F` >>
     `common.ec_env.ce_struct_fields = alloc_env.ce_struct_fields` by
       (qunabbrev_tac `alloc_env` >>
        qpat_assum `ExternalDefaults _ _ _ _ = package_external_group_unit _ _ _ _ _` mp_tac >>
        qpat_assum `ds <> []` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
        Cases_on `rt = NoneT` >>
        simp[package_external_group_unit_def, package_external_fn_unit_def,
             set_external_package_target_def, update_cenv_ret_abi_def,
             update_cenv_nonreentrant_def, NULL_EQ] >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        qpat_assum `common = _` SUBST1_TAC >>
        simp[build_compile_env_unit_def, ELIM_UNCURRY]) >>
     `type_memory_bytes common.ec_env = type_memory_bytes alloc_env` by
       (irule type_memory_bytes_frame >> first_assum ACCEPT_TAC) >>
     `EVERY (\(_,ty). type_memory_bytes alloc_env ty < 2 ** 64) aa` by
       (qpat_assum `fn_allocs_ok_unit mods (other_src,(m,n,r,nm,aa,ds,rt,code))` mp_tac >>
        simp[NoAsms, fn_allocs_ok_unit_def, Abbr `alloc_env`]) >>
     simp[NoAsms, EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
     rename1 `MEM (param,ty,x) specs` >>
     `MEM (param,ty) aa` by
       (irule rich_listTheory.MEM_DROP_IMP >>
        qexists_tac `LENGTH aa - LENGTH ds` >>
        qpat_x_assum `MEM (param,ty,x) specs` mp_tac >>
        qpat_assum `specs = MAP _ _` SUBST1_TAC >>
        pure_rewrite_tac [MEM_MAP] >> simp[NoAsms, EXISTS_PROD] >>
        rpt strip_tac >>
        `LENGTH (DROP (LENGTH aa - LENGTH ds) aa) = LENGTH ds` by simp[LENGTH_DROP] >>
        qpat_x_assum `MEM _ (ZIP _)` mp_tac >>
        simp[MEM_ZIP] >> disch_then (qx_choose_then `idx` strip_assume_tac) >>
        simp[MEM_EL] >> qexists_tac `idx` >> simp[]) >>
     qpat_assum `EVERY (\(_,ty). _) aa`
       (mp_tac o Q.SPEC `(param,ty)` o REWRITE_RULE [EVERY_MEM]) >>
     simp[dimword_def]) >>
  `EVERY (\g. case g of ExternalSingle (sel,_,_) _ =>
      calldata_method_id cd <> n2w sel
    | ExternalDefaults common entries specs _ =>
        FIND (\(sel,_,_,_). calldata_method_id cd = n2w sel) entries = NONE /\
        EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs) pre` by
    (simp[EVERY_MEM] >> qx_gen_tac `g` >> strip_tac >>
     qpat_assum `EVERY _ pre` (mp_tac o Q.SPEC `g` o REWRITE_RULE [EVERY_MEM]) >>
     Cases_on `g` >> simp[] >>
     rename1 `MEM (ExternalDefaults c es sp hd) pre` >>
     `MEM (ExternalDefaults c es sp hd) groups` by simp[] >>
     qpat_assum `!common entries specs off. MEM (ExternalDefaults _ _ _ _) groups ==> _`
       (qspecl_then [`c`,`es`,`sp`,`hd`] mp_tac) >> simp[EVERY_MEM]) >>
  qabbrev_tac `body_code = subst_consts_stmts_mods (consts_env_mods mods) selected_body` >>
  qabbrev_tac `ds = subst_consts_exprs_mods (consts_env_mods mods) dflts` >>
  `entry_key = (src,(mut,nr,selected_raw,tx.function_name,args,ds,ret,body_code))` by
    simp[Abbr `entry_key`, Abbr `ds`, Abbr `body_code`, subst_consts_fn_mods_def] >>
  `LENGTH ds = LENGTH dflts` by
    (qunabbrev_tac `ds` >> qid_spec_tac `dflts` >>
     POP_ASSUM_LIST (K ALL_TAC) >> Induct >> simp[subst_consts_expr_mods_def]) >>
  `MEM (prefix,k) (abi_entries args ds)` by
    simp[abi_entries_member, LENGTH_NIL] >>
  `abi_method_id (type_env_all_modules mods) tx.function_name (MAP SND prefix) =
    cd_selector cd` by
    (qpat_assum `tys = MAP SND prefix` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `calldata_method_id cd = n2w (cd_selector cd)` by
    (qpat_assum `cd_selector cd = w2n _` (fn eq => simp[NoAsms, eq])) >>
  `eval_operand (Var mid) u = SOME (calldata_method_id cd)` by
    (`start.vs_call_ctx.cc_calldata = cd` by
       simp[NoAsms, Abbr `start`, Abbr `cd`] >>
     pop_assum (fn calldata => qpat_assum
       `eval_operand (Var mid) u = SOME (calldata_method_id start.vs_call_ctx.cc_calldata)`
       (ACCEPT_TAC o REWRITE_RULE [calldata]))) >>
  Cases_on `ds = []`
  >- suspend "linked_grouped_legacy_entry" >>
  suspend "linked_grouped_default_entry"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_legacy_entry]:
  `dflts = []` by
    (qpat_assum `LENGTH ds = LENGTH dflts` mp_tac >>
     qpat_assum `ds = []` (fn empty => simp[NoAsms, empty, LENGTH_NIL])) >>
  `prefix = args /\ k = 0` by
    (qpat_assum `MEM (prefix,k) (abi_entries args ds)` mp_tac >>
     qpat_assum `ds = []` (fn empty => simp[NoAsms, empty])) >>
  qabbrev_tac `pkg = set_external_package_target rpolicy.rpol_target
    (package_external_fn_unit mods T (K global_nonreentrant_slot)
      (src,(mut,nr,selected_raw,tx.function_name,args,([]:expr list),ret,body_code)))` >>
  `group = ExternalSingle
     (cd_selector cd,"fn_" ++ tx.function_name,selector_has_trailing_zeroes (cd_selector cd)) pkg` by
    (qpat_assum `entry_key = _` (fn entry =>
       simp_tac std_ss [Abbr `group`, entry]) >>
     qpat_assum `ds = []` SUBST1_TAC >>
     qpat_assum `prefix = args` (fn pref =>
       qpat_assum `abi_method_id _ _ (MAP SND prefix) = cd_selector cd`
         (assume_tac o REWRITE_RULE [pref])) >>
     qpat_assum `abi_method_id (type_env_all_modules mods) tx.function_name
       (MAP SND args) = cd_selector cd` (fn selector =>
       simp[NoAsms, Abbr `pkg`, package_external_group_unit_def,
            compute_selector_method_id, selector])) >>
  `compile_external_groups (Var mid)
     (pre ++ ExternalSingle
       (cd_selector cd,"fn_" ++ tx.function_name,selector_has_trailing_zeroes (cd_selector cd))
       pkg::post) prelude = (jobs,dispatch_end)` by
    (qpat_assum `groups = pre ++ group::post` (fn split =>
       qpat_assum `group = ExternalSingle _ _` (fn packed =>
         qpat_assum `compile_external_groups (Var mid) groups prelude = _`
           (ACCEPT_TAC o REWRITE_RULE [split,packed])))) >>
  `EVERY group_entry_labels_ok
     (pre ++ ExternalSingle
       (cd_selector cd,"fn_" ++ tx.function_name,selector_has_trailing_zeroes (cd_selector cd))
       pkg::post)` by
    (qpat_assum `groups = pre ++ group::post` (fn split =>
       qpat_assum `group = ExternalSingle _ _` (fn packed =>
         qpat_assum `EVERY group_entry_labels_ok groups`
           (ACCEPT_TAC o REWRITE_RULE [split,packed])))) >>
  drule_all compile_external_groups_selected_single_origin >>
  disch_then (qspecl_then [`[]`,`Gu`]
    (qx_choosel_then [`prefix_jobs`,`before_select`,`after_select`,`hit`,`Gh`,`tnh`]
      (map_every assume_tac o CONJUNCTS))) >>
  `?lbl ce pa mc pay key tr view rt.
     pkg = (lbl,ce,pa,mc,pay,nr,key,tr,view,body_code,rt)` by
    (Cases_on `ret = NoneT`
     >- (qpat_assum `ret = NoneT` (fn ret_eq =>
           simp[NoAsms, Abbr `pkg`, ret_eq, set_external_package_target_def,
                package_external_fn_unit_def]))
     >> qpat_assum `ret <> NoneT` (fn ret_neq =>
          simp[NoAsms, Abbr `pkg`, ret_neq, set_external_package_target_def,
               package_external_fn_unit_def])) >>
  pop_assum strip_assume_tac >>
  `MEM (ExternalLegacyJob (lbl,ce,pa,mc,pay,nr,key,tr,view,body_code,rt)) jobs` by
    (qpat_assum `pkg = _` (fn entry =>
       qpat_assum `MEM (ExternalLegacyJob pkg) jobs`
         (ACCEPT_TAC o REWRITE_RULE [entry]))) >>
  drule_all grouped_legacy_paired_code >>
  disch_then (qx_choosel_then
    [`opened`,`checked`,`registered_env`,`registered`,`last`,`shadow_registered`,`shadow_last`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "linked_grouped_legacy_value_check"
QED

val linked_grouped_value_frame_tac =
  `hit.vs_call_ctx = vs.vs_call_ctx` by
    (qpat_assum `selected_registration_frame u tnu hit tnh`
       (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]) >>
     qpat_assum `selected_registration_frame start entry_taint u tnu`
       (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]) >>
     qpat_assum `hit.vs_call_ctx = u.vs_call_ctx` (fn hit =>
       qpat_assum `u.vs_call_ctx = start.vs_call_ctx` (fn prefix =>
         qpat_assum `start.vs_call_ctx = vs.vs_call_ctx` (fn start =>
           simp[NoAsms, hit, prefix, start])))) >>
  `hit.vs_call_ctx.cc_callvalue = n2w tx.value` by
    (qpat_assum `hit.vs_call_ctx = vs.vs_call_ctx` SUBST1_TAC >>
     qpat_assum `initial_venom_state_rel_mods mods am tx vs` mp_tac >>
     simp[NoAsms, initial_venom_state_rel_mods_def, venom_env_rel_def, call_ctx_rel_def]) >>
  `tx.value < dimword (:256)` by
    (qpat_assum `call_tx_well_typed tx` mp_tac >>
     simp[NoAsms, call_tx_well_typed_def, dimword_def]);

val linked_grouped_reject_callvalue_tac =
  `hit.vs_call_ctx.cc_callvalue <> 0w` by
    (qpat_assum `hit.vs_call_ctx.cc_callvalue = _` SUBST1_TAC >>
     qpat_assum `tx.value <> 0` (fn nz =>
       qpat_assum `tx.value < dimword (:256)` (fn bound =>
         simp[NoAsms, wordsTheory.n2w_11, nz, bound]))) >>
  `LENGTH tx.args = LENGTH prefix` by
    (qpat_assum `calldata_decode_args cd decoded_tys 0 = SOME tx.args`
       (mp_tac o MATCH_MP (SPEC_ALL calldata_decode_args_length)) >>
     qpat_assum `OPT_MMAP _ tys = SOME decoded_tys`
       (mp_tac o MATCH_MP (SPEC_ALL OPT_MMAP_LENGTH)) >>
     qpat_assum `tys = MAP SND prefix` (fn tys => simp[NoAsms, tys])) >>
  `LENGTH tx.args <= LENGTH args /\ LENGTH args - LENGTH tx.args <= LENGTH dflts` by
    (qpat_assum `LENGTH tx.args = LENGTH prefix` SUBST1_TAC >>
     qpat_assum `MEM (prefix,k) (abi_entries args dflts)` mp_tac >>
     simp[NoAsms, abi_entries_member, LENGTH_TAKE_EQ] >>
     strip_tac >> decide_tac);

val linked_grouped_reject_source_tac =
  `!gobs. call_external_trace (SOME vs.vs_outcomes) gobs am tx =
    (INR (Error (RuntimeError "not Payable")),am,[],[])` by
    (qpat_assum `Abbrev (src = ALOOKUP exps tx.function_name)` (fn owner =>
       let
         val source = REWRITE_RULE [markerTheory.Abbrev_def] owner
       in
         qpat_assum `ALOOKUP mods src = SOME selected_tops`
           (assume_tac o REWRITE_RULE [source]) >>
         qpat_assum `vyperInterpreter$lookup_function src tx.function_name External selected_tops = _`
           (assume_tac o REWRITE_RULE [source])
       end) >>
     drule_all linked_external_value_reject_trace >>
     disch_then (qspec_then `SOME vs.vs_outcomes` ACCEPT_TAC));

val linked_grouped_reject_resources_tac =
  `~block_is_terminated opened` by
    (qpat_assum `opened.cs_current_insts = []` (fn code =>
       simp[NoAsms, block_is_terminated_def, code])) >>
  `fresh_vars_wrt opened hit /\ ~hit.vs_halted /\
     hit.vs_current_bb = opened.cs_current_bb /\ hit.vs_inst_idx = 0 /\
     allocas_from 0 hit` by
    (qpat_assum `selected_registration_resources _ _ _ 0 opened hit`
       (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
     qpat_assum `hit.vs_inst_idx = LENGTH opened.cs_current_insts` mp_tac >>
     qpat_assum `opened.cs_current_insts = []` (fn code =>
       simp[NoAsms, code]) >> strip_tac >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca unit.cu_context ==> allocas_below_fmp hit` by
    (strip_tac >>
     qpat_assum `ctx_has_dalloca _ ==> allocas_below_fmp hit /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1)));

val linked_grouped_reject_path_tac =
  qpat_assum `compile_entry_checks _ F opened = ((),_)`
    (fn compiled =>
       let
         val reject = Q.INST [`ctx` |-> `unit.cu_context`, `s` |-> `hit`,
           `lo` |-> `0`, `fn` |-> `fn`, `PG` |-> `[]`,
           `G` |-> `Gh`, `tn` |-> `tnh`] nonpayable_check_joint_reject
       in
         mp_tac (MATCH_MP (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] reject) compiled)
       end) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`abort_state`,`abort_prov`,`abort_taint`] strip_assume_tac) >>
  `!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
    (start,FEMPTY,entry_taint) [] (Abort Revert_abort abort_state,abort_prov,abort_taint)` by
    (rpt gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gh`,`hit`,`tnh`] >> asm_rewrite_tac[]);

val linked_grouped_reject_exit_tac =
  `!D fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn [] FEMPTY entry_taint start` by
    (qspecl_then [`unit.cu_context`,`fn`,`vs`,`abort_state`,`abort_prov`,`abort_taint`,`[]`]
       mp_tac entry_joint_revert_exit >>
     qpat_assum `Abbrev (start = vs with <|vs_prev_bb := NONE;
         vs_current_bb := "__entry"; vs_inst_idx := 0|>)`
       (fn initial => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] initial)]) >>
     impl_tac >- (rpt conj_tac >> asm_rewrite_tac[]) >>
     strip_tac >> asm_rewrite_tac[]) >>
  `gas_origin_path T (gas_explicit_sites unit.cu_context shadow_unit.cu_context)
    unit.cu_context fn start [] (Abort Revert_abort abort_state)` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ (start,_,_) [] (Abort Revert_abort abort_state,_,_)`
       (qspecl_then [`ARB`,`gas_explicit_sites unit.cu_context shadow_unit.cu_context`]
        (ACCEPT_TAC o CONJUNCT1 o MATCH_MP (SPEC_ALL gas_origin_ptr_path_projections)))) >>
  qpat_assum `lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn`
    (assume_tac o MATCH_MP lookup_function_MEM) >>
  qpat_assum `lookup_function "__entry" shadow_unit.cu_context.ctx_functions = SOME shfn`
    (assume_tac o MATCH_MP lookup_function_MEM);

val linked_grouped_reject_empty_storage_tac =
  `storage_trace_domain (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am []) []` by
    simp[NoAsms, storage_trace_domain_def, valid_horizon_def,
         storage_observations_ok_def, storage_trace_horizon_def,
         storage_trace_regions_def, storage_trace_locks_def, regions_consistent_def,
         storage_locks_separated_def, storage_well_formed_on_def, storage_roots_fit_def,
         storage_trace_backends_well_formed_def];

val linked_grouped_reject_execution_tac =
  rewrite_tac [source_unit_execution_correct_with_mods_def] >>
  qexistsl_tac [`fn`,`shfn`] >> asm_rewrite_tac[] >>
  disj2_tac >>
  qexistsl_tac [`INR (Error (RuntimeError "not Payable"))`,`am`,`[]`,`[]`] >>
  asm_rewrite_tac[] >> disj2_tac >> qexists_tac `Abort Revert_abort abort_state` >>
  qpat_assum `Abbrev (start = _)` (fn start =>
    PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] start)]) >>
  simp[exit_result_def, external_call_result_rel_mods_def];

val linked_grouped_reject_no_gas_tac =
  disch_tac >> qx_gen_tac `tail` >>
  qpat_assum `!gobs. call_external_trace _ _ _ _ = _`
    (qspec_then `gas_explicit [] vs.vs_gas_readings ++ tail`
      (fn trace =>
        simp[NoAsms, CONJUNCT1 (MATCH_MP call_external_trace_result trace)]));

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_legacy_value_check]:
  `pay = (mut = Payable)` by
    (qpat_assum `pkg = (lbl,ce,pa,mc,pay,nr,key,tr,view,body_code,rt)` mp_tac >>
     Cases_on `ret = NoneT` >>
     simp[NoAsms, Abbr `pkg`, set_external_package_target_def,
          package_external_fn_unit_def] >> strip_tac >>
     first_assum ACCEPT_TAC) >>
  `EVERY group_entry_labels_ok post` by
    (qpat_assum `EVERY group_entry_labels_ok
       (pre ++ ExternalSingle _ pkg::post)` mp_tac >>
     simp[NoAsms, EVERY_APPEND]) >>
  `!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
    (start,FEMPTY,entry_taint) [] (OK hit,Gh,tnh)` by
    (rpt gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gu`,`u`,`tnu`] >> asm_rewrite_tac[]) >>
  `selected_registration_frame vs entry_taint hit tnh` by
    (qpat_assum `selected_registration_frame u tnu hit tnh`
       (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]) >>
     qpat_assum `selected_registration_frame start entry_taint u tnu`
       (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]) >>
     asm_rewrite_tac [selected_registration_frame_def] >>
     simp[NoAsms, Abbr `start`]) >>
  `vs.vs_fmp = vs.vs_initial_fmp` by
    (qpat_assum `initial_venom_state_rel_mods mods am tx vs` mp_tac >>
     simp[NoAsms, initial_venom_state_rel_mods_def]) >>
  `start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` by
    simp[NoAsms, Abbr `start`] >>
  `lbl = "fn_" ++ tx.function_name` by
    (qpat_assum `pkg = (lbl,ce,pa,mc,pay,nr,key,tr,view,body_code,rt)`
       mp_tac >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case =>
       simp[NoAsms, Abbr `pkg`, ret_case, set_external_package_target_def,
            package_external_fn_unit_def]) >>
     strip_tac >> first_assum (ACCEPT_TAC o SYM)) >>
  qpat_x_assum `lbl = "fn_" ++ tx.function_name` SUBST_ALL_TAC >>
  qpat_assum `compile_external_groups (Var mid)
    (pre ++ ExternalSingle (cd_selector cd,"fn_" ++ tx.function_name,_) pkg::post)
    prelude = (jobs,dispatch_end)`
    (fn grouped =>
      let
        val seam = Q.INST
          [`skip_end` |-> `before_select`, `sel_end` |-> `after_select`,
           `checks` |-> `opened`, `m` |-> `mc`, `reg` |-> `checked`,
           `ctx` |-> `unit.cu_context`, `site` |-> `ARB`, `s` |-> `start`,
           `Ghit` |-> `Gh`, `tnhit` |-> `tnh`] grouped_legacy_check_seam
      in
        mp_tac (MATCH_MP (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] seam) grouped)
      end) >>
  impl_tac >- (rpt conj_tac >>
    (first_assum ACCEPT_TAC ORELSE
     qpat_assum `ctx_has_dalloca unit.cu_context ==>
       unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\ _`
       (fn bounds => simp[NoAsms, bounds]))) >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  linked_grouped_value_frame_tac >>
  Cases_on `mut <> Payable /\ tx.value <> 0`
  >- (qpat_x_assum `mut <> Payable /\ tx.value <> 0` strip_assume_tac >>
      `compile_entry_checks mc F opened = ((),checked)` by
        (qpat_assum `compile_entry_checks mc pay opened = _` mp_tac >>
         qpat_assum `pay = _` (fn pay =>
           qpat_assum `mut <> Payable` (fn nonpayable => simp[NoAsms, pay, nonpayable]))) >>
      linked_grouped_reject_callvalue_tac >>
      linked_grouped_reject_source_tac >>
      linked_grouped_reject_resources_tac >>
      linked_grouped_reject_path_tac >>
      linked_grouped_reject_exit_tac >>
      linked_grouped_reject_empty_storage_tac >>
      qexists_tac `[]` >> conj_tac
      >- linked_grouped_reject_execution_tac >>
      linked_grouped_reject_no_gas_tac) >>
  suspend "linked_grouped_legacy_passing_checks"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_legacy_passing_checks]:
  rename1 `eval_operand (Var mid) dispatch_u = SOME (calldata_method_id cd)` >>
  rename1 `compile_register_positional_args ce pos 4 checked = (registered_env,registered)` >>
  `set_external_package_target rpolicy.rpol_target
      (package_external_fn_unit mods T (K global_nonreentrant_slot)
        (src,(mut,nr,selected_raw,tx.function_name,args,([]:expr list),ret,body_code))) =
      ("fn_" ++ tx.function_name,ce,pos,mc,pay,nr,key,tr,view,body_code,rt)` by
    (qpat_assum `Abbrev (pkg = _)`
       (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     first_assum ACCEPT_TAC) >>
  `fn_allocs_ok_unit mods (src,(mut,nr,selected_raw,tx.function_name,args,[],ret,body_code))` by
    (qpat_assum `entry_key = (src,_)` (SUBST1_TAC o SYM) >>
     qpat_assum `EVERY (fn_allocs_ok_unit mods) exts`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >> disch_then drule >> simp[]) >>
  `contract_namespaces_ok F mods` by drule_then ACCEPT_TAC check_contract_namespaces_ok >>
  drule_all (Q.INST [`dflts` |-> `[]:expr list`] linked_registration_package_inputs) >>
  disch_then (CONJUNCTS_THEN2 kall_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (qx_choose_then `package_tys` (map_every assume_tac o CONJUNCTS))))) >>
  `OPT_MMAP (evaluate_type (type_env_all_modules mods)) (MAP SND args) = SOME decoded_tys` by
    (qpat_assum `tys = MAP SND prefix` (fn tys =>
       qpat_assum `prefix = args` (fn pref =>
         PURE_REWRITE_TAC [GSYM (REWRITE_RULE [pref] tys)])) >>
     first_assum ACCEPT_TAC) >>
  `package_tys = decoded_tys` by
    (qpat_assum `OPT_MMAP _ (MAP SND args) = SOME package_tys` mp_tac >>
     qpat_assum `OPT_MMAP _ (MAP SND args) = SOME decoded_tys`
       (fn decoded => simp[NoAsms, decoded])) >>
  qpat_x_assum `package_tys = decoded_tys` SUBST_ALL_TAC >>
  `hit.vs_call_ctx.cc_calldata = cd` by simp[Abbr `cd`] >>
  qpat_assum `((pay \/ hit.vs_call_ctx.cc_callvalue = 0w) /\ _ /\ _ ==> ?s G tn. _)` mp_tac >>
  impl_tac
  >- (conj_tac
      >- (qpat_assum `pay = _` SUBST1_TAC >>
          qpat_assum `hit.vs_call_ctx.cc_callvalue = _` SUBST1_TAC >>
          qpat_assum `~(mut <> Payable /\ tx.value <> 0)` mp_tac >>
          simp[NoAsms, DE_MORGAN_THM] >> disch_then (DISJ_CASES_THEN (fn eq => simp[NoAsms, eq]))) >>
      qpat_assum `hit.vs_call_ctx.cc_calldata = cd` SUBST1_TAC >>
      qpat_assum `mc = 4 + SUM _` SUBST1_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `LENGTH cd < 18446744073709551616` mp_tac >>
      simp[NoAsms, dimword_def] >> decide_tac) >>
  disch_then (qx_choosel_then [`u`,`G1`,`tn1`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "linked_grouped_legacy_positional_register"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_legacy_positional_register]:
  qpat_assum `selected_registration_frame vs entry_taint u tn1`
    (strip_assume_tac o PURE_REWRITE_RULE [selected_registration_frame_def]) >>
  `calldata_decode_args u.vs_call_ctx.cc_calldata decoded_tys 0 = SOME tx.args` by
    (qpat_assum `u.vs_call_ctx = vs.vs_call_ctx` SUBST1_TAC >>
     qpat_assum `Abbrev (cd = _)`
       (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     first_assum ACCEPT_TAC) >>
  `?env. bind_arguments (type_env_all_modules mods) args tx.args = SOME env` by
    (irule dispatchedDecodedBindModsTheory.decoded_parameters_bind >>
     qexistsl_tac [`cd`,`decoded_tys`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `alloca_history fn start /\ alloca_inv start` by
    (conj_tac
     >- (irule alloca_history_empty >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `alloca_history fn u` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) [] (OK u,G1,tn1)`
       (qspecl_then [`ARB`,`ARB`] assume_tac) >>
     drule_all_then ACCEPT_TAC body_full_path_alloca_history) >>
  `LENGTH args = LENGTH decoded_tys /\ LENGTH args = LENGTH tx.args` by
    (conj_tac
     >- (qpat_assum `OPT_MMAP _ (MAP SND args) = SOME decoded_tys`
           (mp_tac o MATCH_MP (SPEC_ALL vyperTypeABITheory.OPT_MMAP_LENGTH)) >> simp[NoAsms]) >>
     drule_then ACCEPT_TAC bind_arguments_length) >>
  `LIST_REL (\ty tv. evaluate_type (type_env_all_modules mods) ty = SOME tv)
     (MAP SND args) decoded_tys` by
    (qpat_assum `OPT_MMAP _ (MAP SND args) = SOME decoded_tys`
       (ACCEPT_TAC o MATCH_MP (SPEC_ALL vyperTypeABITheory.OPT_MMAP_LIST_REL))) >>
  `!i. i < LENGTH args ==>
     abi_decoder_coherent ce (type_env_all_modules mods) ce.ce_struct_fields
       (SND (EL i args)) (EL i decoded_tys) /\
     (?loc. FLOOKUP ce.ce_vars (FST (EL i args)) = SOME loc /\
       var_location_memory_size loc = SOME (type_memory_size (EL i decoded_tys))) /\
     type_memory_size (EL i decoded_tys) < dimword (:256)` by
    (gen_tac >> strip_tac >>
     qpat_assum `LIST_REL _ args (ZIP (MAP SND args,decoded_tys))`
       (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     qpat_assum `LENGTH args = LENGTH decoded_tys` (fn len =>
       qpat_assum `i < LENGTH args` (fn bound =>
         Cases_on `EL i args` >>
         qpat_assum `EL i args = _` (fn arg =>
           simp[NoAsms, bound, GSYM len, EL_ZIP, EL_MAP, arg])))) >>
  `!ce' i. i < LENGTH args /\ ce' = ce with ce_vars := ce'.ce_vars ==>
      selected_slot_accepts ce' (type_env_all_modules mods) ce'.ce_struct_fields
        (SND (EL i args)) (EL i decoded_tys) /\
      abi_decoder_coherent ce' (type_env_all_modules mods) ce'.ce_struct_fields
        (SND (EL i args)) (EL i decoded_tys)` by
    (rpt gen_tac >> strip_tac >>
     `abi_decoder_coherent ce' (type_env_all_modules mods) ce'.ce_struct_fields
        (SND (EL i args)) (EL i decoded_tys)` by
       (qpat_assum `ce' = _` SUBST1_TAC >>
        simp[ctor_decoder_coherent_vars]) >>
     simp[] >> irule selected_register_one >>
     irule selected_argument_decoder_accepts >> first_assum ACCEPT_TAC) >>
  suspend "linked_grouped_legacy_positional_resources"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_legacy_positional_resources]:
  `ce.ce_imm_alloca = NONE /\ ce.ce_vars =
     FST (allocate_args (get_struct_fields (make_struct_fields_map_mods mods))
       args 0 FEMPTY)` by
    (qpat_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[NoAsms, set_external_package_target_def, package_external_fn_unit_def,
          update_cenv_nonreentrant_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `(if _ then _ else _) with
         <|ce_target := _; ce_nonreentrant := _|> = ce`
       (mp_tac o AP_TERM ``\ce:compile_env. (ce.ce_imm_alloca,ce.ce_vars)``) >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case =>
       simp[NoAsms, ret_case, update_cenv_ret_abi_def, build_compile_env_unit_def,
            pairTheory.ELIM_UNCURRY, pairTheory.FST, LET_THM])) >>
  `(!k. ~MEM k (MAP FST args) ==> FLOOKUP ce.ce_vars k = NONE) /\
    EVERY (\a. ?off. FLOOKUP ce.ce_vars (FST a) =
      SOME (MemLoc off (type_mem_bytes (get_struct_fields (make_struct_fields_map_mods mods))
         (SND a)))) args` by
    (qpat_assum `ce.ce_vars = _` SUBST1_TAC >>
     drule_then
       (qspecl_then [`get_struct_fields (make_struct_fields_map_mods mods)`,`0`,`FEMPTY`] mp_tac)
       allocate_args_lookup >> simp[NoAsms, FLOOKUP_EMPTY]) >>
  `!n p sz. FLOOKUP ce.ce_vars n <> SOME (PtrVar (Var p) sz)` by
    (rpt gen_tac >> Cases_on `MEM n (MAP FST args)`
     >- (qpat_assum `MEM n (MAP FST args)`
          (qx_choose_then `arg` strip_assume_tac o REWRITE_RULE [MEM_MAP]) >>
         qpat_assum `EVERY (\a. ?off. FLOOKUP ce.ce_vars (FST a) = _) args`
           (qspec_then `arg` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
         impl_tac >- first_assum ACCEPT_TAC >>
         BETA_TAC >>
         disch_then (qx_choose_then `off` (fn lookup =>
           qpat_assum `n = FST arg` (fn name =>
             simp[NoAsms, name, lookup, var_location_distinct])))) >>
     qpat_assum `!k. ~MEM k (MAP FST args) ==> FLOOKUP ce.ce_vars k = NONE`
       (drule_then (fn absent => simp[NoAsms, absent]))) >>
  `compile_register_positional_args ce (build_positional_args ce args) 4 checked =
    (registered_env,registered)` by
    (qpat_assum `pos = build_positional_args _ _` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  suspend "linked_grouped_legacy_positional_fold"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_legacy_positional_fold]:
  `local_ptrs_reserved registered_env registered` by
    (qspecl_then [`build_positional_args ce args`,`ce`,`4`,`checked`,
                    `registered_env`,`registered`] mp_tac
       compile_register_positional_args_reserved >>
     impl_tac
     >- (rpt conj_tac
         >- first_assum ACCEPT_TAC
         >- (simp[NoAsms, build_positional_args_names] >> rpt strip_tac >>
             CCONTR_TAC >>
             qpat_assum `!k. ~MEM k (MAP FST args) ==> FLOOKUP ce.ce_vars k = NONE`
               (drule_then (fn outside =>
                  qpat_assum `FLOOKUP ce.ce_vars n = SOME _`
                    (CONTR_TAC o REWRITE_RULE [outside, optionTheory.NOT_NONE_SOME]))))
         >- (rpt strip_tac >>
             qpat_assum `FLOOKUP ce.ce_vars _ = SOME (PtrVar (Var _) _)`
               (fn lookup => qpat_assum
                 `!n p sz. FLOOKUP ce.ce_vars n <> SOME (PtrVar (Var p) sz)`
                 (CONTR_TAC o (fn excluded => MATCH_MP (SPEC_ALL excluded) lookup)))) >>
         qpat_assum `ce.ce_imm_alloca = NONE` (fn imm => simp[NoAsms, imm])) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `4 + SUM (MAP tv_abi_size decoded_tys) < dimword (:256)` by
    (qpat_assum `mc = 4 + SUM _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `fresh_vars_wrt checked u` by
    (qpat_assum `selected_registration_resources _ _ _ 0 checked u`
       (strip_assume_tac o PURE_REWRITE_RULE [selected_registration_resources_def]) >>
     first_assum ACCEPT_TAC) >>
  `fresh_vars_wrt registered u` by
    (irule fresh_vars_wrt_mono >> qexists_tac `checked` >>
     qpat_assum `compile_register_positional_args _ _ _ checked = (_,registered)`
       (mp_tac o MATCH_MP compile_register_positional_args_next_var) >>
     asm_rewrite_tac [arithmeticTheory.GREATER_EQ]) >>
  drule_at (Pat `calldata_decode_args u.vs_call_ctx.cc_calldata _ _ = _`)
    (Q.INST [`PG` |-> `[]`] (SPEC_ALL selected_registration_fold)) >>
  disch_then (drule_at (Pat `compile_register_positional_args _ (build_positional_args _ _) _ _ = _`)) >>
  disch_then (drule_at (Pat `selected_registration_resources _ _ _ _ checked u`)) >>
  disch_then (drule_at (Pat `bind_arguments _ _ _ = _`)) >>
  disch_then (qspecl_then [`tn1`,`registered`,`G1`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
  disch_then (qx_choosel_then [`s0`,`G2`,`tn2`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "linked_grouped_legacy_registered_path"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_legacy_registered_path]:
  `!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
    (start,FEMPTY,entry_taint) [] (OK s0,G2,tn2)` by
    (rpt gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`G1`,`u`,`tn1`] >> asm_rewrite_tac[]) >>
  qpat_assum `selected_registration_frame u tn1 s0 tn2`
    (strip_assume_tac o PURE_REWRITE_RULE [selected_registration_frame_def]) >>
  `selected_registration_frame vs entry_taint s0 tn2` by
    (pure_rewrite_tac [selected_registration_frame_def] >>
     asm_rewrite_tac[]) >>
  qpat_assum `selected_registration_frame vs entry_taint s0 tn2`
    (strip_assume_tac o PURE_REWRITE_RULE [selected_registration_frame_def]) >>
  `tn2.t_stor = {} /\ tn2.t_trans = {} /\ tn2.t_imm = {}` by
    (qpat_assum `tn2.t_stor = entry_taint.t_stor` SUBST1_TAC >>
     qpat_assum `tn2.t_trans = entry_taint.t_trans` SUBST1_TAC >>
     qpat_assum `tn2.t_imm = entry_taint.t_imm` SUBST1_TAC >> simp[NoAsms, entry_taint_def]) >>
  `s0.vs_initial_fmp = vs.vs_initial_fmp` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) [] (OK s0,G2,tn2)`
       (qspecl_then [`ARB`,`ARB`] assume_tac) >>
     drule_all decoder_origin_path_allocation_frame >> simp[NoAsms, Abbr `start`]) >>
  qpat_assum `selected_registration_resources _ fn _ 0 registered s0`
    (strip_assume_tac o PURE_REWRITE_RULE [selected_registration_resources_def]) >>
  `fmp_room unit.cu_context fn s0` by
    (irule entry_frontier_fmp_room >> conj_tac
     >- asm_rewrite_tac[] >>
     conj_tac
     >- (qpat_assum `s0.vs_initial_fmp = vs.vs_initial_fmp` SUBST1_TAC >>
         qpat_assum `ctx_has_dalloca unit.cu_context ==> unit_alloca_budget _ <= _ /\ _`
           mp_tac >> simp[NoAsms]) >>
     qexists_tac `ARB:instruction` >> first_assum ACCEPT_TAC) >>
  `!j. j < LENGTH args ==> ?aid q p n.
    FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
    FLOOKUP registered_env.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
    lookup_var q s0 = SOME (n2w p) /\ ptr_covers G2 tn2 q s0 n /\
    (!mem. mem_agree_outside tn2.t_mem s0.vs_memory mem ==>
      val_in_memory (EL j decoded_tys) (EL j tx.args) p mem)` by
    (rpt strip_tac >>
     qpat_assum `selected_registration_owners _ _ _ _ _ _ _ _ _ _`
       (qspec_then `j` mp_tac o REWRITE_RULE [selected_registration_owners_def]) >>
     qpat_assum `j < LENGTH args` (fn bound => simp[NoAsms, bound, EL_MAP]) >>
     strip_tac >> rename1 `FLOOKUP s0.vs_allocas aid = SOME (addr,n)` >>
     qexistsl_tac [`aid`,`q`,`addr`,`n`] >> asm_rewrite_tac[]) >>
  suspend "linked_grouped_legacy_registered_source"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_legacy_registered_source]:
  rename1 `ALOOKUP mods src = SOME tops` >>
  rename1 `Abbrev (body_code = subst_consts_stmts_mods _ fbody)` >>
  rename1 `fn_allocs_ok_unit mods (src,mut,nr,raw,_,args,[],ret,body_code)` >>
  `vyperInterpreter$lookup_function src tx.function_name External tops =
    SOME (mut,nr,args,[],ret,fbody)` by
    (qpat_assum `dflts = []` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `src = ALOOKUP exps tx.function_name` by simp[NoAsms, Abbr `src`] >>
  `lookup_raw_return_or_F src tx.function_name External tops = raw` by
    (qpat_assum `dflts = []` SUBST_ALL_TAC >>
     qpat_assum `(_ /\ top = FunctionDecl _ _ _ _ _ _ _ _ _) \/ public_getter_src _ top = _`
       (DISJ_CASES_THEN2 strip_assume_tac
         (strip_assume_tac o REWRITE_RULE [tagged_getter_source_tuple]))
     >- (`MEM (src,tx.function_name) (external_name_keys_toplevel src top)` by
           (qpat_assum `top = FunctionDecl _ _ _ _ _ _ _ _ _` SUBST1_TAC >>
            simp[NoAsms, external_name_keys_toplevel_def]) >>
         qpat_assum `vyperInterpreter$lookup_function src tx.function_name External tops = _`
           (mp_tac o MATCH_MP (SPEC_ALL lookup_function_external_raw_cases)) >>
         disch_then (DISJ_CASES_THEN strip_assume_tac)
         >- (`top = FunctionDecl External mut nr rr tx.function_name args [] ret fbody` by
              (qspecl_then [`tops`, `external_name_keys_toplevel src`, `top`,
                 `FunctionDecl External mut nr rr tx.function_name args [] ret fbody`,
                 `(src,tx.function_name)`] mp_tac all_distinct_flat_map_unique >>
               impl_tac >- (rpt conj_tac >>
                 (first_assum ACCEPT_TAC ORELSE simp[NoAsms, external_name_keys_toplevel_def])) >>
               disch_then ACCEPT_TAC) >>
             qpat_assum `lookup_raw_return src tx.function_name External tops = SOME rr` (fn ret =>
               qpat_assum `top = FunctionDecl External mut nr raw tx.function_name args [] _ _` (fn left =>
                 qpat_assum `top = FunctionDecl External mut nr rr tx.function_name args [] _ _`
                   (mp_tac o REWRITE_RULE [left]) >>
                 simp[NoAsms, lookup_raw_return_or_F_def, ret]))) >>
         `public_getter_src src decl = SOME (mut,nr,F,tx.function_name,args,
            ([]:expr list),ret,fbody)` by
           (simp[NoAsms, tagged_getter_source_tuple] >>
            rpt conj_tac >> first_assum ACCEPT_TAC) >>
         `MEM (src,tx.function_name) (external_name_keys_toplevel src decl)` by
           (drule tagged_getter_name_key >> simp[NoAsms, fn_decl_name_def]) >>
         `top = decl` by
           (qspecl_then [`tops`, `external_name_keys_toplevel src`, `top`, `decl`,
              `(src,tx.function_name)`] mp_tac all_distinct_flat_map_unique >>
            impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
            disch_then ACCEPT_TAC) >>
         qpat_assum `top = FunctionDecl _ _ _ _ _ _ _ _ _` (fn decl =>
           qpat_assum `top = decl` (fn same =>
             qpat_assum `is_public_getter_decl _ decl`
               (CONTR_TAC o REWRITE_RULE [GSYM same, decl, is_public_getter_decl_def])))) >>
     qspecl_then [`tops`,`src`,`tx.function_name`,`top`] mp_tac public_getter_raw_return_none >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then (fn none => asm_rewrite_tac [lookup_raw_return_or_F_def, none, optionTheory.option_case_def])) >>
  suspend "linked_grouped_legacy_registered_relations"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_legacy_registered_relations]:
  `set_external_package_target rpolicy.rpol_target
      (package_external_fn_unit mods T (K global_nonreentrant_slot)
        (src,subst_consts_fn_mods (consts_env_mods mods)
          (mut,nr,lookup_raw_return_or_F src tx.function_name External tops,
           tx.function_name,args,[],ret,fbody))) =
      ("fn_" ++ tx.function_name,ce,pos,mc,pay,nr,key,tr,view,body_code,rt)` by
    (qpat_assum `lookup_raw_return_or_F _ _ _ _ = raw` (fn rr =>
       qpat_assum `Abbrev (body_code = _)` (fn body =>
         PURE_REWRITE_TAC [rr, subst_consts_fn_mods_def, subst_consts_expr_mods_def,
              GSYM (REWRITE_RULE [markerTheory.Abbrev_def] body)])) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `initial_venom_state_rel_mods _ _ _ vs`
    (strip_assume_tac o PURE_REWRITE_RULE [initial_venom_state_rel_mods_def]) >>
  `?es0. send_call_value mut cx
    (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
    (INL (),es0)` by
    (Cases_on `send_call_value mut cx
      (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>)` >>
     rename1 `send_call_value mut cx _ = (paid,estate)` >>
     Cases_on `paid`
     >- (qexists_tac `estate` >> qpat_assum `send_call_value mut cx _ = _`
           (fn send => simp[NoAsms, send])) >>
     `value_transfer_ok cx.txn
       (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>).accounts` by
       (simp[NoAsms, Abbr `cx`, initial_evaluation_context_def, initial_state_def] >>
        first_assum ACCEPT_TAC) >>
     drule_all send_call_value_reject_condition >>
     qpat_assum `~(mut <> Payable /\ tx.value <> 0)` (fn accepted =>
       simp[NoAsms, Abbr `cx`, initial_evaluation_context_def, CONJ_COMM, accepted])) >>
  `send_call_value mut (initial_evaluation_context am.sources am.layouts tx src)
      (initial_state am [env] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
      (INL (),es0)` by
    (qpat_assum `Abbrev (cx = _)` (fn cx =>
       PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] cx)]) >>
     first_assum ACCEPT_TAC) >>
  `vars_pc_only (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
            vs_inst_idx := 0|>) vs` by
    simp[NoAsms, vars_pc_only_def, venomStateTheory.venom_state_component_equality] >>
  `!H:(bool # 256 word # type_value) list # num list.
    stmt_state_rel H unit.cu_context fn registered_env cx es0 s0 /\
    ghost_inv H NONE registered_env cx es0 G2 tn2 s0` by
    (gen_tac >>
     qpat_assum `Abbrev (cx = _)` (fn cx =>
       PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] cx]) >>
     mp_tac (Q.INST [`efn` |-> `fn`, `cenv0` |-> `ce`,
       `pos_args` |-> `pos`, `mincd` |-> `mc`, `ut'` |-> `tr`, `iv` |-> `view`,
       `lowered_body` |-> `body_code`, `st` |-> `checked`,
       `cenv` |-> `registered_env`, `sa` |-> `registered`,
       `elbl` |-> `"__entry"`, `s1` |-> `vs`, `tvs` |-> `decoded_tys`,
       `G0` |-> `G2`, `tn0` |-> `tn2`, `lbl` |-> `"fn_" ++ tx.function_name`,
       `site` |-> `ARB:instruction`]
        (Q.INST_TYPE [`:'a` |-> `:256`]
          registration_actual_endpoint_relations_from_prefix_mods)) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  suspend "linked_grouped_legacy_shadow_support"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_legacy_shadow_support]:
  `shadow_body_inv_mods mods exps unit.cu_context shadow_unit.cu_context` by
    (map_every (fn pattern =>
       qpat_assum pattern (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]))
       [`Abbrev (groups = _)`,`Abbrev (ips = _)`,`Abbrev (fall = _)`] >>
     qmatch_asmsub_abbrev_tac
       `run_grouped_lowering grouped_shadow_groups
         (MAP gas_shadow_internal_package ips) (OPTION_MAP gas_shadow_fallback_package fall)
         rpolicy "__entry" = SOME shadow_unit` >>
     qpat_assum `check_contract F am.layouts tx.target mods = SOME art`
       (mp_then Any mp_tac (Q.INST [`shadow_groups` |-> `grouped_shadow_groups`,
          `rp` |-> `rpolicy`] grouped_runtime_shadow_body_inv_mods)) >>
     disch_then (qspecl_then [`unit`,`rpolicy`,`ips`,`ints`,`imp_ctors`,
       `groups`,`grouped_shadow_groups`,`fb`,`fall`,`exts`,`exps`,`ctor`] mp_tac) >>
     impl_tac
     >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       qpat_assum `Abbrev (grouped_shadow_groups = _)`
         (ACCEPT_TAC o REWRITE_RULE [markerTheory.Abbrev_def])]) >>
     qpat_assum `run_grouped_lowering grouped_shadow_groups _ _ _ _ = SOME shadow_unit`
       (fn compiled => simp[NoAsms, compiled, optionTheory.SOME_11])) >>
  suspend "linked_grouped_legacy_registered_cut"
QED

(* Normalize the package and retain the actual grouped prefix; it need not
   be a PC-only path after visiting the preceding groups. *)
Resume linked_runtime_dispatched_readings_certificate[linked_grouped_legacy_registered_cut]:
  qpat_x_assum `dflts = []` SUBST_ALL_TAC >>
  qpat_x_assum `ds = []` SUBST_ALL_TAC >>
  `MEM (src,(mut,nr,raw,tx.function_name,args,[],ret,body_code)) exts` by
    (qpat_assum `entry_key = (src,mut,nr,raw,tx.function_name,args,[],ret,body_code)`
       (PURE_ONCE_REWRITE_TAC o single o SYM) >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `lbl = "fn_" ++ tx.function_name` >>
  qabbrev_tac `name = tx.function_name` >>
  `external_return_buffer_ok (lbl,ce,pos,mc,pay,nr,key,tr,view,body_code,rt)` by
    (qpat_assum `EVERY external_return_buffer_ok (MAP _ exts)`
       (MATCH_MP_TAC o PURE_REWRITE_RULE [EVERY_MEM]) >>
     simp_tac bool_ss [MEM_MAP, combinTheory.o_DEF] >>
     qexists_tac `(src,(mut,nr,raw,name,args,[],ret,body_code))` >>
     conj_tac >- (sym_tac >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (name = tx.function_name)` (fn selected =>
    map_every (fn pat => qpat_assum pat
      (assume_tac o PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] selected]))
      [`src = ALOOKUP exps name`,
       `vyperInterpreter$lookup_function src name External tops = SOME (mut,nr,args,[],ret,fbody)`,
       `lookup_raw_return_or_F src name External tops = raw`]) >>
  `cx.txn = tx` by simp[NoAsms, Abbr `cx`, initial_evaluation_context_def] >>
  qpat_assum `compile_guarded_body registered_env nr key tr view body_code rt registered = ((),last)`
    (fn compiled => qpat_assum `fn_has_code registered last fn`
       (mp_tac o MATCH_MP guarded_body_code_from_registration o CONJ compiled)) >>
  disch_then (qx_choosel_then [`locked`,`body_end`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "linked_grouped_legacy_shadow_intervals"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_legacy_shadow_intervals]:
  rename1 `gas_shadow_function fn shadow_fn` >>
  qpat_assum `compile_guarded_body (gas_shadow_env T registered_env) nr key tr view
       (MAP gas_shadow_stmt body_code) rt shadow_registered = ((),shadow_last)`
    (fn compiled => qpat_assum `fn_has_code shadow_registered shadow_last shadow_fn`
       (mp_tac o MATCH_MP guarded_body_code_from_registration o CONJ compiled)) >>
  disch_then (qx_choosel_then [`shadow_locked`,`shadow_body_end`]
    (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `explicit = gas_explicit_sites unit.cu_context shadow_unit.cu_context` >>
  `!D. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
      (start,FEMPTY,entry_taint) [] (OK s0,G2,tn2)` by
    (gen_tac >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) [] (OK s0,G2,tn2)`
       (qspecl_then [`D`,`explicit`] ACCEPT_TAC)) >>
  linked_registered_path_tac >>
  suspend "linked_grouped_legacy_value_accepted"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_legacy_value_accepted]:
  cheat
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_entry]:
  `?common entries specs off.
     group = ExternalDefaults common entries specs off` by
    (Cases_on `ret = NoneT` >>
     pop_assum (fn return => qpat_assum `entry_key = (src,_)` (fn entry =>
       qpat_assum `ds <> []` (fn nonempty =>
         simp[NoAsms, Abbr `group`, entry, return, nonempty,
              package_external_group_unit_def, package_external_fn_unit_def,
              set_external_package_target_def, LET_THM, NULL_EQ])))) >>
  `package_external_group_unit mods rpolicy.rpol_target T
      (K global_nonreentrant_slot) (src,(mut,nr,selected_raw,tx.function_name,args,ds,ret,body_code)) =
    ExternalDefaults common entries specs off` by
    (qpat_assum `entry_key = (src,_)` (SUBST1_TAC o SYM) >>
     qpat_assum `Abbrev (group = _)`
       (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     first_assum ACCEPT_TAC) >>
  `MEM (src,(mut,nr,selected_raw,tx.function_name,args,ds,ret,body_code)) exts` by
    (qpat_assum `entry_key = (src,_)` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  drule_all classified_grouped_default_compile_inputs_mods >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM (FunctionDecl External mut nr selected_raw tx.function_name args dflts ret selected_body) selected_tops` by
    (qpat_assum `(tx.function_name <> "__default__" /\ _) \/ _`
       (DISJ_CASES_THEN strip_assume_tac)
     >- (qpat_assum `top = FunctionDecl _ _ _ _ _ _ _ _ _`
           (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
     qpat_assum `public_getter_src _ _ = SOME _`
       (strip_assume_tac o REWRITE_RULE [tagged_getter_source_tuple]) >>
     `dflts = []` by drule_then ACCEPT_TAC external_getter_defaults >>
     qpat_assum `LENGTH ds = LENGTH dflts` mp_tac >>
     qpat_assum `dflts = []` (fn empty =>
       qpat_assum `ds <> []` (fn nonempty => simp[NoAsms, empty, nonempty]))) >>
  `module_allocated am.layouts tx.target src selected_tops` by
    drule_all_then ACCEPT_TAC classified_external_owner_allocated_mods >>
  qpat_assum `Abbrev (ds = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all grouped_checked_default_syntax_mods >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `tenv = type_env_all_modules mods` >>
  `entries = MAP (\(p,j). (abi_method_id tenv tx.function_name (MAP SND p),
       external_prefix_label tx.function_name j,min_calldata_size common.ec_env p 0,j))
     (abi_entries args ds)` by
    (qunabbrev_tac `tenv` >>
     qpat_assum `package_external_group_unit _ _ _ _ _ = ExternalDefaults _ _ _ _`
       (mp_tac o REWRITE_RULE [package_external_group_unit_def]) >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn return => qpat_assum `ds <> []` (fn nonempty =>
       simp[NoAsms, return, nonempty, package_external_fn_unit_def,
            set_external_package_target_def, LET_THM, compute_selector_method_id,
            update_cenv_ret_abi_def, update_cenv_nonreentrant_def, NULL_EQ])) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `_ = common` (fn eq => pure_rewrite_tac[GSYM eq]) >>
     qpat_assum `MAP _ _ = entries` (fn eq => pure_rewrite_tac[GSYM eq]) >>
     simp[NoAsms]) >>
  qabbrev_tac `selected = (cd_selector cd,external_prefix_label tx.function_name k,
    min_calldata_size common.ec_env prefix 0,k)` >>
  `MEM selected entries` by
    (qpat_assum `entries = MAP _ _` SUBST1_TAC >>
     pure_rewrite_tac[MEM_MAP] >> qexists_tac `(prefix,k)` >> conj_tac
     >- (qpat_assum `abi_method_id tenv tx.function_name (MAP SND prefix) = cd_selector cd`
            (fn method => simp[NoAsms, Abbr `selected`, method])) >>
     first_assum ACCEPT_TAC) >>
  `!p j. MEM (p,j) (abi_entries args ds) /\
     calldata_method_id cd = n2w (abi_method_id tenv tx.function_name (MAP SND p)) ==>
     p = prefix /\ j = k` by
    (rpt gen_tac >> strip_tac >>
     `abi_method_id tenv tx.function_name (MAP SND p) < dimword (:256)` by
       simp[NoAsms, abi_method_id_def, GSYM calldata_method_id_four_bytes, wordsTheory.w2n_lt] >>
     `abi_method_id tenv tx.function_name (MAP SND p) = cd_selector cd` by
       (qpat_assum `calldata_method_id cd = n2w (abi_method_id tenv _ (MAP SND p))`
          (fn eq => pure_rewrite_tac[GSYM eq]) >>
        qpat_assum `cd_selector cd = w2n _`
          (fn eq => pure_rewrite_tac[eq]) >>
        qpat_assum `calldata_method_id cd = n2w (abi_method_id tenv _ (MAP SND p))`
          (fn eq => simp[eq, wordsTheory.w2n_n2w])) >>
     `MEM (tx.function_name,MAP SND p) (abi_deployed_signatures mods exps)` by
       drule_all_then ACCEPT_TAC classified_grouped_member_signature_mods >>
     `MAP SND p = MAP SND prefix` by
       (qpat_assum `!nm ts. MEM _ (abi_deployed_signatures _ _) /\ _ ==> _`
          (qspecl_then [`tx.function_name`,`MAP SND p`] mp_tac) >>
        qpat_assum `Abbrev (tenv = _)`
          (fn def => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] def)]) >>
        impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
        qpat_assum `tys = MAP SND prefix` (fn eq => simp[NoAsms, eq])) >>
     `LENGTH p = LENGTH prefix` by
       (pop_assum (mp_tac o AP_TERM ``LENGTH : type list -> num``) >> simp[NoAsms]) >>
     qpat_assum `MEM (p,j) (abi_entries args ds)`
       (strip_assume_tac o REWRITE_RULE [abi_entries_member]) >>
     qpat_assum `MEM (prefix,k) (abi_entries args ds)`
       (strip_assume_tac o REWRITE_RULE [abi_entries_member]) >>
     `j = k` by
       (qpat_x_assum `LENGTH p = LENGTH prefix` mp_tac >>
        qpat_assum `p = TAKE _ args` (fn eq => pure_rewrite_tac[eq]) >>
        qpat_assum `prefix = TAKE (LENGTH args - LENGTH ds + k) args`
          (fn eq => pure_rewrite_tac[eq]) >>
        qpat_assum `LENGTH ds <= LENGTH args` mp_tac >>
        qpat_assum `j <= LENGTH ds` mp_tac >> qpat_assum `k <= LENGTH ds` mp_tac >>
        simp[NoAsms, LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >> decide_tac) >>
     asm_rewrite_tac[]) >>
  suspend "linked_grouped_default_selector"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_selector]:
  qabbrev_tac `test = \((sel,_,_,_):num # string # num # num).
    calldata_method_id cd = n2w sel` >>
  `test selected` by
    (qpat_assum `calldata_method_id cd = n2w (cd_selector cd)`
       (fn selector => simp[NoAsms, Abbr `test`, Abbr `selected`, selector])) >>
  `!e. MEM e entries /\ test e ==> e = selected` by
    (qpat_assum `entries = MAP _ _` SUBST1_TAC >>
     simp[NoAsms, MEM_MAP, pairTheory.EXISTS_PROD, PULL_EXISTS] >>
     qx_genl_tac [`p`,`j`] >> strip_tac >>
     qpat_assum `Abbrev (test = _)` (fn def =>
       qpat_assum `test _`
         (assume_tac o SIMP_RULE (srw_ss())
           [REWRITE_RULE [markerTheory.Abbrev_def] def])) >>
     qpat_assum `!p j. MEM (p,j) (abi_entries args ds) /\ _ ==> _`
       (qspecl_then [`p`,`j`] mp_tac) >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
     strip_tac >>
     qpat_assum `p = prefix` SUBST1_TAC >>
     qpat_assum `j = k` SUBST1_TAC >>
     qpat_assum `abi_method_id tenv tx.function_name (MAP SND prefix) = cd_selector cd`
       (fn selector => simp[NoAsms, Abbr `selected`, selector])) >>
  `FIND test entries = SOME selected` by
    (Cases_on `FIND test entries` >> simp[NoAsms]
     >- (qpat_x_assum `FIND test entries = NONE`
           (mp_tac o REWRITE_RULE [mem2varBlockSimHelpersTheory.FIND_NONE_EVERY,
              EVERY_MEM, combinTheory.o_DEF]) >>
         disch_then (qspec_then `selected` mp_tac) >>
         qpat_assum `test selected` (fn hit =>
           qpat_assum `MEM selected entries` (fn member =>
             simp[NoAsms, hit, member]))) >>
     qpat_assum `FIND test entries = SOME _`
       (fn found => assume_tac (MATCH_MP venomInstTheory.FIND_MEM found) >>
                    assume_tac (MATCH_MP venomInstTheory.FIND_P found)) >>
     qpat_assum `!e. MEM e entries /\ test e ==> e = selected` irule >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `compile_external_groups (Var mid)
     (pre ++ ExternalDefaults common entries specs off::post) prelude = (jobs,dispatch_end)` by
    (qpat_assum `groups = pre ++ group::post` (fn split =>
       qpat_assum `group = ExternalDefaults _ _ _ _` (fn packed =>
         qpat_assum `compile_external_groups (Var mid) groups prelude = _`
           (ACCEPT_TAC o REWRITE_RULE [split,packed])))) >>
  `EVERY group_entry_labels_ok (pre ++ ExternalDefaults common entries specs off::post) /\
    MEM (ExternalDefaults common entries specs off) groups` by
    (qpat_assum `groups = pre ++ group::post` (fn split =>
       qpat_assum `group = ExternalDefaults _ _ _ _` (fn packed =>
         qpat_assum `EVERY group_entry_labels_ok groups` mp_tac >>
         simp[NoAsms, split, packed, MEM_APPEND]))) >>
  qpat_assum `Abbrev (test = _)` (fn test_def =>
    qpat_assum `Abbrev (selected = _)` (fn selected_def =>
      qpat_assum `FIND test entries = SOME selected`
        (assume_tac o SIMP_RULE (srw_ss())
          (map (REWRITE_RULE [markerTheory.Abbrev_def]) [test_def,selected_def])))) >>
  `EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs` by
    (qpat_assum `!common entries specs off. MEM (ExternalDefaults _ _ _ _) groups ==> _`
       (qspecl_then [`common`,`entries`,`specs`,`off`] mp_tac) >>
     disch_then (fn widths => MATCH_MP_TAC widths) >> first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (test = _)` (fn test_def =>
    qpat_assum `EVERY (\g. case g of ExternalSingle _ _ => _ |
         ExternalDefaults _ entries _ _ => FIND test entries = NONE /\ _) pre`
      (assume_tac o REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] test_def])) >>
  mp_tac (Q.INST
    [`mid` |-> `mid`, `pref` |-> `pre`, `rest` |-> `post`,
     `common` |-> `common`, `entries` |-> `entries`, `specs` |-> `specs`,
     `off` |-> `off`, `sa` |-> `prelude`, `jobs` |-> `jobs`, `sb` |-> `dispatch_end`,
     `fn` |-> `fn`, `m` |-> `calldata_method_id cd`, `sel` |-> `cd_selector cd`,
     `lbl` |-> `external_prefix_label tx.function_name k`,
     `mincd` |-> `min_calldata_size common.ec_env prefix 0`, `k` |-> `k`,
     `ctx` |-> `unit.cu_context`, `site` |-> `ARB`, `lo` |-> `0`,
     `s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tnu`, `PG` |-> `[]`]
       (SPEC_ALL compile_external_groups_selected_default_origin_with_frame)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`vars`,`opened`,`init`,`initialised`,`hit`,`Gh`,`tnh`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "linked_grouped_default_value_check"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_value_check]:
  `!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
    (start,FEMPTY,entry_taint) [] (OK hit,Gh,tnh)` by
    (rpt gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gu`,`u`,`tnu`] >> asm_rewrite_tac[]) >>
  `common.ec_payable = (mut = Payable)` by
    (qpat_assum `package_external_group_unit _ _ _ _ _ = ExternalDefaults _ _ _ _`
       (mp_tac o REWRITE_RULE [package_external_group_unit_def]) >>
     qpat_assum `ds <> []` (fn nonempty =>
       Cases_on `ret = NoneT` >>
       simp[NoAsms, nonempty, package_external_fn_unit_def,
            set_external_package_target_def, LET_THM, NULL_EQ]) >>
     strip_tac >>
     qpat_assum `_ = common` (SUBST1_TAC o SYM) >>
     simp[NoAsms]) >>
  linked_grouped_value_frame_tac >>
  Cases_on `mut <> Payable /\ tx.value <> 0`
  >- (qpat_x_assum `mut <> Payable /\ tx.value <> 0` strip_assume_tac >>
      `compile_entry_checks (min_calldata_size common.ec_env prefix 0) F opened = ((),init)` by
        (qpat_assum `compile_entry_checks _ common.ec_payable opened = _` mp_tac >>
         qpat_assum `common.ec_payable = _` (fn pay =>
           qpat_assum `mut <> Payable` (fn nonpayable => simp[NoAsms, pay, nonpayable]))) >>
      linked_grouped_reject_callvalue_tac >>
      linked_grouped_reject_source_tac >>
      linked_grouped_reject_resources_tac >>
      linked_grouped_reject_path_tac >>
      linked_grouped_reject_exit_tac >>
      linked_grouped_reject_empty_storage_tac >>
      qexists_tac `[]` >> conj_tac
      >- linked_grouped_reject_execution_tac >>
      linked_grouped_reject_no_gas_tac) >>
  suspend "linked_grouped_default_value_accepted"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_value_accepted]:
  `?pos full_min.
     set_external_package_target rpolicy.rpol_target
       (package_external_fn_unit mods T (K global_nonreentrant_slot)
          (src,(mut,nr,selected_raw,tx.function_name,args,([]:expr list),ret,body_code))) =
     ("fn_" ++ tx.function_name,common.ec_env,pos,full_min,common.ec_payable,
       nr,common.ec_nkey,common.ec_transient,common.ec_view,body_code,common.ec_return)` by
    (qpat_assum `package_external_group_unit _ _ _ _ _ = ExternalDefaults _ _ _ _`
       (mp_tac o REWRITE_RULE [package_external_group_unit_def]) >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn return => qpat_assum `ds <> []` (fn nonempty =>
       simp[NoAsms, return, nonempty, package_external_fn_unit_def,
            set_external_package_target_def, LET_THM, NULL_EQ])) >>
     strip_tac >> qpat_assum `_ = common` (SUBST1_TAC o SYM) >>
     simp[NoAsms]) >>
  `contract_namespaces_ok F mods` by drule_then ACCEPT_TAC check_contract_namespaces_ok >>
  `params_ok (type_env_all_modules mods) args` by
    (qpat_assum `Abbrev (tenv = type_env_all_modules mods)`
       (fn tenv =>
         qpat_assum `params_ok tenv args`
           (ACCEPT_TAC o PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] tenv]))) >>
  drule_all (Q.INST [`dflts` |-> `ds`] linked_registration_package_inputs) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (qx_choose_then `all_tvs` (map_every assume_tac o CONJUNCTS))))) >>
  suspend "linked_grouped_default_head_bound"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_head_bound]:
  `LENGTH all_tvs = LENGTH args` by
    (qpat_assum `OPT_MMAP _ (MAP SND args) = SOME all_tvs`
       (mp_tac o MATCH_MP OPT_MMAP_LENGTH) >> simp[NoAsms]) >>
  `LIST_REL (\arg tv. abi_decoder_coherent common.ec_env
     (type_env_all_modules mods) common.ec_env.ce_struct_fields (SND arg) tv)
     args all_tvs` by
    (PURE_REWRITE_TAC [LIST_REL_EL_EQN] >> conj_tac >- (sym_tac >> first_assum ACCEPT_TAC) >>
     gen_tac >> strip_tac >>
     qpat_assum `LIST_REL _ args (ZIP (MAP SND args,all_tvs))`
       (mp_tac o Q.SPEC `n:num` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     qpat_assum `LENGTH all_tvs = LENGTH args` (fn len =>
       qpat_assum `n < LENGTH args` (fn bound =>
         Cases_on `EL n args` >>
         pop_assum (fn form => simp[NoAsms, len, bound, EL_ZIP, EL_MAP, form])))) >>
  qpat_assum `MEM (prefix,k) (abi_entries args ds)`
    (strip_assume_tac o REWRITE_RULE [abi_entries_member]) >>
  `decoded_tys = TAKE (LENGTH args - LENGTH ds + k) all_tvs` by
    (qpat_assum `OPT_MMAP _ (MAP SND args) = SOME all_tvs`
       (qspec_then `LENGTH args - LENGTH ds + k` mp_tac o MATCH_MP opt_mmap_take_some) >>
     qpat_assum `OPT_MMAP _ tys = SOME decoded_tys` mp_tac >>
     qpat_assum `tys = MAP SND prefix` SUBST1_TAC >>
     qpat_assum `prefix = TAKE (LENGTH args - LENGTH ds + k) args` SUBST1_TAC >>
     qpat_assum `Abbrev (tenv = type_env_all_modules mods)` (fn tenv =>
       simp[NoAsms, MAP_TAKE, REWRITE_RULE [markerTheory.Abbrev_def] tenv])) >>
  `min_calldata_size common.ec_env prefix 0 <= LENGTH cd` by
    (qpat_assum `prefix = TAKE (LENGTH args - LENGTH ds + k) args` SUBST1_TAC >>
     qpat_assum `LIST_REL _ args all_tvs`
       (mp_tac o Q.INST [`n` |-> `LENGTH args - LENGTH (ds:expr list) + k`] o
          MATCH_MP (SPEC_ALL grouped_argument_min_calldata_size)) >>
     qpat_assum `decoded_tys = TAKE (LENGTH args - LENGTH ds + k) all_tvs`
       (fn eq => PURE_REWRITE_TAC [GSYM eq]) >>
     disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  suspend "linked_grouped_default_run_checks"
QED

val shadow_group = ``\group. case group of
  ExternalSingle selector package =>
    ExternalSingle selector (gas_shadow_external_package package)
| ExternalDefaults common entries specs off =>
    ExternalDefaults (common with <| ec_env := gas_shadow_env T common.ec_env;
      ec_body := MAP gas_shadow_stmt common.ec_body |>)
      entries (MAP (\(n,ty,e). (n,ty,gas_shadow_expr e)) specs) off``;

val shadow_job = ``\job. case job of
  ExternalLegacyJob package => ExternalLegacyJob (gas_shadow_external_package package)
| ExternalCommonJob common kwvars => ExternalCommonJob
    (common with <| ec_env := gas_shadow_env T common.ec_env;
                    ec_body := MAP gas_shadow_stmt common.ec_body |>)
    (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) kwvars)``;

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_run_checks]:
  Q.SUBGOAL_THEN `common.ec_payable \/ hit.vs_call_ctx.cc_callvalue = 0w` assume_tac
  >- (qpat_assum `common.ec_payable = _` SUBST1_TAC >>
     qpat_assum `hit.vs_call_ctx.cc_callvalue = _` SUBST1_TAC >>
     qpat_assum `~(mut <> Payable /\ tx.value <> 0)` mp_tac >>
     qpat_assum `tx.value < dimword (:256)`
       (fn bound => simp[NoAsms, wordsTheory.n2w_11, arithmeticTheory.LESS_MOD, bound])) >>
  `hit.vs_call_ctx.cc_calldata = cd` by
    (qpat_assum `hit.vs_call_ctx = _` SUBST1_TAC >>
     qpat_assum `Abbrev (cd = _)`
       (ACCEPT_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def])) >>
  `LENGTH hit.vs_call_ctx.cc_calldata < dimword (:256)` by
    (qpat_assum `hit.vs_call_ctx.cc_calldata = cd` SUBST1_TAC >>
     qpat_assum `LENGTH cd < 18446744073709551616` mp_tac >>
     simp[NoAsms, dimword_def] >> decide_tac) >>
  mp_tac (Q.INST [`m` |-> `min_calldata_size common.ec_env prefix 0`,
    `pay` |-> `common.ec_payable`, `sa` |-> `opened`, `sb` |-> `init`,
    `fn` |-> `fn`, `ctx` |-> `unit.cu_context`, `site` |-> `ARB`,
    `lo` |-> `0`, `s` |-> `hit`, `tn` |-> `tnh`, `G` |-> `Gh`,
    `PG` |-> `[]`] (SPEC_ALL grouped_default_checks_pass_origin)) >>
  impl_tac >- (rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC,
      qpat_assum `hit.vs_call_ctx.cc_calldata = cd` SUBST1_TAC >>
      disj2_tac >> first_assum ACCEPT_TAC]) >>
  disch_then (qx_choosel_then [`decode_start`,`Gdecode`,`tndecode`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "linked_grouped_default_supplied"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_supplied]:
  `off = min_calldata_size common.ec_env (TAKE (LENGTH args - LENGTH ds) args) 0` by
    (qpat_assum `package_external_group_unit _ _ _ _ _ = ExternalDefaults _ _ _ _`
       (mp_tac o REWRITE_RULE [package_external_group_unit_def]) >>
     qpat_assum `ds <> []` (fn nonempty =>
       Cases_on `ret = NoneT` >>
       simp[NoAsms, nonempty, package_external_fn_unit_def,
            set_external_package_target_def, LET_THM, NULL_EQ]) >>
     strip_tac >> qpat_assum `_ = common` (SUBST1_TAC o SYM) >>
     qpat_assum `min_calldata_size _ _ 0 = off`
       (fn offset => simp[NoAsms, GSYM offset])) >>
  `off = 4 + SUM (MAP tv_abi_size (TAKE (LENGTH args - LENGTH ds) all_tvs))` by
    (qpat_assum `off = _` SUBST1_TAC >>
     qpat_assum `LIST_REL _ args all_tvs`
       (ACCEPT_TAC o Q.INST [`n` |-> `LENGTH args - LENGTH (ds:expr list)`] o
        MATCH_MP (SPEC_ALL grouped_argument_min_calldata_size))) >>
  qpat_assum `compile_entry_point_kwargs common.ec_env vars _ _ _ init = _` (fn code =>
    qpat_assum `fn_has_code init initialised fn` (fn installed =>
      qx_choose_then `keyword_end` (map_every assume_tac o CONJUNCTS)
        (MATCH_MP compile_entry_point_kwargs_layout (CONJ code installed)))) >>
  `EVERY group_entry_labels_ok (MAP ^shadow_group groups)` by
    (qpat_assum `EVERY group_entry_labels_ok groups` mp_tac >>
     PURE_REWRITE_TAC [EVERY_MAP, EVERY_MEM, combinTheory.o_DEF] >>
     disch_tac >> qx_gen_tac `shadowed` >> strip_tac >>
     qpat_assum `!x. MEM x groups ==> group_entry_labels_ok x`
       (drule_then mp_tac) >>
     BETA_TAC >> Cases_on `shadowed` >> simp[NoAsms, group_entry_labels_ok_def] >>
     qmatch_goalsub_rename_tac `gas_shadow_external_package package` >>
     PairCases_on `package` >>
     simp[NoAsms, gas_shadow_external_package_def]) >>
  suspend "linked_grouped_default_shadow_init"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_shadow_init]:
  qpat_assum `!other other_jobs other_end other_fn.
      compile_group_dispatch_linear other fall_lbl sf = (other_jobs,other_end) /\ _ ==> _`
    (qspecl_then [`MAP ^shadow_group groups`,`MAP ^shadow_job jobs`,`shd`,`shfn`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `shadow_dispatch_end` (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!sha shb shfn shjobs. gas_shadow_state prelude sha /\ _ ==> _`
    (qspecl_then [`prelude`,`shadow_dispatch_end`,`shfn`,`MAP ^shadow_job jobs`] mp_tac) >>
  impl_tac >-
    (qpat_assum `groups = pre ++ group::post` (fn split =>
       qpat_assum `group = ExternalDefaults common entries specs off` (fn packed =>
         PURE_REWRITE_TAC [GSYM (PURE_REWRITE_RULE [packed] split)])) >>
     asm_rewrite_tac [gas_shadow_state_refl]) >>
  disch_then (qx_choosel_then [`shadow_init`,`shadow_initialised`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `compile_entry_point_kwargs _ (MAP _ vars) off k _ shadow_init = _` (fn code =>
    qpat_assum `fn_has_code shadow_init shadow_initialised shfn` (fn installed =>
      qx_choose_then `shadow_keyword_end` (map_every assume_tac o CONJUNCTS)
        (MATCH_MP compile_entry_point_kwargs_layout (CONJ code installed)))) >>
  suspend "linked_grouped_default_supplied_resources"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_supplied_resources]:
  `4 + SUM (MAP tv_abi_size all_tvs) < dimword (:256)` by
    (qpat_assum `full_min = _` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `calldata_decode_args decode_start.vs_call_ctx.cc_calldata decoded_tys 0 = SOME tx.args` by
    (qpat_assum `selected_registration_frame hit tnh decode_start tndecode`
       (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]) >>
     qpat_assum `decode_start.vs_call_ctx = hit.vs_call_ctx` SUBST1_TAC >>
     qpat_assum `hit.vs_call_ctx.cc_calldata = cd` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  `opened.cs_next_id <= init.cs_next_id` by
    (qpat_assum `compile_entry_checks _ _ opened = ((),init)` (fn checks =>
       mp_tac (PART_MATCH (rand o rand) compile_entry_checks_ci_mono
                         (lhs (concl checks))) >>
       simp[NoAsms, checks, ci_mono_def])) >>
  `!name op ty e. MEM (name,op,ty,e) vars ==>
      ?id q base. op = Var q /\ not_fresh_at init q /\
        lookup_var q decode_start = SOME (n2w base) /\
        MEM (mk_inst id ALLOCA [Lit (n2w (type_memory_bytes common.ec_env ty))] [q]) (fn_insts fn) /\
        FLOOKUP decode_start.vs_allocas id = SOME (base,type_memory_bytes common.ec_env ty) /\
        base + type_memory_bytes common.ec_env ty < dimword (:256) /\ id < init.cs_next_id /\
        ptr_covers Gdecode tndecode q decode_start (type_memory_bytes common.ec_env ty)` by
    (qx_genl_tac [`kwname`,`kwop`,`kwtype`,`kwexpr`] >> strip_tac >>
     pop_assum (fn member =>
       first_assum (assume_tac o (fn slots => MATCH_MP slots member))) >>
     pop_assum (qx_choosel_then [`kwallocid`,`kwptr`,`kwbase`] strip_assume_tac) >>
     qpat_assum `!p. not_fresh_at opened p ==> _`
       (fn preserved =>
         qpat_assum `not_fresh_at opened kwptr`
           (strip_assume_tac o MATCH_MP (Q.SPEC `kwptr` preserved))) >>
     qexistsl_tac [`kwallocid`,`kwptr`,`kwbase`] >> asm_rewrite_tac[] >>
     conj_tac
     >- (qpat_assum `opened.cs_next_id <= init.cs_next_id` mp_tac >>
         qpat_assum `kwallocid < opened.cs_next_id` mp_tac >> decide_tac) >>
     PURE_REWRITE_TAC [ptr_covers_def] >>
     qpat_assum `lookup_var kwptr decode_start = lookup_var kwptr hit` SUBST1_TAC >>
     qpat_assum `FLOOKUP Gdecode kwptr = FLOOKUP Gh kwptr` SUBST1_TAC >>
     qpat_assum `op_taint tndecode (Var kwptr) = op_taint tnh (Var kwptr)` SUBST1_TAC >>
     qpat_assum `ptr_covers Gh tnh kwptr hit _`
       (ACCEPT_TAC o PURE_REWRITE_RULE [ptr_covers_def])) >>
  suspend "linked_grouped_default_supplied_run"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_supplied_run]:
  `OPT_MMAP (evaluate_type (type_env_all_modules mods)) (MAP SND prefix) =
    SOME decoded_tys` by
    (qpat_assum `tys = MAP SND prefix` (SUBST1_TAC o SYM) >>
     qpat_assum `Abbrev (tenv = _)`
       (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `?alloc_start alloc_end.
    compile_create_kwarg_allocas common.ec_env specs alloc_start = (vars,alloc_end)`
    (qx_choosel_then [`kwalloc_start`,`kwalloc_end`] (mk_asm "supplied_alloc")) >>
  asm "supplied_alloc" (fn allocation =>
    qpat_assum `selected_registration_resources _ fn _ _ init decode_start`
      (fn resources =>
       qpat_assum `compile_init_kwargs common.ec_env vars off k _ init = ((),keyword_end)`
         (fn init =>
          qpat_assum `off = 4 + SUM _` (fn offset =>
          let
            fun premise name = find_term (fn tm => same_const
              (fst (strip_comb tm)) name) o lhand
            fun compiler_eq name = find_term (fn tm => is_eq tm andalso same_const
              (fst (strip_comb (lhs tm))) name) o lhand
            val at_alloc = PART_MATCH (compiler_eq ``compile_create_kwarg_allocas``)
              grouped_default_supplied_cut (concl allocation)
            val at_entry = PART_MATCH (premise ``selected_registration_resources``)
              at_alloc (concl resources)
            val at_init = PART_MATCH (compiler_eq ``compile_init_kwargs``)
              at_entry (concl (PURE_REWRITE_RULE [offset] init))
          in
            mp_tac (Q.INST [`env` |-> `type_env_all_modules mods`,
              `provided` |-> `decoded_tys`, `vals` |-> `tx.args`,
              `G` |-> `Gdecode`, `tn` |-> `tndecode`,
              `shfn` |-> `shfn`, `PG` |-> `[]`,
              `sha` |-> `shadow_init`, `shb` |-> `shadow_keyword_end`] at_init)
          end)))) >>
  impl_tac
  >- (qpat_assum `off = 4 + SUM _` (fn offset =>
        PURE_ONCE_REWRITE_TAC [GSYM offset]) >>
      rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC, asm "supplied_alloc" ACCEPT_TAC]) >>
  disch_then (qx_choosel_then
    [`slots`,`supplied_end`,`shadow_supplied_end`,`supplied`,`Gsupplied`,`tnsupplied`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "linked_grouped_default_after_supplied"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_after_supplied]:
  `!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
      (start,FEMPTY,entry_taint) [] (OK supplied,Gsupplied,tnsupplied)` by
    (rpt gen_tac >>
     `gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
        (start,FEMPTY,entry_taint) [] (OK decode_start,Gdecode,tndecode)` by
       (irule gas_origin_ptr_path_trans >>
        qexistsl_tac [`Gh`,`hit`,`tnh`] >> asm_rewrite_tac[]) >>
     irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gdecode`,`decode_start`,`tndecode`] >> asm_rewrite_tac[]) >>
  `MAP (\(_,_,_,e). e) (DROP k vars) = DROP k ds` by
    (qpat_assum `MAP (\(_,_,_,e). e) vars = ds`
       (fn dflts => simp[NoAsms, MAP_DROP, dflts])) >>
  `EVERY (runtime_constant_expr mods) (MAP (\(_,_,_,e). e) (DROP k vars))` by
    (qpat_assum `MAP (\(_,_,_,e). e) (DROP k vars) = DROP k ds` SUBST1_TAC >>
     irule EVERY_DROP >> first_assum ACCEPT_TAC) >>
  `no_sha256_exprs (MAP (\(_,_,_,e). e) (DROP k vars))` by
    (qpat_assum `MAP (\(_,_,_,e). e) (DROP k vars) = DROP k ds` SUBST1_TAC >>
     qpat_assum `no_sha256_exprs ds` mp_tac >>
     simp[NoAsms, no_sha256_collections] >>
     strip_tac >> irule EVERY_DROP >> first_assum ACCEPT_TAC) >>
  `well_typed_exprs (artifact_env art mods src)
      (MAP (\(_,_,_,e). e) (DROP k vars))` by
    (qpat_assum `MAP (\(_,_,_,e). e) (DROP k vars) = DROP k ds` SUBST1_TAC >>
     irule well_typed_exprs_DROP >> first_assum ACCEPT_TAC) >>
  qpat_assum `selected_registration_resources _ fn _ 0 supplied_end supplied`
    (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
  qpat_assum `selected_registration_frame decode_start tndecode supplied tnsupplied`
    (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]) >>
  `start.vs_inst_idx = 0` by simp[NoAsms, Abbr `start`] >>
  `alloca_history fn start /\ alloca_inv start` by
    (conj_tac
     >- (irule alloca_history_empty >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     irule alloca_inv_empty >> first_assum ACCEPT_TAC) >>
  `alloca_history fn supplied` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) []
          (OK supplied,Gsupplied,tnsupplied)`
       (qspecl_then [`ARB`,`ARB`] mp_tac) >>
     strip_tac >> drule_all_then ACCEPT_TAC body_full_path_alloca_history) >>
  suspend "linked_grouped_default_omitted_frame"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_omitted_frame]:
  qabbrev_tac `empty_entry =
    initial_state am [FEMPTY] with <|outcomes := SOME vs.vs_outcomes; requests := []|>` >>
  `value_transfer_ok cx.txn empty_entry.accounts` by
    (qpat_assum `initial_venom_state_rel_mods mods am tx vs` mp_tac >>
     simp[NoAsms, initial_venom_state_rel_mods_def, Abbr `empty_entry`,
          Abbr `cx`, initial_state_def, initial_evaluation_context_def]) >>
  Q.SUBGOAL_THEN `?seed. send_call_value mut cx empty_entry = (INL (),seed)`
    (qx_choose_then `seed` assume_tac)
  >- (namedCases_on `send_call_value mut cx empty_entry` ["res paid"] >>
     namedCases_on `res` ["ok", "err"] >> simp[] >>
     drule_all send_call_value_reject_condition >>
     simp[NoAsms, Abbr `cx`, initial_evaluation_context_def] >>
     qpat_assum `~(mut <> Payable /\ tx.value <> 0)` mp_tac >>
     simp[NoAsms, DE_MORGAN_THM, DISJ_COMM]) >>
  `seed with accounts := am.accounts = empty_entry` by
    (drule_then mp_tac external_send_call_value_frame >>
     simp[NoAsms, Abbr `empty_entry`, initial_state_def]) >>
  `seed.scopes = [FEMPTY] /\ seed.immutables = am.immutables /\
    seed.outcomes = SOME vs.vs_outcomes /\ seed.requests = [] /\
    seed.gas_obs = [] /\ seed.storage_trace = []` by
    (qpat_assum `seed with accounts := am.accounts = empty_entry` mp_tac >>
     simp[NoAsms, Abbr `empty_entry`, initial_state_def, evaluation_state_component_equality]) >>
  `accounts_well_typed seed.accounts` by
    (irule send_call_value_accounts_well_typed_c53 >>
     goal_assum (drule_at Any) >>
     qpat_assum `machine_well_typed am` mp_tac >>
     simp[NoAsms, machine_well_typed_def, Abbr `empty_entry`, initial_state_def]) >>
  `state_well_typed seed` by
    (qpat_assum `machine_well_typed am`
       (assume_tac o CONJUNCT2 o REWRITE_RULE [machine_well_typed_def]) >>
     qpat_assum `seed.scopes = [FEMPTY]` (fn scopes =>
       qpat_assum `seed.immutables = am.immutables` (fn imms =>
         simp[NoAsms, state_well_typed_def, scope_well_typed_def, scopes, imms])) >>
     first_assum ACCEPT_TAC) >>
  `checked_contract_runtime_ready art mods am tx` by
    (drule_all source_typing_ok_runtime_ready_mods >>
     qpat_assum `check_contract F am.layouts tx.target mods = SOME art` (fn checked =>
       simp[NoAsms, checked])) >>
  `context_well_typed cx` by
    (qpat_assum `call_tx_well_typed tx` mp_tac >>
     simp[NoAsms, call_tx_well_typed_def, context_well_typed_def,
          Abbr `cx`, initial_evaluation_context_def]) >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx seed.immutables` by
    (qpat_assum `checked_contract_runtime_ready art mods am tx`
       (mp_tac o REWRITE_RULE [checked_contract_runtime_ready_def]) >>
     qpat_assum `seed.immutables = am.immutables` SUBST1_TAC >>
     strip_tac >> qpat_assum `Abbrev (cx = _)`
       (fn context_eq => PURE_ONCE_REWRITE_TAC
         [REWRITE_RULE [markerTheory.Abbrev_def] context_eq]) >>
     qpat_assum `immutables_ready _ _ (initial_evaluation_context _ _ _ NONE) _`
       (fn ready => ACCEPT_TAC (MATCH_MP immutables_ready_initial_evaluation_context_source ready))) >>
  `env_consistent (artifact_env art mods src) cx seed /\ functions_well_typed cx` by
    (mp_tac (Q.INST [`st` |-> `seed`] (SPEC_ALL checked_external_empty_frame_ready)) >>
     impl_tac
     >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[NoAsms, Abbr `cx`]]) >>
     `seed with scopes := [FEMPTY] = seed` by simp[evaluation_state_component_equality] >>
     asm_rewrite_tac[] >> strip_tac >> asm_rewrite_tac[]) >>
  suspend "linked_grouped_default_omitted_linked_inv"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_omitted_linked_inv]:
  qabbrev_tac `default_env = common.ec_env with ce_vars := FEMPTY` >>
  qabbrev_tac `grouped_base =
    build_compile_env_unit mods src External mut tx.function_name args ret body_code T` >>
  `contract_inv mods exps unit.cu_context
    (grouped_base with ce_target := rpolicy.rpol_target) cx` by
    (qpat_assum `!mut args ret ss. contract_inv _ _ _ _ _`
       (qspecl_then [`mut`,`args`,`ret`,`body_code`] mp_tac) >>
     simp[NoAsms, Abbr `grouped_base`]) >>
  `common.ec_env =
    update_cenv_nonreentrant
      (if ret = NoneT then grouped_base with ce_raw_return := selected_raw
       else update_cenv_ret_abi (grouped_base with ce_raw_return := selected_raw) ret)
      nr global_nonreentrant_slot T (mut = View)
    with ce_target := rpolicy.rpol_target` by
    (qpat_assum `set_external_package_target rpolicy.rpol_target
         (package_external_fn_unit mods T (K global_nonreentrant_slot)
           (src,(mut,nr,selected_raw,tx.function_name,args,[],ret,body_code))) = _` mp_tac >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case =>
       simp[NoAsms, ret_case, Abbr `grouped_base`, LET_THM, combinTheory.K_THM,
            package_external_fn_unit_def, set_external_package_target_def]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `mut = View <=> common.ec_view` (fn view =>
       PURE_ONCE_REWRITE_TAC [GSYM view]) >>
     first_assum (ACCEPT_TAC o SYM)) >>
  `module_body_inv mods src selected_tops default_env cx` by
    (qpat_assum `Abbrev (default_env = _)`
       (fn alias => PURE_ONCE_REWRITE_TAC
         [REWRITE_RULE [markerTheory.Abbrev_def] alias]) >>
     qpat_assum `common.ec_env = _` SUBST1_TAC >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case =>
       simp[NoAsms, ret_case, module_body_inv_def, Abbr `grouped_base`,
            build_compile_env_unit_def, pairTheory.ELIM_UNCURRY,
            update_cenv_nonreentrant_def, update_cenv_ret_abi_def]) >>
     first_assum ACCEPT_TAC) >>
  `contract_inv mods exps unit.cu_context default_env cx` by
    (qpat_assum `contract_inv mods exps _ (grouped_base with ce_target := _) cx` mp_tac >>
     qpat_assum `Abbrev (default_env = _)`
       (fn alias => PURE_ONCE_REWRITE_TAC
         [REWRITE_RULE [markerTheory.Abbrev_def] alias]) >>
     qpat_assum `common.ec_env = _` SUBST1_TAC >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case =>
       simp[NoAsms, ret_case, contract_inv_def, cenv_module_pins_mods_def,
            immutable_section_layout_mods_def,
            update_cenv_nonreentrant_def, update_cenv_ret_abi_def]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     asm_rewrite_tac[] >> rpt conj_tac >>
     FIRST [
       qpat_assum `grouped_base.ce_struct_fields = _`
         (fn fields => PURE_REWRITE_TAC [GSYM fields] >> first_assum ACCEPT_TAC),
       qpat_assum `grouped_base.ce_module_vars = _`
         (fn locations => PURE_REWRITE_TAC [GSYM locations] >> first_assum ACCEPT_TAC),
       rpt gen_tac >> strip_tac >>
       qpat_assum `!sid ts. ALOOKUP mods sid = SOME ts ==> supported_module_headers ts /\ _`
         (drule_then (fn headers => simp[NoAsms, headers]))]) >>
  `shadow_body_inv_mods mods exps unit.cu_context shadow_unit.cu_context` by
    (map_every (fn pattern =>
       qpat_assum pattern (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]))
       [`Abbrev (groups = _)`,`Abbrev (ips = _)`,`Abbrev (fall = _)`] >>
     qmatch_asmsub_abbrev_tac
       `run_grouped_lowering grouped_shadow_groups
         (MAP gas_shadow_internal_package ips) (OPTION_MAP gas_shadow_fallback_package fall)
         rpolicy "__entry" = SOME shadow_unit` >>
     qpat_assum `check_contract F am.layouts tx.target mods = SOME art`
       (mp_then Any mp_tac (Q.INST [`shadow_groups` |-> `grouped_shadow_groups`,
          `rp` |-> `rpolicy`] grouped_runtime_shadow_body_inv_mods)) >>
     disch_then (qspecl_then [`unit`,`rpolicy`,`ips`,`ints`,`imp_ctors`,
       `groups`,`grouped_shadow_groups`,`fb`,`fall`,`exts`,`exps`,`ctor`] mp_tac) >>
     impl_tac
     >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       qpat_assum `Abbrev (grouped_shadow_groups = _)`
         (ACCEPT_TAC o REWRITE_RULE [markerTheory.Abbrev_def])]) >>
     qpat_assum `run_grouped_lowering grouped_shadow_groups _ _ _ _ = SOME shadow_unit`
       (fn compiled => simp[NoAsms, compiled, optionTheory.SOME_11])) >>
  suspend "linked_grouped_default_omitted_expr_inv"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_omitted_expr_inv]:
  qabbrev_tac `initializer_env = artifact_env art mods src` >>
  `get_tenv cx = type_env_all_modules mods /\ ALOOKUP cx.sources cx.txn.target = SOME mods` by
    (qpat_assum `ALOOKUP am.sources tx.target = SOME mods` (fn sources =>
       simp[NoAsms, Abbr `cx`, initial_evaluation_context_def, get_tenv_def, sources])) >>
  `~cx.in_deploy /\ check_contract F cx.layouts cx.txn.target mods = SOME art` by
    (qpat_assum `check_contract F am.layouts tx.target mods = SOME art` (fn checked =>
       simp[NoAsms, Abbr `cx`, initial_evaluation_context_def, checked])) >>
  `frame_maps initializer_env art /\
    initializer_env.toplevel_vtypes = art.cta_toplevel_vtypes /\
    initializer_env.type_defs = get_tenv cx /\ initializer_env.current_src = src` by
    (qpat_assum `get_tenv cx = type_env_all_modules mods` (fn tenv =>
       simp[NoAsms, Abbr `initializer_env`, frame_maps_def, artifact_env_def, tenv])) >>
  `imm_len_mods mods < 24576` by
    (PURE_ONCE_REWRITE_TAC [imm_len_mods_def] >> first_assum ACCEPT_TAC) >>
  `popped_keys_indexed seed.scopes /\ IS_SOME seed.outcomes /\
    outcomes_accounts_typed seed.outcomes` by
    (qpat_assum `seed.scopes = [FEMPTY]` (fn scopes =>
       qpat_assum `seed.outcomes = SOME vs.vs_outcomes` (fn outcomes =>
         simp[NoAsms, scopes, outcomes, popped_keys_indexed_def])) >>
    first_assum ACCEPT_TAC) >>
  `body_const_cells_agree_mods mods cx initializer_env seed` by
    (`(case ALOOKUP seed.immutables cx.txn.target of
          NONE => empty_immutables | SOME cells => cells) =
         account_immutables am tx.target` by
       (qpat_assum `seed.immutables = am.immutables` (fn imms =>
          simp[NoAsms, imms, Abbr `cx`, initial_evaluation_context_def,
               account_immutables_def])) >>
     MATCH_MP_TAC (Q.INST [`art` |-> `art`,`imms` |-> `account_immutables am tx.target`]
       checked_body_const_cells_agree_mods) >>
     qpat_assum `~cx.in_deploy` (fn runtime => simp[NoAsms, runtime]) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, first_assum (ACCEPT_TAC o SYM)]) >>
  `art.cta_bare_global_assignable = FEMPTY` by
    drule_then ACCEPT_TAC check_contract_runtime_assignable >>
  `initializer_env.fn_sigs = art.cta_fn_sigs /\
    initializer_env.bare_globals = art.cta_bare_globals /\
    initializer_env.bare_global_assignable = FEMPTY /\
    initializer_env.var_types = FEMPTY` by
    (qpat_assum `art.cta_bare_global_assignable = FEMPTY`
       (fn writable => simp[NoAsms, Abbr `initializer_env`, artifact_env_def, writable])) >>
  `(!id ty. FLOOKUP initializer_env.var_types id = SOME ty ==>
      ?p sz. FLOOKUP default_env.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    (!id ty. FLOOKUP initializer_env.var_types id = SOME ty ==>
      default_env.ce_var_type id = SOME ty)` by
    (qpat_assum `initializer_env.var_types = FEMPTY` (fn vars => simp[NoAsms, vars])) >>
  `expr_sim_inv_mods mods default_env cx initializer_env seed` by
    drule_all_then ACCEPT_TAC linked_external_entry_expr_sim_inv_mods >>
  suspend "linked_grouped_default_omitted_initializer_inputs"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_omitted_initializer_inputs]:
  `selected_registration_frame vs entry_taint supplied tnsupplied` by
    (map_every (fn frame =>
       qpat_assum frame
         (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]))
       [`selected_registration_frame start entry_taint u tnu`,
        `selected_registration_frame u tnu hit tnh`,
        `selected_registration_frame hit tnh decode_start tndecode`,
        `selected_registration_frame decode_start tndecode supplied tnsupplied`] >>
     asm_rewrite_tac [selected_registration_frame_def] >>
     simp[NoAsms, Abbr `start`]) >>
  `supplied.vs_initial_fmp = start.vs_initial_fmp` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) []
          (OK supplied,Gsupplied,tnsupplied)`
       (qspecl_then [`ARB`,`ARB`] assume_tac) >>
     drule_all_then (ACCEPT_TAC o CONJUNCT1) decoder_origin_path_allocation_frame) >>
  `supplied.vs_fmp = supplied.vs_initial_fmp` by
    (qpat_assum `supplied.vs_initial_fmp = start.vs_initial_fmp` SUBST1_TAC >>
     qpat_assum `selected_registration_frame vs entry_taint supplied tnsupplied`
       (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]) >>
     qpat_assum `initial_venom_state_rel_mods mods am tx vs` (mp_tac o REWRITE_RULE
       [initial_venom_state_rel_mods_def]) >>
     qpat_assum `supplied.vs_fmp = vs.vs_fmp` SUBST1_TAC >>
     simp[NoAsms, Abbr `start`]) >>
  `fmp_room unit.cu_context fn supplied` by
    (MATCH_MP_TAC (Q.INST [`site` |-> `ARB`] entry_frontier_fmp_room) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `supplied.vs_initial_fmp = start.vs_initial_fmp` SUBST1_TAC >>
     qpat_assum `ctx_has_dalloca _ ==> unit_alloca_budget _ <= w2n vs.vs_initial_fmp /\ _`
       mp_tac >>
     simp[NoAsms, Abbr `start`]) >>
  suspend "linked_grouped_default_omitted_seed_rel"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_omitted_seed_rel]:
  `~default_env.ce_is_ctor /\ default_env.ce_imm_alloca = NONE /\
   default_env.ce_return_pc = NONE /\ default_env.ce_return_buf = NONE /\
   default_env.ce_vars = FEMPTY` by
    (qpat_assum `common.ec_env = _` (fn package =>
      simp[NoAsms, Abbr `default_env`, package]) >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case =>
       simp[NoAsms, ret_case, Abbr `grouped_base`, build_compile_env_unit_def,
            pairTheory.ELIM_UNCURRY, update_cenv_nonreentrant_def,
            update_cenv_ret_abi_def, LET_THM])) >>
  `immutable_section_layout_mods mods default_env` by
    drule_then ACCEPT_TAC contract_inv_immutable_section_layout >>
  `ALL_DISTINCT (MAP FST mods) /\
   ALL_DISTINCT (contract_keys toplevel_vtype_keys_toplevel mods)` by
    (drule_then mp_tac check_contract_runtime_namespaces >>
     simp[NoAsms, contract_namespaces_ok_def]) >>
  `storage_vars_rel default_env cx /\ transient_vars_rel default_env cx` by
    (qpat_assum `contract_inv mods exps unit.cu_context default_env cx`
       (strip_assume_tac o REWRITE_RULE [contract_inv_def, cenv_module_pins_mods_def]) >>
     MATCH_MP_TAC (Q.INST [`mods` |-> `mods`,`exps` |-> `exps`,
                           `am` |-> `am`,`tx` |-> `tx`]
       unit_module_locations_slot_relations) >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC, simp[NoAsms, Abbr `cx`, initial_evaluation_context_def]]) >>
  `abi_alloca_history (fn_insts fn) supplied` by
    (`abi_alloca_history (fn_insts fn) start` by
       (MATCH_MP_TAC abi_alloca_history_empty >> first_assum ACCEPT_TAC) >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) []
                    (OK supplied,Gsupplied,tnsupplied)`
       (qspecl_then [`ARB`,`ARB`] assume_tac) >>
     drule_all_then ACCEPT_TAC grouped_entry_path_abi_history) >>
  `!inst w b n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_operands = [Lit w] /\
     FLOOKUP supplied.vs_allocas inst.inst_id = SOME (b,n) ==> n = w2n w` by
    (rpt gen_tac >> strip_tac >>
     drule_all_then ACCEPT_TAC abi_alloca_history_function_size) >>
  suspend "linked_grouped_default_omitted_seed_physical"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_omitted_seed_physical]:
  qpat_assum `initial_venom_state_rel_mods mods am tx vs`
    (strip_assume_tac o REWRITE_RULE [initial_venom_state_rel_mods_def]) >>
  qpat_assum `selected_registration_frame vs entry_taint supplied tnsupplied`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [selected_registration_frame_def, entry_taint_def]) >>
  `local_ptrs_rel fn default_env [FEMPTY] supplied` by
    (qpat_assum `default_env.ce_vars = FEMPTY` (fn vars =>
       simp[NoAsms, vars, local_ptrs_rel_def, local_region_def])) >>
  `send_call_value mut cx
    (initial_state am [FEMPTY] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
      (INL (),seed)` by
    (qpat_assum `Abbrev (empty_entry = _)` (fn alias =>
       PURE_ONCE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] alias)]) >>
     first_assum ACCEPT_TAC) >>
  `!H:(bool # 256 word # type_value) list # num list.
      stmt_state_rel H unit.cu_context fn default_env cx seed supplied` by
    (qx_gen_tac `horizon` >>
     mp_tac (Q.INST [`mods` |-> `mods`,`am` |-> `am`,`tx` |-> `tx`,
       `src` |-> `src`,`mut` |-> `mut`,`H` |-> `horizon`,
       `cenv` |-> `default_env`,`ctx` |-> `unit.cu_context`,
       `efn` |-> `fn`,`s0` |-> `supplied`,`s1` |-> `vs`,`es0` |-> `seed`,
       `G0` |-> `Gsupplied`,`tn0` |-> `tnsupplied`,`args` |-> `[]:argument list`,
       `vals` |-> `[]:value list`,`env` |-> `FEMPTY:scope`,
       `tvs` |-> `[]:type_value list`,`site` |-> `ARB:instruction`,
       `elbl` |-> `"__entry"`]
       (INST_TYPE [alpha |-> ``:256``] linked_registration_endpoint_from_frame)) >>
     qpat_assum `Abbrev (cx = _)` (fn context =>
       PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] context)]) >>
     impl_tac
     >- (simp[NoAsms, bind_arguments_def, vars_pc_only_def, venom_state_component_equality] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         first_assum ACCEPT_TAC) >>
     disch_then (MATCH_ACCEPT_TAC o CONJUNCT1)) >>
  `immutable_frame_mods fn default_env cx seed supplied` by
    (qpat_assum `~default_env.ce_is_ctor` (fn runtime =>
       simp[NoAsms, runtime, immutable_frame_mods_def, immutables_rel_mods_def,
            immutable_alloca_sep_mods_def, immutable_alloca_sep_def, immutable_decl_sep_def]) >>
     rpt gen_tac >> strip_tac >>
     irule linked_section_runtime_relation >> qexists_tac `mods` >>
     qpat_assum `seed.immutables = am.immutables` (fn source =>
       qpat_assum `supplied.vs_data_section = vs.vs_data_section` (fn section =>
         simp[NoAsms, source, section, Abbr `cx`, initial_evaluation_context_def,
              GSYM account_immutables_def])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!D. ghost_inv_at D 0 NONE default_env cx seed Gsupplied tnsupplied supplied` by
    (gen_tac >>
     qpat_assum `default_env.ce_vars = FEMPTY` (fn vars =>
       qpat_assum `default_env.ce_return_pc = NONE` (fn retpc =>
         simp[NoAsms, ghost_inv_at_def, vars, retpc, return_buf_ptr_def, stor_taint_ok_at_def,
              allocas_from_def])) >>
     asm_simp_tac (srw_ss()) [pred_setTheory.EMPTY_SUBSET]) >>
  `!(regions:(bool # 256 word # type_value) list).
     storage_well_formed_on cx (initial_state am []) regions ==>
     storage_well_formed_on cx seed regions` by
    (gen_tac >> strip_tac >>
     irule send_call_value_preserves_storage_well_formed_on >>
     qexistsl_tac [`mut`,`INL ()`,`empty_entry`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     `storage_well_formed_on cx empty_entry regions <=>
       storage_well_formed_on cx (initial_state am []) regions` by
       (MATCH_MP_TAC storage_well_formed_on_backends >>
        simp[NoAsms, Abbr `empty_entry`, initial_state_def]) >>
     first_assum (fn same => PURE_ONCE_REWRITE_TAC [same]) >>
     first_assum ACCEPT_TAC) >>
  suspend "linked_grouped_default_omitted_readiness"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_omitted_readiness]:
  `!key rhs. ALOOKUP (consts_env_mods mods) key = SOME rhs ==>
      accesses_expr rhs = []` by
    (qpat_assum `body_const_cells_agree_mods mods cx initializer_env seed`
       (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_mods_def]) >>
     qx_genl_tac [`key`,`rhs`] >> PairCases_on `key` >> strip_tac >>
     qpat_assum `!sid id r. ALOOKUP (consts_env_mods mods) (sid,id) = SOME r ==> _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     first_assum ACCEPT_TAC) >>
  `!sid id vt. FLOOKUP initializer_env.toplevel_vtypes (sid,id) = SOME vt ==>
     well_formed_vtype initializer_env.type_defs vt` by
    (qpat_assum `initializer_env.toplevel_vtypes = art.cta_toplevel_vtypes` SUBST1_TAC >>
     qpat_assum `initializer_env.type_defs = get_tenv cx` SUBST1_TAC >>
     qpat_assum `get_tenv cx = type_env_all_modules mods` SUBST1_TAC >>
     qpat_assum `check_contract F am.layouts tx.target mods = SOME art` (fn checked =>
       qpat_assum `ALOOKUP am.sources tx.target = SOME mods` (fn sources =>
         let
           val frame_types = PART_MATCH (hd o strip_conj o lhand)
             check_contract_toplevel_vtypes_consistent_initial (concl checked)
         in
           mp_tac (Q.INST [`sources` |-> `am.sources`, `tx` |-> `tx`] frame_types) >>
           simp[NoAsms, checked, sources]
         end)) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `LIST_REL (\arg tv. abi_decoder_coherent common.ec_env
      (type_env_all_modules mods) common.ec_env.ce_struct_fields (SND arg) tv)
      (DROP (LENGTH args - LENGTH ds) args) (DROP (LENGTH args - LENGTH ds) all_tvs)` by
    (irule LIST_REL_DROP >> first_assum ACCEPT_TAC) >>
  `LIST_REL (\(_,_,ty,_) tv. abi_decoder_coherent common.ec_env
      (type_env_all_modules mods) common.ec_env.ce_struct_fields ty tv)
      vars (MAP (\(_,_,_,tv). tv) slots)` by
    (qpat_assum `LIST_REL _ (DROP (LENGTH args - LENGTH ds) args)
                        (DROP (LENGTH args - LENGTH ds) all_tvs)` mp_tac >>
     qpat_assum `MAP (\(name,_,ty,_). (name,ty)) vars = DROP _ args`
       (fn arg_rows => PURE_REWRITE_TAC [GSYM arg_rows]) >>
     qpat_assum `MAP (\(_,_,_,tv). tv) slots = DROP _ all_tvs`
       (fn type_rows => PURE_REWRITE_TAC [GSYM type_rows]) >>
     simp[NoAsms, LIST_REL_MAP1, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]) >>
  suspend "linked_grouped_default_omitted_preconditions"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_omitted_preconditions]:
  `check_linked_state_ownership am.layouts tx.target mods (linked_live_functions mods exps)` by
    (PURE_REWRITE_TAC [GSYM linked_state_ownership_ok_def] >>
     drule_all_then ACCEPT_TAC check_contract_linked_state_ownership_ok) >>
  `src = ALOOKUP exps tx.function_name` by simp[NoAsms, Abbr `src`] >>
  `MEM (src,tx.function_name) (linked_main_roots mods ++ linked_export_roots exps)` by
    (Cases_on `src` >> simp_tac bool_ss [MEM_APPEND]
     >- (disj1_tac >>
         `MEM (NONE:num option,tx.function_name)
           (FLAT (MAP (external_name_keys_toplevel NONE) selected_tops))` by
           (simp[NoAsms, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
            qexists_tac `FunctionDecl External mut nr selected_raw tx.function_name args dflts ret selected_body` >>
            simp[NoAsms, external_name_keys_toplevel_def] >>
            first_assum ACCEPT_TAC) >>
         qpat_assum `ALOOKUP mods NONE = SOME selected_tops` (fn main =>
           simp[NoAsms, linked_main_roots_def, main, contract_keys_def, MEM_APPEND]) >>
         disj1_tac >> first_assum ACCEPT_TAC) >>
     disj2_tac >> simp[NoAsms, linked_export_roots_def, MEM_MAP, EXISTS_PROD] >>
     qpat_assum `SOME _ = ALOOKUP exps tx.function_name`
       (ACCEPT_TAC o MATCH_MP ALOOKUP_MEM o SYM)) >>
  `MEM (src,tx.function_name) (linked_live_functions mods exps)` by
    (PURE_REWRITE_TAC [linked_live_functions_def, linked_live_functions_from_def, LET_THM] >>
     BETA_TAC >> irule (cj 1 call_closure_from_roots) >> first_assum ACCEPT_TAC) >>
  `~supported_exprs_exists (unallocated_bare_global_root default_env initializer_env) ds` by
    (qpat_assum `ds = subst_consts_exprs_mods (consts_env_mods mods) dflts` SUBST1_TAC >>
     drule_all_then ACCEPT_TAC linkedEntryImmutableGuardsTheory.linked_checked_default_immutable_guards) >>
  `!e. MEM e ds ==> ~supported_expr_exists (unallocated_bare_global_root default_env initializer_env) e` by
    (rpt strip_tac >>
     qpat_assum `~supported_exprs_exists (unallocated_bare_global_root default_env initializer_env) ds`
       mp_tac >>
     simp[NoAsms, supportedExprTraverseTheory.supported_exprs_exists_every, EXISTS_MEM] >>
     qexists_tac `e` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `!e. MEM e ds ==> ~supported_expr_exists (const_name_root_mods mods) e` by
    (`!xs. subst_consts_exprs_mods (consts_env_mods mods) xs =
      MAP (subst_consts_expr_mods (consts_env_mods mods)) xs` by
        (Induct >> simp[subst_consts_expr_mods_def]) >>
     qpat_assum `ds = subst_consts_exprs_mods (consts_env_mods mods) dflts` SUBST1_TAC >>
     qpat_assum `!xs. subst_consts_exprs_mods (consts_env_mods mods) xs = _`
       (pure_rewrite_tac o single) >>
     simp[NoAsms, MEM_MAP, PULL_EXISTS] >>
     qx_gen_tac `raw_expr` >> strip_tac >>
     qpat_assum `!key rhs. ALOOKUP (consts_env_mods mods) key = SOME rhs ==> _` (fn closed =>
       mp_tac (MATCH_MP (Q.INST [`ss` |-> `[Expr raw_expr]`]
         linkedEntryImmutableGuardsTheory.substituted_stmts_const_name_free_mods) closed)) >>
     simp[NoAsms, subst_consts_stmt_mods_def,
          supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
          supportedExprTraverseTheory.supported_expr_exists_def]) >>
  `call_evaluation_safe cx []` by
    (`cx with stk := [(src,tx.function_name)] = cx` by
       simp[NoAsms, Abbr `cx`, initial_evaluation_context_def] >>
     pop_assum (fn stk => PURE_ONCE_REWRITE_TAC [GSYM stk]) >>
     irule checked_contract_call_evaluation_safe_singleton >>
     qexistsl_tac [`art`,`cx.layouts`,`mods`] >>
     simp[NoAsms, calls_follow_call_graph_def, Abbr `cx`, initial_evaluation_context_def] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "linked_grouped_default_omitted_expr_checks"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_omitted_expr_checks]:
  `!e es'. MEM e (DROP k ds) ==>
    expr_sim_inv_mods mods default_env cx initializer_env es' ==>
    expr_body_pre_mods mods default_env cx initializer_env e es'` by
    (rpt strip_tac >>
     `MEM e ds` by drule_then ACCEPT_TAC rich_listTheory.MEM_DROP_IMP >>
     `well_typed_expr initializer_env e` by
       (irule frame_well_typed_exprs_member >> qexists_tac `ds` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     `byte_widths_expr e` by
       (irule well_typed_expr_byte_widths >> qexists_tac `initializer_env` >>
        qpat_assum `initializer_env.var_types = FEMPTY` (fn vars =>
          simp[NoAsms, vars]) >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     `runtime_constant_expr mods e` by
       (qpat_assum `EVERY (runtime_constant_expr mods) ds`
         (drule_then ACCEPT_TAC o REWRITE_RULE [EVERY_MEM])) >>
     `alloc_limits_expr default_env e` by
       (irule exprSimSourceTheory.alloc_limits_exprs_mem >>
        qexists_tac `ds` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     irule groupedDefaultPreTheory.runtime_constant_expr_body_pre_mods >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
            qpat_assum `!e. MEM e ds ==> ~supported_expr_exists (const_name_root_mods mods) e`
              (drule_then ACCEPT_TAC),
            qpat_assum `!e. MEM e ds ==>
               ~supported_expr_exists (unallocated_bare_global_root default_env initializer_env) e`
              (drule_then ACCEPT_TAC)]) >>
  `!H:(bool # 256 word # type_value) list # num list.
    dead_lo_ok H (cx_dead H cx) 0 default_env cx` by
    (qpat_assum `~default_env.ce_is_ctor` (fn runtime =>
      simp[NoAsms, dead_lo_ok_def, runtime])) >>
  `storage_trace_domain cx (initial_state am []) seed.storage_trace` by
    (qpat_assum `seed.storage_trace = []` SUBST1_TAC >> EVAL_TAC >> simp[NoAsms]) >>
  `!H. valid_horizon cx (initial_state am []) H seed.storage_trace ==>
    stmt_state_rel H unit.cu_context fn default_env cx seed supplied /\
    immutable_frame_mods fn default_env cx seed supplied /\
    storage_well_formed_on cx seed (FST H) /\
    ghost_inv_at (cx_dead H cx) 0 NONE default_env cx seed Gsupplied tnsupplied supplied` by
    (gen_tac >>
     disch_then (strip_assume_tac o REWRITE_RULE [valid_horizon_def]) >>
     conj_tac >- (qpat_assum `!H. stmt_state_rel H _ _ _ _ _ _` (qspec_then `H` ACCEPT_TAC)) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (qpat_assum `!regions. storage_well_formed_on cx (initial_state am []) regions ==>
                    storage_well_formed_on cx seed regions` (irule o SPEC_ALL) >>
         first_assum ACCEPT_TAC) >>
     qpat_assum `!D. ghost_inv_at D 0 NONE default_env cx seed Gsupplied tnsupplied supplied`
       (qspec_then `cx_dead H cx` ACCEPT_TAC)) >>
  `!i. contextCodegenRel$active_inst fn i supplied ==> raw_reachable vs unit.cu_context fn i supplied` by
    (rpt strip_tac >>
     `gas_path unit.cu_context fn start 0 (OK supplied)` by
       (qpat_assum `!D explicit. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) []
           (OK supplied,Gsupplied,tnsupplied)`
          (qspecl_then [`ARB`,`EMPTY`]
             (mp_tac o MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_erase)) >>
        simp[NoAsms]) >>
     mp_tac (Q.INST [`ctx` |-> `unit.cu_context`,`n` |-> `0`,
       `s` |-> `start`,`w` |-> `supplied`,`inst` |-> `i`]
       callRejectMemoryTheory.raw_reachable_from_entry_path) >>
     impl_tac
     >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[Abbr `start`]]) >>
     disch_then ACCEPT_TAC) >>
  `!callee inst w. frag_reachable unit.cu_context fn supplied callee inst w ==>
    dalloca_fmp_headroom inst w` by
    (Cases_on `ctx_has_dalloca unit.cu_context`
     >- (rpt strip_tac >>
         qpat_assum `ctx_has_dalloca unit.cu_context ==>
            !fn inst s. raw_reachable vs _ fn inst s ==> _` (drule_then irule) >>
         qexists_tac `callee` >>
         drule_then (qspec_then `vs` irule) deployBodyReachabilityTheory.raw_reachable_through_fragment >>
         first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     `MEM fn unit.cu_context.ctx_functions` by
       (qpat_assum `venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn`
          (ACCEPT_TAC o MATCH_MP venomInstTheory.lookup_function_MEM)) >>
     qpat_assum `frag_reachable unit.cu_context fn supplied callee inst w`
       (fn reached => qpat_assum `MEM fn unit.cu_context.ctx_functions`
         (map_every assume_tac o CONJUNCTS o MATCH_MP (MATCH_MP
           contextRawReachableTheory.frag_reachable_members reached))) >>
     qpat_assum `~ctx_has_dalloca unit.cu_context` mp_tac >>
     simp[NoAsms, ctx_has_dalloca_def, EXISTS_MEM, unitTransformDefsTheory.dalloca_fmp_headroom_def] >>
     disch_then (qspec_then `callee` mp_tac) >>
     qpat_assum `MEM callee unit.cu_context.ctx_functions` (fn mem => simp[NoAsms, mem]) >>
     disch_then (qspec_then `inst` mp_tac) >>
     qpat_assum `MEM inst (fn_insts callee)` (fn mem => simp[NoAsms, mem])) >>
  suspend "linked_grouped_default_omitted_initializer_rows"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_omitted_initializer_rows]:
  qabbrev_tac `allocation_env =
    build_compile_env_unit mods src Internal mut tx.function_name args ret body_code F` >>
  `type_memory_bytes common.ec_env = type_memory_bytes allocation_env` by
    (irule type_memory_bytes_frame >>
     qpat_assum `common.ec_env = _` (PURE_ONCE_REWRITE_TAC o single) >>
     Cases_on `ret = NoneT` >>
     pop_assum (fn ret_case =>
       simp[NoAsms, ret_case, Abbr `allocation_env`, Abbr `grouped_base`,
            build_compile_env_unit_def, pairTheory.ELIM_UNCURRY, LET_THM,
            update_cenv_nonreentrant_def, update_cenv_ret_abi_def])) >>
  `!n ty. MEM (n,ty) args ==> type_memory_bytes common.ec_env ty < 2 ** 64` by
    (qpat_assum `fn_allocs_ok_unit mods (src,(mut,nr,selected_raw,tx.function_name,args,ds,ret,body_code))`
       mp_tac >>
     qpat_assum `type_memory_bytes common.ec_env = type_memory_bytes allocation_env`
       (fn eq => PURE_REWRITE_TAC [eq]) >>
     simp[NoAsms, fn_allocs_ok_unit_def, Abbr `allocation_env`, EVERY_MEM, FORALL_PROD] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `!n dst ty e. MEM (n,dst,ty,e) vars ==> MEM (n,ty) args /\ MEM e ds /\ expr_type e = ty` by
    (rpt gen_tac >> PURE_REWRITE_TAC [MEM_EL] >>
     disch_then (qx_choose_then `j` strip_assume_tac) >>
     `LENGTH (DROP (LENGTH args - LENGTH ds) args) = LENGTH vars /\ LENGTH ds = LENGTH vars` by
       (qpat_assum `MAP (\(name,_,ty,_). (name,ty)) vars = DROP _ args`
          (mp_tac o Q.AP_TERM `LENGTH`) >>
        qpat_assum `MAP (\(_,_,_,e). e) vars = ds`
          (mp_tac o Q.AP_TERM `LENGTH`) >> simp[NoAsms]) >>
     `EL j (DROP (LENGTH args - LENGTH ds) args) = (n,ty) /\ EL j ds = e` by
       (qpat_assum `MAP (\(name,_,ty,_). (name,ty)) vars = DROP _ args`
          (mp_tac o Q.AP_TERM `EL j`) >>
        qpat_assum `MAP (\(_,_,_,e). e) vars = ds`
          (mp_tac o Q.AP_TERM `EL j`) >>
        qpat_assum `j < LENGTH vars` (fn bound =>
          qpat_assum `(n,dst,ty,e) = EL j vars` (fn row =>
            simp[NoAsms, bound, GSYM row, EL_MAP]))) >>
     conj_tac
     >- (`MEM (n,ty) (DROP (LENGTH args - LENGTH ds) args)` by
           (PURE_REWRITE_TAC [MEM_EL] >> qexists_tac `j` >>
            conj_tac
            >- (qpat_assum `LENGTH (DROP _ args) = LENGTH vars` SUBST1_TAC >>
                first_assum ACCEPT_TAC) >>
            sym_tac >> first_assum ACCEPT_TAC) >>
         qpat_assum `MEM (n,ty) (DROP _ args)`
           (ACCEPT_TAC o PURE_REWRITE_RULE [MEM_EL] o
            MATCH_MP (SPEC_ALL rich_listTheory.MEM_DROP_IMP))) >>
     conj_tac
     >- (qexists_tac `j` >> conj_tac
         >- (qpat_assum `LENGTH ds = LENGTH vars` SUBST1_TAC >>
             first_assum ACCEPT_TAC) >>
         sym_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `MAP expr_type ds = MAP SND (DROP _ args)` (mp_tac o Q.AP_TERM `EL j`) >>
     qpat_assum `LENGTH (DROP _ args) = LENGTH vars` (fn len_drop =>
       qpat_assum `LENGTH ds = LENGTH vars` (fn len_ds =>
         qpat_assum `j < LENGTH vars` (fn bound =>
           qpat_assum `EL j (DROP _ args) = (n,ty)` (fn arg =>
             qpat_assum `EL j ds = e` (fn expr =>
               simp[NoAsms, len_drop, len_ds, bound, arg, expr, EL_MAP])))))) >>
  `LIST_REL (\(_,_,ty,_) tv. abi_decoder_coherent common.ec_env
    (type_env_all_modules mods) common.ec_env.ce_struct_fields ty tv)
      (DROP k vars) (DROP k (MAP (\(_,_,_,tv). tv) slots))` by
    (irule LIST_REL_DROP >> first_assum ACCEPT_TAC) >>
  `LIST_REL (\(n,dst,ty,e) (aid,p,base,tv).
    dst = Var p /\ runtime_constant_expr mods e /\ expr_type e = ty /\
    (!es'. expr_sim_inv_mods mods default_env cx initializer_env es' ==>
      expr_body_pre_mods mods default_env cx initializer_env e es') /\
    lower_value compile_expr default_env ty e = lower_value compile_expr common.ec_env ty e /\
    lower_value compile_expr (gas_shadow_env T default_env) ty (gas_shadow_expr e) =
      lower_value compile_expr (gas_shadow_env T common.ec_env) ty (gas_shadow_expr e) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    type_memory_bytes common.ec_env ty = type_memory_size tv /\
    type_memory_size tv + 64 < dimword (:256)) (DROP k vars) (DROP k slots)` by
    (qpat_assum `LIST_REL (\(name,op,ty,e) (id,q,base,tv). op = Var q /\ _)
       vars slots` (mp_tac o Q.SPEC `k` o MATCH_MP LIST_REL_DROP) >>
     PURE_REWRITE_TAC [LIST_REL_EL_EQN] >>
     disch_then (CONJUNCTS_THEN2 assume_tac (mk_asm "allocated_at_index")) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qx_gen_tac `j` >> strip_tac >>
     Cases_on `EL j (DROP k vars)` >> PairCases_on `r` >>
     Cases_on `EL j (DROP k slots)` >> PairCases_on `r` >>
     rename1 `EL j (DROP k vars) = (nm,dst,ty,e)` >>
     rename1 `EL j (DROP k slots) = (row_aid,row_p,row_base,tval:type_value)` >>
     `j < LENGTH (DROP k slots)` by
       (qpat_assum `LENGTH (DROP k vars) = LENGTH (DROP k slots)`
          (PURE_ONCE_REWRITE_TAC o single o SYM) >> first_assum ACCEPT_TAC) >>
     `MEM (nm,dst,ty,e) (DROP k vars) /\ MEM (nm,dst,ty,e) vars` by
       (`MEM (nm,dst,ty,e) (DROP k vars)` by
          (PURE_REWRITE_TAC [MEM_EL] >> qexists_tac `j` >>
           conj_tac >- first_assum ACCEPT_TAC >>
           sym_tac >> first_assum ACCEPT_TAC) >>
        conj_tac >- first_assum ACCEPT_TAC >>
        drule_then ACCEPT_TAC rich_listTheory.MEM_DROP_IMP) >>
     `MEM (nm,ty) args /\ MEM e ds /\ expr_type e = ty` by
       (qpat_assum `!n dst ty e. MEM (n,dst,ty,e) vars ==> _` (drule_then ACCEPT_TAC)) >>
     `MEM e (DROP k ds)` by
       (qpat_assum `MAP _ (DROP k vars) = DROP k ds` (SUBST1_TAC o SYM) >>
        PURE_REWRITE_TAC [MEM_MAP] >> qexists_tac `(nm,dst,ty,e)` >>
        simp[NoAsms] >> first_assum ACCEPT_TAC) >>
     `runtime_constant_expr mods e` by
       (qpat_assum `EVERY (runtime_constant_expr mods) ds`
          (drule_then ACCEPT_TAC o REWRITE_RULE [EVERY_MEM])) >>
     `well_typed_expr initializer_env e` by
       (irule frame_well_typed_exprs_member >> qexists_tac `ds` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     asm "allocated_at_index" (qspec_then `j` mp_tac) >>
     qpat_assum `j < LENGTH (DROP k vars)` (fn bound =>
       qpat_assum `EL j (DROP k vars) = (nm,dst,ty,e)` (fn expr =>
         qpat_assum `EL j (DROP k slots) = (row_aid,row_p,row_base,tval)`
           (fn slot => simp[NoAsms, bound, expr, slot]))) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `abi_decoder_header common.ec_env (type_env_all_modules mods) ty tval` by
       (irule abi_decoder_coherent_header >>
        qexists_tac `common.ec_env.ce_struct_fields` >>
        qpat_assum `LIST_REL _ (DROP k vars) (DROP k (MAP (\(_,_,_,tv). tv) slots))`
          (mp_tac o REWRITE_RULE [GSYM MAP_DROP, LIST_REL_EL_EQN]) >>
        disch_then (qspec_then `j` mp_tac o CONJUNCT2) >>
        qpat_assum `EL j (DROP k vars) = (nm,dst,ty,e)` (fn expr =>
          qpat_assum `EL j (DROP k slots) = (row_aid,row_p,row_base,tval)` (fn slot =>
            qpat_assum `j < LENGTH (DROP k slots)` (fn bound =>
              qpat_assum `j < LENGTH (DROP k vars)` (fn ix =>
                simp[NoAsms, EL_MAP, expr, slot, bound, ix]))))) >>
     `type_memory_bytes common.ec_env ty < 2 ** 64` by
       (qpat_assum `!n ty. MEM (n,ty) args ==> _`
          (qspecl_then [`nm`,`ty`] (drule_then ACCEPT_TAC))) >>
     `type_memory_size tval + 64 < dimword (:256)` by
       (qpat_assum `type_memory_bytes common.ec_env ty = type_memory_size tval`
          (SUBST1_TAC o SYM) >>
        qpat_assum `type_memory_bytes common.ec_env ty < 2 ** 64` mp_tac >>
        simp[NoAsms, wordsTheory.dimword_def] >> decide_tac) >>
     `!ce. lower_value compile_expr (ce with ce_vars := FEMPTY) ty e =
             lower_value compile_expr ce ty e /\
           lower_value compile_expr (ce with ce_vars := FEMPTY) ty (gas_shadow_expr e) =
             lower_value compile_expr ce ty (gas_shadow_expr e)` by
       (gen_tac >> MATCH_MP_TAC (Q.INST [`mods` |-> `mods`]
          runtimeDefaultCompileTheory.runtime_default_lower_value_vars_frame) >>
        map_every assume_tac (CONJUNCTS runtimeDefaultCompileTheory.well_typed_expr_builtin_args_length) >>
        qpat_assum `!en x. well_typed_expr en x ==> ~supported_expr_exists _ x`
          (drule_then assume_tac) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `EL j (DROP k vars) = (nm,dst,ty,e)` (fn expr =>
       qpat_assum `EL j (DROP k slots) = (row_aid,row_p,row_base,tval)`
         (fn slot => simp[NoAsms, expr, slot])) >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       qpat_assum `!e es'. MEM e (DROP k ds) ==> _`
         (qspec_then `e` (drule_then ACCEPT_TAC)),
       qpat_assum `!ce. lower_value _ _ _ _ = _ /\ _`
         (qspec_then `common.ec_env` mp_tac) >>
       simp[NoAsms, Abbr `default_env`] >> NO_TAC,
       qpat_assum `!ce. lower_value _ _ _ _ = _ /\ _`
         (qspec_then `gas_shadow_env T common.ec_env` mp_tac) >>
       simp[NoAsms, Abbr `default_env`, gasShadowCompileBaseTheory.gas_shadow_env_def] >> NO_TAC,
       qpat_assum `get_tenv cx = type_env_all_modules mods` SUBST1_TAC >>
       qpat_assum `abi_decoder_header _ _ ty tval`
         (strip_assume_tac o REWRITE_RULE [abi_decoder_header_def]) >>
       first_assum ACCEPT_TAC]) >>
  suspend "linked_grouped_default_omitted_initializer_full"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_omitted_initializer_full]:
  `EVERY (struct_args_unique o SND) mods` by
    (simp[NoAsms, EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
     rename1 `MEM (owner,ts) mods` >>
     irule typedCopyProducerTheory.distinct_type_keys_struct_args_unique >>
     `ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel owner) ts))` by
       drule_all_then ACCEPT_TAC contract_namespaces_ok_module_type_def_keys >>
     `!decls. FLAT (MAP (type_def_keys_toplevel (NONE:num option)) decls) =
         MAP (\(_,n). (NONE:num option,n)) (FLAT (MAP (type_def_keys_toplevel owner) decls)) /\
       EVERY (\(s,_). s = owner) (FLAT (MAP (type_def_keys_toplevel owner) decls))` by
       (POP_ASSUM_LIST (K ALL_TAC) >> Induct >> simp[] >>
        Cases_on `h` >> simp[type_def_keys_toplevel_def]) >>
     pop_assum (qspec_then `ts` strip_assume_tac) >>
     qpat_assum `FLAT (MAP (type_def_keys_toplevel NONE) ts) = MAP _ _` SUBST1_TAC >>
     irule ALL_DISTINCT_MAP_INJ >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     simp[NoAsms, FORALL_PROD] >>
     qpat_assum `EVERY _ (FLAT (MAP (type_def_keys_toplevel owner) ts))` mp_tac >>
     simp[NoAsms, EVERY_MEM, FORALL_PROD] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `exports_ok cx.layouts cx.txn.target mods exps` by
    (simp[NoAsms, Abbr `cx`, initial_evaluation_context_def] >> first_assum ACCEPT_TAC) >>
  `IS_SOME (check_contract F cx.layouts cx.txn.target mods)` by
    (qpat_assum `check_contract F cx.layouts cx.txn.target mods = SOME art`
       (fn checked => simp[NoAsms, checked])) >>
  `EVERY (body_expr_full_ok_mods mods exps cx) (MAP (\(_,_,_,e). e) (DROP k vars))` by
    (qpat_assum `EVERY (runtime_constant_expr mods) (MAP (\(_,_,_,e). e) (DROP k vars))` mp_tac >>
     simp[NoAsms, EVERY_MEM] >> strip_tac >> rpt strip_tac >>
     `runtime_constant_expr mods e` by
       (qpat_assum `!e. MEM e _ ==> runtime_constant_expr mods e`
         (drule_then ACCEPT_TAC)) >>
     `int_calls_expr e = []` by drule_then ACCEPT_TAC groupedDefaultPreTheory.runtime_constant_expr_no_internal_calls >>
     qspecl_then [`mods`,`exps`] (map_every assume_tac o CONJUNCTS)
       bodySimFullMainTheory.body_sim_full_mutual_mods >>
     qpat_assum `!cx e. _ ==> body_expr_full_ok_mods mods exps cx e` irule >>
     qpat_assum `int_calls_expr e = []` (fn eq => simp[NoAsms, eq]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ctx_inst_ids_distinct unit.cu_context` by
    (drule lowering_context_ok_static_integrity >> strip_tac >> first_assum ACCEPT_TAC) >>
  `MEM fn unit.cu_context.ctx_functions /\ MEM shfn shadow_unit.cu_context.ctx_functions` by
    (conj_tac >> drule_then ACCEPT_TAC lookup_function_MEM) >>
  `!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (drule lowering_context_ok_bridge >> strip_tac >>
     qpat_assum `EVERY (\f. ALL_DISTINCT (fn_labels f) /\ _) _`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `fn` mp_tac) >>
     qpat_assum `MEM fn unit.cu_context.ctx_functions` (fn member => simp[NoAsms, member]) >>
     strip_tac >> rpt strip_tac >>
     `venomInst$lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
       (irule venomExecPropsTheory.MEM_lookup_block >>
        conj_tac >- (qpat_assum `ALL_DISTINCT (fn_labels fn)`
          (ACCEPT_TAC o REWRITE_RULE [fn_labels_def])) >>
        simp[NoAsms] >> first_assum ACCEPT_TAC) >>
     qpat_assum `!label bb. venomInst$lookup_block label fn.fn_blocks = SOME bb ==> _`
       (drule_then ACCEPT_TAC)) >>
  qabbrev_tac `values = DROP (LENGTH args - LENGTH ds) tx.args` >>
  qabbrev_tac `kept =
    MAP (\((aid,p,base,tv),v). (aid,p,base,tv,v)) (ZIP (TAKE k slots,values))` >>
  `LENGTH (TAKE k slots) = LENGTH values` by
    (qpat_assum `LIST_REL _ (TAKE k slots) values`
       (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     simp[NoAsms]) >>
  `MAP FST kept = MAP FST (TAKE k slots)` by
    (qpat_assum `LENGTH (TAKE k slots) = LENGTH values` (fn len =>
       simp[NoAsms, Abbr `kept`, Once LIST_EQ_REWRITE, LENGTH_ZIP, EL_MAP, EL_ZIP, len]) >>
     rpt strip_tac >> qabbrev_tac `slot = EL x (TAKE k slots)` >>
     PairCases_on `slot` >> simp[NoAsms]) >>
  `ALL_DISTINCT (MAP FST (DROP k slots) ++ MAP FST kept)` by
    (`ALL_DISTINCT (MAP FST (TAKE k slots) ++ MAP FST (DROP k slots))` by
       (pure_once_rewrite_tac [GSYM MAP_APPEND] >>
        pure_rewrite_tac [TAKE_DROP] >> first_assum ACCEPT_TAC) >>
     qpat_assum `ALL_DISTINCT (_ ++ _)` mp_tac >>
     qpat_assum `MAP FST kept = _` (fn fst_kept => simp[NoAsms, fst_kept, ALL_DISTINCT_APPEND']) >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[pred_setTheory.DISJOINT_SYM]) >>
  `EVERY (\(aid,p,base,tv,v). aid < supplied_end.cs_next_id /\ not_fresh_at supplied_end p /\
      base < dimword (:256) /\ FLOOKUP supplied.vs_allocas aid = SOME (base,type_memory_size tv) /\
      lookup_var p supplied = SOME (n2w base) /\ ptr_covers Gsupplied tnsupplied p supplied (type_memory_size tv) /\
      value_has_type tv v /\
      (!mem. mem_agree_outside tnsupplied.t_mem supplied.vs_memory mem ==> val_in_memory tv v base mem))
      kept` by
    (qpat_assum `LIST_REL _ (TAKE k slots) values` mp_tac >>
     simp[NoAsms, Abbr `kept`, LIST_REL_EVERY_ZIP, EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
     disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  `gas_shadow_function fn shfn` by
    (qpat_assum `gas_shadow_context unit.cu_context shadow_unit.cu_context`
       (strip_assume_tac o REWRITE_RULE [gas_shadow_context_def]) >>
     qspecl_then [`unit.cu_context.ctx_functions`,`shadow_unit.cu_context.ctx_functions`,
                  `"__entry"`] mp_tac gas_shadow_lookup_function >>
     qpat_assum `venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn`
       (fn entry =>
         qpat_assum `venomInst$lookup_function "__entry" shadow_unit.cu_context.ctx_functions = SOME shfn`
           (fn shadow_entry => simp[NoAsms, entry, shadow_entry])) >>
     disch_then irule >> first_assum ACCEPT_TAC) >>
  `~common.ec_env.ce_is_ctor /\ common.ec_env.ce_imm_alloca = NONE /\
    common.ec_env.ce_return_pc = NONE /\ common.ec_env.ce_return_buf = NONE` by
    (qpat_assum `Abbrev (default_env = _)` (fn ce =>
      map_every (fn property => qpat_assum property
        (assume_tac o SIMP_RULE (srw_ss()) [REWRITE_RULE [markerTheory.Abbrev_def] ce]))
        [`~default_env.ce_is_ctor`, `default_env.ce_imm_alloca = NONE`,
         `default_env.ce_return_pc = NONE`, `default_env.ce_return_buf = NONE`]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca unit.cu_context ==> allocas_below_fmp supplied` by
    qpat_assum `!H. stmt_state_rel H unit.cu_context fn default_env cx seed supplied`
      (qspec_then `ARB` (ACCEPT_TAC o MATCH_MP
        (SPEC_ALL bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp))) >>
  qpat_assum `compile_init_kwargs common.ec_env (DROP k vars) _ 0 _
    supplied_end = ((),keyword_end)`
    (fn compile =>
      qpat_assum `check_contract F am.layouts tx.target mods = SOME art`
        (fn checked =>
      let
        fun equation head tm =
          find_term (fn t => is_eq t andalso same_const
             (fst (strip_comb (lhs t))) head) (lhand tm)
        val selected = PART_MATCH (equation ``compile_init_kwargs``)
          linkedGroupedKeywordInitializeTheory.grouped_omitted_initializers_mods
          (concl compile)
        val selected = PART_MATCH (equation ``vyperTypeContract$check_contract``)
          selected (concl checked)
      in
        mp_tac (Q.INST [`mods` |-> `mods`, `exps` |-> `exps`,
          `ctx` |-> `unit.cu_context`, `shadow_ctx` |-> `shadow_unit.cu_context`,
          `src` |-> `src`, `tops` |-> `selected_tops`, `env` |-> `initializer_env`,
          `cx` |-> `cx`, `es` |-> `seed`, `st0` |-> `initial_state am []`,
          `DF` |-> `\H. cx_dead H cx`, `PG` |-> `[]`,
          `fn` |-> `fn`, `shfn` |-> `shfn`, `sha` |-> `shadow_supplied_end`,
          `shb` |-> `shadow_keyword_end`, `slots` |-> `DROP k slots`, `kept` |-> `kept`,
          `s` |-> `supplied`, `G` |-> `Gsupplied`, `tn` |-> `tnsupplied`] selected)
      end)) >>
  qpat_assum `Abbrev (default_env = _)` (fn env =>
    PURE_ONCE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] env)]) >>
  impl_tac
  >- (BETA_TAC >> rpt conj_tac
      >- qpat_assum `compile_init_kwargs common.ec_env (DROP k vars) _ 0 _
            supplied_end = ((),keyword_end)` (MATCH_ACCEPT_TAC o BETA_RULE)
      >- qpat_assum `compile_init_kwargs (gas_shadow_env T common.ec_env) _ _ 0 _
            shadow_supplied_end = ((),shadow_keyword_end)` (MATCH_ACCEPT_TAC o BETA_RULE) >>
      TRY (first_assum (MATCH_ACCEPT_TAC o BETA_RULE)) >>
      TRY
        (qpat_assum `EVERY (\(aid,p,base,tv,v). _ /\ _) kept` (fn kept =>
           ACCEPT_TAC (SIMP_RULE (srw_ss()) [EVERY_MEM, FORALL_PROD, CONJ_ASSOC] kept))) >>
      TRY
        (qpat_assum `EVERY (\(aid,p,base,tv,v). _ /\ _) kept` (fn kept =>
           CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
           mp_tac kept >> simp[NoAsms, EVERY_MEM, FORALL_PROD, CONJ_ASSOC])) >>
      (fn goal as (_,conclusion) =>
         (print ("OMITTED INPUT: " ^ term_to_string conclusion ^ "\n"); ALL_TAC goal)) >>
      NO_TAC) >>
  disch_then (mk_asm "omitted_execution") >>
  suspend "linked_grouped_default_omitted_replay"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_omitted_replay]:
  `LENGTH tx.args = LENGTH args - LENGTH dflts + k` by
    (`LENGTH tx.args = LENGTH prefix` by
       (qpat_assum `calldata_decode_args cd decoded_tys 0 = SOME tx.args`
          (mp_tac o MATCH_MP (SPEC_ALL calldata_decode_args_length)) >>
        qpat_assum `OPT_MMAP _ tys = SOME decoded_tys`
          (mp_tac o MATCH_MP (SPEC_ALL OPT_MMAP_LENGTH)) >>
        qpat_assum `tys = MAP SND prefix` (fn types => simp[NoAsms, types])) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`LENGTH tx.args = LENGTH prefix`, `LENGTH ds = LENGTH dflts`,
        `LENGTH ds <= LENGTH args`, `k <= LENGTH dflts`] >>
     qpat_assum `prefix = TAKE (LENGTH args - LENGTH dflts + k) args`
       (fn pref => simp[NoAsms, pref, LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF]) >>
     decide_tac) >>
  `LENGTH tx.args <= LENGTH args /\ LENGTH args - LENGTH tx.args <= LENGTH dflts /\
    LENGTH dflts - (LENGTH args - LENGTH tx.args) = k` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`LENGTH tx.args = LENGTH args - LENGTH dflts + k`, `LENGTH ds = LENGTH dflts`,
        `LENGTH ds <= LENGTH args`, `k <= LENGTH dflts`] >> decide_tac) >>
  `EVERY (runtime_constant_expr mods) dflts /\ well_typed_exprs initializer_env dflts` by
    (`External <> Deploy` by simp[NoAsms] >>
     drule_all vyperTypeContractContextTheory.check_contract_runtime_function_body_MEM >>
     qpat_assum `Abbrev (initializer_env = _)` (fn ien =>
       simp_tac bool_ss [check_function_body_def, LET_THM, defaults_env_function_entry_env,
         GSYM (REWRITE_RULE [markerTheory.Abbrev_def] ien)]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `MAP (\(_,_,_,e). e) (DROP k vars) =
     subst_consts_exprs_mods (consts_env_mods mods) (DROP k dflts)` by
    (qpat_assum `MAP _ (DROP k vars) = DROP k ds` SUBST1_TAC >>
     qpat_assum `ds = subst_consts_exprs_mods _ _` SUBST1_TAC >>
     `!es. subst_consts_exprs_mods (consts_env_mods mods) es =
       MAP (subst_consts_expr_mods (consts_env_mods mods)) es` by
       (POP_ASSUM_LIST (K ALL_TAC) >> Induct >> simp[subst_consts_expr_mods_def]) >>
     pop_assum (fn eq => simp[NoAsms, eq, MAP_DROP])) >>
  `!gs. eval_external_defaults cx (DROP k dflts) (seed with gas_obs := gs) =
     eval_exprs cx (MAP (\(_,_,_,e). e) (DROP k vars)) (seed with gas_obs := gs)` by
    (gen_tac >>
     `eval_external_defaults cx
        (subst_consts_exprs_mods (consts_env_mods mods) (DROP k dflts)) (seed with gas_obs := gs) =
      eval_external_defaults cx (DROP k dflts) (seed with gas_obs := gs)` by
       (qpat_assum `body_const_cells_agree_mods mods cx initializer_env seed`
          (qx_choosel_then [`roots`,`cell_art`,`imms`] (map_every assume_tac o CONJUNCTS) o
           REWRITE_RULE [body_const_cells_agree_mods_def]) >>
        irule (cj 2 linkedRuntimeDefaultReplayTheory.const_subst_runtime_default_exprs_mods) >>
        qexistsl_tac [`cell_art`,`initializer_env`,`mods`,`roots`] >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        TRY (irule EVERY_DROP >> first_assum ACCEPT_TAC) >>
        TRY (irule vyperTypeEvalProofsTheory.well_typed_exprs_DROP >> first_assum ACCEPT_TAC) >>
        qpat_assum `const_cells_agree roots seed`
           (mp_tac o PURE_REWRITE_RULE [const_cells_agree_def]) >>
        simp[NoAsms,const_cells_agree_def]) >>
     qpat_assum `eval_external_defaults cx (subst_consts_exprs_mods _ _) _ = _`
       (fn replay => PURE_ONCE_REWRITE_TAC [GSYM replay]) >>
     qpat_assum `MAP _ (DROP k vars) = subst_consts_exprs_mods _ _`
       (fn eq => PURE_REWRITE_TAC [GSYM eq]) >>
     namedCases_on `eval_exprs cx (MAP (\(_,_,_,e). e) (DROP k vars))
                          (seed with gas_obs := gs)` ["res endpoint"] >>
     `endpoint with gas_obs := [] = (seed with gas_obs := gs) with gas_obs := []` by
       drule_all_then ACCEPT_TAC linkedDefaultSourceFrameTheory.grouped_checked_default_source_frame_mods >>
     `endpoint.scopes = [FEMPTY]` by
       (pop_assum (mp_tac o Q.AP_TERM `\s:evaluation_state. s.scopes`) >>
        qpat_assum `seed.scopes = [FEMPTY]` (fn sc => simp[NoAsms,sc])) >>
     `(seed with gas_obs := gs) with scopes := [FEMPTY] = seed with gas_obs := gs` by
       (qpat_assum `seed.scopes = [FEMPTY]` (fn sc =>
          simp[NoAsms,sc,evaluation_state_component_equality])) >>
     `endpoint with scopes := [FEMPTY] = endpoint` by
       (qpat_assum `endpoint.scopes = [FEMPTY]` (fn sc =>
          simp[NoAsms,sc,evaluation_state_component_equality])) >>
     PURE_REWRITE_TAC [eval_external_defaults_run, LET_THM] >>
     qpat_assum `(seed with gas_obs := gs) with scopes := [FEMPTY] = _`
       (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `eval_exprs cx (MAP _ (DROP k vars)) (seed with gas_obs := gs) = _`
       (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `seed.scopes = [FEMPTY]` (fn sc =>
       qpat_assum `endpoint with scopes := [FEMPTY] = endpoint`
         (fn ep => simp[NoAsms,sc,ep]))) >>
  `!gs. (SND (eval_exprs cx (MAP (\(_,_,_,e). e) (DROP k vars))
        (seed with gas_obs := gs))).storage_trace = seed.storage_trace` by
    (gen_tac >>
     namedCases_on `eval_exprs cx (MAP (\(_,_,_,e). e) (DROP k vars))
                          (seed with gas_obs := gs)` ["res endpoint"] >>
     `endpoint with gas_obs := [] = (seed with gas_obs := gs) with gas_obs := []` by
       drule_all_then ACCEPT_TAC linkedDefaultSourceFrameTheory.grouped_checked_default_source_frame_mods >>
     pop_assum (mp_tac o Q.AP_TERM `\s:evaluation_state. s.storage_trace`) >>
     simp[NoAsms]) >>
  asm_x "omitted_execution"
    (qx_choose_then `init_marks` (DISJ_CASES_THEN2 strip_assume_tac
      (DISJ_CASES_THEN2 (qx_choosel_then [`init_res`,`init_ee`,`init_result`,`Ginit`,`tninit`]
          (map_every assume_tac o CONJUNCTS)) strip_assume_tac)) o
       BETA_RULE o REWRITE_RULE [gasOutcomeFullModsTheory.gas_outcome_full_mods_def])
  >- (qpat_assum `gas_bad_storage_at _ _ _ _ _ _`
        (qspec_then `[]:bytes32 list` mp_tac o REWRITE_RULE [gasStorageTheory.gas_bad_storage_at_def]) >>
      qpat_assum `!gs. (SND (eval_exprs cx _ _)).storage_trace = seed.storage_trace`
        (qspec_then `gas_explicit init_marks supplied.vs_gas_readings ++ []` (fn tr =>
          qpat_assum `storage_trace_domain cx (initial_state am []) seed.storage_trace`
            (fn dom => PURE_REWRITE_TAC [tr,dom]))) >> simp[NoAsms])
  >- suspend "linked_grouped_default_omitted_run" >>
  drule_then (map_every assume_tac o CONJUNCTS)
    gasExemptCertModsTheory.gas_exempt_cert_execution_mods >>
  `eval_exprs cx (MAP (\(_,_,_,e). e) (DROP k vars))
      (seed with gas_obs := gas_explicit init_marks supplied.vs_gas_readings) =
    (INR (Error err), ee with gas_obs := [])` by
    (qpat_assum `!tail. ignore_bind (eval_exprs cx _) _ _ = _`
       (qspec_then `[]:bytes32 list`
         (mp_tac o MATCH_MP vyperStatePreservationTheory.ignore_bind_split o
          REWRITE_RULE [APPEND_NIL])) >>
     disch_then (DISJ_CASES_THEN strip_assume_tac)
     >- (qpat_assum `return () _ = _` mp_tac >> simp[NoAsms,return_def]) >>
     qpat_assum `INR (Error err) = INR _` mp_tac >>
     qpat_assum `eval_exprs cx _ _ = (INR _,_)` mp_tac >>
     simp[NoAsms, pairTheory.ELIM_UNCURRY] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  drule_all_then (fn no_exempt =>
    qpat_assum `unspecified_behaviour_exempt_mods mods err`
      (CONTR_TAC o MP (NOT_ELIM no_exempt)))
    linkedDefaultErrorTheory.runtime_constant_defaults_no_exempt_mods
QED

(* The supplied decoder is a suffix start, not a new block boundary. *)
val linked_default_cut_layout_tac =
  `cs_extends opened init` by
    (qpat_assum `compile_entry_checks _ _ opened = ((),init)` (fn eq =>
       mp_tac (PART_MATCH (rand o rand) compile_entry_checks_ci_mono (lhs (concl eq))) >>
       simp[NoAsms, eq, ci_mono_def])) >>
  `ci_mono keyword_end sd` by
    (`ci_mono keyword_end initialised` by
       (qpat_assum `emit_inst JMP _ [] keyword_end = ((),initialised)` (fn eq =>
          mp_tac (PART_MATCH (rand o rand) ci_mono_emit_inst (lhs (concl eq))) >>
          simp[NoAsms, eq])) >>
     irule ci_mono_trans >> qexists_tac `initialised` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule ci_mono_trans >> qexists_tac `dispatch_end` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `state_insts sf = []` by
    (`sf.cs_blocks = []` by
       (qpat_assum `fresh_label "fallback" _ = (fall_lbl,sf)`
          (mp_tac o Q.AP_TERM `\p. (SND p).cs_blocks`) >>
        simp[NoAsms, fresh_label_def, initial_compile_state_def]) >>
     qpat_assum `sf.cs_blocks = []` (fn blocks =>
       qpat_assum `sf.cs_current_insts = []` (fn insts =>
         simp[NoAsms, state_insts_def, all_blocks_def, blocks, insts]))) >>
  `ALL_DISTINCT (fn_labels fn)` by
    (`MEM fn unit.cu_context.ctx_functions` by
       (qpat_assum `venomInst$lookup_function "__entry" _ = SOME fn`
          (ACCEPT_TAC o MATCH_MP lookup_function_MEM)) >>
     qpat_assum `lowering_context_ok unit.cu_context`
       (strip_assume_tac o MATCH_MP lowering_context_ok_bridge) >>
     qpat_assum `EVERY _ unit.cu_context.ctx_functions`
       (qspec_then `fn` mp_tac o SIMP_RULE bool_ss [EVERY_MEM]) >>
     qpat_assum `MEM fn unit.cu_context.ctx_functions`
       (fn member => simp[NoAsms, member])) >>
  `fragFuel$no_phi_fn fn` by
    (simp[NoAsms, fragFuelTheory.no_phi_fn_def, EVERY_MEM] >>
     qx_gen_tac `code_block` >> strip_tac >>
     qpat_assum `!label bb. lookup_block label fn.fn_blocks = SOME bb ==> _`
       (qspecl_then [`code_block.bb_label`,`code_block`] irule) >>
     match_mp_tac venomExecPropsTheory.MEM_lookup_block >>
     qpat_assum `ALL_DISTINCT (fn_labels fn)` (fn distinct =>
       qpat_assum `MEM code_block fn.fn_blocks` (fn member =>
         simp[NoAsms, GSYM fn_labels_def, distinct, member]))) >>
  `acyclic_struct_metadata common.ec_env.ce_struct_fields` by
    (qpat_assum `contract_inv mods exps unit.cu_context default_env cx`
       (mp_tac o MATCH_MP contract_inv_acyclic_struct_metadata) >>
     simp[NoAsms, Abbr `default_env`]);

val linked_default_cut_packages_tac =
  let open loweringShapePropsTheory in
  `EVERY (external_group_shape_mode_ok F) groups` by
    (simp[NoAsms, Abbr `groups`, EVERY_MAP] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[EVERY_MEM] >> qx_gen_tac `decl` >>
     disch_tac >> pop_assum kall_tac >>
     `external_fn_shape_mode_ok F (set_external_package_target rpolicy.rpol_target
        (package_external_fn_unit mods T (K global_nonreentrant_slot) decl))` by
       (PairCases_on `decl` >>
        qabbrev_tac `cenv = build_compile_env_unit mods decl0 External decl1 decl4 decl5 decl7 decl8 T` >>
        `cenv_static_mode_ok F cenv /\ (External <> Internal ==> cenv.ce_return_pc = NONE)` by
          (unabbrev_all_tac >> match_mp_tac build_compile_env_unit_static_mode >>
           simp[expr_shape_root_mode_dynamic, EVERY_MEM, dynamic_raw_expr_shape]) >>
        Cases_on `decl7 = NoneT` >>
        gvs[package_external_fn_unit_def, set_external_package_target_def,
            external_fn_shape_mode_ok_def, update_cenv_ret_abi_def,
            update_cenv_nonreentrant_def, cenv_static_mode_ok_def,
            expr_shape_root_mode_dynamic, dynamic_raw_stmt_shape] >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     PairCases_on `decl` >>
     simp[package_external_group_unit_def] >> IF_CASES_TAC >> simp[]
     >- simp[external_group_shape_mode_ok_def, compute_selector_def, IS_PREFIX_APPEND] >>
     qmatch_asmsub_abbrev_tac `external_fn_shape_mode_ok F pkg` >> PairCases_on `pkg` >>
     fs[external_fn_shape_mode_ok_def, external_group_shape_mode_ok_def,
        external_common_shape_mode_ok_def, external_common_label_def,
        jump_label_ok_def, IS_PREFIX_APPEND] >>
     conj_tac
     >- simp[EVERY_MAP, EVERY_MEM, FORALL_PROD, external_prefix_label_def,
             compute_selector_def, IS_PREFIX_APPEND] >>
     simp[EVERY_MAP, EVERY_MEM, FORALL_PROD,
          expr_shape_root_mode_dynamic, dynamic_raw_expr_shape])
  end;

val linked_default_cut_shape_tac =
  let open loweringShapePropsTheory in
  `shape_state sd` by
    (`shape_state sf /\ compiler_label fall_lbl /\ label_sfx "fallback" fall_lbl` by
       (mp_tac (Q.SPECL [`F`,`jump_label_ok`,`\st. T`,`"fallback"`]
                  loweringShapeRulesTheory.shape_step_fresh_label_sfx) >>
        simp[NoAsms, shape_stable_def, shape_step_def] >>
        disch_then (qspecl_then [`initial_compile_state "__entry"`,`fall_lbl`,`sf`] mp_tac) >>
        qpat_assum `fresh_label "fallback" _ = (fall_lbl,sf)` (fn eq =>
          simp[NoAsms, eq, shape_state_initial_compile_state])) >>
     `jump_label_ok fall_lbl` by
       (qpat_assum `compiler_label fall_lbl` (fn label => simp[NoAsms, jump_label_ok_def, label])) >>
     `~label_sfx "dispatch" fall_lbl` by
       (strip_tac >> mp_tac (Q.INST [`s1` |-> `"fallback"`,`s2` |-> `"dispatch"`,
          `l1` |-> `fall_lbl`,`l2` |-> `fall_lbl`] loweringShapeRulesTheory.label_sfx_distinct) >>
        simp[NoAsms] >> conj_tac >> first_assum ACCEPT_TAC) >>
     mp_tac (Q.INST [`static` |-> `F`] compile_group_dispatch_linear_shape_mode) >>
     disch_then (qspecl_then [`groups`,`fall_lbl`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     simp[NoAsms, shape_mode_step_def] >>
     disch_then (qspecl_then [`sf`,`jobs`,`sd`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     strip_tac >> first_assum ACCEPT_TAC)
  end;

val linked_default_cut_names_tac =
  qabbrev_tac `unknown_default_root = \z. case z of
    TopLevelName _ (owner,id) => ~(declared_constant mods owner id \/ declared_immutable mods owner id)
  | _ => F` >>
  `!e. runtime_constant_expr mods e ==> ~supported_expr_exists unknown_default_root e` by
    (qpat_assum `Abbrev (unknown_default_root = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     `(!p e. p = unknown_default_root /\ runtime_constant_expr mods e ==>
             ~supported_expr_exists p e) /\
      (!p t. p = unknown_default_root /\ F ==> ~supported_target_exists p t) /\
      (!p es. p = unknown_default_root /\ EVERY (runtime_constant_expr mods) es ==>
             ~supported_exprs_exists p es) /\
      (!p opt. p = unknown_default_root /\ F ==> ~supported_opt_exists p opt) /\
      (!p fs. p = unknown_default_root /\ EVERY (runtime_constant_expr mods) (MAP SND fs) ==>
             ~supported_fields_exists p fs)` by
       (ho_match_mp_tac supportedExprTraverseTheory.supported_expr_exists_ind >>
        (rw[runtime_constant_expr_def, supportedExprTraverseTheory.supported_expr_exists_def,
            Abbr `unknown_default_root`, FORALL_PROD] >-
          (qpat_assum `runtime_constant_expr mods (TopLevelName _ _)` mp_tac >>
           rename1 `runtime_constant_expr _ (TopLevelName _ read_key) ==> _` >>
           PairCases_on `read_key` >> fs[runtime_constant_expr_def])) >>
        fs[EVERY_MEM] >> metis_tac[whitelistCheckerConstsTheory.constant_expr_runtime_constant]) >>
     gen_tac >> disch_tac >>
     qpat_assum `!p e. p = unknown_default_root /\ runtime_constant_expr mods e ==> _` irule >> simp[]) >>
  `!owner id. declared_constant mods owner id ==> cx_const_name_mods mods (owner,id)` by
    (`!ts acc id vis e ty slot. MEM (VariableDecl vis (Constant e) id ty slot) ts ==>
        MEM id (MAP FST (module_consts_env ts acc))` by
       (POP_ASSUM_LIST (K ALL_TAC) >>
        recInduct constSubstTheory.module_consts_env_ind >> simp[constSubstTheory.module_consts_env_def] >>
        rpt strip_tac >> gvs[] >>
        qmatch_goalsub_abbrev_tac `module_consts_env rest acc'` >>
        qspecl_then [`rest`,`acc'`] strip_assume_tac constSubstTheory.module_consts_env_acc_prefix >>
        simp[Abbr `acc'`] >> first_x_assum (drule_then mp_tac) >> simp[]) >>
     `ALL_DISTINCT (MAP FST mods)` by
       (qpat_assum `contract_inv mods exps unit.cu_context default_env cx`
          (mp_tac o REWRITE_RULE [contract_inv_def]) >> strip_tac >> first_assum ACCEPT_TAC) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`ALL_DISTINCT (MAP FST mods)`, `!ts acc id vis e ty slot. _ ==> MEM id _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[declared_constant_def, cx_const_name_mods_def] >> metis_tac[ALOOKUP_ALL_DISTINCT_MEM]);

val linked_default_cut_immutable_access_tac =
  `!read_key. MEM (ReadAcc (StateRef read_key)) (accesses_exprs dflts) ==>
    ((?ts. mods = [(NONE,ts)]) \/ linked_state_ref_allocated am.layouts tx.target mods read_key)` by
    (gen_tac >> disch_tac >>
     qpat_assum `check_linked_state_ownership _ _ _ _` mp_tac >>
     pure_rewrite_tac[check_linked_state_ownership_def] >>
     disch_then (DISJ_CASES_THEN2 mp_tac assume_tac)
     >- (Cases_on `mods` >> simp[NoAsms] >> PairCases_on `h` >>
         Cases_on `h0` >> Cases_on `t` >> simp[NoAsms]) >>
     `MEM (src,selected_tops) mods` by (irule ALOOKUP_MEM >> first_assum ACCEPT_TAC) >>
     qpat_assum `EVERY _ mods` (fn own =>
       qpat_assum `MEM (src,selected_tops) mods`
         (mp_tac o MATCH_MP (SIMP_RULE bool_ss [EVERY_MEM] own))) >>
     simp[NoAsms, Once EVERY_MEM] >>
     qpat_assum `MEM (FunctionDecl External mut nr selected_raw tx.function_name args dflts ret selected_body) selected_tops`
       (fn decl => disch_then (mp_tac o C MATCH_MP decl)) >>
     qpat_assum `MEM (src,tx.function_name) (linked_live_functions mods exps)` (fn live => simp[NoAsms, live]) >>
     strip_tac >> disj2_tac >>
     qpat_assum `!a. MEM a (accesses_exprs dflts) \/ MEM a (accesses_stmts selected_body) ==> _`
       (qspec_then `ReadAcc (StateRef read_key)` mp_tac) >>
     qpat_assum `MEM (ReadAcc (StateRef read_key)) (accesses_exprs dflts)`
       (fn read => simp[NoAsms, MEM_APPEND, read])) >>
  `immutable_section_layout_mods mods common.ec_env` by
    (`default_env.ce_module_vars = common.ec_env.ce_module_vars` by
       simp[NoAsms, Abbr `default_env`] >>
     qpat_assum `contract_inv mods exps unit.cu_context default_env cx`
       (mp_tac o MATCH_MP contract_inv_immutable_section_layout) >>
     qpat_assum `default_env.ce_module_vars = common.ec_env.ce_module_vars`
       (fn fields => PURE_REWRITE_TAC [immutable_section_layout_mods_def, fields]) >>
     DISCH_TAC >> first_assum ACCEPT_TAC) >>
  `!owner id. declared_immutable mods owner id /\
      MEM (ReadAcc (StateRef (owner,id))) (accesses_exprs ds) ==>
      ?i. FLOOKUP common.ec_env.ce_module_vars (owner,id) = SOME (ImmutableLoc i)` by
    (simp[NoAsms, declared_immutable_def, PULL_EXISTS] >> rpt strip_tac >>
     rename1 `MEM (VariableDecl vis Immutable id ty ini) itops` >>
     `ALL_DISTINCT (MAP FST mods)` by
       (qpat_assum `contract_inv mods exps unit.cu_context default_env cx`
          (mp_tac o REWRITE_RULE [contract_inv_def]) >> strip_tac >> first_assum ACCEPT_TAC) >>
     `ALOOKUP mods owner = SOME itops` by
       (irule ALOOKUP_ALL_DISTINCT_MEM >> conj_tac >> first_assum ACCEPT_TAC) >>
     `MEM (ReadAcc (StateRef (owner,id))) (accesses_exprs dflts)` by
       (qpat_assum `!key rhs. ALOOKUP (consts_env_mods mods) key = SOME rhs ==> _`
          (strip_assume_tac o MATCH_MP linkedConstAccessSubsetTheory.linked_subst_accesses_subset) >>
        qpat_assum `!es a. MEM a (accesses_exprs (subst_consts_exprs_mods _ es)) ==> _` irule >>
        qpat_assum `ds = subst_consts_exprs_mods _ dflts`
          (fn eq => PURE_REWRITE_TAC [GSYM eq]) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!read_key. MEM (ReadAcc (StateRef read_key)) (accesses_exprs dflts) ==> _`
       (drule_then strip_assume_tac) >>
     irule (INST_TYPE [``:'a`` |-> ``:160 word``, ``:'b`` |-> ``:num``]
       linkedOwnedImmutableLocationTheory.linked_owned_immutable_location) >>
     qexistsl_tac [`tx.target`,`am.layouts`,`mods`,`ini`,`itops`,`ty`,`vis`] >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       disj2_tac >> first_assum ACCEPT_TAC,
       disj1_tac >>
       map_every (fn pat => qpat_assum pat mp_tac)
         [`ALOOKUP mods owner = SOME itops`, `mods = [(NONE,_)]`] >>
       simp[NoAsms, AllCaseEqs()]]);

val linked_default_cut_immutable_root_tac =
  qabbrev_tac `bad_immutable_root = \z. case z of
    TopLevelName _ (owner,id) => declared_immutable mods owner id /\
      ~(?i. FLOOKUP common.ec_env.ce_module_vars (owner,id) = SOME (ImmutableLoc i))
  | _ => F` >>
  `!p P. (!e. p e ==> ?key. P key /\ MEM (ReadAcc (StateRef key)) (accesses_expr e)) ==>
    (!es. supported_exprs_exists p es ==>
      ?key. P key /\ MEM (ReadAcc (StateRef key)) (accesses_exprs es))` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >> strip_tac >>
     `(!e. supported_expr_exists p e ==>
           ?key. P key /\ MEM (ReadAcc (StateRef key)) (accesses_expr e)) /\
      (!t. supported_target_exists p t ==>
           ?key. P key /\ MEM (ReadAcc (StateRef key)) (accesses_target t)) /\
      (!es. supported_exprs_exists p es ==>
           ?key. P key /\ MEM (ReadAcc (StateRef key)) (accesses_exprs es)) /\
      (!opt. supported_opt_exists p opt ==>
           ?key. P key /\ MEM (ReadAcc (StateRef key)) (accesses_opt opt)) /\
      (!fs. supported_fields_exists p fs ==>
           ?key. P key /\ MEM (ReadAcc (StateRef key)) (accesses_named_exprs fs))` suffices_by
       (strip_tac >> first_assum ACCEPT_TAC) >>
     ho_match_mp_tac accesses_expr_ind >>
     simp[supportedExprTraverseTheory.supported_expr_exists_def, accesses_expr_def, MEM_APPEND] >>
     rpt strip_tac >> res_tac >> fs[accesses_expr_def, MEM_APPEND] >> metis_tac[]) >>
  `!z. bad_immutable_root z ==>
       ?key. (\(owner,id). declared_immutable mods owner id /\
                ~(?i. FLOOKUP common.ec_env.ce_module_vars (owner,id) = SOME (ImmutableLoc i))) key /\
         MEM (ReadAcc (StateRef key)) (accesses_expr z)` by
    (Cases >> simp[NoAsms, Abbr `bad_immutable_root`] >>
     PairCases_on `p` >> simp[NoAsms, accesses_expr_def, pairTheory.ELIM_UNCURRY]) >>
  `~supported_exprs_exists bad_immutable_root ds` by
    (strip_tac >>
     qpat_assum `!p P. (!e. p e ==> _) ==> _` (fn cover =>
       qpat_assum `!z. bad_immutable_root z ==> _`
         (mp_then Any (qspec_then `ds` mp_tac) cover)) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (qx_choose_then `bad_key` strip_assume_tac) >> PairCases_on `bad_key` >>
     qpat_x_assum `(\(owner,id). _) (bad_key0,bad_key1)`
       (mp_tac o CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)) >>
     disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
     qpat_assum `!owner id. declared_immutable mods owner id /\ _ ==> _`
       (qspecl_then [`bad_key0`,`bad_key1`] mp_tac) >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!e. MEM e ds ==> ~supported_expr_exists bad_immutable_root e` by
    (qpat_assum `~supported_exprs_exists bad_immutable_root ds` mp_tac >>
     simp[NoAsms, supportedExprTraverseTheory.supported_exprs_exists_every, EXISTS_MEM] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]);

val linked_default_cut_builtin_tac =
  qabbrev_tac `sha_root = \z. case z of Builtin _ Sha256 _ => T | _ => F` >>
  `!e. MEM e ds ==> ~supported_expr_exists sha_root e` by
    (`(!e. no_sha256_expr e <=> ~supported_expr_exists sha_root e) /\
      (!bt. no_sha256_btarget bt <=> ~supported_target_exists sha_root bt) /\
      (!xs. no_sha256_exprs xs <=> ~supported_exprs_exists sha_root xs) /\
      (!opt. no_sha256_opt opt <=> ~supported_opt_exists sha_root opt) /\
      (!fs. no_sha256_fields fs <=> ~supported_fields_exists sha_root fs)` by
       (qpat_assum `Abbrev (sha_root = _)` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
        ho_match_mp_tac constSubstTheory.no_sha256_expr_ind >>
        simp[constSubstTheory.no_sha256_expr_def, supportedExprTraverseTheory.supported_expr_exists_def,
             Abbr `sha_root`] >> rpt gen_tac >> CASE_TAC >> simp[]) >>
     qpat_assum `no_sha256_exprs ds` mp_tac >>
     qpat_assum `!xs. no_sha256_exprs xs <=> _` (fn no_sha =>
       simp[NoAsms, no_sha, supportedExprTraverseTheory.supported_exprs_exists_every, EXISTS_MEM]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  qabbrev_tac `arity_root = \z. case z of
    Builtin _ b xs => ~builtin_args_length_ok b (LENGTH xs)
  | TypeBuiltin _ b _ xs => ~type_builtin_args_length_ok b (LENGTH xs)
  | _ => F` >>
  `!e. MEM e ds ==> ~supported_expr_exists arity_root e` by
    (gen_tac >> strip_tac >>
     `well_typed_expr initializer_env e` by
       (irule frame_well_typed_exprs_member >> qexists_tac `ds` >> conj_tac >> first_assum ACCEPT_TAC) >>
     map_every assume_tac (CONJUNCTS runtimeDefaultCompileTheory.well_typed_expr_builtin_args_length) >>
     qpat_assum `!en x. well_typed_expr en x ==> ~supported_expr_exists _ x`
       (qspecl_then [`initializer_env`,`e`] mp_tac) >>
     qpat_assum `well_typed_expr initializer_env e`
       (fn typed => simp[NoAsms, typed, Abbr `arity_root`]));

val linked_default_checked_root = runtimeDefaultRejectSyntaxLib.checked_default_expr;

val linked_default_cut_roots_tac =
  `!z. ^linked_default_checked_root common.ec_env z ==>
    unknown_default_root z \/ bad_immutable_root z \/ const_name_root_mods mods z \/
    sha_root z \/ arity_root z` by
    (qpat_assum `!owner id. declared_constant mods owner id ==> cx_const_name_mods mods (owner,id)` mp_tac >>
     simp[NoAsms, Abbr `unknown_default_root`, Abbr `bad_immutable_root`, Abbr `sha_root`, Abbr `arity_root`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >> Cases >> simp[NoAsms, const_name_root_mods_def]
     >> TRY (rename1 `(bi = Sha256 \/ _) ==> _` >> Cases_on `bi` >> simp[NoAsms] >> NO_TAC) >>
     rename1 `(!offset. FLOOKUP _ key <> SOME (ImmutableLoc offset)) ==> _` >>
     PairCases_on `key` >> simp[NoAsms] >> metis_tac[]);

val linked_default_cut_checked_tac =
    (`EVERY (\e. runtime_constant_expr mods e /\
                  ~supported_expr_exists (^linked_default_checked_root common.ec_env) e) ds` suffices_by
       (qpat_assum `MAP (\(_,_,_,e). e) vars = ds` (SUBST1_TAC o SYM) >>
        simp[NoAsms, EVERY_MAP, combinTheory.o_DEF, ELIM_UNCURRY]) >>
     simp[NoAsms, EVERY_MEM] >> qx_gen_tac `e` >> disch_tac >>
     conj_asm1_tac >-
       (qpat_assum `EVERY (runtime_constant_expr mods) ds` (drule_then ACCEPT_TAC o REWRITE_RULE [EVERY_MEM])) >>
     strip_tac >>
     `supported_expr_exists (\z. unknown_default_root z \/ bad_immutable_root z \/
                                  const_name_root_mods mods z \/ sha_root z \/ arity_root z) e` by
       (irule (cj 1 supportedExprTraverseTheory.supported_expr_exists_mono) >>
        qexists `^linked_default_checked_root common.ec_env` >> BETA_TAC >>
        conj_tac >- (first_assum (ACCEPT_TAC o BETA_RULE) ORELSE first_assum ACCEPT_TAC) >>
        simp[NoAsms] >> first_assum ACCEPT_TAC) >>
     qpat_assum `supported_expr_exists (\z. unknown_default_root z \/ bad_immutable_root z \/
                                  const_name_root_mods mods z \/ sha_root z \/ arity_root z) e` mp_tac >>
     qpat_assum `!e. runtime_constant_expr mods e ==> ~supported_expr_exists unknown_default_root e`
       (drule_then mp_tac) >>
     map_every (fn pat => qpat_assum pat (drule_then mp_tac))
       [`!e. MEM e ds ==> ~supported_expr_exists bad_immutable_root e`,
        `!e. MEM e ds ==> ~supported_expr_exists (const_name_root_mods mods) e`,
        `!e. MEM e ds ==> ~supported_expr_exists sha_root e`,
        `!e. MEM e ds ==> ~supported_expr_exists arity_root e`] >>
     simp[NoAsms, supportedExprTraverseTheory.supported_expr_exists_disj] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[NoAsms]);

val linked_default_cut_dispatch_extends_tac =
  `cs_extends sd se` by
    (irule cs_extends_trans >> qexists_tac `sx` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `compile_external_jobs jobs sd = ((),sx)` (fn eq =>
       qspecl_then [`jobs`,`sd`] mp_tac entryRejectAllocationIdsTheory.compile_external_jobs_ci_mono >>
       simp[NoAsms, eq, ci_mono_def]));

val linked_default_cut_compile_tac =
  drule_all_then mp_tac groupedInternalLabelsTheory.compile_grouped_runtime_entry_layout >>
  qpat_assum `fresh_label "fallback" (initial_compile_state "__entry") = (fall_lbl,sf)`
    (fn eq => simp[NoAsms, eq, PAIR_EQ]) >>
  qpat_assum `compile_group_dispatch_linear groups fall_lbl sf = (jobs,sd)`
    (fn eq => simp[NoAsms, eq, PAIR_EQ]) >>
  qpat_assum `compile_external_jobs jobs sd = ((),sx)`
    (fn eq => simp[NoAsms, eq, PAIR_EQ]) >>
  qpat_assum `new_block fall_lbl sx = (sx.cs_current_bb,sn)`
    (fn eq => simp[NoAsms, eq, PAIR_EQ]) >>
  qpat_assum `_ sn = ((),se)` (fn eq => simp[NoAsms, eq, PAIR_EQ]);

val linked_default_cut_labels_tac =
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks se))` by
    (
     qpat_assum `compile_generate_grouped_runtime groups [] fall (initial_compile_state "__entry") = ((),se)`
       (fn actual => qpat_assum `venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn`
         (mp_then Any (drule_all_then (strip_assume_tac o SIMP_RULE bool_ss [actual, PAIR_EQ]))
           entryRejectCodeTheory.run_grouped_lowering_retained_entry_prefix)) >>
     qpat_assum `fn.fn_blocks = all_blocks se ++ _` (fn blocks =>
       qpat_assum `ALL_DISTINCT (fn_labels fn)` mp_tac >>
       simp[NoAsms, fn_labels_def, blocks, MAP_APPEND, ALL_DISTINCT_APPEND]));

val linked_default_row22_cut_facts = groupedRejectCutLib.row22_cut_facts;

val linked_default_cut_row22_tac =
  BETA_TAC >> rpt gen_tac >> disch_tac >>
  `sd.cs_next_id <= common_entry.cs_next_id /\ sd.cs_next_var <= common_entry.cs_next_var` by
    (qpat_assum `ci_mono sd common_entry` mp_tac >> simp[NoAsms, ci_mono_def]) >>
  `^linked_default_row22_cut_facts unit.cu_context fn keyword_end decode_start common_entry` by
    (BETA_TAC >>
     let
       fun use pat k th = qpat_assum pat (mp_then Any k th)
     in
       (use `selected_registration_resources unit.cu_context fn ARB 0 init decode_start` o
        use `compile_init_kwargs common.ec_env vars off k (Lit 0w) init = ((),keyword_end)` o
        use `compile_init_kwargs common.ec_env vars off k (Lit 0w) init = ((),keyword_end)` o
        use `compile_entry_checks (min_calldata_size common.ec_env prefix 0) common.ec_payable opened = ((),init)` o
        use `compile_group_dispatch_linear groups fall_lbl sf = (jobs,sd)`)
         irule (BETA_RULE groupedRejectCutObserverTheory.row22_before_cut_certificate_count)
     end >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- (qexists_tac `mods` >> first_assum (ACCEPT_TAC o BETA_RULE)) >>
     qexists_tac `se` >> conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum (ACCEPT_TAC o CONJUNCT2 o BETA_RULE);

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_omitted_run]:
  linked_default_cut_layout_tac >>
  linked_default_cut_dispatch_extends_tac >>
  Q.SUBGOAL_THEN `compiled = se` assume_tac >- linked_default_cut_compile_tac >>
  `compile_generate_grouped_runtime groups [] fall (initial_compile_state "__entry") = ((),se)` by
    (qpat_x_assum `compiled = se` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  linked_default_cut_labels_tac >>
  linked_default_cut_packages_tac >>
  linked_default_cut_shape_tac >>
  linked_default_cut_names_tac >>
  linked_default_cut_immutable_access_tac >>
  linked_default_cut_immutable_root_tac >>
  linked_default_cut_builtin_tac >>
  linked_default_cut_roots_tac >>
  Q.SUBGOAL_THEN `EVERY (\(_,_,_,e). runtime_constant_expr mods e /\
                     ~supported_expr_exists (^linked_default_checked_root common.ec_env) e) vars` assume_tac
  >- linked_default_cut_checked_tac >>
  Q.SUBGOAL_THEN
    `!common_entry. ci_mono sd common_entry ==> !w.
       RTC (\u v. ~at_point keyword_end u /\ ?j. gas_path_edge unit.cu_context fn u j (OK v))
         decode_start w /\ at_point keyword_end w ==>
       fresh_vars_wrt common_entry w /\ w.vs_call_ctx = decode_start.vs_call_ctx /\
       (!id e. FLOOKUP w.vs_allocas id = SOME e ==> id < common_entry.cs_next_id)` assume_tac
  >- linked_default_cut_row22_tac >>
  qpat_assum `!tail. eval_exprs cx _ _ = (init_res,_)`
    (qspec_then `[]:bytes32 list` (assume_tac o PURE_REWRITE_RULE [pairTheory.ELIM_UNCURRY])) >>
  `init_ee with gas_obs := [] = seed` by
    (map_every (fn pat => qpat_assum pat
       (assume_tac o SIMP_RULE bool_ss [pairTheory.ELIM_UNCURRY]))
       [`EVERY (runtime_constant_expr mods) (MAP _ (DROP k vars))`,
        `no_sha256_exprs (MAP _ (DROP k vars))`,
        `eval_exprs cx _ _ = (init_res,_)`] >>
     drule_all_then mp_tac linkedDefaultSourceFrameTheory.grouped_checked_default_source_frame_mods >>
     qpat_assum `seed.gas_obs = []` (fn gas =>
       simp[NoAsms, GSYM gas, evaluation_state_component_equality])) >>
  `!tail. eval_external_defaults cx
      (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts)
      (seed with gas_obs := gas_explicit init_marks vs.vs_gas_readings ++ tail) =
      (init_res,seed with gas_obs := tail)` by
    (gen_tac >>
     map_every (fn pat => qpat_assum pat (fn eq => PURE_REWRITE_TAC [eq]))
       [`LENGTH dflts - (LENGTH args - LENGTH tx.args) = k`,
        `!gs. eval_external_defaults cx (DROP k dflts) _ = _`] >>
     qpat_assum `!tail. eval_exprs cx _ _ = (init_res,_)`
       (qspec_then `tail` mp_tac) >>
     qpat_assum `supplied.vs_gas_readings = vs.vs_gas_readings`
       (fn gas => simp[NoAsms,gas,pairTheory.ELIM_UNCURRY]) >>
     qpat_assum `init_ee with gas_obs := [] = seed` (SUBST1_TAC o SYM) >>
     simp[NoAsms]) >>
  `!H. valid_horizon cx (initial_state am []) H seed.storage_trace ==>
     gas_origin_ptr_path (cx_dead H cx,0,
       gas_explicit_sites unit.cu_context shadow_unit.cu_context,unit.cu_context,fn,[])
       (start,FEMPTY,entry_taint) init_marks (init_result,Ginit,tninit)` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx (initial_state am []) H init_ee.storage_trace` by
       (qpat_assum `init_ee with gas_obs := [] = seed`
          (mp_tac o Q.AP_TERM `\s:evaluation_state. s.storage_trace`) >>
        simp[NoAsms] >> disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     qpat_assum `!H. valid_horizon cx (initial_state am []) H init_ee.storage_trace ==> _`
       (drule_then (CONJUNCTS_THEN2 assume_tac kall_tac)) >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (start,FEMPTY,entry_taint) []
       (OK supplied,Gsupplied,tnsupplied)` (qspecl_then
         [`cx_dead H cx`,`gas_explicit_sites unit.cu_context shadow_unit.cu_context`]
         (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
     simp[NoAsms] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  `!P defaults.
      EVERY (\(aid,p,base,tv,v). P (aid,p,base,tv) v) kept /\
      LIST_REL P (DROP k slots) defaults ==>
      LIST_REL P slots (values ++ defaults)` by
    (rpt gen_tac >> strip_tac >>
     `LIST_REL P (TAKE k slots) values` by
       (qpat_assum `EVERY _ kept` mp_tac >>
        qpat_assum `LENGTH (TAKE k slots) = LENGTH values` (fn len =>
          simp[NoAsms, Abbr `kept`, LIST_REL_EVERY_ZIP, EVERY_MAP,
               EVERY_MEM, FORALL_PROD, len])) >>
     `LIST_REL P (TAKE k slots ++ DROP k slots) (values ++ defaults)` by
       (irule LIST_REL_APPEND_suff >> conj_tac >> first_assum ACCEPT_TAC) >>
     pop_assum (ACCEPT_TAC o PURE_REWRITE_RULE [TAKE_DROP])) >>
  `find_function_module am tx.target tx.function_name = src /\
    get_module_code cx src = SOME selected_tops /\
    lookup_exported_function cx am tx.function_name = SOME (mut,nr,args,dflts,ret,selected_body)` by
    (qpat_assum `Abbrev (cx = _)` (assume_tac o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
     drule_all linkedRuntimeSourceLookupTheory.linked_runtime_source_lookup >>
     qpat_assum `vyperInterpreter$lookup_function src tx.function_name External selected_tops = _`
       (fn lookup => simp[NoAsms,lookup])) >>
  `!gs. send_call_value mut cx
      (initial_state am [FEMPTY] with
       <|outcomes := SOME vs.vs_outcomes; requests := []; gas_obs := gs; storage_trace := []|>) =
      (INL (),seed with gas_obs := gs)` by
    (qpat_assum `send_call_value mut cx
      (initial_state am [FEMPTY] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) = _`
        (mp_tac o MATCH_MP externalEntryBoundTheory.send_call_value_with_gas_obs) >>
     simp[NoAsms, initial_state_def, evaluation_state_accfupds]) >>
  `tx.args = TAKE (LENGTH args - LENGTH ds) tx.args ++ values` by
    (qpat_assum `Abbrev (values = _)` (fn split =>
       simp[NoAsms, REWRITE_RULE [markerTheory.Abbrev_def] split, TAKE_DROP])) >>
  suspend "linked_grouped_default_omitted_apply"
QED

Resume linked_runtime_dispatched_readings_certificate[linked_grouped_default_omitted_apply]:
  cheat
QED

Finalise linked_runtime_dispatched_readings_certificate
