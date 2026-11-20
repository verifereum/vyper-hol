(*
 * The log statement of the full body induction (bodySimFullMain), over the
 * finite-horizon joint judgment: the arguments' joint fragments, the
 * event's memory encoding and the LOG instruction share one origin/
 * memory/pointer witness.
 *
 * TOP-LEVEL:
 *   compile_log_frag_full -- scalar and aggregate events
 *   body_log_aggregate_full -- retained aggregate specialization
 *)
Theory bodyFullLog
Ancestors exprSimAggregateNestedStore[qualified,ignore_grammar]
  bodyFullPreds bodySimFull bodyFullShared gasShadow bodySim exprSimHypsDefs supportedStmts arithmetic
  loweringPosts vyperInterpreter vyperTypeSystem vyperState vyperAST list
  bodyExprPreFacts allocLimits allocLimitsProps exprSimSource vyperTypeCallGraph
  bodyFullLogScalarTopics bodyFullLogSuffix supportedStmtTraverse
  bodySimLogArgs stmtSimLogTrace exprSimHyps whitelistLogWiden
  supportedExprs supportedExprTraverse
  vyperTypeCallStackSoundness vyperTypeExprSoundness vyperTypeInvariants
  stmtLowering context compileEnv gasShadowState gasShadowCompileStmtHelpers gasShadowCompileStmtCases
  gasOutcomeFullCompose gasStorage vyperStorageTrace vyperStorageFootprint
  logComposeFacts gasExemptCert exprSimDefs stmtSimDefs bodyPtrDefs
  eventLogSplitProps eventEncodingProps vyperEventArgCompat vyperTypeArgFits
  abiLogSourceEncoding typedLogSplitComplete stmtSimLogSource vyperTypeABI vyperEventSoundness
  vyperEventCompatibility vyperEvent vyperABI supportedTypes e2eDefs vyperTypeContract
  stmtSimLogSuffix eventLoweringStructure
  exprSimIfExpCompat structFieldsProps typedCopyCompatibility typedLogSplitArgs
  exprLowering exprLoweringProps loweringStateRelDefs gasOutcomeFull
  fragGasPathFrameMem bodyMemAggregatePath bodyFullAllocaFresh
  fragGasOriginPtr
  exprSimCopy exprSimAlloc typedMemoryCopy exprSimStorageCopy
  valueEncodingDefs vyperTypeDefaults valueEncodingProps
  robustCopyTransportPtr abiEncoderWindow abiTypeBoundProps decoderGhostFramePtr
  allocaSiteResource abiEncoderAdmissible abiEncoderWindowContract reasonCopySourcePtr
  abiEncoderWindowJoint
  exprSimAbiEncodeExecFrame
  exprSimAbiEncodeCallerFrame exprSimAbiEncodeFrameTransfer abiDecodeStaticProps
  exprSimAbiEncodeStateTransport
  bodyFullUnwrapSlotPost bodyInvNoDalloca stateRelProj bodyFullPathHistory
  bodyMemoryDefs exprSimWordArgs fragGasOriginPtrLoop contractABI
  bodyFullExtCallPosList bodyFullExtCallDirectSaved bodyFullExtCallDirectLayout
  bodyFullExtCallSavedOperand freshWrites
  logArgumentTyping assignPlaceOperandFacts exprSafeOperand loweringShapeRules
  aggregateEvaluatedLayout entryDecodeStaticProps wordArgsPtr
  placeRelayoutSemantic exprSimOperands abiEncodeValuesMetadata abiDecodeRanges
  logEmitStep rawLogPtrInst instMemFrontier venomInst venomExecSemantics
  ptrDiscipline ptrSafeRun emitHelper fragExec rich_list
  abiBuiltinAllocation abiEncoderAppend abiEncoderAllocationShape
  compilerInstructionSuffix emitHelperProps stmtLoweringMono loweringHalt abiEncoderProps
  bodyFullAllocGeneric bodyCopyMemoryBase valueCopy valueCopyBytes representationCleanPtr
  immutableMemoryFrame exprSimProps valueEncoding venomState tuplePlaceZero exprPtrUnwrapFacts placeMemoryTypeInterfaces typedLogFieldChecked venomMemDefs bytesCopyProps vyperTyping

val _ = Parse.hide "body";
val irule_body_pre = bodyConstNameLib.irule_body_pre;

Theorem log_full_compatible_source_event_encoded:
  lookup_event_metadata tenv sources target id = SOME (h,dtys,flags) /\
  LENGTH flags = LENGTH dtys /\
  LIST_REL event_arg_compatible dtys ltys /\
  EVERY (\(ty,indexed). indexed ==> supported_event_leaf_type ty) (ZIP (dtys,flags)) /\
  LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v) ltys vals /\
  LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v)
    (log_non_indexed_types flags dtys) (log_non_indexed_values flags vals) ==>
  ?topics avs.
    encode_indexed_event_topics flags ltys vals = SOME topics /\
    vyper_to_abi_list tenv (log_non_indexed_types flags dtys)
      (log_non_indexed_values flags vals) = SOME avs /\
    encode_source_event tenv sources target id vals =
      SOME <|logger := target; topics := n2w h::topics;
        data := enc (Tuple (vyper_to_abi_types tenv (log_non_indexed_types flags dtys))) (ListV avs)|>
Proof
  strip_tac >>
  `!flags dtys ltys vals.
    LENGTH flags = LENGTH dtys /\ LIST_REL event_arg_compatible dtys ltys /\
    EVERY (\(ty,indexed). indexed ==> supported_event_leaf_type ty) (ZIP (dtys,flags)) /\
    LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v) ltys vals /\
    LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v)
      (log_non_indexed_types flags dtys) (log_non_indexed_values flags vals) ==>
    ?topics avs.
      encode_indexed_event_topics flags ltys vals = SOME topics /\
      encode_indexed_event_topics flags dtys vals = SOME topics /\
      vyper_to_abi_list tenv (log_non_indexed_types flags dtys)
        (log_non_indexed_values flags vals) = SOME avs` by
    (rpt (pop_assum kall_tac) >> Induct
     >- (Cases_on `dtys` >> Cases_on `ltys` >> Cases_on `vals` >>
         simp[encode_indexed_event_topics_def, compileEnvTheory.log_non_indexed_types_def,
           loweringStateRelDefsTheory.log_non_indexed_values_def, Once vyper_to_abi_def]) >>
     rpt gen_tac >> Cases_on `dtys` >> Cases_on `ltys` >> Cases_on `vals` >> simp[] >>
     rename1 `encode_indexed_event_topics (flag::flags) (lty::ltys) (v::vals)` >>
     rename1 `event_arg_compatible dty lty` >>
     Cases_on `flag` >>
     simp[compileEnvTheory.log_non_indexed_types_def,
       loweringStateRelDefsTheory.log_non_indexed_values_def] >> rpt strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     simp[encode_indexed_event_topics_def, compileEnvTheory.log_non_indexed_types_def,
       loweringStateRelDefsTheory.log_non_indexed_values_def, Once vyper_to_abi_def]
     >- (drule_all event_leaf_arg_compatible >>
         disch_then (qspec_then `tenv` strip_assume_tac) >>
         drule_all typed_event_topic_total >> strip_tac >> gvs[]) >>
     `?av. vyper_to_abi tenv dty v = SOME av` by
       metis_tac[cj 1 vyper_to_abi_total] >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  `LENGTH flags = LENGTH vals` by metis_tac[listTheory.LIST_REL_LENGTH] >>
  drule_all non_indexed_event_args_exists >> strip_tac >>
  simp[encode_source_event_def, encode_vyper_event_metadata_def] >> metis_tac[]
QED

Theorem log_full_snapshot_cuts[local]:
  cenv.ce_event_info (nsid_to_string id) = SOME (hash,declared,flags) /\
  compile_stmt cenv lctx ret (Log id args) sa = ((),sb) /\
  compile_stmt cenv lctx ret (Log id (MAP gas_shadow_expr args)) shadow_sa = ((),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?saved sm shadow_sm.
    compile_ext_call_args compile_expr cenv [] (MAP (lowered_value_type cenv) args)
      args sa = (saved,sm) /\
    compile_ext_call_args compile_expr cenv []
      (MAP (lowered_value_type cenv) (MAP gas_shadow_expr args))
      (MAP gas_shadow_expr args) shadow_sa = (saved,shadow_sm) /\
    gas_shadow_state sm shadow_sm /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code shadow_sa shadow_sm shadow_func
Proof
  strip_tac >>
  Cases_on `compile_ext_call_args compile_expr cenv []
    (MAP (lowered_value_type cenv) args) args sa` >> rename1 `_ = (saved,sm)` >>
  Cases_on `compile_ext_call_args compile_expr cenv []
    (MAP (lowered_value_type cenv) (MAP gas_shadow_expr args))
    (MAP gas_shadow_expr args) shadow_sa` >> rename1 `_ = (shadow_saved,shadow_sm)` >>
  qspecl_then [`sa`,`shadow_sa`] mp_tac
    (REWRITE_RULE [gas_shadow_compiles_def] gas_shadow_log_snapshots) >>
  simp[] >> strip_tac >> gvs[] >>
  drule_all_then strip_assume_tac compile_log_stmt_snapshot_code >>
  mp_tac (Q.INST [`args` |-> `MAP gas_shadow_expr args`, `sa` |-> `shadow_sa`,
      `sm` |-> `shadow_sm`, `sf` |-> `shadow_sb`, `fn` |-> `shadow_func`]
    (SPEC_ALL compile_log_stmt_snapshot_code)) >> simp[]
QED

Theorem log_full_physical_source_encoding[local]:
  lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id = SOME (h,dtys,flags) /\
  LENGTH flags = LENGTH dtys /\ LIST_REL event_arg_compatible dtys atys /\
  EVERY (\(ty,indexed). indexed ==> supported_event_leaf_type ty) (ZIP (dtys,flags)) /\
  LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v)
    atys vals /\
  expr_sim_inv cenv cx env es /\ body_inv tops ctx cenv cx /\
  EVERY (supported_nested_type supported_event_leaf_type (LENGTH tops) tops)
    (log_non_indexed_types flags dtys) /\
  SUM (MAP (type_memory_bytes cenv) (log_non_indexed_types flags dtys)) < 2 ** 64 ==>
  ?topics avs.
    encode_indexed_event_topics flags atys vals = SOME topics /\
    vyper_to_abi_list (get_tenv cx) (log_non_indexed_types flags atys)
      (log_non_indexed_values flags vals) = SOME avs /\
    encode_source_event (get_tenv cx) cx.sources cx.txn.target id vals =
      SOME <|logger := cx.txn.target; topics := n2w h::topics;
        data := enc (Tuple (vyper_to_abi_types (get_tenv cx) (log_non_indexed_types flags atys)))
          (ListV avs)|> /\
    (!ty. MEM ty (log_non_indexed_types flags atys) ==>
      abi_enc_plan (get_tenv cx) ty (type_to_abi_enc_info cenv.ce_struct_fields cenv ty))
Proof
  strip_tac >>
  qabbrev_tac `src = log_non_indexed_types flags atys` >>
  qabbrev_tac `decl = log_non_indexed_types flags dtys` >>
  qabbrev_tac `vs = log_non_indexed_values flags vals` >>
  `LENGTH flags = LENGTH atys` by metis_tac[LIST_REL_LENGTH] >>
  `LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v)
    src vs` by
    (simp_tac bool_ss [Abbr `src`, Abbr `vs`, log_non_indexed_types_select,
       log_non_indexed_values_select] >> irule select_log_args_rel >> simp[] >>
     fs[LIST_REL_EL_EQN, EL_ZIP] >> metis_tac[]) >>
  `LIST_REL event_arg_compatible decl src` by
    (simp_tac bool_ss [Abbr `decl`, Abbr `src`] >>
     metis_tac[log_non_indexed_types_preserve, EVERY_TRIVIAL]) >>
  `arg_types_fit src decl` by
    metis_tac[event_arg_compatible_list_alias_def, event_compatible_list_rel] >>
  `?tvs. OPT_MMAP (evaluate_type (get_tenv cx)) src = SOME tvs` by
    (qexists_tac `MAP (THE o evaluate_type (get_tenv cx)) src` >>
     simp[vyperMiscTheory.OPT_MMAP_SOME_IFF, EVERY_EL, EL_MAP] >>
     fs[LIST_REL_EL_EQN] >> metis_tac[optionTheory.THE_DEF]) >>
  `?dtvs. OPT_MMAP (evaluate_type (get_tenv cx)) decl = SOME dtvs` by
    metis_tac[cj 2 log_compatible_bounded_evaluation, optionTheory.IS_SOME_EXISTS] >>
  `LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v)
     decl vs` by
    (imp_res_tac vyperTypeABITheory.OPT_MMAP_LIST_REL >>
     fs[LIST_REL_EL_EQN] >> metis_tac[log_compatible_declared_value]) >>
  `EVERY (well_formed_type (get_tenv cx)) src /\
   EVERY (well_formed_type (get_tenv cx)) decl` by
    (imp_res_tac vyperTypeABITheory.OPT_MMAP_LIST_REL >>
     fs[LIST_REL_EL_EQN, EVERY_EL, well_formed_type_def] >>
     metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  `type_env tops SUBMAP get_tenv cx` by
    (irule body_main_type_env_submap >> fs[body_inv_def]) >>
  `EVERY (assignable_type (get_tenv cx)) decl` by
    (`EVERY (supported_nested_type supported_event_leaf_type (LENGTH tops) tops) decl` by
       simp[Abbr `decl`] >>
     fs[EVERY_MEM, well_formed_type_def] >> qx_gen_tac `ty` >> strip_tac >>
     qspecl_then [`supported_event_leaf_type`,`LENGTH tops`,`tops`,`ty`] mp_tac
       supported_nested_evaluated_assignable >> simp[] >>
     disch_then (qspecl_then [`get_tenv cx`,`{}`] mp_tac) >>
     simp[finite_mapTheory.DRESTRICT_UNIV] >> metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  `EVERY (assignable_type (get_tenv cx)) src` by
    metis_tac[cj 2 arg_type_fits_source_assignable] >>
  `!ty. MEM ty src ==>
    abi_enc_plan (get_tenv cx) ty (type_to_abi_enc_info cenv.ce_struct_fields cenv ty)` by
    (fs[EVERY_MEM] >> metis_tac[body_log_assignable_abi_plan]) >>
  `event_arg_compatible_list decl src` by simp[event_compatible_list_rel] >>
  `vyper_to_abi_types (get_tenv cx) decl = vyper_to_abi_types (get_tenv cx) src /\
   vyper_to_abi_list (get_tenv cx) decl vs = vyper_to_abi_list (get_tenv cx) src vs` by
    metis_tac[cj 2 event_arg_compatible_abi_type, cj 2 event_arg_compatible_abi_value] >>
  mp_tac (Q.INST [`tenv` |-> `get_tenv cx`, `sources` |-> `cx.sources`,
      `target` |-> `cx.txn.target`, `ltys` |-> `atys`] (SPEC_ALL log_full_compatible_source_event_encoded)) >>
  simp[Abbr `src`, Abbr `decl`, Abbr `vs`] >> metis_tac[]
QED

Theorem log_capture_type[local]:
  expr_body_pre cenv cx env e es /\ env.type_defs = get_tenv cx /\
  ty = lowered_value_type cenv e /\ type_alloc_ok cenv ty /\
  value_runtime_typed env ty v /\
  compile_expr cenv (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv cenv copy (ext_call_arg_value ty vv) sm = (sv,ss) ==>
  (~is_word_type ty ==> ~is_word_type (expr_type e)) /\
  (!l. vv_operand sv <> Label l) /\
  ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\ type_memory_size tv < 2**64
Proof
  strip_tac >>
  `arg_type_fits ty (expr_type e)` by metis_tac[expr_body_pre_lowered_fits] >>
  conj_tac >- metis_tac[arg_type_fits_word_type] >>
  reverse conj_tac
  >- (qpat_x_assum `value_runtime_typed env ty v`
         (qx_choose_then `tv` strip_assume_tac o REWRITE_RULE [value_runtime_typed_def]) >>
      `evaluate_type (get_tenv cx) ty = SOME tv` by metis_tac[] >>
      `type_memory_bytes cenv ty = type_memory_size tv` by
        metis_tac[expr_sim_inv_memory_size, cj 1 expr_body_pre_def] >>
      qexists_tac `tv` >> simp[] >> Cases_on `is_word_type ty` >>
      fs[type_alloc_ok_def, cj 3 word_type_dec_sizes] >> decide_tac) >>
  `!l. vv_operand vv <> Label l` by metis_tac[assign_place_operand_not_label] >>
  `vv_operand (ext_call_arg_value ty vv) = vv_operand vv` by
    (Cases_on `vv` >> simp[ext_call_arg_value_def, vv_operand_def]) >>
  qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
  simp[compile_snapshot_vv_def] >> IF_CASES_TAC
  >- (simp[comp_bind_def] >> pairarg_tac >> simp[comp_return_def] >>
      strip_tac >> gvs[vv_operand_def] >> drule unwrap_value_not_label >> simp[]) >>
  Cases_on `copy` >> simp[comp_bind_def, comp_return_def]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[vv_operand_def, mk_ptr_def] >>
      qpat_x_assum `compile_materialize_vv _ _ _ _ = _` mp_tac >>
      simp[compile_materialize_vv_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
      drule abi_builtin_alloc_buffer_shape >> simp[emit_op_eq]) >>
  strip_tac >> gvs[]
QED

Definition log_saved_row_def:
  log_saved_row cenv cx st0 es sa front s G tn (saved,ty) v <=>
    ?e si sm ss vv raw copy tv.
      ty = lowered_value_type cenv e /\
      compile_expr cenv (expr_type e) e si = (vv,sm) /\
      compile_snapshot_vv cenv copy (ext_call_arg_value ty vv) sm = (saved,ss) /\
      ((?tag op0. saved = StackValue tag op0) \/
       (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory) \/
       (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location <> LocMemory /\
            ty = expr_type e /\ saved = vv)) /\
      local_ptrs_reserved cenv si /\ sa.cs_next_id <= si.cs_next_id /\
      sm.cs_next_var <= front.cs_next_var /\ sm.cs_next_id <= front.cs_next_id /\
      ss.cs_next_var <= front.cs_next_var /\ ss.cs_next_id <= front.cs_next_id /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      (~is_word_type ty ==> ~is_word_type (expr_type e)) /\
      (!l. vv_operand saved <> Label l) /\
      read_result cx raw es = (INL v,es) /\
      evaluate_type (get_tenv cx) ty = SOME tv /\ type_memory_bytes cenv ty = type_memory_size tv /\
      type_memory_size tv < 2**64 /\ value_has_type tv v /\
      vv_holds cenv cx ty raw saved es s /\ vv_at cenv cx ty si ss es raw saved s /\
      ptr_vv_ok cx ty raw saved es G tn s /\ vv_store_bound cx ty ty es raw saved s /\
      (!H. valid_horizon cx st0 H es.storage_trace ==> vv_storage_live H cx saved es s) /\
      ((case saved of StackValue tag op0 => ~is_word_type ty
          | LocatedValue tag p => p.ptr_location = LocMemory) ==>
        ptr_buf_ok cenv e (vv_operand saved) G s)
End

Theorem log_saved_row_advance[local]:
  log_saved_row cenv cx st0 es sa front s G tn (sv,ty) v /\
  log_topic_state ctx func cenv cx st0 es DF lo d front s G tn a u Gu tu /\
  (?H. valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\ local_ptrs_reserved cenv front ==>
  log_saved_row cenv cx st0 es sa a u Gu tu (sv,ty) v
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `log_saved_row _ _ _ _ _ _ _ _ _ _ _`
    (qx_choosel_then [`e`,`si`,`sm`,`ss`,`vv`,`raw`,`copy`,`tv`] strip_assume_tac o
     REWRITE_RULE [log_saved_row_def]) >>
  qpat_x_assum `log_topic_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [log_topic_state_def]) >>
  `!x. vv_operand sv = Var x ==> not_fresh_at front x` by
    metis_tac[extcall_saved_operand_not_fresh, not_fresh_at_mono] >>
  `(vv_location sv = SOME LocMemory ==> ~is_word_type ty) /\
   (!tag p. sv = LocatedValue tag p ==> tag = ty)` by
    (qpat_assum `(?tag op0. sv = StackValue tag op0) \/ _` mp_tac >>
     Cases_on `sv` >> simp[vv_location_def] >> metis_tac[]) >>
  qpat_assum `?H. valid_horizon cx st0 H es.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  `stmt_state_rel hz ctx func cenv cx es s /\ stmt_state_rel hz ctx func cenv cx es u /\
    ghost_inv_at (DF hz) lo d cenv cx es Gu tu u /\ vv_storage_live hz cx sv es s` by
    metis_tac[] >>
  mp_tac (Q.INST [`ce` |-> `cenv`,`ee` |-> `es`,`saved` |-> `sv`,
    `t` |-> `u`,`Gnext` |-> `Gu`,`tt` |-> `tu`,`H` |-> `hz`]
    (SPEC_ALL extcall_direct_saved_advance)) >>
  impl_tac >- (asm_rewrite_tac[] >> metis_tac[]) >> strip_tac >>
  simp_tac bool_ss [log_saved_row_def] >>
  qexistsl_tac [`e`,`si`,`sm`,`ss`,`vv`,`raw`,`copy`,`tv`] >>
  asm_rewrite_tac[] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem compile_log_one_saved_topic[local]:
  log_saved_row cenv cx st0 es sa front s G tn (sv,ty) v /\
  supported_event_leaf_type ty /\ encode_event_topic ty v = SOME topic /\
  log_topic_state ctx func cenv cx st0 es DF lo d front s G tn a u Gu tu /\
  (?H. valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s) /\
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  local_ptrs_reserved cenv front /\ sa.cs_next_id <= front.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at front x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at front x) /\
  ~u.vs_halted /\ fn_inst_ids_distinct func /\ fn_has_code a b func /\
  compile_log_saved_topics cenv [(sv,is_bytestring_type ty)] a = ([op],b) ==>
  ?t Gf tf.
    log_topic_state ctx func cenv cx st0 es DF lo d front s G tn b t Gf tf /\ ~t.vs_halted /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,Gf,tf)) /\
    safe_operand b op /\ eval_operand op t = SOME topic /\ op_taint tf op = {} /\
    (!x. not_fresh_at a x ==>
      lookup_var x t = lookup_var x u /\ FLOOKUP Gf x = FLOOKUP Gu x /\
      op_taint tf (Var x) = op_taint tu (Var x))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `log_saved_row _ _ _ _ _ _ _ _ _ _ _`
    (qx_choosel_then [`e`,`si`,`sm`,`ss`,`vv`,`raw`,`copy`,`tv`] strip_assume_tac o
     REWRITE_RULE [log_saved_row_def]) >>
  qpat_assum `log_topic_state ctx func cenv cx st0 es DF lo d front s G tn a u Gu tu`
    (strip_assume_tac o REWRITE_RULE [log_topic_state_def]) >>
  qpat_x_assum `compile_log_saved_topics _ _ _ = _`
    (qx_choosel_then [`src`,`m`] strip_assume_tac o REWRITE_RULE [compile_log_saved_topic_cut]) >>
  `ci_mono a m /\ ci_mono m b` by
    (conj_tac
     >- (qspecl_then [`cenv`,`sv`,`a`] mp_tac ci_mono_unwrap_value >> simp[]) >>
     qspecl_then [`src`,`is_bytestring_type ty`,`m`] mp_tac compile_encode_log_topic_ci_mono >> simp[]) >>
  `fn_has_code a m func /\ fn_has_code m b func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  `front.cs_next_var <= m.cs_next_var /\ front.cs_next_id <= m.cs_next_id /\
   sm.cs_next_var <= a.cs_next_var /\ sm.cs_next_id <= a.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ vv_storage_live H cx sv es s` by simp[] >>
  mp_tac (Q.INST [`ce` |-> `cenv`,`ee` |-> `es`,`saved` |-> `sv`,`su` |-> `a`,`sb` |-> `m`]
    (SPEC_ALL extcall_direct_restore_saved)) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac) >>
  `expr_val_at cenv cx ty sa m es v src z` by
    (irule log_topic_physical_val_at >> qexistsl_tac [`a`,`si`,`ss`] >>
     fs[ci_mono_def] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  `safe_operand m src` by metis_tac[safe_operand_def, unwrap_value_not_label] >>
  `local_ptrs_reserved cenv m` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at m x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at m x)` by
    metis_tac[not_fresh_at_mono] >>
  mp_tac (Q.INST [`s` |-> `z`,`G` |-> `Gz`,`tn` |-> `tz`,`sm` |-> `m`]
    (SPEC_ALL compile_log_saved_topic_hash)) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac) >>
  qpat_assum `?H. valid_horizon cx st0 H es.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  `stmt_state_rel hz ctx func cenv cx es s` by metis_tac[] >>
  `log_topic_state ctx func cenv cx st0 es DF lo d front s G tn m z Gz tz` by
    (mp_tac (Q.INST [`ce` |-> `cenv`,`H` |-> `hz`,`b` |-> `m`,
        `v` |-> `z`,`Gv` |-> `Gz`,`tv` |-> `tz`] (SPEC_ALL log_topic_state_step)) >>
     simp[ci_mono_def] >> fs[ci_mono_def]) >>
  `log_topic_state ctx func cenv cx st0 es DF lo d front s G tn b t Gf tf` by
    (mp_tac (Q.INST [`ce` |-> `cenv`,`H` |-> `hz`,`a` |-> `m`,
        `u` |-> `z`,`Gu` |-> `Gz`,`tu` |-> `tz`,`v` |-> `t`,`Gv` |-> `Gf`,`tv` |-> `tf`]
        (SPEC_ALL log_topic_state_step)) >> fs[ci_mono_def]) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> asm_rewrite_tac[] >> conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gz`,`z`,`tz`] >> simp[]) >>
  fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]
QED

Theorem log_saved_data_layout[local]:
  LIST_REL (log_saved_row cenv cx st0 es sa front s G tn) rows vs /\
  vyper_to_abi_list (get_tenv cx) (MAP SND rows) vs = SOME avs /\
  ats = vyper_to_abi_types (get_tenv cx) (MAP SND rows) /\
  bytes = enc (Tuple ats) (ListV avs) /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) ==>
  LENGTH bytes <= abi_size_bound cenv.ce_struct_fields (TupleT (MAP SND rows)) /\
  LIST_REL abi_encoder_layout_valid ats avs /\
  LIST_REL (\row at. abi_embedded_static_size cenv.ce_struct_fields (SND row) =
    abi_member_head_size at) rows ats
Proof
  strip_tac >>
  `LENGTH rows = LENGTH vs` by metis_tac[LIST_REL_LENGTH] >>
  `ZIP (MAP FST rows,MAP SND rows) = rows` by
    (Induct_on `rows` >> simp[] >> PairCases_on `h` >> simp[]) >>
  mp_tac (Q.INST [`sf` |-> `cenv.ce_struct_fields`,`env` |-> `get_tenv cx`,
    `tys` |-> `MAP SND rows`,`arg_types` |-> `MAP SND rows`,`saved` |-> `MAP FST rows`]
    (SPEC_ALL extcall_direct_args_layout)) >>
  impl_tac >- (simp[EL_MAP] >> gen_tac >> strip_tac >>
    qpat_assum `LIST_REL _ rows vs`
      (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
    impl_tac >- simp[] >>
    `EL i rows = (FST (EL i rows),SND (EL i rows))` by simp[] >>
    pop_assum (fn row => PURE_ONCE_REWRITE_TAC [row]) >>
    simp_tac bool_ss [log_saved_row_def] >>
    disch_then (qx_choosel_then [`e`,`si`,`sm`,`ss`,`vv`,`raw`,`copy`,`tv`] strip_assume_tac) >>
    qexistsl_tac [`tv`,`tv`] >> simp[]) >>
  strip_tac >> gvs[]
QED

Theorem log_data_buffer[local]:
  compile_alloc_buffer n a = (buf,b) /\ n < dimword (:256) /\ fn_has_code a b func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv a /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  alloca_history func s /\ ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  (?H. valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) ==>
  ?p w u Gu tu inst.
    buf.buf_operand = Var p /\ not_fresh_at b p /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_id = a.cs_next_id /\
    inst.inst_outputs = [p] /\ not_local_ptr cenv es.scopes p /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es u /\ storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es Gu tu u) /\
    u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts /\ ~u.vs_halted /\
    a.cs_next_var <= b.cs_next_var /\ a.cs_next_id < b.cs_next_id /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    wb_frame cenv es es a s u /\ ghost_kept_at lo cenv es a G tn s Gu tu /\
    eval_operand (Var p) u = SOME w /\ ptr_covers Gu tu p u n /\
    FLOOKUP u.vs_allocas a.cs_next_id = SOME (w2n w,n) /\
    w2n w + n < dimword (:256) /\ w2n w + n <= u.vs_alloca_next
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `?H. valid_horizon cx st0 H es.storage_trace` (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (qspec_then `hz` (drule_then strip_assume_tac)) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``] (SPEC_ALL alloc_buffer_origin_ptr_path_exact)) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`p`,`w`,`u`,`Gu`,`tu`] strip_assume_tac)) >>
  `p = STRING #"%" (toString a.cs_next_var) /\
   a.cs_next_var <= b.cs_next_var /\ a.cs_next_id < b.cs_next_id` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >> gvs[]) >>
  `not_local_ptr cenv es.scopes p` by
    (irule fresh_not_local_ptr >> qexists_tac `a` >> simp[not_fresh_at_def, toString_inj]) >>
  `u.vs_memory = s.vs_memory /\ ~u.vs_halted` by
    (qpat_assum `u with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = s`
       (mp_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >> simp[]) >>
  `wb_frame cenv es es a s u` by simp[wb_frame_def, locals_kept_mem] >>
  `ghost_kept_at lo cenv es a G tn s Gu tu` by
    (irule alloc_buffer_ghost_kept_at >>
     qexistsl_tac [`G`,`w2n w+n`,`s`,`tn`] >>
     simp[ghost_kept_at_refl] >>
     `alloca_inv s` by fs[stmt_state_rel_def] >>
     conj_tac >- metis_tac[alloca_site_registered_below] >>
     rpt strip_tac >>
     metis_tac[body_local_region_frontier]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es u /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es Gu tu u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     simp[] >>
     irule (Q.INST [`e` |-> `w2n w + n`] alloc_buffer_ghost_inv_at) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  qexistsl_tac [`p`,`w`,`u`,`Gu`,`tu`,`mk_inst a.cs_next_id ALLOCA [Lit (n2w n)] [p]`] >>
  simp[mk_inst_def, eval_operand_def] >> metis_tac[buffer_alloc_code]
QED

(* A static LOG still checks the pointer discipline before aborting. *)
Theorem compile_log_emit_static_origin_ptr_path:
  emit_inst LOG (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++
    [len_op;ptr_op]) [] sa = ((),sb) /\
  LENGTH topic_ops < dimword (:256) /\
  eval_operands topic_ops s = SOME topics /\
  eval_operand ptr_op s = SOME off /\ eval_operand len_op s = SOME len /\
  EVERY (\op. op_taint tn op = {}) (ptr_op::len_op::topic_ops) /\
  (w2n len <> 0 ==> ?v. ptr_op = Var v /\ ptr_covers G tn v s (w2n len)) /\
  (!i. w2n off <= i /\ i < w2n off + w2n len ==> i NOTIN tn.t_mem) /\
  (w2n len = 0 \/ w2n off + w2n len <= s.vs_alloca_next) /\
  s.vs_call_ctx.cc_static /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (Abort ExHalt_abort (halt_state (set_returndata [] s)),G,tn)
Proof
  strip_tac >> gen_tac >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id LOG
    (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op]) []` >>
  `step_inst_base inst s = Abort ExHalt_abort (halt_state (set_returndata [] s))` by
    (irule log_emit_static_step >> simp[Abbr `inst`, mk_inst_def] >> gvs[wordsTheory.dimword_def]) >>
  `access_ok 0 G func inst s /\ taint_ok func tn inst s` by
    (conj_tac
     >- (mp_tac (Q.INST [`fn` |-> `func`, `id` |-> `sa.cs_next_id`,
           `n` |-> `len`, `off` |-> `off`, `vals` |-> `topics`]
           (Q.INST [`topics` |-> `topic_ops`, `len` |-> `len_op`,
                    `pop` |-> `ptr_op`] (SPEC_ALL rawLogPtrInstTheory.log_access_ok))) >>
         (impl_tac >-
           (simp[] >> rpt strip_tac >> gvs[ptr_covers_def, eval_operand_def] >>
            metis_tac[wordsTheory.w2n_eq_0])) >> simp[Abbr `inst`]) >>
     mp_tac (Q.INST [`fn` |-> `func`, `id` |-> `sa.cs_next_id`,
       `n` |-> `len`, `off` |-> `off`, `vals` |-> `topics`]
       (Q.INST [`topics` |-> `topic_ops`, `len` |-> `len_op`,
                `pop` |-> `ptr_op`] (SPEC_ALL rawLogPtrInstTheory.log_taint_ok))) >>
     (impl_tac >- fs[]) >> simp[Abbr `inst`]) >>
  `access_ok lo G func inst s` by
    (gvs[access_ok_def] >> rpt strip_tac >> metis_tac[arithmeticTheory.ADD_EQ_0]) >>
  `step_inst 0 ctx inst s = Abort ExHalt_abort (halt_state (set_returndata [] s))` by
    simp[step_inst_non_invoke, Abbr `inst`, mk_inst_def] >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    simp[ptr_inst_ok_def, Abbr `inst`, mk_inst_def, step_inst_non_invoke] >>
  `inst_mem_below_frontier inst s /\ inst_dload_in_section inst s` by
    (simp[Abbr `inst`, memSafeRunTheory.inst_dload_in_section_other] >>
     qspecl_then [`sa.cs_next_id`, `LENGTH topic_ops`, `REVERSE topic_ops`,
                   `len_op`, `ptr_op`, `[]`, `s`] mp_tac below_frontier_LOG >>
     simp[] >> gvs[]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ [inst]` by
    gvs[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, emit_def, Abbr `inst`] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX sb.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (gvs[IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN] >> simp[]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (Abort ExHalt_abort (halt_state (set_returndata [] s)),G,tn)` by
    (rewrite_tac[fragGasOriginPtrTheory.gas_origin_ptr_edge_def] >> conj_tac
     >- (rewrite_tac[fragGasOriginTheory.gas_origin_edge_def] >> conj_tac >- simp[] >>
         qexistsl [`0`, `bb`, `inst`, `Abort ExHalt_abort (halt_state (set_returndata [] s))`] >>
         simp[gasEventsTheory.gas_events_step_def, memSafeRunTheory.mem_safe_step_non_invoke,
              exit_result_def, Abbr `inst`, mk_inst_def] >> gvs[mk_inst_def]) >>
     rewrite_tac[fragGasPathPtrTheory.gas_path_ptr_edge_def] >> simp[] >> qexists `0` >>
     simp[gasCountTheory.gas_count_step_def, ptr_safe_step_def] >>
     qexists `inst` >>
     simp[Abbr `inst`, mk_inst_def, exit_result_def] >> gvs[mk_inst_def]) >>
  irule (cj 3 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
  simp[exit_result_def]
QED

Theorem log_full_source_suffix_result:
  encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs = SOME ev ==>
  bind (lift_option (encode_source_event (get_tenv cx) cx.sources
                       cx.txn.target id vs) "Log encode event")
    (\event. ignore_bind (check_not_static cx) (push_log event)) mid =
  (if cx.txn.is_static then
     (INR (Error (RuntimeError "write in static context")), mid)
   else (INL (), mid with logs := mid.logs ++ [ev]))
Proof
  strip_tac >> Cases_on `cx.txn.is_static` >>
  simp[bind_def, ignore_bind_def, lift_option_def, return_def,
       check_not_static_eq, push_log_def]
QED

Theorem log_topics_values[local]:
  !ops ws. LIST_REL (\op w. safe_operand a op /\ eval_operand op s = SOME w /\
    op_taint tn op = {}) ops ws ==>
    eval_operands ops s = SOME ws /\ EVERY (\op. safe_operand a op /\ op_taint tn op = {}) ops
Proof
  Induct >> Cases_on `ws` >> simp[eval_operands_def, exec_operand_list_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

(* Runtime coverage, not nominal source capacity, suffices for bytes stores. *)
Theorem log_full_emit_outcome[local]:
  encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs = SOME ev /\
  ev = <|logger := cx.txn.target; topics := topics;
          data := mem_bytes_at (w2n off) (w2n len) u.vs_memory|> /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op])
    [] send = ((),sb) /\
  LENGTH ops < dimword (:256) /\ eval_operands ops u = SOME topics /\
  eval_operand ptr_op u = SOME off /\ eval_operand len_op u = SOME len /\
  EVERY (\op. op_taint tu op = {}) (ptr_op::len_op::ops) /\
  (w2n len <> 0 ==> ?p. ptr_op = Var p /\ ptr_covers Gu tu p u (w2n len)) /\
  (!i. w2n off <= i /\ i < w2n off + w2n len ==> i NOTIN tu.t_mem) /\
  (w2n len = 0 \/ w2n off + w2n len <= u.vs_alloca_next) /\
  fn_has_code send sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ ~u.vs_halted /\ ~t.vs_halted /\
  u.vs_current_bb = send.cs_current_bb /\ u.vs_inst_idx = LENGTH send.cs_current_insts /\
  (?H. valid_horizon cx st0 H mid.storage_trace) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func ce cx mid u /\
    storage_well_formed_on cx mid (FST H) /\ ghost_inv_at (DF H) lo d ce cx mid Gu tu u) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK u,Gu,tu)) /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s0 /\
  local_ptrs_reserved ce sa /\ return_buf_frame d ce sa s0 /\ return_buf_sep d ce es s0 /\
  sa.cs_next_var <= send.cs_next_var /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  alloca_history func u /\ MAP FDOM mid.scopes = MAP FDOM es.scopes /\
  wb_frame ce es mid sa s0 u /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gu tu ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (lift_option (encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs)
      "Log encode event") (\event. ignore_bind (check_not_static cx) (push_log event)))
    (mid,t,G,tn)
    (\H res ee G' tn' v.
       (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) v) ==>
       ?ce'.
         stmt_lands lctx sb res v /\ ~v.vs_halted /\
         (res = INL () ==> ~block_is_terminated sb /\ ce' = ce) /\
         cenv_top_ext ce ce' ee.scopes /\ stmt_state_rel H ctx func ce' cx ee v /\
         storage_well_formed_on cx ee (FST H) /\ return_buf_frame d ce' sb v /\
         alloca_history func v /\ return_buf_sep d ce' ee v /\
         (ctx_has_dalloca ctx ==> allocas_below_fmp v) /\
         s0.vs_alloca_next <= v.vs_alloca_next /\ ghost_inv_at (DF H) lo d ce' cx ee G' tn' v /\
         (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x v = SOME w) /\
         (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP v.vs_allocas aid = SOME b) /\
         (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G0 x /\
           op_taint tn' (Var x) = op_taint tn0 (Var x)) /\
         alloca_frame ce es sa s0 ce' ee v /\
         (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
           (!n b sz'. local_region ce es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
           off <= i /\ i < off + sz /\ i IN tn'.t_mem ==> i IN tn0.t_mem))
    (\H res ee gt r.
       (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
       halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `?H. valid_horizon cx st0 H mid.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (qspec_then `hz` (drule_then strip_assume_tac)) >>
  `u.vs_call_ctx.cc_static = cx.txn.is_static /\ u.vs_call_ctx.cc_address = cx.txn.target` by
    (qpat_assum `stmt_state_rel hz ctx func ce cx mid u`
       (mp_tac o MATCH_MP state_rel_call_ctx_rel o MATCH_MP stmt_state_rel_state_rel) >>
     simp[call_ctx_rel_def]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by metis_tac[ghost_inv_at_def] >>
  Cases_on `cx.txn.is_static`
  >- (`!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) []
          (Abort ExHalt_abort (halt_state (set_returndata [] u)),Gu,tu)` by
        (mp_tac (Q.INST [`topic_ops` |-> `ops`, `sa` |-> `send`, `s` |-> `u`,
           `G` |-> `Gu`, `tn` |-> `tu`] (SPEC_ALL compile_log_emit_static_origin_ptr_path)) >>
         simp[]) >>
      irule gas_outcome_full_exit >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`Gu`,`mid`,
        `Abort ExHalt_abort (halt_state (set_returndata [] u))`,
        `INR (Error (RuntimeError "write in static context"))`,`tu`] >>
      conj_tac
      >- (qx_gen_tac `tail` >>
          mp_tac (Q.INST [`mid` |-> `mid with gas_obs := tail`]
            (SPEC_ALL log_full_source_suffix_result)) >> simp[]) >>
      reverse conj_tac >- simp[exit_result_def] >>
      qx_gen_tac `H` >> strip_tac >> BETA_TAC >>
      conj_tac
      >- (irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gu`,`u`,`tu`] >> simp[]) >>
      simp[stmt_exit_ptr_def, expr_exit_def, halt_exit_def]) >>
  qabbrev_tac `done_es = mid with logs := mid.logs ++ [ev]` >>
  qabbrev_tac `fin = u with <|vs_logs := u.vs_logs ++ [ev];
      vs_inst_idx := LENGTH sb.cs_current_insts|>` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK fin,Gu,tu)` by
    (mp_tac (Q.INST [`topic_ops` |-> `ops`, `sa` |-> `send`, `s` |-> `u`,
      `G` |-> `Gu`, `tn` |-> `tu`] (SPEC_ALL compile_log_emit_origin_ptr_path)) >>
     impl_tac >- simp[] >>
     simp[Abbr `fin`]) >>
  `alloca_history func fin` by
    (qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,tu) [] (OK fin,Gu,tu)`
       (qspec_then `DF hz` (mp_then Any irule body_full_path_alloca_history)) >>
     metis_tac[stmt_state_rel_local_ptrs_alloca]) >>
  `sa.cs_next_var <= sb.cs_next_var /\ send.cs_current_bb = sb.cs_current_bb` by
    (drule emit_inst_extends >> strip_tac >> decide_tac) >>
  `~block_is_terminated sb` by metis_tac[log_emit_not_terminated] >>
  `return_buf_frame d ce sb fin` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s0`,`sa`] >>
     fs[Abbr `fin`, wb_frame_def, lookup_var_def]) >>
  `wb_frame ce es (done_es with gas_obs := []) sa s0 fin /\
   ghost_kept_at lo ce es sa G0 tn0 s0 Gu tu` by
    (fs[Abbr `done_es`, Abbr `fin`, wb_frame_def, locals_kept_def,
        popped_kept_def, lookup_var_def]) >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gu`,`done_es`,`INL ()`,`fin`,`tu`] >>
  conj_tac
  >- (qx_gen_tac `tail` >>
      mp_tac (Q.INST [`mid` |-> `mid with gas_obs := tail`] (SPEC_ALL log_full_source_suffix_result)) >>
      simp[Abbr `done_es`]) >>
  qx_gen_tac `H` >> BETA_TAC >>
  disch_then (assume_tac o SIMP_RULE (srw_ss()) [Abbr `done_es`]) >>
  conj_tac
  >- (irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gu`,`u`,`tu`] >> simp[]) >>
  strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `stmt_state_rel H ctx func ce cx (done_es with gas_obs := []) fin` by
    (simp[Abbr `done_es`, Abbr `fin`, stmt_state_rel_inst_idx, stmt_state_rel_gas_obs] >>
     metis_tac[log_append_stmt_state_rel]) >>
  `storage_well_formed_on cx (done_es with gas_obs := []) (FST H)` by
    (`storage_well_formed_on cx (done_es with gas_obs := []) (FST H) <=>
      storage_well_formed_on cx mid (FST H)` by
       (irule storage_well_formed_on_backends >> simp[Abbr `done_es`]) >>
     asm_rewrite_tac[]) >>
  `ghost_inv_at (DF H) lo d ce cx (done_es with gas_obs := []) Gu tu fin` by
    (`ghost_inv_at (DF H) lo d ce cx (done_es with gas_obs := []) Gu tu u` by
       fs[Abbr `done_es`, ghost_inv_at_def] >>
     simp[Abbr `fin`, ghost_inv_at_logs_idx]) >>
  `alloca_frame ce es sa s0 ce (done_es with gas_obs := []) fin /\
   return_buf_sep d ce (done_es with gas_obs := []) fin` by
    (fs[wb_frame_def] >>
     metis_tac[alloca_frame_of_mem_frame, return_buf_sep_locals_kept]) >>
  qexists_tac `ce` >>
  fs[Abbr `done_es`, Abbr `fin`, stmt_lands_def, cenv_top_ext_refl,
     wb_frame_def, ghost_kept_at_def]
QED

Theorem log_full_bytes_store_runtime_path:
  !tenv sty dty stv dtv v len n xs xd sw dw sa sb s G tn lo explicit ctx func PG.
    compile_store_bytestring (Var xs) (Var xd) sa = ((),sb) /\
    not_fresh_at sa xs /\ not_fresh_at sa xd /\
    lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
    is_bytestring_type sty /\ is_bytestring_type dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
     (?str. v = StringV str /\ len = LENGTH str)) /\
    n = 32 + 32 * word_size len /\ len + 31 < dimword(:256) /\ n < dimword(:256) /\
    n <= type_memory_size dtv /\
    w2n sw + n <= s.vs_alloca_next /\ w2n dw + n <= s.vs_alloca_next /\
    ptr_covers G tn xs s n /\ ptr_covers G tn xd s n /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory stv v (w2n sw) mem) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t Gf tnf.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
      typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
        (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
        val_in_memory dtv v (w2n dw) mem) /\
      (!p. not_fresh_at sa p ==>
        FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `(!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     mem_word_at (w2n sw) mem = n2w len) /\ val_footprint stv v <= n` by
    (mp_tac (Q.SPECL [`tenv`, `sty`, `stv`] bytestring_type_value) >>
     simp[] >> strip_tac >>
     gvs[vyperTypingTheory.value_has_type_def, val_footprint_def] >>
     simp[exprSimPropsTheory.le_word_size_mul] >> rpt strip_tac >>
     first_x_assum (qspec_then `mem` mp_tac) >>
     simp[val_in_memory_def]) >>
  `mem_word_at (w2n sw) s.vs_memory = n2w len` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `!i. w2n sw <= i /\ i < w2n sw + 32 ==> i NOTIN tn.t_mem` by
    (drule robust_mem_word_at_clean >> simp[]) >>
  `mload (w2n sw) s = n2w len` by simp[GSYM mem_word_at_eq_mload] >>
  `32 + 32 * word_size len < dimword(:256)` by metis_tac[] >>
  drule store_bytestring_run_exact >>
  disch_then (qspecl_then [`s`, `sw`, `dw`, `len`] mp_tac) >>
  simp[venomStateTheory.eval_operand_def] >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule compile_store_bytestring_body_mem_ok >> goal_assum (drule_at Any) >>
     qexistsl_tac [`dw`, `Var xd`, `Var xs`] >>
     simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `n = 32 + 32 * ((len+31) DIV 32)` by
    simp[GSYM vfmConstantsTheory.word_size_def] >>
  drule_all (Q.SPECL [`lo`, `explicit`, `ctx`, `func`, `PG`]
    compile_store_bytestring_origin_ptr_path) >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `sf = t` by fs[] >> qpat_x_assum `sf = t` SUBST_ALL_TAC >>
  qexistsl_tac [`t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)`, `Gf`, `tnf`] >>
  simp[] >>
  conj_tac >- suspend "runtime_frame" >>
  conj_tac >- gvs[venomStateTheory.venom_state_component_equality] >>
  conj_tac >- gvs[venomStateTheory.venom_state_component_equality, same_blocks_def] >>
  conj_tac >- suspend "runtime_taint_frame" >>
  suspend "runtime_value"
QED

Resume log_full_bytes_store_runtime_path[runtime_frame]:
  simp[typed_copy_state_frame_def] >> conj_tac
  >- gvs[venomStateTheory.venom_state_component_equality] >>
  conj_tac >- gvs[venomStateTheory.lookup_var_def] >>
  simp[typed_copy_frame_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule valueCopyTheory.mem_bytes_at_mcopy_disjoint >>
      gvs[vfmConstantsTheory.word_size_def] >> decide_tac) >>
  simp[venomExecSemanticsTheory.mcopy_def,
       immutableMemoryFrameTheory.immutable_write_memory_capacity,
       arithmeticTheory.MAX_DEF]
QED
Resume log_full_bytes_store_runtime_path[runtime_taint_frame]:
  rpt strip_tac >>
  `~(w2n dw <= i /\ i < w2n dw + n)` by decide_tac >>
  simp[] >> eq_tac >- (strip_tac >> fs[] >> decide_tac) >> simp[]
QED
Resume log_full_bytes_store_runtime_path[runtime_value]:
  `!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
    val_in_memory stv v (w2n dw) mem` by
    (rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `n`, `w2n sw`, `tn.t_mem`, `tnf.t_mem`] >>
     simp[valueEncodingPropsTheory.mcopy_mem_bytes_at_same]) >>
  rpt strip_tac >> irule bytestring_val_in_memory_transfer >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`sty`, `dty`, `tenv`, `stv`] >> simp[] >>
  first_x_assum irule >> gvs[vfmConstantsTheory.word_size_def]
QED
Finalise log_full_bytes_store_runtime_path

(* Structural packing is independent of the concrete source packet.  The
   interfaces expose precisely its framing, field execution and layout facts. *)
Theorem compile_log_frag_full:
  !cx id args DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    body_exprs_full_ok cx args /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\ supported_stmt tops bindings (Log id args) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Log id args) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Log id args) = SOME env' /\
    stmt_exprs_ok cenv (Log id args) /\
    call_evaluation_safe cx (int_calls_stmt (Log id args)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Log id args))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Log id args)))
      (eval_stmt cx (Log id args)) es
Proof
  rpt gen_tac >> strip_tac >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  `supported_log tops id args` by
    (qpat_assum `supported_stmt tops bindings (Log id args)` mp_tac >>
     simp_tac bool_ss [supported_stmt_def]) >>
  `?fields. supported_event_fields tops id = SOME fields` by
    (Cases_on `supported_event_fields tops id` >> fs[supported_log_def]) >>
  `supported_pure_exprs tops args /\
   LIST_REL (\e ((name,dty),indexed).
     event_arg_compatible dty (expr_type e)) args fields` by
    gvs[supported_log_def, AllCaseEqs()] >>
  `well_typed_exprs env args` by
    fs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()] >>
  `alloc_limits_exprs cenv args /\ log_alloc_ok cenv id args` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `!name ty. FLOOKUP env.var_types name = SOME ty ==>
     ?p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz)` by
    fs[expr_sim_inv_def] >>
  `supported_stmt tops [] (Log id args)` by simp[supported_stmt_def] >>
  `body_stmt_safe tops (Log id args)` by metis_tac[supported_stmt_body_safe] >>
  `EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) args` by
    (fs[body_stmt_safe_log_args, EVERY_CONJ] >>
     rw[EVERY_MEM] >> irule alloc_limits_expr_not_extcode >>
     metis_tac[exprSimSourceTheory.alloc_limits_exprs_mem]) >>
  `~supported_exprs_exists
      (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) args /\
   call_evaluation_safe cx (int_calls_exprs args) /\
   (!target. supported_exprs_exists (expr_abi_decode_target_root target) args ==>
      occurs_abi_decode_target target tops)` by
    fs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
       int_calls_stmt_def, AllCaseEqs()] >>
  `!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
     expr_body_pre cenv cx env e st` by
    (irule body_log_snapshot_expr_pre >> metis_tac[]) >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  `cenv' = cenv /\ compile_stmt cenv lctx ret_ty (Log id args) sa = ((),sb)` by
    (qpat_x_assum `stmt_env cenv lctx ret_ty (Log id args) sa = _` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[]) >>
  `compile_stmt cenv lctx ret_ty (Log id (MAP gas_shadow_expr args)) shadow_sa =
     ((),shadow_sb)` by
    (qpat_x_assum `stmt_env cenv lctx ret_ty (gas_shadow_stmt (Log id args)) _ = _` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, gas_shadow_stmt_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[]) >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
        fs[storage_trace_domain_def] >>
      `gas_admissible (eval_exprs cx args)
         (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception)) es` by
        (irule log_arguments_admissible >>
         qexistsl_tac [`id`,`lctx`] >> first_assum ACCEPT_TAC) >>
      `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
        fs[ret_pc_ok_def] >>
      `?h. cenv.ce_event_info (nsid_to_string id) =
              SOME (h, MAP (SND o FST) fields, MAP SND fields) /\
           lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id =
              SOME (h, MAP (SND o FST) fields, MAP SND fields) /\
           LENGTH (FILTER I (MAP SND fields)) <= 3 /\
           EVERY (\f. if SND f then supported_event_leaf_type (SND (FST f))
                       else supported_nested_type supported_event_leaf_type (LENGTH tops) tops (SND (FST f))) fields` by
        (qspecl_then [`tops`,`ctx`,`cenv`,`cx`,`id`,`fields`] mp_tac
           bodySimLogArgsTheory.body_log_aggregate_metadata >>
         impl_tac >- simp[] >> disch_then ACCEPT_TAC) >>
      drule_all_then strip_assume_tac log_full_snapshot_cuts >>
      mp_tac (Q.INST [`xs` |-> `args`,`kw_es` |-> `[]`,`svs` |-> `saved`,
        `sb` |-> `sm`,`shadow_sb` |-> `shadow_sm`]
        (SPEC_ALL extcall_request_positional_packing_outcome)) >>
      impl_tac >- asm_rewrite_tac [MAP] >>
      disch_tac >>
      qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ captureQ captureR` >>
      qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
        qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
          irule (MATCH_MP gas_outcome_full_use_return_buf_allocas (CONJ frame sep)))) >>
      rewrite_tac[log_eval_bind] >>
      irule gas_outcome_full_bind_all >> rpt conj_tac
      >~ [`gas_marked_exec _ _ _ _ _ _ _`]
      >- (rpt strip_tac >> irule gas_exempt_cert_bind_values >>
          qexistsl_tac [`mid`, `t`, `v`] >> RULE_ASSUM_TAC BETA_RULE >>
          BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC)
      >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
      >- (rpt strip_tac >> irule gas_exempt_cert_error_values >> simp[])
      >~ [`storage_trace_frame (eval_exprs _ _)`]
      >- simp[evaluate_storage_trace_frame]
      >~ [`storage_trace_frame _`]
      >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
          simp[storage_trace_frame_lifts] >> gen_tac >>
          irule storage_trace_frame_ignore_bind >>
          simp[storage_trace_frame_check_not_static, storage_trace_frame_state_updates]) >>
      qexists_tac `\H res ee G tn t.
        captureQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
      reverse conj_tac
      >- (irule gas_outcome_full_post_source >>
          qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
          conj_tac >- simp[] >> simp[Abbr `captureR`] >>
          rpt strip_tac >> Cases_on `res` >- fs[expr_exit_def] >>
          simp[stmt_exit_ptr_def] >>
          gvs[stmtSimPropsTheory.expr_exit_INR_type, halt_exit_def]) >>
      suspend "selected_capture") >>
  irule gas_outcome_full_bad_intro >>
  qexistsl_tac [`storage_trace_horizon es.storage_trace`, `func`, `G0`,
                `PG`, `tn0`, `[]`, `s0`] >>
  simp[gas_origin_ptr_focus_nil] >> irule gas_bad_storage_at_initial >>
  simp[evaluate_storage_trace_frame]
QED

Resume compile_log_frag_full[selected_capture]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
  BETA_TAC >> strip_tac >>
  qunabbrev_tac `captureQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> disch_then (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `vs` >> simp[] >>
  `LENGTH args = LENGTH fields /\ LENGTH args = LENGTH vs` by
    metis_tac[LIST_REL_LENGTH, LENGTH_ZIP, LENGTH_MAP] >>

`EVERY (\e. expr_body_pre cenv cx env e es) args` by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  `eval_exprs cx args (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL vs,mid)` by
    (qpat_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[evaluation_state_component_equality]) >>
  `LIST_REL (\e v. value_runtime_typed env (lowered_value_type cenv e) v) args vs` by
    (match_mp_tac (Q.INST [`ce` |-> `cenv`,`cx` |-> `cx`,`env` |-> `env`]
       (Q.SPECL [`args`,`es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                 `vs`,`mid`] eval_exprs_physical_runtime_typed)) >>
     simp[exprSimSourceTheory.expr_body_pre_gas_obs] >> rpt gen_tac >> strip_tac >>
     qspecl_then [`cenv`,`e`,`env`,`cx`,`st`,`v`,`st'`] match_mp_tac
       memory_rhs_read_lowered_typed_unwidened >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >>
     RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  qabbrev_tac `atys = MAP (lowered_value_type cenv) args` >>
  qabbrev_tac `dtys = MAP (SND o FST) (fields : ((string # type) # bool) list)` >>
  qabbrev_tac `flags = MAP SND (fields : ((string # type) # bool) list)` >>
  qabbrev_tac `rows = ZIP (saved,atys)` >>
  `LENGTH flags = LENGTH rows /\ LENGTH dtys = LENGTH atys /\ LENGTH atys = LENGTH vs` by
    simp[Abbr `flags`, Abbr `dtys`, Abbr `atys`, Abbr `rows`, LENGTH_ZIP] >>
  `MAP SND rows = atys` by
    (simp[Abbr `rows`, MAP_ZIP] >> simp[Abbr `atys`]) >>
  `LIST_REL event_arg_compatible dtys atys` by
    (simp_tac bool_ss [Abbr `atys`, Abbr `dtys`] >>
     match_mp_tac (Q.SPECL [`args`,`MAP (SND o FST) fields`,`env`,`cx`,`es`,`cenv`]
       checked_exprs_event_arg_compatible) >>
     fs[GSYM event_fields_expr_compatibility, expr_sim_inv_def]) >>
  `EVERY (\(ty,indexed). indexed ==> supported_event_leaf_type ty) (ZIP (dtys,flags))` by
    (simp[Abbr `flags`, Abbr `dtys`, EVERY_EL, EL_ZIP, EL_MAP, LENGTH_ZIP] >>
     fs[EVERY_EL] >> metis_tac[]) >>
  `LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v)
    atys vs` by fs[Abbr `atys`, LIST_REL_EL_EQN, EL_MAP, value_runtime_typed_def] >>
  `EVERY (type_alloc_ok cenv) atys /\
   SUM (MAP (type_memory_bytes cenv) (log_non_indexed_types flags dtys)) < 2**64 /\
   abi_size_bound cenv.ce_struct_fields (TupleT (log_non_indexed_types flags atys)) < 2**64` by
    fs[log_alloc_ok_def, Abbr `atys`, Abbr `dtys`, Abbr `flags`] >>
  `EVERY (supported_nested_type supported_event_leaf_type (LENGTH tops) tops)
    (log_non_indexed_types flags dtys)` by
    (`LIST_REL (\ty f. supported_nested_type supported_event_leaf_type (LENGTH tops) tops ty)
       (log_non_indexed_types flags dtys) (select_log_args F flags fields)` by
      (simp_tac bool_ss [Abbr `dtys`, Abbr `flags`, log_non_indexed_types_select] >>
       irule select_log_args_rel >> simp[] >>
       simp[LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >> rpt strip_tac >>
       qpat_assum `EVERY (\f. if SND f then _ else _) fields`
         (mp_tac o Q.SPEC `n` o REWRITE_RULE [EVERY_EL]) >> simp[]) >>
     fs[LIST_REL_EL_EQN, EVERY_EL]) >>
  drule_all log_full_physical_source_encoding >>
  disch_then (qx_choosel_then [`topics`,`avs`] strip_assume_tac) >>
  `LIST_REL (log_saved_row cenv cx st0 mid sa sm t G1 tn1) rows vs` by
    (simp[LIST_REL_EL_EQN] >> qx_gen_tac `i` >> strip_tac >>
     `i < LENGTH saved /\ i < LENGTH args` by fs[Abbr `rows`,Abbr `atys`,LENGTH_ZIP] >>
     `EL i rows = (EL i saved,lowered_value_type cenv (EL i args))` by
       simp[Abbr `rows`,Abbr `atys`,EL_ZIP,EL_MAP] >>
     `EL i (ZIP (args,saved)) = (EL i args,EL i saved)` by simp[EL_ZIP] >>
     qpat_assum `LIST_REL _ (ZIP (args,saved)) vs`
       (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     impl_tac >- simp[LENGTH_ZIP] >> simp[] >>
     disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     qpat_x_assum `?si. _` (qx_choosel_then [`si`,`sm0`,`ss`,`vv`,`raw`,`copy`] strip_assume_tac) >>
     `expr_body_pre cenv cx env (EL i args) es /\
      type_alloc_ok cenv (lowered_value_type cenv (EL i args)) /\
      value_runtime_typed env (lowered_value_type cenv (EL i args)) (EL i vs)` by
       fs[EVERY_EL,LIST_REL_EL_EQN,Abbr `atys`,EL_MAP] >>
     drule_all log_capture_type >>
     disch_then (strip_assume_tac o CONV_RULE (DEPTH_CONV BETA_CONV)) >>
     simp[log_saved_row_def] >>
     qexistsl_tac [`EL i args`,`si`,`sm0`,`ss`,`vv`,`raw`,`copy`,`tv`] >>
     asm_rewrite_tac[] >> conj_tac
     >- (gen_tac >> disch_tac >>
         qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
           (qspec_then `H` (drule_then (strip_assume_tac o BETA_RULE))) >>
         gvs[] >>
         qpat_assum `LIST_REL _ (ZIP (args,saved)) vs`
           (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
         simp[LENGTH_ZIP]) >>
     Cases_on `EL i saved` >> fs[vv_operand_def]) >>
  `LIST_REL (\(flag,row) v. flag ==>
       supported_event_leaf_type (SND row) /\ log_saved_row cenv cx st0 mid sa sm t G1 tn1 row v)
     (ZIP (flags,rows)) vs` by
    (simp[LIST_REL_EL_EQN, LENGTH_ZIP, EL_ZIP] >> rpt strip_tac
     >- (qpat_assum `EVERY (\(ty,indexed). _) (ZIP (dtys,flags))`
           (mp_tac o Q.SPEC `n` o REWRITE_RULE [EVERY_EL]) >>
         qpat_assum `LIST_REL event_arg_compatible dtys atys`
           (mp_tac o Q.SPEC `n` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
         qpat_assum `MAP SND rows = atys` (mp_tac o Q.AP_TERM `EL n`) >>
         simp[LENGTH_ZIP,EL_ZIP,EL_MAP] >> metis_tac[event_leaf_arg_compatible]) >>
     fs[LIST_REL_EL_EQN]) >>
  `LIST_REL (\(sv,hashed) topic.
      ?ty v. hashed = is_bytestring_type ty /\
        supported_event_leaf_type ty /\ log_saved_row cenv cx st0 mid sa sm t G1 tn1 (sv,ty) v /\
        encode_event_topic ty v = SOME topic) (FST (split_log_ops rows flags)) topics` by
    (qspecl_then [`flags`,`rows`,`vs`,`topics`] mp_tac split_log_ops_indexed_rel >>
     simp[]) >>
  suspend "selected_topics"
QED

Resume compile_log_frag_full[selected_topics]:
  qpat_assum `compile_stmt cenv lctx ret_ty (Log id args) sa = ((),sb)`
    (mp_then (Pat `compile_stmt _ _ _ _ _ = _`) mp_tac compile_log_stmt_trace) >>
  impl_tac >- simp[Abbr `dtys`, Abbr `flags`] >>
  simp_tac bool_ss [LET_THM,pairTheory.ELIM_UNCURRY] >>
  disch_then (qx_choosel_then [`saved0`,`sm0`,`ops`,`se`]
    (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `saved0 = saved /\ sm0 = sm` by metis_tac[] >>
  qpat_x_assum `saved0 = saved` SUBST_ALL_TAC >>
  qpat_x_assum `sm0 = sm` SUBST_ALL_TAC >>
  qpat_assum `Abbrev (atys = _)`
    (RULE_ASSUM_TAC o REWRITE_RULE o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qabbrev_tac `data_rows = SND (split_log_ops rows flags)` >>
  qabbrev_tac `raw_topics = FST (split_log_ops rows flags)` >>
  qpat_assum `Abbrev (rows = _)`
    (RULE_ASSUM_TAC o REWRITE_RULE o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (raw_topics = _)`
    (RULE_ASSUM_TAC o REWRITE_RULE o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (data_rows = _)`
    (RULE_ASSUM_TAC o REWRITE_RULE o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qabbrev_tac `all_ops = Lit (n2w h)::ops` >>
  qabbrev_tac `log_ev = <|logger := cx.txn.target; topics := n2w h::topics;
    data := enc (Tuple (vyper_to_abi_types (get_tenv cx) (log_non_indexed_types flags atys)))
      (ListV avs)|>` >>
  `ci_mono sa sm` by
    (qpat_assum `compile_ext_call_args _ _ _ _ _ sa = _`
      (fn eq => SUBST1_TAC (SYM (SIMP_RULE (srw_ss()) [] (Q.AP_TERM `SND` eq)))) >>
     irule ci_mono_compile_ext_call_args >> simp[cj 1 compile_expr_ci_mono]) >>
  `ci_mono sm se /\ fn_has_code sm se func /\ fn_has_code se sb func` by
    (qpat_assum `(_ /\ emit_inst LOG _ _ _ = _) \/ _`
       (DISJ_CASES_THEN strip_assume_tac) >>
     imp_res_tac compile_alloc_buffer_extends >> imp_res_tac emit_inst_extends >>
     `ci_mono sm se` by
       (qpat_assum `compile_log_saved_topics _ _ sm = _`
         (fn code => ACCEPT_TAC (SIMP_RULE bool_ss [code, pairTheory.SND]
           (Q.SPECL [`raw_topics`,`cenv`,`sm`] compile_log_saved_topics_ci_mono)))) >>
     fs[ci_mono_def] >>
     metis_tac[compile_abi_encode_values_to_buf_labels, fn_has_code_split, cs_extends_trans, pairTheory.SND]) >>
  `local_ptrs_reserved cenv sm /\ sa.cs_next_id <= sm.cs_next_id /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var, not_fresh_at_mono]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\ storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` (drule_then (strip_assume_tac o BETA_RULE))) >> gvs[]) >>
  `log_topic_state ctx func cenv cx st0 mid DF lo d sm t G1 tn1 sm t G1 tn1` by
    simp[log_topic_state_def, wb_frame_refl, ghost_kept_at_refl] >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
      `P` |-> `log_topic_state ctx func cenv cx st0 mid DF lo d sm t G1 tn1`,
      `R` |-> `(\(sv,hashed) topic. ?ty v. hashed = is_bytestring_type ty /\
         supported_event_leaf_type ty /\ log_saved_row cenv cx st0 mid sa sm t G1 tn1 (sv,ty) v /\
         encode_event_topic ty v = SOME topic)`]
    (SPEC_ALL compile_log_saved_topics_run)) >> BETA_TAC >>
  impl_tac >-
    (ntac 2 gen_tac >> rename1 `compile_log_saved_topics cenv [row] _ = _` >>
     PairCases_on `row` >> rpt gen_tac >>
     simp_tac bool_ss [pairTheory.ELIM_UNCURRY] >> strip_tac >> gvs[] >>
     irule compile_log_one_saved_topic >>
     qexistsl_tac [`env`,`t`,`row0`,`sm`,`G1`,`sa`,`tn1`,`tops`,`ty`,`v`] >>
     simp[] >> metis_tac[]) >>
  disch_then (qspecl_then [`raw_topics`,`topics`,`sm`,`se`,`ops`,`t`,`G1`,`tn1`] mp_tac) >>
  impl_tac >- simp[Abbr `raw_topics`] >>
  disch_then (qx_choosel_then [`tp`,`Gp`,`tnp`] strip_assume_tac) >>
  `LENGTH all_ops < dimword (:256)` by
    (imp_res_tac LIST_REL_LENGTH >>
     `LENGTH raw_topics = LENGTH (FILTER I flags)` by
       simp[Abbr `raw_topics`, split_log_ops_lengths] >>
     fs[Abbr `all_ops`, Abbr `flags`, wordsTheory.dimword_def] >> decide_tac) >>
  `LIST_REL (\op w. safe_operand se op /\ eval_operand op tp = SOME w /\
     op_taint tnp op = {}) all_ops (n2w h::topics)` by
    simp[Abbr `all_ops`, eval_operand_def, op_taint_def] >>
  drule log_topics_values >> strip_tac >>
  suspend "selected_data"
QED

Resume compile_log_frag_full[selected_data]:
  `MAP SND data_rows = log_non_indexed_types flags atys` by
    simp[Abbr `data_rows`, split_log_ops_data_types] >>
  `LIST_REL (log_saved_row cenv cx st0 mid sa sm t G1 tn1)
      data_rows (log_non_indexed_values flags vs)` by
    (irule split_log_ops_data_rel >> qexists_tac `rows` >> simp[Abbr `data_rows`]) >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by metis_tac[] >>
  qpat_assum `log_topic_state ctx func cenv cx st0 mid DF lo d sm t G1 tn1 se tp Gp tnp`
    (strip_assume_tac o REWRITE_RULE [log_topic_state_def]) >>
  `wb_frame cenv es mid sa s0 tp` by
    (mp_tac (Q.INST [`H` |-> `storage_trace_horizon es.storage_trace`] (Q.SPECL
       [`func`,`cenv`,`cx`,`es`,`s0`,`sa`,`mid`,`mid`,`sm`,`t`,`tp`,`ctx`] wb_frame_trans)) >>
     fs[ci_mono_def]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gp tnp` by
    (qspecl_then [`lo`,`cenv`,`es`,`sa`,`G0`,`tn0`,`s0`,`G1`,`tn1`,`mid`,`sm`,`Gp`,`tnp`,
        `t`,`storage_trace_horizon es.storage_trace`,`ctx`,`func`,`cx`,`mid`]
       mp_tac ghost_kept_at_wb_trans >> fs[ci_mono_def]) >>
  `sa.cs_next_var <= se.cs_next_var /\ s0.vs_alloca_next <= tp.vs_alloca_next` by
    (fs[ci_mono_def] >> decide_tac) >>
  qpat_x_assum `(data_rows = [] /\ _) \/ _`
    (DISJ_CASES_THEN2 strip_assume_tac (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`buf`,`alloc_end`,`len`,`enc_end`] strip_assume_tac)))
  >- (qpat_x_assum `data_rows = []` SUBST_ALL_TAC >> fs[] >>
      `avs = []` by fs[Once vyper_to_abi_def] >>
      `log_ev.data = []` by simp[Abbr `log_ev`, enc_def] >>
      mp_tac (Q.INST [`u` |-> `tp`,`G` |-> `G1`,`tn` |-> `tn1`,`Gu` |-> `Gp`,`tu` |-> `tnp`,
        `ce` |-> `cenv`,`send` |-> `se`,`ev` |-> `log_ev`,
        `ops` |-> `all_ops`,`topics` |-> `n2w h::topics`,
        `off` |-> `0w:bytes32`,`len` |-> `0w:bytes32`,`len_op` |-> `Lit 0w`,`ptr_op` |-> `Lit 0w`,
        `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
        `H0` |-> `storage_trace_horizon es.storage_trace`]
        (SPEC_ALL log_full_emit_outcome)) >>
      impl_tac >-
        (asm_simp_tac (srw_ss()) [Abbr `all_ops`, Abbr `log_ev`,
           eval_operand_def, op_taint_def, EVERY_MEM] >> metis_tac[]) >>
      disch_then ACCEPT_TAC) >>
  suspend "direct_data"
QED

Resume compile_log_frag_full[direct_data]:
  qabbrev_tac `dvs = log_non_indexed_values flags vs` >>
  qabbrev_tac `ats = vyper_to_abi_types (get_tenv cx) (MAP SND data_rows)` >>
  qabbrev_tac `bytes = log_ev.data` >>
  qabbrev_tac `capacity = abi_size_bound cenv.ce_struct_fields (TupleT (MAP SND data_rows))` >>
  `bytes = enc (Tuple ats) (ListV avs)` by simp[Abbr `bytes`, Abbr `log_ev`, Abbr `ats`] >>
  `capacity < dimword (:256)` by
    (irule vyperArithTheory.lt_dimword_256 >> qexists_tac `64` >> simp[Abbr `capacity`]) >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by fs[expr_sim_inv_def] >>
  mp_tac (Q.INST [`rows` |-> `data_rows`,`vs` |-> `dvs`,`es` |-> `mid`,
    `s` |-> `t`,`G` |-> `G1`,`tn` |-> `tn1`,`front` |-> `sm`]
    (SPEC_ALL log_saved_data_layout)) >>
  impl_tac >- simp[Abbr `ats`, Abbr `dvs`] >>
  qpat_assum `Abbrev (capacity = _)`
    (rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  strip_tac >>
  `ci_mono se alloc_end /\ ci_mono alloc_end enc_end /\ ci_mono enc_end sb` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_abi_encode_values_to_buf,
      ci_mono_emit_inst, pairTheory.SND] >>
  `fn_has_code se alloc_end func /\ fn_has_code alloc_end enc_end func /\
    fn_has_code enc_end sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `local_ptrs_reserved cenv se /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x)` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var, not_fresh_at_mono]) >>
  mp_tac (Q.INST [`n` |-> `capacity`,`a` |-> `se`,`b` |-> `alloc_end`,
    `es` |-> `mid`,`s` |-> `tp`,`G` |-> `Gp`,`tn` |-> `tnp`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (SPEC_ALL log_data_buffer)) >>
  impl_tac >- (simp[Abbr `capacity`] >> metis_tac[]) >>
  disch_then (qx_choosel_then [`p`,`w`,`u`,`Gu`,`tu`,`inst`] strip_assume_tac) >>
  suspend "direct_rows"
QED

Theorem body_log_aggregate_full:
  !cx id args fields DF lo d PG tops ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    body_exprs_full_ok cx args /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    supported_log tops id args /\
    supported_event_fields tops id = SOME fields /\
    ~EVERY supported_scalar_type (MAP (SND o FST) fields) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Log id args) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Log id args) = SOME env' /\
    stmt_exprs_ok cenv (Log id args) /\
    call_evaluation_safe cx (int_calls_stmt (Log id args)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Log id args))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Log id args)))
      (eval_stmt cx (Log id args)) es
Proof
  rpt gen_tac >> strip_tac >>
  irule compile_log_frag_full >>
  asm_simp_tac bool_ss [] >> conj_tac >-
    (qexistsl_tac [`[]`, `tops`] >>
     asm_simp_tac bool_ss [supported_stmt_def]) >>
  qexistsl_tac [`env`, `env'`] >> asm_simp_tac bool_ss []
QED
