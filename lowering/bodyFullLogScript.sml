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
Ancestors
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  loweringPosts vyperInterpreter vyperTypeSystem vyperState vyperAST list
  bodyExprPreFacts allocLimits allocLimitsProps exprSimSource vyperTypeCallGraph
  bodyFullLogArgs bodyFullLogScalarTopics bodyFullLogSuffix
  abiEncoderSourceRobust supportedStmtTraverse
  bodySimLogArgs stmtSimLogTrace exprSimHyps whitelistLogWiden
  supportedExprs supportedExprTraverse
  vyperTypeCallStackSoundness vyperTypeExprSoundness vyperTypeInvariants
  stmtLowering context compileEnv gasShadowState gasShadowCompileStmtHelpers
  gasOutcomeFullCompose gasStorage vyperStorageTrace vyperStorageFootprint
  logComposeFacts gasExemptCert exprSimDefs stmtSimDefs bodyPtrDefs
  eventLogSplitProps vyperEventArgCompat vyperTypeArgFits
  abiLogSourceEncoding typedLogSplitComplete stmtSimLogSource vyperTypeABI
  vyperEventCompatibility vyperEvent vyperABI supportedTypes e2eDefs vyperTypeContract
  stmtSimLogSuffix stmtSimLogSuffixActual eventLoweringStructure
  bodyPtrSubscriptSeamTupleLayoutBridge structFieldsProps typedCopyCompatibility typedLogSplitArgs
  exprLoweringProps loweringStateRelDefs gasOutcomeFull
  fragGasPathFrameMem bodyMemAggregatePath bodyFullAllocaFresh
  logStoreDataFieldsOriginPtr fragGasOriginPtr
  exprSimCopy exprSimAlloc typedMemoryCopy exprSimStorageCopy
  valueEncodingDefs vyperTypeDefaults valueEncodingProps
  robustCopyTransportPtr abiEncoderWindow abiTypeBoundProps decoderGhostFramePtr
  allocaSiteResource abiEncoderAdmissible abiEncoderWindowContract reasonCopySourcePtr
  abiEncoderWindowJoint
  exprSimAbiEncodeExecFrame
  exprSimAbiEncodeCallerFrame exprSimAbiEncodeFrameTransfer abiDecodeStaticProps
  exprSimAbiEncodeStateTransport
  bodyFullUnwrapSlotPost bodyInvNoDalloca
  logEmitStep logEmitPtr instMemFrontier venomInst venomExecSemantics
  ptrDiscipline ptrSafeRun emitHelper fragExec rich_list
  abiBuiltinAllocation abiEncoderAppend abiEncoderAllocationShape
  compilerInstructionSuffix emitHelperProps stmtLoweringMono loweringHalt abiEncoderProps
  bodyFullAllocGeneric bodyCopyMemoryBase valueCopy valueCopyBytes representationCleanPtr
  immutableMemoryFrame exprSimProps valueEncoding venomState tuplePlaceZero exprPtrUnwrapFacts stmtSimLogDataFrame placeMemoryTypeInterfaces memoryLocalRhsProps typedLogFieldChecked venomMemDefs bytesCopyProps vyperTyping

val _ = Parse.hide "body";
val irule_body_pre = bodyConstNameLib.irule_body_pre;

(* Exact declared-data compiler boundaries; no runtime registration is claimed. *)
Theorem log_full_declared_data_stage_code:
  cs_extends sm st /\
  compile_alloc_buffer cap st = (src,s1) /\
  compile_log_store_data ce xs dtys src.buf_operand 0 s1 = ((),s2) /\
  compile_alloc_buffer outcap s2 = (dst,s3) /\
  compile_abi_encode_to_buf dst.buf_operand src.buf_operand ei s3 = (len,s4) /\
  emit_inst LOG operands [] s4 = ((),sb) /\
  fn_has_code sm sb func ==>
  fn_has_code st s1 func /\ fn_has_code s1 s2 func /\
  fn_has_code s2 s3 func /\ fn_has_code s3 s4 func /\
  fn_has_code s4 sb func /\ cs_extends sm s3 /\ cs_extends s3 sb
Proof
  strip_tac >>
  imp_res_tac compile_alloc_buffer_extends >>
  `cs_extends s1 s2` by
    (mp_tac (cj 3 ci_mono_list_helpers) >>
     disch_then (qspecl_then [`ce`, `xs`, `dtys`, `src.buf_operand`, `0`, `s1`] mp_tac) >>
     simp[ci_mono_def]) >>
  drule cs_extends_abi_encode >> strip_tac >>
  drule emit_inst_extends >> strip_tac >>
  `cs_extends s4 sb` by
    (irule cs_extends_same_block >> simp[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]) >>
  `cs_extends sm s1` by (irule cs_extends_trans >> qexists_tac `st` >> simp[]) >>
  `cs_extends sm s2` by (irule cs_extends_trans >> qexists_tac `s1` >> simp[]) >>
  `cs_extends sm s3` by (irule cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  `cs_extends sm s4` by (irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  `cs_extends s3 sb` by (irule cs_extends_trans >> qexists_tac `s4` >> simp[]) >>
  `cs_extends s2 sb` by (irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  `cs_extends s1 sb` by (irule cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  rpt conj_tac >> metis_tac[fn_has_code_mid, cs_extends_refl]
QED

Theorem log_full_declared_data_allocation_sites:
  cs_extends sm st /\
  compile_alloc_buffer cap st = (src,s1) /\
  compile_log_store_data ce xs dtys src.buf_operand 0 s1 = ((),s2) /\
  compile_alloc_buffer outcap s2 = (dst,s3) /\
  compile_abi_encode_to_buf dst.buf_operand src.buf_operand ei s3 = (len,s4) /\
  emit_inst LOG operands [] s4 = ((),sb) /\
  fn_has_code sm sb func ==>
  src.buf_size = cap /\ dst.buf_size = outcap /\
  src.buf_operand = Var (STRING #"%" (toString st.cs_next_var)) /\
  dst.buf_operand = Var (STRING #"%" (toString s2.cs_next_var)) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w cap)]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst s2.cs_next_id ALLOCA [Lit (n2w outcap)]
    [STRING #"%" (toString s2.cs_next_var)]) (fn_insts func) /\
  st.cs_next_id < s2.cs_next_id /\ s2.cs_next_id < s3.cs_next_id
Proof
  strip_tac >> drule_all log_full_declared_data_stage_code >> strip_tac >>
  imp_res_tac log_buffer_trace_code >>
  imp_res_tac abi_builtin_alloc_buffer_shape >>
  imp_res_tac emitted_insts_emit_op >>
  mp_tac (cj 3 ci_mono_list_helpers) >>
  disch_then (qspecl_then [`ce`, `xs`, `dtys`, `src.buf_operand`, `0`, `s1`] mp_tac) >>
  simp[ci_mono_def] >> strip_tac >> simp[]
QED

Theorem log_full_declared_data_encoder_sites:
  cs_extends sm st /\
  compile_alloc_buffer cap st = (src,s1) /\
  compile_log_store_data ce xs dtys src.buf_operand 0 s1 = ((),s2) /\
  compile_alloc_buffer outcap s2 = (dst,s3) /\
  compile_abi_encode_to_buf dst.buf_operand src.buf_operand ei s3 = (len,s4) /\
  emit_inst LOG operands [] s4 = ((),sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func ==>
  st.cs_next_id NOTIN frag_ids s3 s4 /\
  s2.cs_next_id NOTIN frag_ids s3 s4 /\
  (!inst. MEM inst (fn_insts func) /\ inst.inst_id IN frag_ids s3 s4 /\
    inst.inst_opcode = ALLOCA ==>
    inst.inst_operands = [Lit 32w] /\
    ?q. inst.inst_outputs = [q] /\ ~not_fresh_at s3 q)
Proof
  strip_tac >>
  drule_all log_full_declared_data_stage_code >> strip_tac >>
  drule_all log_full_declared_data_allocation_sites >> strip_tac >>
  conj_tac >- simp[frag_ids_def] >>
  conj_tac >- simp[frag_ids_def] >>
  rpt strip_tac >>
  `ci_mono s3 s4 /\
   EVERY (\i. i.inst_opcode = ALLOCA ==> i.inst_operands = [Lit 32w] /\
     ?q. i.inst_outputs = [q] /\ ~not_fresh_at s3 q) (added_insts s3 s4)` by
    metis_tac[encoder_to_buf_allocation_shape, pairTheory.SND] >>
  `!id. id IN frag_ids s3 s4 ==>
    ?i. MEM i (added_insts s3 s4) /\ i.inst_id = id` by
    metis_tac[encoder_to_buf_id_coverage, pairTheory.SND] >>
  `cs_extends s3 s4` by fs[ci_mono_def] >>
  drule_all added_insts_function_property >> simp[]
QED

(* Indexed topics use compatible actual types; non-indexed data uses
   declared typing, so aggregate data does not require scalar support. *)
Theorem log_full_compatible_source_event_encoded:
  lookup_event_metadata tenv sources target id = SOME (h,dtys,flags) /\
  LENGTH flags = LENGTH dtys /\
  LIST_REL event_arg_compatible dtys ltys /\
  EVERY (\(ty,indexed). indexed ==> supported_scalar_type ty) (ZIP (dtys,flags)) /\
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
    EVERY (\(ty,indexed). indexed ==> supported_scalar_type ty) (ZIP (dtys,flags)) /\
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
     >- (`supported_scalar_type lty` by
           (Cases_on `dty` >> Cases_on `lty` >>
            gvs[supported_scalar_type_def, supported_word_type_def,
              supported_string_type_def, event_arg_compatible_def] >>
            rename1 `event_arg_compatible (BaseT db) (BaseT ab)` >>
            Cases_on `db` >> Cases_on `ab` >>
            gvs[supported_scalar_type_def, supported_word_type_def,
              supported_string_type_def, event_arg_compatible_def] >>
            rename1 `event_arg_compatible (BaseT (BytesT fb)) (BaseT (BytesT ab))` >>
            Cases_on `fb` >> Cases_on `ab` >>
            gvs[supported_scalar_type_def, supported_word_type_def,
              supported_string_type_def, event_arg_compatible_def]) >>
         `event_indexable_type dty` by
           (Cases_on `dty` >> gvs[supported_scalar_type_def,
             supported_word_type_def, supported_string_type_def, event_indexable_type_def]) >>
         drule_all event_arg_compatible_topic >> strip_tac >>
         drule_all log_scalar_topic_exists >> strip_tac >> simp[]) >>
     `?av. vyper_to_abi tenv dty v = SOME av` by
       metis_tac[cj 1 vyper_to_abi_total] >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  `LENGTH flags = LENGTH vals` by metis_tac[listTheory.LIST_REL_LENGTH] >>
  drule_all non_indexed_event_args_exists >> strip_tac >>
  simp[encode_source_event_def, encode_vyper_event_metadata_def] >> metis_tac[]
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
  s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
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
    (irule log_emit_access_taint >> simp[Abbr `inst`, mk_inst_def] >> gvs[] >> metis_tac[]) >>
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

(* Historical initial Log proof retained (inactive).
Proof
  rpt gen_tac >> strip_tac >>
  `supported_log tops id args` by
    (qpat_assum `supported_stmt tops bindings (Log id args)` mp_tac >>
     simp_tac bool_ss [supported_stmt_def]) >>
  `?fields. supported_event_fields tops id = SOME fields` by
    (Cases_on `supported_event_fields tops id` >>
     fs[supported_log_def]) >>
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
  `supported_stmt tops [] (Log id args)` by
    simp[supported_stmt_def] >>
  `body_stmt_safe tops (Log id args)` by
    metis_tac[supported_stmt_body_safe] >>
  `EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) args` by
    (fs[body_stmt_safe_log_args, EVERY_CONJ] >>
     rw[EVERY_MEM] >> irule alloc_limits_expr_not_extcode >>
     metis_tac[exprSimSourceTheory.alloc_limits_exprs_mem]) >>
  `EVERY (\e. ~expr_has_effect e) args` by
    (fs[supported_pure_exprs_every, EVERY_MEM] >>
     metis_tac[supported_pure_expr_effect_free]) >>
  `EVERY (\e. post_value_type cenv e = expr_type e) args` by
    (fs[supported_pure_exprs_every, EVERY_MEM] >> rpt strip_tac >>
     irule post_value_type_not_int_call >> rpt strip_tac >>
     qpat_x_assum `!e. MEM e args ==> supported_pure_expr tops e` drule >>
     simp[supported_pure_expr_def]) >>
  `~supported_exprs_exists
      (\e. ~is_extcode e /\
         ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) args /\
   call_evaluation_safe cx (int_calls_exprs args) /\
   (!target. supported_exprs_exists (expr_abi_decode_target_root target) args ==>
      occurs_abi_decode_target target tops)` by
    fs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
       int_calls_stmt_def, AllCaseEqs()] >>
  qabbrev_tac `RR = \tail ee.
    EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) tail /\
    body_exprs_full_ok cx tail /\ expr_sim_inv cenv cx env ee /\
    supported_pure_exprs tops tail /\ well_typed_exprs env tail /\
    ~supported_exprs_exists
      (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) tail /\
    call_evaluation_safe cx (int_calls_exprs tail) /\
    (!target. supported_exprs_exists (expr_abi_decode_target_root target) tail ==>
       occurs_abi_decode_target target tops)` >>
  `!e tail ee. RR (e::tail) ee ==>
     expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
       cenv cx (expr_type e) e ee /\
     !v ee1. bind (eval_expr cx e) (read_result cx) ee = (INL v, ee1) ==>
       RR tail ee1 /\
       ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
            value_has_type tv v` by
    (rpt gen_tac >> simp[Abbr `RR`] >> strip_tac >>
     qpat_x_assum `supported_pure_exprs _ _`
       (strip_assume_tac o SIMP_RULE std_ss [Once supported_pure_expr_def]) >>
     qpat_x_assum `well_typed_exprs _ _`
       (strip_assume_tac o SIMP_RULE std_ss [Once well_typed_expr_def]) >>
     qpat_x_assum `~supported_exprs_exists _ _`
       (strip_assume_tac o SIMP_RULE std_ss
         [Once supported_expr_exists_def, DE_MORGAN_THM]) >>
     qpat_x_assum `call_evaluation_safe _ _`
       (assume_tac o SIMP_RULE std_ss [Once int_calls_expr_def]) >>
     qpat_x_assum `!target. supported_exprs_exists _ _ ==> _`
       (strip_assume_tac o SIMP_RULE std_ss
         [Once supported_expr_exists_def, DISJ_IMP_THM, FORALL_AND_THM]) >>
     fs[body_exprs_full_ok_def] >>
     `call_evaluation_safe cx (int_calls_exprs tail)` by
       (irule call_evaluation_safe_append_right >>
        qexists_tac `int_calls_expr e` >> first_assum ACCEPT_TAC) >>
     `expr_body_pre cenv cx env e ee` by
       (qpat_assum `body_stmt_safe _ (Expr _)`
         (strip_assume_tac o SIMP_RULE std_ss
           [body_stmt_safe_def, supported_stmt_expr_exists_def,
            int_calls_stmt_def, EVERY_CONJ, GSYM expr_has_evm_run_def]) >>
        `supported_program tops /\ get_module_code cx NONE = SOME tops /\
         (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
           is_dynamic (vyper_to_abi_type (type_env tops) target))` by
          fs[body_inv_def] >>
        `cx_tops cx = tops` by simp[gasContextTheory.cx_tops_def] >>
        qspecl_then [`cenv`,`cx`,`env`,`e`,`ee`,`int_calls_exprs tail`]
          irule stmt_expr_body_pre >> simp[] >> metis_tac[]) >>
     conj_tac
     >- (qpat_x_assum `body_expr_full_ok cx e`
           (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
         disch_then (qspecl_then
           [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,`func`,`shadow_func`,
            `cenv`,`env`,`expr_type e`,`ee`] mp_tac) >>
         impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
         simp[]) >>
     rpt gen_tac >> strip_tac >>
     qspecl_then [`cenv`,`cx`,`env`,`e`,`ee`,`INL v`,`ee1`]
       mp_tac exprSimSourceTheory.expr_body_pre_eval >>
     impl_tac
     >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
         conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
     `body_exprs_full_ok cx tail` by
       (qpat_x_assum `(?s tv t s1 v t1. _) ==> _` irule >>
        qpat_x_assum `bind (eval_expr cx e) (read_result cx) ee = _` mp_tac >>
        simp[NoAsms, bind_def, AllCaseEqs()] >> metis_tac[]) >>
     simp[] >>
     fs[vyperTypeExprResultTheory.expr_result_typed_def, expr_runtime_typed_def,
        value_result_typed_def, value_runtime_typed_def] >>
     `env.type_defs = get_tenv cx` suffices_by metis_tac[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def]) >>
  `!tail ee gs. RR tail ee ==> RR tail (ee with gas_obs := gs)` by
    simp[Abbr `RR`] >>
  rewrite_tac[stmt_frag_full_def] >>
  rpt gen_tac >> strip_tac >>
  `cenv' = cenv /\ compile_stmt cenv lctx ret_ty (Log id args) sa = ((),sb)` by
    (qpat_x_assum `stmt_env cenv lctx ret_ty (Log id args) sa = _` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[]) >>
  `compile_stmt cenv lctx ret_ty (Log id (MAP gas_shadow_expr args)) shadow_sa =
     ((),shadow_sb)` by
    (qpat_x_assum `stmt_env cenv lctx ret_ty (gas_shadow_stmt (Log id args)) _ = _`
       mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, gas_shadow_stmt_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[]) >>
  Cases_on `compile_log_eval_all cenv args sa` >>
  rename1 `compile_log_eval_all cenv args sa = (ops,sm)` >>
  Cases_on `compile_log_eval_all cenv (MAP gas_shadow_expr args) shadow_sa` >>
  rename1 `compile_log_eval_all cenv (MAP gas_shadow_expr args) shadow_sa =
    (shadow_ops,shadow_sm)` >>
  `shadow_ops = ops /\ gas_shadow_state sm shadow_sm` by
    (qspecl_then [`sa`,`shadow_sa`] mp_tac
       (REWRITE_RULE [gas_shadow_compiles_def]
         (Q.SPEC `args` gas_shadow_compile_log_eval_all)) >>
     simp[] >> strip_tac >> simp[]) >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
         es.storage_trace` by fs[storage_trace_domain_def] >>
      `~cx.txn.is_static` by
        (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
           (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
         impl_tac >- first_assum ACCEPT_TAC >>
         simp[stmt_state_rel_def, state_rel_def]) >>
      `gas_admissible (eval_exprs cx args)
         (\r. !exc. r = INR exc ==>
           expr_res_ok (INR exc : value + exception)) es` by
        (irule log_arguments_admissible >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl_tac [`id`,`lctx`] >> first_assum ACCEPT_TAC) >>
      `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x` by fs[ret_pc_ok_def] >>
      `~exprs_can_mutate cenv args` by
        metis_tac[bodySimLogArgsTheory.supported_pure_expr_no_mutate] >>
      `?h. cenv.ce_event_info (nsid_to_string id) =
              SOME (h, MAP (SND o FST) fields, MAP SND fields) /\
           lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id =
              SOME (h, MAP (SND o FST) fields, MAP SND fields) /\
           LENGTH (FILTER I (MAP SND fields)) <= 3 /\
           EVERY (\f. if SND f then supported_scalar_type (SND (FST f))
                       else supported_place_type tops (SND (FST f))) fields` by
        (qspecl_then [`tops`,`ctx`,`cenv`,`cx`,`id`,`fields`] mp_tac
           bodySimLogArgsTheory.body_log_aggregate_metadata >>
         impl_tac >- simp[] >> disch_then ACCEPT_TAC) >>
      `fn_has_code sa sm func` by
        (mp_tac (Q.INST
          [`info` |-> `(h, MAP (SND o FST)
                        (fields : ((string # type) # bool) list), MAP SND fields)`,
           `ty` |-> `ret_ty`]
          (SPEC_ALL stmtSimLogTraceTheory.compile_log_eval_all_code)) >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
      `fn_has_code shadow_sa shadow_sm shadow_func` by
        (mp_tac (Q.INST
          [`info` |-> `(h, MAP (SND o FST)
                        (fields : ((string # type) # bool) list), MAP SND fields)`,
           `ty` |-> `ret_ty`, `args` |-> `MAP gas_shadow_expr args`,
           `ops` |-> `shadow_ops`,
           `sa` |-> `shadow_sa`, `sm` |-> `shadow_sm`,
           `sb` |-> `shadow_sb`, `func` |-> `shadow_func`]
          (SPEC_ALL stmtSimLogTraceTheory.compile_log_eval_all_code)) >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
      qspecl_then [`DF`,`lo`,`d`,`PG`,`ctx`,`shadow_ctx`,`func`,
                    `shadow_func`,`cenv`,`cx`,`st0`,`RR`,`env`] mp_tac
        compile_log_eval_all_full_store_bound >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (qspecl_then
        [`args`,`es`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`ops`,`s0`,`G0`,`tn0`]
        mp_tac) >>
      impl_tac >- (simp[Abbr `RR`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      strip_tac >>
      qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ captureQ captureR` >>
      qpat_assum `~cx.txn.is_static`
        (rewrite_tac o single o MATCH_MP eval_log_nonstatic_bind) >>
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
          simp[storage_trace_frame_lifts, storage_trace_frame_state_updates]) >>
      qexists_tac `\H res ee G tn t.
        captureQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
      reverse conj_tac
      >- (irule gas_outcome_full_post_source >>
          qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
          conj_tac >- simp[] >> simp[Abbr `captureR`] >>
          rpt strip_tac >> Cases_on `res` >- fs[expr_exit_def] >>
          simp[stmt_exit_ptr_def] >>
          metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
      suspend "selected_capture") >>
  irule gas_outcome_full_bad_intro >>
  qexistsl_tac [`storage_trace_horizon es.storage_trace`, `func`, `G0`,
                `PG`, `tn0`, `[]`, `s0`] >>
  simp[gas_origin_ptr_focus_nil] >>
  irule gas_bad_storage_at_initial >>
  simp[evaluate_storage_trace_frame]
QED
*)
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

(* Runtime coverage, not nominal source capacity, suffices for bytes stores. *)
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
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
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
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by simp[] >>
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
Theorem log_full_store_data_fold:
  !R.
  (!sa sb G tn s f dty dtv v w len t Gf tnf.
     R sa G tn s f dty dtv v /\
     ci_mono sa sb /\ typed_copy_state_frame sa w len s t /\
     w2n bw <= w /\ w + len <= w2n bw + cap /\
     (!i. ~(w <= i /\ i < w + len) ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
     (!q. not_fresh_at sa q ==>
       FLOOKUP Gf q = FLOOKUP G q /\ op_taint tnf (Var q) = op_taint tn (Var q)) ==>
     R sb Gf tnf t f dty dtv v) /\
  (!sa sb s G tn f dty dtv v off.
     compile_log_store_data cenv [f] [dty] (Var xb) off sa = ((),sb) /\
     R sa G tn s f dty dtv v /\
     acyclic_struct_metadata cenv.ce_struct_fields /\
     sfields_tenv_consistent cenv.ce_struct_fields tenv /\
     (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
         sz = type_memory_size tv) fields) /\
     not_fresh_at sa xb /\ lookup_var xb s = SOME bw /\
     ptr_covers G tn xb s cap /\ off + type_memory_size dtv <= cap /\
     w2n bw + cap < dimword (:256) /\ w2n bw + cap <= s.vs_alloca_next /\
     allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
     fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
     ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
     s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
     ?t Gf tnf.
       (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
       typed_copy_state_frame sa (w2n bw + off) (type_memory_size dtv) s t /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
       (!i. ~(w2n bw + off <= i /\ i < w2n bw + off + type_memory_size dtv) ==>
         (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
       (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
         val_in_memory dtv v (w2n bw + off) mem) /\
       (!p. not_fresh_at sa p ==>
         FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))) /\
  (!sa G tn s f dty dtv v.
     R sa G tn s f dty dtv v ==>
     type_memory_bytes cenv dty = type_memory_size dtv /\ val_wf dtv v) ==>
  !fs dtys dtvs vs off sa sb s G tn.
    compile_log_store_data cenv fs dtys (Var xb) off sa = ((),sb) /\
    LENGTH dtys = LENGTH fs /\ LENGTH dtvs = LENGTH fs /\ LENGTH vs = LENGTH fs /\
    (!i. i < LENGTH fs ==>
       R sa G tn s (EL i fs) (EL i dtys) (EL i dtvs) (EL i vs)) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
         sz = type_memory_size tv) fields) /\
    not_fresh_at sa xb /\ lookup_var xb s = SOME bw /\
    ptr_covers G tn xb s cap /\ off + type_memory_size_list dtvs <= cap /\
    w2n bw + cap < dimword (:256) /\ w2n bw + cap <= s.vs_alloca_next /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t Gf tnf.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
      typed_copy_state_frame sa (w2n bw + off) (type_memory_size_list dtvs) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!i. ~(w2n bw + off <= i /\ i < w2n bw + off + type_memory_size_list dtvs) ==>
           (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
             tuple_in_memory vs dtvs (w2n bw + off) mem) /\
      (!p. not_fresh_at sa p ==>
         FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  gen_tac >> strip_tac >>
  qpat_x_assum `!sa sb G tn s f dty dtv v w len t Gf tnf. _` (mk_asm "packet_frame") >>
  qpat_x_assum `!sa sb s G tn f dty dtv v off. _` (mk_asm "field_run") >>
  qpat_x_assum `!sa G tn s f dty dtv v. _` (mk_asm "packet_facts") >>
  Induct
  >- (rpt gen_tac >> strip_tac >> gvs[listTheory.LENGTH_NIL] >>
      gvs[compile_log_store_data_def, comp_return_def] >>
      qexistsl_tac [`s`, `G`, `tn`] >>
      simp[gas_origin_ptr_path_rules, val_in_memory_def]) >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  namedCases_on `dtys` ["", "dty dtys"] >> gvs[] >>
  namedCases_on `dtvs` ["", "dtv dtvs"] >> gvs[] >>
  namedCases_on `vs` ["", "v vs"] >> gvs[] >>
  rename1 `compile_log_store_data cenv (f::fs) (dty::dtys) _ _ _ = _` >>
  rename1 `tuple_in_memory (v::vs) (dtv::dtvs) _ _` >>
  qpat_x_assum `compile_log_store_data _ _ _ _ _ _ = _`
    (strip_assume_tac o ONCE_REWRITE_RULE [compile_log_store_data_split]) >>
  rename1 `compile_log_store_data cenv [f] [dty] _ off sa = ((),mid)` >>
  `R sa G tn s f dty dtv v` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `!i. i < LENGTH fs ==>
     R sa G tn s (EL i fs) (EL i dtys) (EL i dtvs) (EL i vs)` by
    (rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]) >>
  qpat_x_assum `!i. i < SUC _ ==> _` kall_tac >>
  suspend "field"
QED

Resume log_full_store_data_fold[field]:
  `type_memory_size_list (dtv::dtvs) =
     type_memory_size dtv + type_memory_size_list dtvs` by
    simp[type_memory_size_def] >>
  `ci_mono sa mid /\ ci_mono mid sb` by
    metis_tac[compile_log_store_data_ci_mono, pairTheory.SND] >>
  `fn_has_code sa mid func /\ fn_has_code mid sb func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `type_memory_bytes cenv dty = type_memory_size dtv /\ val_wf dtv v` by
    (asm "packet_facts" drule >> simp[]) >>
  asm "field_run" drule >> disch_then drule >>
  (* Normalize the shared-buffer no-wrap hypothesis together with the goal. *)
  (impl_tac >- (rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC, (gvs[wordsTheory.dimword_def] >> decide_tac)])) >>
  disch_then (qx_choosel_then [`t1`, `G1`, `tn1`] strip_assume_tac) >>
  `lookup_var xb t1 = SOME bw /\ t1.vs_allocas = s.vs_allocas /\
   t1.vs_alloca_next = s.vs_alloca_next` by
    gvs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `not_fresh_at mid xb` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, ci_mono_def] >>
  `ptr_covers G1 tn1 xb t1 cap` by (gvs[ptr_covers_def] >> metis_tac[]) >>
  `allocas_from lo t1` by
    (qpat_assum `allocas_from lo s` mp_tac >>
     pure_rewrite_tac [allocas_from_def] >> asm_rewrite_tac []) >>
  `!i. i < LENGTH fs ==>
     R mid G1 tn1 t1 (EL i fs) (EL i dtys) (EL i dtvs) (EL i vs)` by
    (rpt strip_tac >> asm "packet_frame" irule >>
     qexistsl_tac [`G`, `type_memory_size dtv`, `s`, `sa`, `tn`,
                   `w2n bw + off`] >>
     simp[] >> decide_tac) >>
  suspend "rest"
QED

Resume log_full_store_data_fold[rest]:
  qpat_x_assum `type_memory_bytes cenv dty = _` (fn eq =>
    RULE_ASSUM_TAC (REWRITE_RULE [eq]) >> assume_tac eq) >>
  first_x_assum (qspecl_then [`dtys`, `dtvs`, `vs`, `off + type_memory_size dtv`,
    `mid`, `sb`, `t1`, `G1`, `tn1`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC, (asm_simp_tac bool_ss [] >> decide_tac)])) >>
  disch_then (qx_choosel_then [`t2`, `G2`, `tn2`] strip_assume_tac) >>
  qexistsl_tac [`t2`, `G2`, `tn2`] >>
  conj_tac
  >- (gen_tac >>
      qpat_x_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
        (mp_tac o MATCH_MP gas_origin_ptr_path_append o Q.SPEC `D`) >>
      disch_then (qspecl_then [`t1`, `G1`, `tn1`, `[]`, `OK t2`, `G2`, `tn2`]
        mp_tac) >> simp[]) >>
  conj_tac
  >- (irule typed_copy_state_frame_trans >> qexists_tac `t1` >> conj_tac
      >- (irule typed_copy_state_frame_subinterval >>
          qexistsl_tac [`w2n bw + off`, `type_memory_size dtv`] >> simp[]) >>
      irule typed_copy_state_frame_subinterval >>
      qexistsl_tac [`w2n bw + (off + type_memory_size dtv)`,
                    `type_memory_size_list dtvs`] >> simp[] >>
      irule typed_copy_state_frame_mono >> qexists_tac `mid` >> simp[] >>
      qpat_x_assum `typed_copy_state_frame mid _ _ t1 _` mp_tac >> simp[]) >>
  ntac 6 (conj_tac >- simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!i. _ ==> (_ IN tn2.t_mem <=> _ IN tn1.t_mem)`
        (qspec_then `i` mp_tac) >>
      qpat_x_assum `!i. _ ==> (_ IN tn1.t_mem <=> _ IN tn.t_mem)`
        (qspec_then `i` mp_tac) >>
      simp[]) >>
  conj_tac >- suspend "tuple" >>
  rpt strip_tac >>
  `not_fresh_at mid p` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, ci_mono_def] >>
  simp[]
QED

Resume log_full_store_data_fold[tuple]:
  qpat_assum `val_wf dtv v`
    (assume_tac o MATCH_MP exprSimPropsTheory.val_footprint_le) >>
  `!mem. mem_agree_outside tn2.t_mem t2.vs_memory mem ==>
     val_in_memory dtv v (w2n bw + off) mem` by
    (rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`t1.vs_memory`, `t2.vs_memory`, `tn1.t_mem`, `tn2.t_mem`,
       `{i | w2n bw + (off + type_memory_size dtv) <= i /\
             i < w2n bw + (off + type_memory_size dtv) +
                 type_memory_size_list dtvs}`] >>
     simp[] >> gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  rpt strip_tac >> simp[Once val_in_memory_def] >>
  `w2n bw + (off + type_memory_size dtv) = w2n bw + off + type_memory_size dtv` by
    decide_tac >>
  gvs[]
QED

Finalise log_full_store_data_fold

(* Keep the mixed source packet explicit, without a new semantic judgment. *)
Theorem log_full_field_packet_frame:
    (\sa G tn s.
    log_field_src ce tenv b cap sa G tn s f dty dtv v \/
    (evaluate_type tenv dty = SOME dtv /\ value_has_type dtv v /\ val_wf dtv v /\
     type_memory_bytes ce dty = type_memory_size dtv /\
     (!x. FST f = Var x ==> not_fresh_at sa x) /\
     is_bytestring_type dty /\ is_bytestring_type (SND f) /\
     (?xs stv sw len n. FST f = Var xs /\
       evaluate_type tenv (SND f) = SOME stv /\ value_has_type stv v /\ val_wf stv v /\
       lookup_var xs s = SOME sw /\
       ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
        (?str. v = StringV str /\ len = LENGTH str)) /\
       n = 32 + 32 * word_size len /\ len + 31 < dimword(:256) /\
       n < dimword(:256) /\ n <= type_memory_size dtv /\
       w2n sw + n <= s.vs_alloca_next /\ ptr_covers G tn xs s n /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory stv v (w2n sw) mem) /\
       (!i. w2n sw <= i /\ i < w2n sw + val_footprint stv v ==>
          ~(b <= i /\ i < b + cap)))) \/
    (evaluate_type tenv dty = SOME dtv /\ value_has_type dtv v /\ val_wf dtv v /\
     type_memory_bytes ce dty = type_memory_size dtv /\ type_memory_size dtv = 0 /\
     (!x. FST f = Var x ==> not_fresh_at sa x) /\
     (!dst sc. compile_store_memory ce (FST f) dst dty (SND f) sc = ((),sc)) /\
     (!p mem. val_in_memory dtv v p mem))) sa G tn s /\ ci_mono sa sb /\ typed_copy_state_frame sa w len s t /\
    b <= w /\ w + len <= b + cap /\
    (!i. ~(w <= i /\ i < w+len) ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!q. not_fresh_at sa q ==>
      FLOOKUP Gf q = FLOOKUP G q /\ op_taint tnf (Var q) = op_taint tn (Var q)) ==>
    (\sa G tn s.
    log_field_src ce tenv b cap sa G tn s f dty dtv v \/
    (evaluate_type tenv dty = SOME dtv /\ value_has_type dtv v /\ val_wf dtv v /\
     type_memory_bytes ce dty = type_memory_size dtv /\
     (!x. FST f = Var x ==> not_fresh_at sa x) /\
     is_bytestring_type dty /\ is_bytestring_type (SND f) /\
     (?xs stv sw len n. FST f = Var xs /\
       evaluate_type tenv (SND f) = SOME stv /\ value_has_type stv v /\ val_wf stv v /\
       lookup_var xs s = SOME sw /\
       ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
        (?str. v = StringV str /\ len = LENGTH str)) /\
       n = 32 + 32 * word_size len /\ len + 31 < dimword(:256) /\
       n < dimword(:256) /\ n <= type_memory_size dtv /\
       w2n sw + n <= s.vs_alloca_next /\ ptr_covers G tn xs s n /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory stv v (w2n sw) mem) /\
       (!i. w2n sw <= i /\ i < w2n sw + val_footprint stv v ==>
          ~(b <= i /\ i < b + cap)))) \/
    (evaluate_type tenv dty = SOME dtv /\ value_has_type dtv v /\ val_wf dtv v /\
     type_memory_bytes ce dty = type_memory_size dtv /\ type_memory_size dtv = 0 /\
     (!x. FST f = Var x ==> not_fresh_at sa x) /\
     (!dst sc. compile_store_memory ce (FST f) dst dty (SND f) sc = ((),sc)) /\
     (!p mem. val_in_memory dtv v p mem))) sb Gf tnf t
Proof
  simp_tac bool_ss [LET_THM] >>
  disch_then (CONJUNCTS_THEN2
    (DISJ_CASES_THEN2 assume_tac (DISJ_CASES_THEN2 assume_tac assume_tac))
    (map_every assume_tac o CONJUNCTS))
  >- (disj1_tac >> metis_tac[log_field_src_frame])
  >- (disj2_tac >> disj1_tac >>
      qpat_x_assum `evaluate_type _ _ = _ /\ _` (map_every assume_tac o CONJUNCTS) >>
      qpat_x_assum `?xs stv sw len. _`
        (qx_choosel_then [`xs`, `stv`, `sw`, `sz`]
          (map_every assume_tac o CONJUNCTS)) >>
      `t.vs_alloca_next = s.vs_alloca_next` by
        gvs[typed_copy_state_frame_def, venomStateTheory.venom_state_component_equality] >>
      `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
        metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, ci_mono_def] >>
      `not_fresh_at sa xs` by metis_tac[] >>
      `lookup_var xs t = SOME sw` by gvs[typed_copy_state_frame_def] >>
      simp[] >> qexists_tac `sz` >> gnvs[] >>
      conj_tac >- (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
        goal_assum (drule_at Any) >> simp[]) >>
      match_mp_tac robust_val_in_memory_exterior_frame >>
      qexistsl_tac [`tn.t_mem`, `s.vs_memory`, `{i | w <= i /\ i < w+len}`] >>
      asm_simp_tac bool_ss [pred_setTheory.IN_GSPEC] >>
      conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!i. w2n sw <= i /\ _ ==> _` (qspec_then `i` mp_tac) >>
          gvs[]) >>
      conj_tac
      >- (gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
          rpt strip_tac >> first_x_assum irule >> decide_tac) >>
      simp[] >> first_assum ACCEPT_TAC)
  >> disj2_tac >> disj2_tac >> simp[] >>
  metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, ci_mono_def]
QED

Theorem log_full_data_field_runtime_path:
  compile_log_store_data cenv [f] [dty] (Var xb) off sa = ((),sb) /\
  (\sa G tn s.
    log_field_src cenv tenv (w2n bw) cap sa G tn s f dty dtv v \/
    (evaluate_type tenv dty = SOME dtv /\ value_has_type dtv v /\ val_wf dtv v /\
     type_memory_bytes cenv dty = type_memory_size dtv /\
     (!x. FST f = Var x ==> not_fresh_at sa x) /\
     is_bytestring_type dty /\ is_bytestring_type (SND f) /\
     (?xs stv sw len n. FST f = Var xs /\
       evaluate_type tenv (SND f) = SOME stv /\ value_has_type stv v /\ val_wf stv v /\
       lookup_var xs s = SOME sw /\
       ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
        (?str. v = StringV str /\ len = LENGTH str)) /\
       n = 32 + 32 * word_size len /\ len + 31 < dimword(:256) /\
       n < dimword(:256) /\ n <= type_memory_size dtv /\
       w2n sw + n <= s.vs_alloca_next /\ ptr_covers G tn xs s n /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory stv v (w2n sw) mem) /\
       (!i. w2n sw <= i /\ i < w2n sw + val_footprint stv v ==>
          ~(w2n bw <= i /\ i < w2n bw + cap)))) \/
    (evaluate_type tenv dty = SOME dtv /\ value_has_type dtv v /\ val_wf dtv v /\
     type_memory_bytes cenv dty = type_memory_size dtv /\ type_memory_size dtv = 0 /\
     (!x. FST f = Var x ==> not_fresh_at sa x) /\
     (!dst sc. compile_store_memory cenv (FST f) dst dty (SND f) sc = ((),sc)) /\
     (!p mem. val_in_memory dtv v p mem))) sa G tn s /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  not_fresh_at sa xb /\ lookup_var xb s = SOME bw /\
  ptr_covers G tn xb s cap /\ off + type_memory_size dtv <= cap /\
  w2n bw + cap < dimword (:256) /\ w2n bw + cap <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    typed_copy_state_frame sa (w2n bw + off) (type_memory_size dtv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n bw + off <= i /\ i < w2n bw + off + type_memory_size dtv) ==>
         (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
           val_in_memory dtv v (w2n bw + off) mem) /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  simp_tac bool_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_log_store_data _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_log_store_data_def, comp_bind_def, comp_ignore_bind_def,
       compile_log_store_data_def, comp_return_def] >>
  Cases_on `emit_op ADD [Var xb; Lit (n2w off)] sa` >>
  rename1 `emit_op ADD _ sa = (dst,s1)` >> simp[] >>
  Cases_on `compile_store_memory cenv (FST f) dst dty (SND f) s1` >>
  rename1 `compile_store_memory _ _ dst _ _ s1 = (u,s2)` >> simp[] >>
  strip_tac >> gnvs[] >>
  rename1 `compile_store_memory _ _ dst _ _ s1 = (_,sb)` >>
  suspend "address"
QED

Resume log_full_data_field_runtime_path[address]:
  `ci_mono sa s1` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono s1 sb` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `w2n bw + off < dimword (:256)` by (simp[] >> decide_tac) >>
  mp_tac (Q.SPECL [`xb`, `off`, `type_memory_size dtv`, `cap`, `sa`, `dst`,
    `s1`, `bw`, `lo`, `explicit`, `ctx`, `func`, `PG`, `s`, `G`, `tn`,
    `w2n (bw:bytes32) + off`, `type_memory_size dtv`]
    typedCopyOriginPtrFieldsTheory.typed_copy_origin_ptr_add_path) >>
  (impl_tac >- (rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC, (asm_simp_tac bool_ss [] >> decide_tac)])) >>
  disch_then (qx_choosel_then [`p`, `t1`, `G1`, `tn1`]
    (map_every assume_tac o CONJUNCTS)) >>
  gnvs[] >>
  `w2n (n2w (w2n (bw:bytes32) + off) : bytes32) = w2n bw + off` by
    (rewrite_tac [wordsTheory.w2n_n2w] >> irule arithmeticTheory.LESS_MOD >> simp[]) >>
  suspend "field_store"
QED

Resume log_full_data_field_runtime_path[field_store]:
  `?t2 G2 tn2.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t1,G1,tn1) [] (OK t2,G2,tn2)) /\
    typed_copy_state_frame s1 (w2n bw + off) (type_memory_size dtv) t1 t2 /\
    ~t2.vs_halted /\ t2.vs_current_bb = sb.cs_current_bb /\
    t2.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tn2.t_imm = tn1.t_imm /\ tn2.t_stor = tn1.t_stor /\ tn2.t_trans = tn1.t_trans /\
    (!i. ~(w2n bw + off <= i /\ i < w2n bw + off + type_memory_size dtv) ==>
       (i IN tn2.t_mem <=> i IN tn1.t_mem)) /\
    (!mem. mem_agree_outside tn2.t_mem t2.vs_memory mem ==>
       val_in_memory dtv v (w2n bw + off) mem) /\
    (!q. not_fresh_at s1 q ==>
       FLOOKUP G2 q = FLOOKUP G1 q /\ op_taint tn2 (Var q) = op_taint tn1 (Var q))` by
    (qpat_x_assum `log_field_src _ _ _ _ _ _ _ _ _ _ _ _ \/ _`
       (DISJ_CASES_THEN2 assume_tac (DISJ_CASES_THEN2 assume_tac assume_tac))
     >- suspend "nominal_store"
     >- suspend "bytes_store"
     >> suspend "zero_store") >>
  suspend "compose_store"
QED

Resume log_full_data_field_runtime_path[nominal_store]:
  `log_field_src cenv tenv (w2n bw) cap s1 G1 tn1 t1 f dty dtv v` by
    (irule log_field_src_frame >>
     qexistsl_tac [`G`, `type_memory_size dtv`, `s`, `sa`, `tn`, `w2n bw + off`] >>
     simp[] >> decide_tac) >>
  mp_tac (Q.INST [`sa` |-> `s1`, `G` |-> `G1`, `tn` |-> `tn1`, `s` |-> `t1`,
    `xd` |-> `p`, `dw` |-> `n2w (w2n (bw:bytes32) + off)`,
    `b` |-> `w2n (bw:bytes32)`] log_field_store_origin_ptr_path) >>
  (impl_tac >- (rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC, (asm_simp_tac bool_ss [] >> decide_tac),
           (gnvs[allocas_from_def] >> NO_TAC)])) >>
  simp[]
QED

Resume log_full_data_field_runtime_path[bytes_store]:
  qpat_x_assum `evaluate_type _ _ = _ /\ _` (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?xs stv sw len. _`
    (qx_choosel_then [`xs`, `stv`, `sw`, `len`] (map_every assume_tac o CONJUNCTS)) >>
  `not_fresh_at sa xs` by metis_tac[] >>
  `not_fresh_at s1 xs` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, ci_mono_def] >>
  `lookup_var xs t1 = SOME sw` by metis_tac[] >>
  `ptr_covers G1 tn1 xs t1 (32 * word_size len + 32)` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`G`, `s`, `tn`] >> simp[]) >>
  `~is_word_type dty` by metis_tac[eventTopicValuePropsTheory.bytestring_type_not_word] >>
  `compile_store_bytestring (Var xs) (Var p) s1 = ((),sb)` by
    (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_store_memory_def]) >>
  qpat_assum `w2n (n2w (w2n bw + off)) = _` (fn eq =>
    irule (REWRITE_RULE [eq] (Q.INST [`dw` |-> `n2w (w2n (bw:bytes32) + off)`]
      (SPEC_ALL log_full_bytes_store_runtime_path)))) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`dty`, `len`, `stv`, `SND (f:operand # type)`, `tenv`] >>
  simp[] >>
  qpat_x_assum `ptr_covers G1 tn1 p t1 _` mp_tac >>
  simp[ptr_covers_def] >> strip_tac >> goal_assum (drule_at Any) >> simp[]
QED

Resume log_full_data_field_runtime_path[zero_store]:
  qpat_x_assum `evaluate_type _ _ = _ /\ _` (map_every assume_tac o CONJUNCTS) >>
  `sb = s1` by metis_tac[pairTheory.PAIR_EQ] >>
  qexistsl_tac [`t1`, `G1`, `tn1`] >>
  simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules, typed_copy_state_frame_def,
    typed_copy_frame_def, venomStateTheory.venom_state_component_equality]
QED

Resume log_full_data_field_runtime_path[compose_store]:
  qpat_x_assum `log_field_src _ _ _ _ _ _ _ _ _ _ _ _ \/ _` kall_tac >>
  qexistsl_tac [`t2`, `G2`, `tn2`] >>
  conj_tac
  >- (gen_tac >>
      `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t1,G1,tn1)` by
        (irule fragGasOriginPtrDeadTheory.gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
      pop_assum (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
      disch_then (qspecl_then [`t1`, `G1`, `tn1`, `[]`, `OK t2`, `G2`, `tn2`]
        mp_tac) >> simp[]) >>
  conj_tac
  >- (irule typed_copy_state_frame_trans >> qexists_tac `t1` >> simp[arithmeticTheory.ADD_COMM] >>
      irule typed_copy_state_frame_mono >> qexists_tac `s1` >> simp[] >>
      qpat_x_assum `typed_copy_state_frame s1 _ _ t1 _` mp_tac >>
      simp[arithmeticTheory.ADD_COMM]) >>
  ntac 6 (conj_tac >- simp[]) >>
  conj_tac
  >- (qpat_x_assum `!i. _ ==> (_ IN tn2.t_mem <=> _)` mp_tac >>
      simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  conj_tac
  >- (qpat_x_assum `!mem. mem_agree_outside tn2.t_mem _ _ ==> _` mp_tac >>
      simp[arithmeticTheory.ADD_COMM]) >>
  rpt strip_tac >>
  `not_fresh_at s1 p'` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, ci_mono_def] >>
  simp[]
QED

Finalise log_full_data_field_runtime_path

(* Capture qualification: runtime bytes extent, nominal nonbytes extent. *)
Theorem log_full_field_capture_runtime:
  stmt_state_rel H ctx func cenv cx ee s /\
  expr_val_rel cx lty v op s /\
  expr_val_at cenv cx lty sa sb ee v op s /\
  expr_store_bound cx lty v op s /\
  ptr_val_ok cx lty v op G tn s /\
  evaluate_type (get_tenv cx) lty = SOME ltv /\ value_has_type ltv v /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
  assignable_type (get_tenv cx) dty /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  event_arg_compatible dty lty /\ type_widens_to (get_tenv cx) sty dty /\
  (~is_word_type dty /\ ~is_bytestring_type dty ==> sty = lty) /\
  (!x. op = Var x ==> not_fresh_at packing_sa x) /\
  FLOOKUP s.vs_allocas dest = SOME (b,cap) /\ sb.cs_next_id <= dest /\
  (!name a n. local_region cenv ee.scopes s name a n ==>
     a + n <= b \/ b + cap <= a) ==>
  log_field_src cenv (get_tenv cx) b cap packing_sa G tn s (op,sty) dty dtv v \/
  (evaluate_type (get_tenv cx) dty = SOME dtv /\
   value_has_type dtv v /\ val_wf dtv v /\
   type_memory_bytes cenv dty = type_memory_size dtv /\
   (!x. op = Var x ==> not_fresh_at packing_sa x) /\
   is_bytestring_type dty /\ is_bytestring_type sty /\
   (?xs stv sw len n. op = Var xs /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    value_has_type stv v /\ val_wf stv v /\ lookup_var xs s = SOME sw /\
    ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
     (?str. v = StringV str /\ len = LENGTH str)) /\
    n = 32 + 32 * word_size len /\ len + 31 < dimword(:256) /\
    n < dimword(:256) /\ n <= type_memory_size dtv /\
    w2n sw + n <= s.vs_alloca_next /\ ptr_covers G tn xs s n /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory stv v (w2n sw) mem) /\
    (!i. w2n sw <= i /\ i < w2n sw + val_footprint stv v ==>
       ~(b <= i /\ i < b + cap))))
Proof
  rpt strip_tac >>
  `val_wf ltv v /\ val_wf stv v /\ val_wf dtv v` by
    metis_tac[CONJUNCT1 exprSimAggregateChildrenTheory.typed_value_wf] >>
  `op_taint tn op = {}` by fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  `allocas_non_overlapping s` by
    fs[stmt_state_rel_def, state_rel_def, alloca_inv_def] >>
  `log_source_apart cx b cap (op,lty) v s` by
    (irule log_allocated_source_apart >> metis_tac[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  Cases_on `is_word_type dty`
  >- (disj1_tac >> `dty = lty` by metis_tac[word_event_compatible_same] >>
      gvs[] >> simp[log_field_src_def] >> gvs[expr_val_rel_def]) >>
  `~is_word_type lty` by
    metis_tac[CONJUNCT1 event_arg_compatible_word_shape] >>
  `?sw. eval_operand op s = SOME sw` by gvs[expr_val_rel_def] >>
  `ptr_mem_ok cx lty v op G tn s` by fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  Cases_on `is_bytestring_type dty`
  >- suspend "bytes" >>
  suspend "aggregate"
QED

Resume log_full_field_capture_runtime[aggregate]:
  disj1_tac >>
  `sty = lty` by metis_tac[] >>
  `stv = ltv` by metis_tac[optionTheory.SOME_11] >>
  `~is_bytestring_type lty` by
    (fs[event_arg_compatible_alias_def] >>
     metis_tac[valueCopyBytesTheory.arg_type_fits_bytestring_target]) >>
  `0 < type_memory_size stv` by
    metis_tac[tuple_place_widened_source_positive] >>
  `val_footprint ltv v = type_memory_size stv` by
    metis_tac[exprSimAggregateChildrenTheory.evaluated_nonbytes_footprint] >>
  `?xs. op = Var xs /\ ptr_covers G tn xs s (type_memory_size stv)` by
    (mp_tac (Q.INST [`ty` |-> `lty`, `tv` |-> `ltv`,
      `m` |-> `type_memory_size stv`, `w` |-> `sw`]
      (SPEC_ALL ptr_val_ok_read_covers)) >> simp[] >>
     metis_tac[arithmeticTheory.NOT_ZERO_LT_ZERO]) >>
  `lookup_var xs s = SOME sw` by gvs[venomStateTheory.eval_operand_def] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem` by
    (fs[bodyPtrDefsTheory.ptr_mem_ok_def] >> metis_tac[]) >>
  `w2n sw <= w2n sw + type_memory_size stv - 1 /\
   w2n sw + type_memory_size stv - 1 < w2n sw + val_footprint ltv v` by decide_tac >>
  `w2n sw + type_memory_size stv - 1 < s.vs_alloca_next` by
    (mp_tac (Q.INST [`t` |-> `lty`, `tv` |-> `ltv`,
      `es` |-> `ee`, `w` |-> `sw`,
      `i` |-> `w2n (sw : bytes32) + type_memory_size stv - 1`]
      (SPEC_ALL allocationPtrTheory.expr_val_at_below_frontier)) >>
     simp[] >> gvs[] >> decide_tac) >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next` by decide_tac >>
  `w2n sw + type_memory_size stv <= b \/ b + cap <= w2n sw` by
    (qpat_x_assum `log_source_apart _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [log_source_apart_def]) >>
     disch_then (qspecl_then [`ltv`, `sw`] mp_tac) >> simp[] >>
     gvs[] >> decide_tac) >>
  simp[log_field_src_def] >> gvs[] >> decide_tac
QED

Resume log_full_field_capture_runtime[bytes]:
  disj2_tac >>
  `is_bytestring_type lty` by metis_tac[event_arg_compatible_bytestring] >>
  `arg_type_fits sty dty` by fs[type_widens_to_def] >>
  `is_bytestring_type sty` by
    metis_tac[compileEnvTheory.arg_type_fits_bytestring_source] >>
  `val_footprint ltv v <> 0 /\ val_store_size ltv v <> 0` by
    (qspecl_then [`get_tenv cx`, `lty`, `ltv`] mp_tac bytestring_type_value >>
     simp[] >> strip_tac >> gvs[] >>
     Cases_on `v` >> gvs[value_has_type_def, val_footprint_def, val_store_size_def]) >>
  `val_store_size stv v = val_store_size ltv v /\
   val_footprint stv v = val_footprint ltv v` by
    metis_tac[bytestring_val_store_size_eq, bytestring_val_footprint_eq] >>
  `?xs. op = Var xs /\ ptr_covers G tn xs s (val_store_size ltv v)` by
    (mp_tac (Q.INST [`t` |-> `lty`, `tv` |-> `ltv`,
      `n` |-> `val_store_size ltv v`, `w` |-> `sw`] ptr_mem_ok_read_covers) >> simp[]) >>
  `lookup_var xs s = SOME sw` by gvs[venomStateTheory.eval_operand_def] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory ltv v (w2n sw) mem` by
    (fs[bodyPtrDefsTheory.ptr_mem_ok_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem` by
    metis_tac[bytestring_val_in_memory_transfer] >>
  `w2n sw + val_store_size ltv v <= s.vs_alloca_next` by
    (fs[exprSimMemDefsTheory.expr_store_bound_def] >> metis_tac[]) >>
  `w2n sw + val_footprint stv v <= b \/ b + cap <= w2n sw` by
    (qpat_x_assum `log_source_apart _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [log_source_apart_def]) >>
     disch_then (qspecl_then [`ltv`, `sw`] mp_tac) >> simp[]) >>
  `?len. ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
          (?str. v = StringV str /\ len = LENGTH str)) /\
         val_store_size stv v = 32 + 32 * word_size len` by
    (qspecl_then [`get_tenv cx`, `sty`, `stv`] mp_tac bytestring_type_value >>
     simp[] >> strip_tac >> Cases_on `v` >>
     gvs[value_has_type_def, val_store_size_def]) >>
  `val_store_size stv v = val_store_size dtv v` by
    metis_tac[bytestring_val_store_size_eq] >>
  `val_store_size stv v <= type_memory_size dtv` by
    metis_tac[exprSimPropsTheory.val_store_size_le] >>
  `32 + 32 * word_size len < dimword(:256)` by decide_tac >>
  `len + 31 < dimword(:256)` by
    metis_tac[exprSimBufferStoreTheory.buffer_round_no_wrap] >>
  gvs[] >> rpt strip_tac >> decide_tac
QED

Finalise log_full_field_capture_runtime

Theorem compile_log_frag_full:
  !cx id args DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    body_exprs_full_ok cx args /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (Log id args) /\
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
  `EVERY (\e. ~expr_has_effect e) args` by
    (fs[supported_pure_exprs_every, EVERY_MEM] >>
     metis_tac[supported_pure_expr_effect_free]) >>
  `EVERY (\e. post_value_type cenv e = expr_type e) args` by
    (fs[supported_pure_exprs_every, EVERY_MEM] >> rpt strip_tac >>
     irule post_value_type_not_int_call >> rpt strip_tac >>
     qpat_x_assum `!e. MEM e args ==> supported_pure_expr tops e` drule >>
     simp[supported_pure_expr_def]) >>
  `~supported_exprs_exists
      (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) args /\
   call_evaluation_safe cx (int_calls_exprs args) /\
   (!target. supported_exprs_exists (expr_abi_decode_target_root target) args ==>
      occurs_abi_decode_target target tops)` by
    fs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
       int_calls_stmt_def, AllCaseEqs()] >>
  qabbrev_tac `RR = \tail ee.
    EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) tail /\
    body_exprs_full_ok cx tail /\ expr_sim_inv cenv cx env ee /\
    supported_pure_exprs tops tail /\ well_typed_exprs env tail /\
    ~supported_exprs_exists
      (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) tail /\
    call_evaluation_safe cx (int_calls_exprs tail) /\
    (!target. supported_exprs_exists (expr_abi_decode_target_root target) tail ==>
       occurs_abi_decode_target target tops)` >>
  `!e tail ee. RR (e::tail) ee ==>
     expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
       cenv cx (expr_type e) e ee /\
     !v ee1. bind (eval_expr cx e) (read_result cx) ee = (INL v, ee1) ==>
       RR tail ee1 /\
       ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v` by
    (rpt gen_tac >> simp[Abbr `RR`] >> strip_tac >>
     qpat_x_assum `supported_pure_exprs _ _`
       (strip_assume_tac o SIMP_RULE std_ss [Once supported_pure_expr_def]) >>
     qpat_x_assum `well_typed_exprs _ _`
       (strip_assume_tac o SIMP_RULE std_ss [Once well_typed_expr_def]) >>
     qpat_x_assum `~supported_exprs_exists _ _`
       (strip_assume_tac o SIMP_RULE std_ss
         [Once supported_expr_exists_def, DE_MORGAN_THM]) >>
     qpat_x_assum `call_evaluation_safe _ _`
       (assume_tac o SIMP_RULE std_ss [Once int_calls_expr_def]) >>
     qpat_x_assum `!target. supported_exprs_exists _ _ ==> _`
       (strip_assume_tac o SIMP_RULE std_ss
         [Once supported_expr_exists_def, DISJ_IMP_THM, FORALL_AND_THM]) >>
     fs[body_exprs_full_ok_def] >>
     `call_evaluation_safe cx (int_calls_exprs tail)` by
       (irule call_evaluation_safe_append_right >>
        qexists_tac `int_calls_expr e` >> first_assum ACCEPT_TAC) >>
     `expr_body_pre cenv cx env e ee` by
       (qpat_assum `body_stmt_safe _ (Expr _)`
         (strip_assume_tac o SIMP_RULE std_ss
           [body_stmt_safe_def, supported_stmt_expr_exists_def,
            int_calls_stmt_def, EVERY_CONJ, GSYM expr_has_evm_run_def]) >>
        `supported_program tops /\ get_module_code cx NONE = SOME tops /\
         (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
           is_dynamic (vyper_to_abi_type (type_env tops) target))` by fs[body_inv_def] >>
        `cx_tops cx = tops` by simp[gasContextTheory.cx_tops_def] >>
        qspecl_then [`cenv`,`cx`,`env`,`e`,`ee`,`int_calls_exprs tail`]
          irule_body_pre stmt_expr_body_pre >> simp[] >> metis_tac[]) >>
     conj_tac
     >- (qpat_x_assum `body_expr_full_ok cx e`
           (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
         disch_then (qspecl_then
           [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,`func`,`shadow_func`,
            `cenv`,`env`,`expr_type e`,`ee`] mp_tac) >>
         impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
     rpt gen_tac >> strip_tac >>
     qspecl_then [`cenv`,`cx`,`env`,`e`,`ee`,`INL v`,`ee1`]
       mp_tac exprSimSourceTheory.expr_body_pre_eval >>
     impl_tac
     >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
         conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
     `body_exprs_full_ok cx tail` by
       (qpat_x_assum `(?s tv t s1 v t1. _) ==> _` irule >>
        qpat_x_assum `bind (eval_expr cx e) (read_result cx) ee = _` mp_tac >>
        simp[NoAsms, bind_def, AllCaseEqs()] >> metis_tac[]) >>
     simp[] >>
     fs[vyperTypeExprResultTheory.expr_result_typed_def, expr_runtime_typed_def,
        value_result_typed_def, value_runtime_typed_def] >>
     `env.type_defs = get_tenv cx` suffices_by metis_tac[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def]) >>
  `!tail ee gs. RR tail ee ==> RR tail (ee with gas_obs := gs)` by simp[Abbr `RR`] >>
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
  Cases_on `compile_log_eval_all cenv args sa` >>
  rename1 `compile_log_eval_all cenv args sa = (ops,sm)` >>
  Cases_on `compile_log_eval_all cenv (MAP gas_shadow_expr args) shadow_sa` >>
  rename1 `compile_log_eval_all cenv (MAP gas_shadow_expr args) shadow_sa =
    (shadow_ops,shadow_sm)` >>
  `shadow_ops = ops /\ gas_shadow_state sm shadow_sm` by
    (qspecl_then [`sa`,`shadow_sa`] mp_tac
       (REWRITE_RULE [gas_shadow_compiles_def]
         (Q.SPEC `args` gas_shadow_compile_log_eval_all)) >>
     simp[] >> strip_tac >> simp[]) >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
        fs[storage_trace_domain_def] >>
      `gas_admissible (eval_exprs cx args)
         (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception)) es` by
        (irule log_arguments_admissible >>
         qexistsl_tac [`id`,`lctx`] >> first_assum ACCEPT_TAC) >>
      `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
        fs[ret_pc_ok_def] >>
      `~exprs_can_mutate cenv args` by
        metis_tac[bodySimLogArgsTheory.supported_pure_expr_no_mutate] >>
      `?h. cenv.ce_event_info (nsid_to_string id) =
              SOME (h, MAP (SND o FST) fields, MAP SND fields) /\
           lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id =
              SOME (h, MAP (SND o FST) fields, MAP SND fields) /\
           LENGTH (FILTER I (MAP SND fields)) <= 3 /\
           EVERY (\f. if SND f then supported_scalar_type (SND (FST f))
                       else supported_place_type tops (SND (FST f))) fields` by
        (qspecl_then [`tops`,`ctx`,`cenv`,`cx`,`id`,`fields`] mp_tac
           bodySimLogArgsTheory.body_log_aggregate_metadata >>
         impl_tac >- simp[] >> disch_then ACCEPT_TAC) >>
      `fn_has_code sa sm func` by
        ((drule_all stmtSimLogTraceTheory.compile_log_eval_all_code >> simp[] >> (metis_tac[stmtSimLogTraceTheory.compile_log_eval_all_code]))) >>
      `fn_has_code shadow_sa shadow_sm shadow_func` by
        (qpat_assum `compile_stmt _ _ _ _ shadow_sa = _` mp_tac >>
         qpat_assum `compile_log_eval_all _ _ shadow_sa = _` mp_tac >>
         qpat_assum `fn_has_code shadow_sa shadow_sb shadow_func` mp_tac >>
         qpat_assum `cenv.ce_event_info _ = _` mp_tac >>
         metis_tac[stmtSimLogTraceTheory.compile_log_eval_all_code]) >>
      qspecl_then [`DF`,`lo`,`d`,`PG`,`ctx`,`shadow_ctx`,`func`,
                    `shadow_func`,`cenv`,`cx`,`st0`,`RR`,`env`] mp_tac
        compile_log_eval_all_full_store_bound_halt >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (qspecl_then
        [`args`,`es`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`ops`,`s0`,`G0`,`tn0`] mp_tac) >>
      impl_tac >- (simp[Abbr `RR`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      strip_tac >>
      qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ captureQ captureR` >>
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
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (strip_assume_tac o BETA_RULE o REWRITE_RULE [log_full_post_def]) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `vs` >> simp[] >>
  `LENGTH args = LENGTH fields /\ LENGTH args = LENGTH vs` by
    metis_tac[LIST_REL_LENGTH, LENGTH_ZIP, LENGTH_MAP] >>
  `LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
      value_has_type tv v) (MAP expr_type args) vs` by
    (simp[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
     qpat_assum `LIST_REL _ (ZIP (MAP FST ops,args)) vs`
       (mp_tac o Q.SPEC `n` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     simp[EL_ZIP, EL_MAP]) >>
  `LIST_REL event_arg_compatible (MAP (SND o FST) fields) (MAP expr_type args)` by
    (fs[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
     Cases_on `EL n fields` >> rename1 `EL n fields = (decl_arg,indexed)` >>
     Cases_on `decl_arg` >>
     qpat_x_assum `!n. n < LENGTH fields ==> _` (qspec_then `n` mp_tac) >> simp[]) >>
  `LIST_REL arg_type_fits
    (log_non_indexed_types (MAP SND fields) (MAP expr_type args))
    (log_non_indexed_types (MAP SND fields) (MAP (SND o FST) fields))` by
    (rewrite_tac[log_non_indexed_types_select] >>
     irule select_log_args_rel >> simp[] >>
     fs[LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >> rpt strip_tac >>
     qpat_x_assum `!n. n < LENGTH fields ==> _` (qspec_then `n` mp_tac) >>
     simp[event_arg_compatible_alias_def, EL_MAP]) >>
  `LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
      value_has_type tv v)
    (log_non_indexed_types (MAP SND fields) (MAP expr_type args))
    (log_non_indexed_values (MAP SND fields) vs)` by
    (rewrite_tac[log_non_indexed_types_select, log_non_indexed_values_select] >>
     irule select_log_args_rel >> simp[] >>
     fs[LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >> rpt strip_tac >> metis_tac[]) >>
  qabbrev_tac `ltys = log_non_indexed_types (MAP SND fields) (MAP expr_type args)` >>
  qabbrev_tac `dtys = log_non_indexed_types (MAP SND fields) (MAP (SND o FST) fields)` >>
  qabbrev_tac `dvs = log_non_indexed_values (MAP SND fields) vs` >>
  `?ltvs. OPT_MMAP (evaluate_type (get_tenv cx)) ltys = SOME ltvs` by
    (qexists_tac `MAP (THE o evaluate_type (get_tenv cx)) ltys` >>
     simp[vyperMiscTheory.OPT_MMAP_SOME_IFF, EVERY_EL, EL_MAP] >> rpt strip_tac >>
     qpat_assum `LIST_REL _ ltys dvs` (fn th =>
       assume_tac (MATCH_MP LIST_REL_LENGTH th) >>
       mp_tac (Q.SPEC `n` (CONJUNCT2 (REWRITE_RULE [LIST_REL_EL_EQN] th)))) >>
     impl_tac >- simp[] >> disch_then (strip_assume_tac o BETA_RULE) >> simp[]) >>
  `arg_types_fit ltys dtys` by fs[arg_types_fit_LIST_REL] >>
  `IS_SOME (OPT_MMAP (evaluate_type (get_tenv cx)) dtys)` by
    (mp_tac (CONJUNCT2 log_compatible_bounded_evaluation) >>
     disch_then (qspecl_then [`ltys`,`dtys`,`cenv`,`cx`,`env`,`es`,`ltvs`] mp_tac) >>
     impl_tac >- fs[Abbr `dtys`, log_alloc_ok_def] >> disch_then ACCEPT_TAC) >>
  qpat_x_assum `IS_SOME (OPT_MMAP _ dtys)`
    (qx_choose_then `dtvs` assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  `LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
      value_has_type tv v) dtys dvs` by
    (qpat_assum `LIST_REL _ ltys dvs` mp_tac >>
     qpat_assum `arg_types_fit ltys dtys` mp_tac >>
     qpat_assum `OPT_MMAP _ dtys = SOME dtvs`
       (mp_tac o MATCH_MP vyperTypeABITheory.OPT_MMAP_LIST_REL) >>
     rpt (pop_assum kall_tac) >>
     simp[arg_types_fit_LIST_REL, LIST_REL_EL_EQN] >> rpt strip_tac >>
     metis_tac[log_compatible_declared_value, event_arg_compatible_alias_def]) >>
  `EVERY (\(ty,indexed). indexed ==> supported_scalar_type ty)
    (ZIP (MAP (SND o FST) fields, MAP SND fields))` by
    (qpat_assum `EVERY (\f. if SND f then _ else _) fields` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[EVERY_EL, EL_ZIP, EL_MAP] >> rpt strip_tac >>
     first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
  `?topics avs.
    encode_indexed_event_topics (MAP SND fields) (MAP expr_type args) vs = SOME topics /\
    vyper_to_abi_list (get_tenv cx) dtys dvs = SOME avs /\
    encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs =
      SOME <|logger := cx.txn.target; topics := n2w h::topics;
        data := enc (Tuple (vyper_to_abi_types (get_tenv cx) dtys)) (ListV avs)|>` by
    (simp_tac bool_ss [Abbr `dtys`, Abbr `dvs`] >>
     irule log_full_compatible_source_event_encoded >> simp[]) >>
  suspend "selected_physical"
QED

Resume compile_log_frag_full[selected_physical]:
  `EVERY (\e. expr_body_pre cenv cx env e es) args` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `supported_pure_expr tops e /\ well_typed_expr env e /\
      ~supported_expr_exists
        (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) e /\
      (!target. supported_expr_exists (expr_abi_decode_target_root target) e ==>
         occurs_abi_decode_target target tops)` by
       (fs[supported_pure_exprs_every, EVERY_MEM,
           supported_exprs_exists_every, EXISTS_MEM] >>
        metis_tac[well_typed_exprs_member]) >>
     `supported_expr tops e` by simp[supportedExprsTheory.supported_expr_def] >>
     drule_then strip_assume_tac supported_expr_body_calls >>
     `call_evaluation_safe cx (int_calls_expr e)` by
       metis_tac[exprSimSourceTheory.call_evaluation_safe_exprs_mem] >>
     `int_calls_expr e = []` by metis_tac[supported_pure_int_calls] >>
     `cx_tops cx = tops` by fs[body_inv_def, gasContextTheory.cx_tops_def] >>
     irule_body_pre stmt_expr_body_pre >> fs[body_inv_def] >> metis_tac[]) >>
  `mid with gas_obs := [] = mid` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `eval_exprs cx args
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL vs,mid)` by
    (qpat_assum `mid with gas_obs := [] = mid` (fn mid_empty =>
       qpat_assum `!tail. eval_exprs _ _ _ = _`
         (ACCEPT_TAC o SIMP_RULE (srw_ss()) [mid_empty] o Q.SPEC `[]`))) >>
  `LIST_REL (\e v. value_runtime_typed env (lowered_value_type cenv e) v) args vs` by
    (match_mp_tac (Q.INST [`ce` |-> `cenv`, `cx` |-> `cx`, `env` |-> `env`]
       (Q.SPECL [`args`,
          `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
          `vs`, `mid`] exprSimHypsTheory.eval_exprs_physical_runtime_typed)) >>
     conj_tac
     >- (PURE_REWRITE_TAC [exprSimSourceTheory.expr_body_pre_gas_obs] >>
         first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> strip_tac >>
     qspecl_then [`cenv`,`e`,`env`,`cx`,`st`,`v`,`st'`] match_mp_tac
       exprSimHypsTheory.memory_rhs_read_lowered_typed_unwidened >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >>
     RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  mp_tac (Q.INST [`ce` |-> `cenv`]
    (Q.SPECL [`args`,`vs`,`es`]
      exprSimHypsTheory.physical_runtime_typed_list_layouts)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  suspend "selected_layouts"
QED

Resume compile_log_frag_full[selected_layouts]:
  `EVERY (\e. is_bytestring_type (lowered_value_type cenv e) <=>
             is_bytestring_type (expr_type e)) args` by
    metis_tac[bodySimLogArgsTheory.supported_pure_exprs_bytestring_iff] >>
  qabbrev_tac `lops = ZIP (MAP FST ops, MAP expr_type args)` >>
  `LIST_REL (\y x. FST y = FST x /\
       (is_bytestring_type (SND y) <=> is_bytestring_type (SND x))) ops lops` by
    (simp[Abbr `lops`, LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >> rpt strip_tac >>
     qpat_assum `MAP SND ops = _` (mp_tac o Q.AP_TERM `EL n`) >>
     gvs[EL_MAP, EVERY_EL]) >>
  `log_eval_view cenv args sa lops sm` by
    (rewrite_tac[log_eval_view_def] >> qexists_tac `ops` >> simp[]) >>
  `FST (split_log_ops ops (MAP SND fields)) =
     FST (split_log_ops lops (MAP SND fields))` by
    metis_tac[stmtSimLogTraceTheory.split_log_ops_view] >>
  Cases_on `compile_log_topic_ops (FST (split_log_ops lops (MAP SND fields))) sm` >>
  rename1 `compile_log_topic_ops _ sm = (topic_ops,topic_sa)` >>
  `compile_log_topic_ops (FST (split_log_ops ops (MAP SND fields))) sm =
    (topic_ops,topic_sa)` by simp[] >>
  `fn_has_code sm sb func` by
    ((drule_all stmtSimLogTraceTheory.compile_log_eval_all_code >> simp[] >> (metis_tac[stmtSimLogTraceTheory.compile_log_eval_all_code]))) >>
  `LENGTH ops = LENGTH fields` by metis_tac[LENGTH_MAP] >>
  Cases_on `SND (split_log_ops ops (MAP SND fields)) = []`
  >- suspend "empty_data" >>
  mp_tac (Q.INST [`h` |-> `h`,
       `dtys` |-> `MAP (SND o FST) (fields : ((string # type) # bool) list)`,
       `flags` |-> `MAP SND (fields : ((string # type) # bool) list)`,
       `ys` |-> `ops`, `st` |-> `topic_sa`, `topics` |-> `topic_ops`,
       `data_ops` |-> `SND (split_log_ops ops
         (MAP SND (fields : ((string # type) # bool) list)))`,
       `ty` |-> `ret_ty`]
     (SPEC_ALL stmtSimLogTraceTheory.compile_log_data_trace_declared)) >>
  impl_tac >- simp[] >>
  disch_then strip_assume_tac >> gvs[] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (metis_tac[stmtSimLogTraceTheory.compile_log_eval_all_code]) >>
  `cs_extends sm topic_sa` by
    (mp_tac (Q.SPECL
       [`FST (split_log_ops lops
           (MAP SND (fields : ((string # type) # bool) list)))`, `sm`]
       eventLoweringStructureTheory.compile_log_topic_ops_ci_mono) >>
     simp[ci_mono_def]) >>
  drule_all log_full_declared_data_stage_code >> strip_tac >>
  qabbrev_tac `log_ev = <|logger := cx.txn.target; topics := n2w h::topics;
    data := enc (Tuple (vyper_to_abi_types (get_tenv cx) dtys)) (ListV avs)|>` >>
  `encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs = SOME log_ev` by
    simp[Abbr `log_ev`] >>
  suspend "packing_static"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[selected_capture]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
  BETA_TAC >> strip_tac >>
  qunabbrev_tac `captureQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (strip_assume_tac o BETA_RULE o
    REWRITE_RULE [log_full_post_def]) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `vs` >> simp[] >>
  `LENGTH args = LENGTH fields /\ LENGTH args = LENGTH vs` by
    metis_tac[LIST_REL_LENGTH, LENGTH_ZIP, LENGTH_MAP] >>
  `LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
      value_has_type tv v) (MAP expr_type args) vs` by
    (simp[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
     qpat_assum `LIST_REL _ (ZIP (MAP FST ops,args)) vs`
       (mp_tac o Q.SPEC `n` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     simp[EL_ZIP, EL_MAP]) >>
  `LIST_REL event_arg_compatible (MAP (SND o FST) fields) (MAP expr_type args)` by
    (fs[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
     Cases_on `EL n fields` >> rename1 `EL n fields = (decl_arg,indexed)` >>
     Cases_on `decl_arg` >>
     qpat_x_assum `!n. n < LENGTH fields ==> _`
       (qspec_then `n` mp_tac) >> simp[]) >>
  `LIST_REL arg_type_fits
    (log_non_indexed_types (MAP SND fields) (MAP expr_type args))
    (log_non_indexed_types (MAP SND fields) (MAP (SND o FST) fields))` by
    (rewrite_tac[log_non_indexed_types_select] >>
     irule select_log_args_rel >> simp[] >>
     fs[LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >> rpt strip_tac >>
     qpat_x_assum `!n. n < LENGTH fields ==> _`
       (qspec_then `n` mp_tac) >>
     simp[event_arg_compatible_alias_def, EL_MAP]) >>
  `LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
      value_has_type tv v)
    (log_non_indexed_types (MAP SND fields) (MAP expr_type args))
    (log_non_indexed_values (MAP SND fields) vs)` by
    (rewrite_tac[log_non_indexed_types_select, log_non_indexed_values_select] >>
     irule select_log_args_rel >> simp[] >>
     fs[LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >> rpt strip_tac >> metis_tac[]) >>
  qabbrev_tac `ltys = log_non_indexed_types (MAP SND fields) (MAP expr_type args)` >>
  qabbrev_tac `dtys = log_non_indexed_types (MAP SND fields) (MAP (SND o FST) fields)` >>
  qabbrev_tac `dvs = log_non_indexed_values (MAP SND fields) vs` >>
  `?ltvs. OPT_MMAP (evaluate_type (get_tenv cx)) ltys = SOME ltvs` by
    (qexists_tac `MAP (THE o evaluate_type (get_tenv cx)) ltys` >>
     simp[vyperMiscTheory.OPT_MMAP_SOME_IFF, EVERY_EL, EL_MAP] >>
     rpt strip_tac >>
     qpat_assum `LIST_REL _ ltys dvs` (fn th =>
       assume_tac (MATCH_MP LIST_REL_LENGTH th) >>
       mp_tac (Q.SPEC `n` (CONJUNCT2
         (REWRITE_RULE [LIST_REL_EL_EQN] th)))) >>
     impl_tac >- simp[] >>
     disch_then (strip_assume_tac o BETA_RULE) >> simp[]) >>
  `arg_types_fit ltys dtys` by fs[arg_types_fit_LIST_REL] >>
  `IS_SOME (OPT_MMAP (evaluate_type (get_tenv cx)) dtys)` by
    (mp_tac (CONJUNCT2 log_compatible_bounded_evaluation) >>
     disch_then (qspecl_then [`ltys`,`dtys`,`cenv`,`cx`,`env`,`es`,`ltvs`] mp_tac) >>
     impl_tac >- fs[Abbr `dtys`, log_alloc_ok_def] >>
     disch_then ACCEPT_TAC) >>
  qpat_x_assum `IS_SOME (OPT_MMAP _ dtys)`
    (qx_choose_then `dtvs` assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  `LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
      value_has_type tv v) dtys dvs` by
    (qpat_assum `LIST_REL _ ltys dvs` mp_tac >>
     qpat_assum `arg_types_fit ltys dtys` mp_tac >>
     qpat_assum `OPT_MMAP _ dtys = SOME dtvs`
       (mp_tac o MATCH_MP vyperTypeABITheory.OPT_MMAP_LIST_REL) >>
     rpt (pop_assum kall_tac) >>
     simp[arg_types_fit_LIST_REL, LIST_REL_EL_EQN] >> rpt strip_tac >>
     metis_tac[log_compatible_declared_value, event_arg_compatible_alias_def]) >>
  `EVERY (\(ty,indexed). indexed ==> supported_scalar_type ty)
    (ZIP (MAP (SND o FST) fields, MAP SND fields))` by
    (qpat_assum `EVERY (\f. if SND f then _ else _) fields` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[EVERY_EL, EL_ZIP, EL_MAP] >> rpt strip_tac >>
     first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
  `?topics avs.
    encode_indexed_event_topics (MAP SND fields) (MAP expr_type args) vs =
      SOME topics /\
    vyper_to_abi_list (get_tenv cx) dtys dvs = SOME avs /\
    encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs =
      SOME <|logger := cx.txn.target; topics := n2w h::topics;
        data := enc (Tuple (vyper_to_abi_types (get_tenv cx) dtys)) (ListV avs)|>` by
    (simp_tac bool_ss [Abbr `dtys`, Abbr `dvs`] >>
     irule stmtSimLogSourceTheory.log_compatible_source_event_encoded >>
     simp[]) >>
  `EVERY (\e. expr_body_pre cenv cx env e es) args` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `supported_pure_expr tops e /\ well_typed_expr env e /\
      ~supported_expr_exists
        (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) e /\
      (!target. supported_expr_exists (expr_abi_decode_target_root target) e ==>
         occurs_abi_decode_target target tops)` by
       (fs[supported_pure_exprs_every, EVERY_MEM,
           supported_exprs_exists_every, EXISTS_MEM] >>
        metis_tac[well_typed_exprs_member]) >>
     `supported_expr tops e` by simp[supportedExprsTheory.supported_expr_def] >>
     drule_then strip_assume_tac supported_expr_body_calls >>
     `call_evaluation_safe cx (int_calls_expr e)` by
       metis_tac[exprSimSourceTheory.call_evaluation_safe_exprs_mem] >>
     `int_calls_expr e = []` by metis_tac[supported_pure_int_calls] >>
     `cx_tops cx = tops` by
       fs[body_inv_def, gasContextTheory.cx_tops_def] >>
     qspecl_then [`cenv`,`cx`,`env`,`e`,`es`,`[]`] irule stmt_expr_body_pre >>
     fs[body_inv_def]) >>
  `mid with gas_obs := [] = mid` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `eval_exprs cx args
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL vs,mid)` by
    (qpat_assum `mid with gas_obs := [] = mid` (fn mid_empty =>
       qpat_assum `!tail. eval_exprs _ _ _ = _`
         (ACCEPT_TAC o SIMP_RULE (srw_ss()) [mid_empty] o Q.SPEC `[]`))) >>
  `LIST_REL (\e v. value_runtime_typed env (lowered_value_type cenv e) v) args vs` by
    (match_mp_tac (Q.INST [`ce` |-> `cenv`, `cx` |-> `cx`, `env` |-> `env`]
       (Q.SPECL [`args`,
          `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
          `vs`, `mid`] exprSimHypsTheory.eval_exprs_physical_runtime_typed)) >>
     conj_tac
     >- (PURE_REWRITE_TAC [exprSimSourceTheory.expr_body_pre_gas_obs] >>
         first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> strip_tac >>
     qspecl_then [`cenv`,`e`,`env`,`cx`,`st`,`v`,`st'`] match_mp_tac
       exprSimHypsTheory.memory_rhs_read_lowered_typed_unwidened >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >>
     RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  mp_tac (Q.INST [`ce` |-> `cenv`]
    (Q.SPECL [`args`,`vs`,`es`]
      exprSimHypsTheory.physical_runtime_typed_list_layouts)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `EVERY (\e. is_bytestring_type (lowered_value_type cenv e) <=>
             is_bytestring_type (expr_type e)) args` by
    metis_tac[bodySimLogArgsTheory.supported_pure_exprs_bytestring_iff] >>
  qabbrev_tac `lops = ZIP (MAP FST ops, MAP expr_type args)` >>
  `LIST_REL (\y x. FST y = FST x /\
       (is_bytestring_type (SND y) <=> is_bytestring_type (SND x))) ops lops` by
    (simp[Abbr `lops`, LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >>
     rpt strip_tac >>
     qpat_assum `MAP SND ops = _` (mp_tac o Q.AP_TERM `EL n`) >>
     gvs[EL_MAP, EVERY_EL]) >>
  `log_eval_view cenv args sa lops sm` by
    (rewrite_tac[log_eval_view_def] >> qexists_tac `ops` >> simp[]) >>
  `FST (split_log_ops ops (MAP SND fields)) =
     FST (split_log_ops lops (MAP SND fields))` by
    metis_tac[stmtSimLogTraceTheory.split_log_ops_view] >>
  Cases_on `compile_log_topic_ops (FST (split_log_ops lops (MAP SND fields))) sm` >>
  rename1 `compile_log_topic_ops _ sm = (topic_ops,topic_sa)` >>
  `compile_log_topic_ops (FST (split_log_ops ops (MAP SND fields))) sm =
    (topic_ops,topic_sa)` by simp[] >>
  `fn_has_code sm sb func` by
    (mp_tac (Q.INST
       [`info` |-> `(h, MAP (SND o FST)
                     (fields : ((string # type) # bool) list), MAP SND fields)`,
        `ty` |-> `ret_ty`]
       (SPEC_ALL stmtSimLogTraceTheory.compile_log_eval_all_code)) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `LENGTH ops = LENGTH fields` by
    metis_tac[LENGTH_MAP] >>
  Cases_on `SND (split_log_ops ops (MAP SND fields)) = []`
  >- suspend "empty_data" >>
  mp_tac (Q.INST [`h` |-> `h`,
       `dtys` |-> `MAP (SND o FST) (fields : ((string # type) # bool) list)`,
       `flags` |-> `MAP SND (fields : ((string # type) # bool) list)`,
       `ys` |-> `ops`, `st` |-> `topic_sa`, `topics` |-> `topic_ops`,
       `data_ops` |-> `SND (split_log_ops ops
         (MAP SND (fields : ((string # type) # bool) list)))`,
       `ty` |-> `ret_ty`]
     (SPEC_ALL stmtSimLogTraceTheory.compile_log_data_trace_declared)) >>
  impl_tac >- simp[] >>
  disch_then (strip_assume_tac o REWRITE_RULE [ASSUME
    ``compile_stmt cenv lctx ret_ty (Log id args) sa = ((),sb)``]) >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (mp_tac (Q.INST
       [`info` |-> `(h, MAP (SND o FST)
                     (fields : ((string # type) # bool) list), MAP SND fields)`,
        `ty` |-> `ret_ty`]
       (SPEC_ALL stmtSimLogTraceTheory.compile_log_eval_all_code)) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `cs_extends sm topic_sa` by
    (mp_tac (Q.SPECL
       [`FST (split_log_ops lops
           (MAP SND (fields : ((string # type) # bool) list)))`, `sm`]
       eventLoweringStructureTheory.compile_log_topic_ops_ci_mono) >>
     simp[ci_mono_def]) >>
  drule_all log_full_declared_data_stage_code >> strip_tac >>
  qabbrev_tac `log_ev = <|logger := cx.txn.target; topics := n2w h::topics;
    data := enc (Tuple (vyper_to_abi_types (get_tenv cx) dtys)) (ListV avs)|>` >>
  `encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs = SOME log_ev` by
    simp[Abbr `log_ev`] >>
  `!tail. bind (lift_option
      (encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs)
      "Log encode event") push_log (mid with gas_obs := tail) =
      (INL (), (mid with logs := mid.logs ++ [log_ev]) with gas_obs := tail)` by
    simp[vyperStateTheory.lift_option_def, vyperStateTheory.bind_def,
         vyperStateTheory.push_log_def, vyperStateTheory.return_def] >>
  suspend "packing_static"
QED
*)

Resume compile_log_frag_full[packing_static]:
  qabbrev_tac `flags = MAP SND fields` >>
  qabbrev_tac `data_ops = SND (split_log_ops ops flags)` >>
  qabbrev_tac `data_args = select_log_args F flags args` >>
  `type_env tops SUBMAP get_tenv cx` by
    (irule body_main_type_env_submap >> fs[body_inv_def]) >>
  `SUM (MAP (type_memory_bytes cenv) dtys) = type_memory_size_list dtvs` by
    (irule tuple_memory_bytes_size >> qexists_tac `get_tenv cx` >>
     simp[] >> qx_genl_tac [`ty`,`tv`] >> strip_tac >>
     qspecl_then [`cenv`,`ty`,`cx`,`env`,`es`,`tv`]
       match_mp_tac expr_sim_inv_memory_size >> simp[]) >>
  qabbrev_tac `cap = MAX 32 (SUM (MAP (type_memory_bytes cenv) dtys))` >>
  `cap < dimword (:256) /\ type_memory_size_list dtvs <= cap` by
    (fs[Abbr `cap`, Abbr `dtys`, log_alloc_ok_def] >>
     CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> decide_tac) >>
  `MAP SND data_ops = MAP (lowered_value_type cenv) data_args` by
    (mp_tac (Q.SPECL [`flags`, `ops`] split_log_ops_select) >>
     impl_tac >- simp[Abbr `flags`] >> strip_tac >>
     gvs[Abbr `data_ops`, Abbr `data_args`, GSYM select_log_args_MAP]) >>
  `MAP expr_type data_args = ltys` by
    simp[Abbr `data_args`, Abbr `ltys`, Abbr `flags`,
      log_non_indexed_types_select, select_log_args_MAP] >>
  `LIST_REL (\e v. value_runtime_typed env (lowered_value_type cenv e) v)
     data_args dvs` by
    (simp_tac bool_ss [Abbr `data_args`, Abbr `dvs`, log_non_indexed_values_select] >>
     irule select_log_args_rel >> simp[Abbr `flags`] >>
     fs[LIST_REL_EL_EQN, EL_ZIP] >> rpt strip_tac >> metis_tac[]) >>
  `EVERY (\e. expr_body_pre cenv cx env e es) data_args` by
    (simp_tac bool_ss [Abbr `data_args`] >>
     irule EVERY_select_log_args >> first_assum ACCEPT_TAC) >>
  suspend "packing_field_packet"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[packing_static]:
  qabbrev_tac `flags = MAP SND fields` >>
  qabbrev_tac `data_ops = SND (split_log_ops ops flags)` >>
  qabbrev_tac `data_args = select_log_args F flags args` >>
  `type_env tops SUBMAP get_tenv cx` by
    (irule body_main_type_env_submap >> fs[body_inv_def]) >>
  `SUM (MAP (type_memory_bytes cenv) dtys) = type_memory_size_list dtvs` by
    (irule tuple_memory_bytes_size >> qexists_tac `get_tenv cx` >>
     simp[] >> qx_genl_tac [`ty`,`tv`] >> strip_tac >>
     qspecl_then [`cenv`,`ty`,`cx`,`env`,`es`,`tv`]
       match_mp_tac expr_sim_inv_memory_size >> simp[]) >>
  qabbrev_tac `cap = MAX 32 (SUM (MAP (type_memory_bytes cenv) dtys))` >>
  `cap < dimword (:256) /\ type_memory_size_list dtvs <= cap` by
    (fs[Abbr `cap`, Abbr `dtys`, log_alloc_ok_def] >>
     CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> decide_tac) >>
  `MAP SND data_ops = MAP (lowered_value_type cenv) data_args` by
    (mp_tac (Q.SPECL [`flags`, `ops`] split_log_ops_select) >>
     impl_tac >- simp[Abbr `flags`] >> strip_tac >>
     gvs[Abbr `data_ops`, Abbr `data_args`,
       GSYM select_log_args_MAP]) >>
  `MAP expr_type data_args = ltys` by
    simp[Abbr `data_args`, Abbr `ltys`, Abbr `flags`,
      log_non_indexed_types_select, select_log_args_MAP] >>
  `LIST_REL (\e v. value_runtime_typed env (lowered_value_type cenv e) v)
     data_args dvs` by
    (simp_tac bool_ss [Abbr `data_args`, Abbr `dvs`,
       log_non_indexed_values_select] >>
     irule select_log_args_rel >> simp[Abbr `flags`] >>
     fs[LIST_REL_EL_EQN, EL_ZIP] >> rpt strip_tac >> metis_tac[]) >>
  `EVERY (\e. expr_body_pre cenv cx env e es) data_args` by
    (simp_tac bool_ss [Abbr `data_args`] >>
     irule EVERY_select_log_args >> first_assum ACCEPT_TAC) >>
  suspend "packing_field_packet"
QED
*)

Resume compile_log_frag_full[packing_field_packet]:
  `EVERY (\e. post_value_type cenv e = expr_type e) data_args` by
    (simp_tac bool_ss [Abbr `data_args`] >>
     irule EVERY_select_log_args >> first_assum ACCEPT_TAC) >>
  `LIST_REL (\ty f. supported_place_type tops ty) dtys
     (select_log_args F flags fields)` by
    (simp_tac bool_ss [Abbr `dtys`, Abbr `flags`, log_non_indexed_types_select] >>
     irule select_log_args_rel >> simp[] >>
     simp[LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >> rpt strip_tac >>
     qpat_assum `EVERY (\f. if SND f then _ else _) fields`
       (mp_tac o Q.SPEC `n` o REWRITE_RULE [EVERY_EL]) >> simp[]) >>
  `EVERY (supported_place_type tops) dtys` by
    (qpat_assum `LIST_REL (\ty f. supported_place_type tops ty) dtys _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]) >>
  `!i. i < LENGTH data_ops ==>
    ?ltv ptv.
      evaluate_type (get_tenv cx) (expr_type (EL i data_args)) = SOME ltv /\
      value_has_type ltv (EL i dvs) /\
      evaluate_type (get_tenv cx) (SND (EL i data_ops)) = SOME ptv /\
      value_has_type ptv (EL i dvs) /\
      evaluate_type (get_tenv cx) (EL i dtys) = SOME (EL i dtvs) /\
      value_has_type (EL i dtvs) (EL i dvs) /\
      assignable_type (get_tenv cx) (EL i dtys) /\
      type_memory_bytes cenv (EL i dtys) = type_memory_size (EL i dtvs) /\
      event_arg_compatible (EL i dtys) (expr_type (EL i data_args)) /\
      type_widens_to (get_tenv cx) (SND (EL i data_ops)) (EL i dtys) /\
      (~is_word_type (EL i dtys) /\ ~is_bytestring_type (EL i dtys) ==>
         SND (EL i data_ops) = expr_type (EL i data_args))` by
    (gen_tac >> strip_tac >>
     `LENGTH data_ops = LENGTH data_args /\ LENGTH data_args = LENGTH ltys /\
      LENGTH ltys = LENGTH dtys /\ LENGTH dtys = LENGTH dtvs /\
      LENGTH dtys = LENGTH dvs` by
       (qpat_assum `MAP SND data_ops = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
        qpat_assum `MAP expr_type data_args = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
        qpat_assum `arg_types_fit ltys dtys`
          (mp_tac o MATCH_MP LIST_REL_LENGTH o REWRITE_RULE [arg_types_fit_LIST_REL]) >>
        qpat_assum `OPT_MMAP _ dtys = SOME dtvs`
          (mp_tac o MATCH_MP LIST_REL_LENGTH o MATCH_MP vyperTypeABITheory.OPT_MMAP_LIST_REL) >>
        qpat_assum `LIST_REL _ dtys dvs` (mp_tac o MATCH_MP LIST_REL_LENGTH) >> simp[]) >>
     `SND (EL i data_ops) = lowered_value_type cenv (EL i data_args) /\
      expr_type (EL i data_args) = EL i ltys` by
       (qpat_assum `MAP SND data_ops = _` (mp_tac o Q.AP_TERM `EL i`) >>
        qpat_assum `MAP expr_type data_args = _` (mp_tac o Q.AP_TERM `EL i`) >> simp[EL_MAP]) >>
     `?ltv. evaluate_type (get_tenv cx) (expr_type (EL i data_args)) = SOME ltv /\
       value_has_type ltv (EL i dvs)` by
       (qpat_assum `LIST_REL _ ltys dvs`
         (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >> simp[]) >>
     `?ptv. evaluate_type (get_tenv cx) (SND (EL i data_ops)) = SOME ptv /\
       value_has_type ptv (EL i dvs)` by
       (qpat_assum `LIST_REL _ data_args dvs`
         (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
        simp[value_runtime_typed_def]) >>
     `evaluate_type (get_tenv cx) (EL i dtys) = SOME (EL i dtvs)` by
       (qpat_assum `OPT_MMAP _ dtys = SOME dtvs`
         (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN] o
           MATCH_MP vyperTypeABITheory.OPT_MMAP_LIST_REL) >> simp[]) >>
     `value_has_type (EL i dtvs) (EL i dvs)` by
       (qpat_assum `LIST_REL _ dtys dvs`
         (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >> simp[]) >>
     `expr_body_pre cenv cx env (EL i data_args) es /\
      post_value_type cenv (EL i data_args) = expr_type (EL i data_args) /\
      supported_place_type tops (EL i dtys)` by
       (qpat_assum `EVERY (\e. expr_body_pre cenv cx env e es) data_args`
          (mp_tac o Q.SPEC `i` o REWRITE_RULE [EVERY_EL]) >>
        qpat_assum `EVERY (\e. post_value_type cenv e = expr_type e) data_args`
          (mp_tac o Q.SPEC `i` o REWRITE_RULE [EVERY_EL]) >>
        qpat_assum `EVERY (supported_place_type tops) dtys`
          (mp_tac o Q.SPEC `i` o REWRITE_RULE [EVERY_EL]) >> simp[]) >>
     `arg_type_fits (expr_type (EL i data_args)) (EL i dtys)` by
       (qpat_assum `arg_types_fit ltys dtys`
         (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE
           [arg_types_fit_LIST_REL, LIST_REL_EL_EQN]) >> simp[]) >>
     `event_arg_compatible (EL i dtys) (expr_type (EL i data_args))` by
       simp[event_arg_compatible_alias_def] >>
     `arg_type_fits (SND (EL i data_ops)) (expr_type (EL i data_args))` by
       (mp_tac (Q.INST [`ce` |-> `cenv`, `e` |-> `EL i data_args`]
          expr_body_pre_lowered_fits) >> simp[]) >>
     `type_widens_to (get_tenv cx) (SND (EL i data_ops)) (expr_type (EL i data_args))` by
       simp[type_widens_to_def, well_formed_type_def] >>
     `type_widens_to (get_tenv cx) (expr_type (EL i data_args)) (EL i dtys)` by
       simp[type_widens_to_def, well_formed_type_def] >>
     `type_widens_to (get_tenv cx) (SND (EL i data_ops)) (EL i dtys)` by
       (irule typedCopyCompatibilityTheory.type_widens_to_trans >>
        qexists_tac `expr_type (EL i data_args)` >> simp[]) >>
     `assignable_type (get_tenv cx) (EL i dtys)` by
       (qspecl_then [`tops`,`get_tenv cx`,`EL i dtys`,`EL i dtvs`]
          match_mp_tac supported_place_evaluated_assignable >> simp[]) >>
     `type_memory_bytes cenv (EL i dtys) = type_memory_size (EL i dtvs)` by
       (qspecl_then [`cenv`,`EL i dtys`,`cx`,`env`,`es`,`EL i dtvs`]
          match_mp_tac expr_sim_inv_memory_size >> simp[]) >>
     `~is_word_type (EL i dtys) /\ ~is_bytestring_type (EL i dtys) ==>
        SND (EL i data_ops) = expr_type (EL i data_args)` by
       (strip_tac >>
        `~is_word_type (expr_type (EL i data_args)) /\
         ~is_bytestring_type (expr_type (EL i data_args))` by
          (qspecl_then [`EL i dtys`,`expr_type (EL i data_args)`]
             match_mp_tac log_compatible_aggregate_source >> simp[]) >>
        `lowered_value_type cenv (EL i data_args) = post_value_type cenv (EL i data_args)` by
          (qspecl_then [`cenv`,`cx`,`env`,`EL i data_args`,`es`]
             match_mp_tac aggregate_lowered_post_type >> simp[]) >> simp[]) >>
     qexistsl_tac [`ltv`,`ptv`] >> simp[]) >>
  suspend "topic_selection"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[packing_field_packet]:
  `EVERY (\e. post_value_type cenv e = expr_type e) data_args` by
    (simp_tac bool_ss [Abbr `data_args`] >>
     irule EVERY_select_log_args >> first_assum ACCEPT_TAC) >>
  `LIST_REL (\ty f. supported_place_type tops ty) dtys
     (select_log_args F flags fields)` by
    (simp_tac bool_ss [Abbr `dtys`, Abbr `flags`, log_non_indexed_types_select] >>
     irule select_log_args_rel >> simp[] >>
     simp[LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >> rpt strip_tac >>
     qpat_assum `EVERY (\f. if SND f then _ else _) fields`
       (mp_tac o Q.SPEC `n` o REWRITE_RULE [EVERY_EL]) >> simp[]) >>
  `EVERY (supported_place_type tops) dtys` by
    (qpat_assum `LIST_REL (\ty f. supported_place_type tops ty) dtys _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]) >>
  `!i. i < LENGTH data_ops ==>
    ?ltv ptv.
      evaluate_type (get_tenv cx) (expr_type (EL i data_args)) = SOME ltv /\
      value_has_type ltv (EL i dvs) /\
      evaluate_type (get_tenv cx) (SND (EL i data_ops)) = SOME ptv /\
      value_has_type ptv (EL i dvs) /\
      evaluate_type (get_tenv cx) (EL i dtys) = SOME (EL i dtvs) /\
      value_has_type (EL i dtvs) (EL i dvs) /\
      assignable_type (get_tenv cx) (EL i dtys) /\
      type_memory_bytes cenv (EL i dtys) = type_memory_size (EL i dtvs) /\
      event_arg_compatible (EL i dtys) (expr_type (EL i data_args)) /\
      type_widens_to (get_tenv cx) (SND (EL i data_ops)) (EL i dtys) /\
      (~is_word_type (EL i dtys) /\ ~is_bytestring_type (EL i dtys) ==>
         SND (EL i data_ops) = expr_type (EL i data_args))` by
    (gen_tac >> strip_tac >>
     `LENGTH data_ops = LENGTH data_args /\ LENGTH data_args = LENGTH ltys /\
      LENGTH ltys = LENGTH dtys /\ LENGTH dtys = LENGTH dtvs /\
      LENGTH dtys = LENGTH dvs` by
       (qpat_assum `MAP SND data_ops = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
        qpat_assum `MAP expr_type data_args = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
        qpat_assum `arg_types_fit ltys dtys`
          (mp_tac o MATCH_MP LIST_REL_LENGTH o REWRITE_RULE [arg_types_fit_LIST_REL]) >>
        qpat_assum `OPT_MMAP _ dtys = SOME dtvs`
          (mp_tac o MATCH_MP LIST_REL_LENGTH o MATCH_MP vyperTypeABITheory.OPT_MMAP_LIST_REL) >>
        qpat_assum `LIST_REL _ dtys dvs` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
        simp[]) >>
     `SND (EL i data_ops) = lowered_value_type cenv (EL i data_args) /\
      expr_type (EL i data_args) = EL i ltys` by
       (qpat_assum `MAP SND data_ops = _` (mp_tac o Q.AP_TERM `EL i`) >>
        qpat_assum `MAP expr_type data_args = _` (mp_tac o Q.AP_TERM `EL i`) >>
        simp[EL_MAP]) >>
     `?ltv. evaluate_type (get_tenv cx) (expr_type (EL i data_args)) = SOME ltv /\
       value_has_type ltv (EL i dvs)` by
       (qpat_assum `LIST_REL _ ltys dvs`
         (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >> simp[]) >>
     `?ptv. evaluate_type (get_tenv cx) (SND (EL i data_ops)) = SOME ptv /\
       value_has_type ptv (EL i dvs)` by
       (qpat_assum `LIST_REL _ data_args dvs`
         (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
        simp[value_runtime_typed_def]) >>
     `evaluate_type (get_tenv cx) (EL i dtys) = SOME (EL i dtvs)` by
       (qpat_assum `OPT_MMAP _ dtys = SOME dtvs`
         (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN] o
           MATCH_MP vyperTypeABITheory.OPT_MMAP_LIST_REL) >> simp[]) >>
     `value_has_type (EL i dtvs) (EL i dvs)` by
       (qpat_assum `LIST_REL _ dtys dvs`
         (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >> simp[]) >>
     `expr_body_pre cenv cx env (EL i data_args) es /\
      post_value_type cenv (EL i data_args) = expr_type (EL i data_args) /\
      supported_place_type tops (EL i dtys)` by
       (qpat_assum `EVERY (\e. expr_body_pre cenv cx env e es) data_args`
          (mp_tac o Q.SPEC `i` o REWRITE_RULE [EVERY_EL]) >>
        qpat_assum `EVERY (\e. post_value_type cenv e = expr_type e) data_args`
          (mp_tac o Q.SPEC `i` o REWRITE_RULE [EVERY_EL]) >>
        qpat_assum `EVERY (supported_place_type tops) dtys`
          (mp_tac o Q.SPEC `i` o REWRITE_RULE [EVERY_EL]) >> simp[]) >>
     `arg_type_fits (expr_type (EL i data_args)) (EL i dtys)` by
       (qpat_assum `arg_types_fit ltys dtys`
         (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE
           [arg_types_fit_LIST_REL, LIST_REL_EL_EQN]) >> simp[]) >>
     `event_arg_compatible (EL i dtys) (expr_type (EL i data_args))` by
       simp[event_arg_compatible_alias_def] >>
     `arg_type_fits (SND (EL i data_ops)) (expr_type (EL i data_args))` by
       (mp_tac (Q.INST [`ce` |-> `cenv`, `e` |-> `EL i data_args`]
          expr_body_pre_lowered_fits) >> simp[]) >>
     `type_widens_to (get_tenv cx) (SND (EL i data_ops)) (expr_type (EL i data_args))` by
       simp[type_widens_to_def, well_formed_type_def] >>
     `type_widens_to (get_tenv cx) (expr_type (EL i data_args)) (EL i dtys)` by
       simp[type_widens_to_def, well_formed_type_def] >>
     `type_widens_to (get_tenv cx) (SND (EL i data_ops)) (EL i dtys)` by
       (irule typedCopyCompatibilityTheory.type_widens_to_trans >>
        qexists_tac `expr_type (EL i data_args)` >> simp[]) >>
     `assignable_type (get_tenv cx) (EL i dtys)` by
       (qspecl_then [`tops`,`get_tenv cx`,`EL i dtys`,`EL i dtvs`]
          match_mp_tac supported_place_evaluated_assignable >> simp[]) >>
     `type_memory_bytes cenv (EL i dtys) = type_memory_size (EL i dtvs)` by
       (qspecl_then [`cenv`,`EL i dtys`,`cx`,`env`,`es`,`EL i dtvs`]
          match_mp_tac expr_sim_inv_memory_size >> simp[]) >>
     `~is_word_type (EL i dtys) /\ ~is_bytestring_type (EL i dtys) ==>
        SND (EL i data_ops) = expr_type (EL i data_args)` by
       (strip_tac >>
        `~is_word_type (expr_type (EL i data_args)) /\
         ~is_bytestring_type (expr_type (EL i data_args))` by
          (qspecl_then [`EL i dtys`,`expr_type (EL i data_args)`]
             match_mp_tac log_compatible_aggregate_source >> simp[]) >>
        `lowered_value_type cenv (EL i data_args) = post_value_type cenv (EL i data_args)` by
          (qspecl_then [`cenv`,`cx`,`env`,`EL i data_args`,`es`]
             match_mp_tac aggregate_lowered_post_type >> simp[]) >> simp[]) >>
     qexistsl_tac [`ltv`,`ptv`] >> simp[]) >>
  suspend "topic_selection"
QED
*)

Resume compile_log_frag_full[topic_selection]:
  qabbrev_tac `topic_args = select_log_args T flags lops` >>
  qabbrev_tac `topic_vals = select_log_args T flags vs` >>
  `LIST_REL (\arg v. ?j. j < LENGTH args /\ v = EL j vs /\
       FST arg = FST (EL j ops) /\ SND arg = expr_type (EL j args))
     topic_args topic_vals` by
    (simp_tac bool_ss [Abbr `topic_args`, Abbr `topic_vals`] >>
     irule typedLogSplitCompleteTheory.select_log_args_list_rel >>
     conj_tac >- simp[Abbr `flags`, Abbr `lops`] >>
     simp[LIST_REL_EL_EQN, Abbr `lops`, EL_ZIP, EL_MAP] >>
     rpt strip_tac >> qexists_tac `n` >> simp[]) >>
  `MAP (\p. (FST p,is_bytestring_type (SND p))) topic_args =
     FST (split_log_ops lops flags)` by
    (mp_tac (Q.SPECL [`flags`, `lops`] eventLogSplitPropsTheory.split_log_ops_select) >>
     impl_tac >- simp[Abbr `flags`, Abbr `lops`] >>
     disch_then (mp_tac o Q.AP_TERM `FST`) >>
     simp[Abbr `topic_args`, pairTheory.LAMBDA_PROD]) >>
  `compile_log_topic_ops
     (MAP (\p. (FST p,is_bytestring_type (SND p))) topic_args) sm =
     (topic_ops,topic_sa)` by simp[Abbr `flags`] >>
  `MAP SND topic_args = select_log_args T flags (MAP expr_type args)` by
    simp[Abbr `topic_args`, Abbr `lops`, GSYM select_log_args_MAP, MAP_ZIP] >>
  `encode_indexed_event_topics (REPLICATE (LENGTH topic_args) T)
       (MAP SND topic_args) topic_vals = SOME topics` by
    (mp_tac (Q.SPECL [`flags`,`MAP expr_type args`,`vs`]
       eventLogSplitPropsTheory.encode_indexed_event_topics_select) >>
     impl_tac >- simp[Abbr `flags`] >>
     `LENGTH topic_args = LENGTH (select_log_args T flags (MAP expr_type args))` by
       metis_tac[LENGTH_MAP] >> simp[Abbr `topic_vals`, Abbr `flags`]) >>
  `LIST_REL (\arg f. supported_scalar_type (SND arg)) topic_args
      (select_log_args T flags fields)` by
    (simp_tac bool_ss [Abbr `topic_args`] >>
     irule eventLogSplitPropsTheory.select_log_args_rel >>
     conj_tac >- simp[Abbr `flags`, Abbr `lops`] >>
     simp[LIST_REL_EL_EQN, EL_ZIP, Abbr `lops`, Abbr `flags`, EL_MAP] >>
     rpt strip_tac >>
     `supported_scalar_type (SND (FST (EL n fields)))` by
       (qpat_assum `EVERY (\f. if SND f then _ else _) fields`
          (mp_tac o Q.SPEC `n` o REWRITE_RULE [EVERY_EL]) >> simp[]) >>
     `event_arg_compatible (SND (FST (EL n fields))) (expr_type (EL n args))` by
       (qpat_assum `LIST_REL event_arg_compatible _ _`
          (mp_tac o Q.SPEC `n` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
        simp[EL_MAP, combinTheory.o_THM]) >>
     metis_tac[whitelistLogWidenTheory.scalar_event_arg_compatible]) >>
  `EVERY (\arg. supported_scalar_type (SND arg)) topic_args` by
    (qpat_assum `LIST_REL (\arg f. supported_scalar_type (SND arg)) _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]) >>
  `LIST_REL (\arg v. supported_scalar_type (SND arg) /\
       ?j. j < LENGTH args /\ v = EL j vs /\
       FST arg = FST (EL j ops) /\ SND arg = expr_type (EL j args))
     topic_args topic_vals` by
    (fs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]) >>
  suspend "topic_producer"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[topic_selection]:
  qabbrev_tac `topic_args = select_log_args T flags lops` >>
  qabbrev_tac `topic_vals = select_log_args T flags vs` >>
  `LIST_REL (\arg v. ?j. j < LENGTH args /\ v = EL j vs /\
       FST arg = FST (EL j ops) /\ SND arg = expr_type (EL j args))
     topic_args topic_vals` by
    (simp_tac bool_ss [Abbr `topic_args`, Abbr `topic_vals`] >>
     irule typedLogSplitCompleteTheory.select_log_args_list_rel >>
     conj_tac >- simp[Abbr `flags`, Abbr `lops`] >>
     simp[LIST_REL_EL_EQN, Abbr `lops`, EL_ZIP, EL_MAP] >>
     rpt strip_tac >> qexists_tac `n` >> simp[]) >>
  `MAP (\p. (FST p,is_bytestring_type (SND p))) topic_args =
     FST (split_log_ops lops flags)` by
    (mp_tac (Q.SPECL [`flags`, `lops`]
       eventLogSplitPropsTheory.split_log_ops_select) >>
     impl_tac >- simp[Abbr `flags`, Abbr `lops`] >>
     disch_then (mp_tac o Q.AP_TERM `FST`) >>
     simp[Abbr `topic_args`, pairTheory.LAMBDA_PROD]) >>
  `compile_log_topic_ops
     (MAP (\p. (FST p,is_bytestring_type (SND p))) topic_args) sm =
     (topic_ops,topic_sa)` by simp[Abbr `flags`] >>
  `MAP SND topic_args = select_log_args T flags (MAP expr_type args)` by
    simp[Abbr `topic_args`, Abbr `lops`, GSYM select_log_args_MAP,
      MAP_ZIP] >>
  `encode_indexed_event_topics (REPLICATE (LENGTH topic_args) T)
       (MAP SND topic_args) topic_vals = SOME topics` by
    (mp_tac (Q.SPECL [`flags`,`MAP expr_type args`,`vs`]
       eventLogSplitPropsTheory.encode_indexed_event_topics_select) >>
     impl_tac >- simp[Abbr `flags`] >>
     `LENGTH topic_args = LENGTH (select_log_args T flags (MAP expr_type args))` by
       metis_tac[LENGTH_MAP] >>
     simp[Abbr `topic_vals`, Abbr `flags`]) >>
  `LIST_REL (\arg f. supported_scalar_type (SND arg)) topic_args
      (select_log_args T flags fields)` by
    (simp_tac bool_ss [Abbr `topic_args`] >>
     irule eventLogSplitPropsTheory.select_log_args_rel >>
     conj_tac >- simp[Abbr `flags`, Abbr `lops`] >>
     simp[LIST_REL_EL_EQN, EL_ZIP, Abbr `lops`, Abbr `flags`, EL_MAP] >>
     rpt strip_tac >>
     `supported_scalar_type (SND (FST (EL n fields)))` by
       (qpat_assum `EVERY (\f. if SND f then _ else _) fields`
          (mp_tac o Q.SPEC `n` o REWRITE_RULE [EVERY_EL]) >> simp[]) >>
     `event_arg_compatible (SND (FST (EL n fields))) (expr_type (EL n args))` by
       (qpat_assum `LIST_REL event_arg_compatible _ _`
          (mp_tac o Q.SPEC `n` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
        simp[EL_MAP, combinTheory.o_THM]) >>
     metis_tac[stmtSimLogSourceTheory.scalar_event_arg_compatible]) >>
  `EVERY (\arg. supported_scalar_type (SND arg)) topic_args` by
    (qpat_assum `LIST_REL (\arg f. supported_scalar_type (SND arg)) _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]) >>
  `LIST_REL (\arg v. supported_scalar_type (SND arg) /\
       ?j. j < LENGTH args /\ v = EL j vs /\
       FST arg = FST (EL j ops) /\ SND arg = expr_type (EL j args))
     topic_args topic_vals` by
    (fs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]) >>
  suspend "topic_producer"
QED
*)

Resume compile_log_frag_full[topic_producer]:
  `log_full_post DF lo d ctx func cenv cx es sa sm s0 G0 tn0 args ops
     (storage_trace_horizon mid.storage_trace) (INL vs : value list + exception)
     mid G1 tn1 t` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id` by
    (mp_tac (cj 1 stmtLoweringMonoTheory.ci_mono_list_helpers) >>
     disch_then (qspecl_then [`cenv`,`args`,`sa`] mp_tac) >> simp[ci_mono_def]) >>
  `local_ptrs_reserved cenv sm` by
    (qspecl_then [`cenv`,`sa`,`sm`] match_mp_tac
       exprLoweringPropsTheory.local_ptrs_reserved_next_var >> fs[cs_extends_def]) >>
  `cs_extends sm topic_sa /\ sm.cs_next_var <= topic_sa.cs_next_var /\
   sm.cs_next_id <= topic_sa.cs_next_id` by
    (mp_tac (cj 2 stmtLoweringMonoTheory.ci_mono_list_helpers) >>
     disch_then (qspecl_then
       [`MAP (\p. (FST p,is_bytestring_type (SND p))) topic_args`,`sm`] mp_tac) >>
     simp[ci_mono_def]) >>
  `cs_extends topic_sa s1 /\ cs_extends s2 s3` by
    (imp_res_tac loweringHaltTheory.compile_alloc_buffer_extends >> simp[]) >>
  `cs_extends s1 s2` by
    (mp_tac (cj 3 stmtLoweringMonoTheory.ci_mono_list_helpers) >>
     disch_then (qspecl_then [`cenv`,`data_ops`,`dtys`,`src.buf_operand`,`0`,`s1`]
       mp_tac) >> simp[ci_mono_def, Abbr `dtys`]) >>
  `cs_extends topic_sa sb` by
    (irule cs_extends_trans >> qexists_tac `s1` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s2` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  `fn_has_code sm topic_sa func` by
    (qspecl_then [`sm`,`sm`,`topic_sa`,`sb`,`func`] match_mp_tac
       fragExecTheory.fn_has_code_mid >> simp[cs_extends_refl]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ lo d cenv cx mid G1 tn1 t`
       (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >> simp[]) >>
  drule_all bodyFullLogScalarTopicsTheory.compile_log_scalar_topics_from_capture >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`tp`,`Gp`,`tnp`] strip_assume_tac)) >>
  suspend "topic_endpoint"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[topic_producer]:
  `log_full_post DF lo d ctx func cenv cx es sa sm s0 G0 tn0 args ops
     (storage_trace_horizon mid.storage_trace) (INL vs : value list + exception)
     mid G1 tn1 t` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
`cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
 sa.cs_next_id <= sm.cs_next_id` by
 (mp_tac (cj 1 stmtLoweringMonoTheory.ci_mono_list_helpers) >>
  disch_then (qspecl_then [`cenv`,`args`,`sa`] mp_tac) >>
  simp[ci_mono_def]) >>
`local_ptrs_reserved cenv sm` by
 (qspecl_then [`cenv`,`sa`,`sm`] match_mp_tac
    exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
  fs[cs_extends_def]) >>
`cs_extends sm topic_sa /\ sm.cs_next_var <= topic_sa.cs_next_var /\
 sm.cs_next_id <= topic_sa.cs_next_id` by
 (mp_tac (cj 2 stmtLoweringMonoTheory.ci_mono_list_helpers) >>
  disch_then (qspecl_then
    [`MAP (\p. (FST p,is_bytestring_type (SND p))) topic_args`,`sm`] mp_tac) >>
  simp[ci_mono_def]) >>
`cs_extends topic_sa s1 /\ cs_extends s2 s3` by
 (imp_res_tac loweringHaltTheory.compile_alloc_buffer_extends >> simp[]) >>
`cs_extends s1 s2` by
 (mp_tac (cj 3 stmtLoweringMonoTheory.ci_mono_list_helpers) >>
  disch_then (qspecl_then [`cenv`,`data_ops`,`dtys`,`src.buf_operand`,`0`,`s1`]
    mp_tac) >> simp[ci_mono_def, Abbr `dtys`]) >>
`cs_extends topic_sa sb` by
 (irule cs_extends_trans >> qexists_tac `s1` >> simp[] >>
  irule cs_extends_trans >> qexists_tac `s2` >> simp[] >>
  irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
`fn_has_code sm topic_sa func` by
 (qspecl_then [`sm`,`sm`,`topic_sa`,`sb`,`func`] match_mp_tac
    fragExecTheory.fn_has_code_mid >> simp[cs_extends_refl]) >>
`allocas_from lo t /\ lo <= t.vs_alloca_next` by
 (qpat_assum `ghost_inv_at _ lo d cenv cx mid G1 tn1 t`
   (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >> simp[]) >>
mp_tac (Q.INST
  [`captured` |-> `ops`, `xs` |-> `topic_args`, `ivs` |-> `topic_vals`,
   `result_ops` |-> `topic_ops`, `sb` |-> `topic_sa`, `ee` |-> `mid`,
   `inv_es` |-> `es`, `s` |-> `t`, `G` |-> `G1`, `tn` |-> `tn1`,
   `H` |-> `storage_trace_horizon mid.storage_trace`,
   `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
  (INST_TYPE [``:'a`` |-> ``:256``, ``:'b`` |-> ``:exception``]
    (INST [{redex=mk_var ("ops", ``:operand list``),
            residue=mk_var ("result_ops", ``:operand list``)}]
      bodyFullLogScalarTopicsTheory.compile_log_scalar_topics_from_capture))) >>
(impl_tac
>- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
disch_then (qx_choosel_then [`tp`,`Gp`,`tnp`] strip_assume_tac) >>

  suspend "topic_endpoint"
QED
*)

Resume compile_log_frag_full[topic_endpoint]:
  `tp.vs_memory = t.vs_memory /\ tp.vs_allocas = t.vs_allocas /\
   tp.vs_alloca_next = t.vs_alloca_next /\
   tp.vs_accounts = t.vs_accounts /\ tp.vs_transient = t.vs_transient /\
   tp.vs_requests = t.vs_requests /\ tp.vs_call_ctx = t.vs_call_ctx` by
    (qpat_assum `tp with <|vs_vars := _; vs_inst_idx := _|> = t`
      (mp_tac o SIMP_RULE (srw_ss()) [venomStateTheory.venom_state_component_equality]) >> simp[]) >>
  `gas_path_mem ctx func t 0 (OK tp)` by
    (qpat_assum `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t,G1,tn1) [] (OK tp,Gp,tnp)`
      (qspec_then `DF (storage_trace_horizon mid.storage_trace)` mp_tac) >>
     disch_then (mp_tac o CONJUNCT1 o MATCH_MP
       fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
     disch_then (mp_tac o MATCH_MP fragGasOriginTheory.gas_origin_path_erase) >>
     simp[fragGasModeTheory.gas_marked_path_def]) >>
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  `!u. gas_path_mem ctx func t 0 (OK u) ==> alloca_inv u` by
    (rpt strip_tac >>
     drule_all bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv >> simp[]) >>
  `alloca_history func tp` by
    (drule_all fragGasPathFrameMemTheory.gas_path_mem_zero_history >> simp[]) >>
  suspend "topic_frame"
QED

Resume compile_log_frag_full[topic_frame]:
  `(!x sz. cenv.ce_return_buf=SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc=SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    (rpt conj_tac >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
     fs[ci_mono_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
   stmt_state_rel H ctx func cenv cx mid tp /\
   storage_well_formed_on cx mid (FST H) /\
   ghost_inv_at (DF H) lo d cenv cx mid Gp tnp tp` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >>
     disch_then (strip_assume_tac o BETA_RULE o
       REWRITE_RULE [bodyFullLogArgsTheory.log_full_post_def]) >> gvs[] >>
     `stmt_state_rel H ctx func cenv cx mid tp` by
       (mp_tac (Q.INST
         [`H0` |-> `storage_trace_horizon mid.storage_trace`, `H` |-> `H`,
          `es` |-> `mid`, `u` |-> `tp`, `s` |-> `t`]
         (INST_TYPE [``:'a`` |-> ``:256``, ``:'b`` |-> ``:256``]
           exprLoweringPropsTheory.stmt_state_rel_fields_transport)) >>
        (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >> simp[]) >>
  suspend "topic_all_h"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[topic_endpoint]:
(* Project readonly fields once; leave the original equality available. *)
`tp.vs_memory = t.vs_memory /\ tp.vs_allocas = t.vs_allocas /\
 tp.vs_alloca_next = t.vs_alloca_next /\
 tp.vs_accounts = t.vs_accounts /\ tp.vs_transient = t.vs_transient /\
 tp.vs_requests = t.vs_requests /\ tp.vs_call_ctx = t.vs_call_ctx`
 by (qpat_assum `tp with <|vs_vars := _; vs_inst_idx := _|> = t`
      (mp_tac o SIMP_RULE (srw_ss()) [venomStateTheory.venom_state_component_equality]) >>
     simp[]) >>

(* alloca_history is sensitive to the cursor, so a state-field equality
   alone cannot transport it. Project the SAME topic path; no re-execution
   and no second endpoint are selected. *)
`gas_path_mem ctx func t 0 (OK tp)` by
 (qpat_assum `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t,G1,tn1) [] (OK tp,Gp,tnp)`
    (qspec_then `DF (storage_trace_horizon mid.storage_trace)` mp_tac) >>
  disch_then (mp_tac o CONJUNCT1 o MATCH_MP
    fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
  disch_then (mp_tac o MATCH_MP fragGasOriginTheory.gas_origin_path_erase) >>
  simp[fragGasModeTheory.gas_marked_path_def]) >>
`alloca_inv t` by fs[stmt_state_rel_def] >>
`!u. gas_path_mem ctx func t 0 (OK u) ==> alloca_inv u` by
 (rpt strip_tac >>
  drule_all bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv >> simp[]) >>
`alloca_history func tp` by
 (drule_all fragGasPathFrameMemTheory.gas_path_mem_zero_history >> simp[]) >>

  suspend "topic_frame"
QED
*)

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[topic_frame]:
(* 2. Preserve original all-H facts at the one chosen topic endpoint.
   Return freshness comes from stmt_frag_full / ret_pc_ok at sa;
   local_ptrs_reserved deliberately does NOT contain these two facts. *)
`(!x sz. cenv.ce_return_buf=SOME (PtrVar (Var x) sz) ==>
   not_fresh_at sm x) /\
 (!x sz. cenv.ce_return_pc=SOME (PtrVar (Var x) sz) ==>
   not_fresh_at sm x)` by
 (rpt conj_tac >> rpt strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
  fs[ci_mono_def] >> metis_tac[]) >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 stmt_state_rel H ctx func cenv cx mid tp /\
 storage_well_formed_on cx mid (FST H) /\
 ghost_inv_at (DF H) lo d cenv cx mid Gp tnp tp` by
 (gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >>
  disch_then (strip_assume_tac o BETA_RULE o
    REWRITE_RULE [bodyFullLogArgsTheory.log_full_post_def]) >> gvs[] >>
  `stmt_state_rel H ctx func cenv cx mid tp` by
    (mp_tac (Q.INST
        [`H0` |-> `storage_trace_horizon mid.storage_trace`, `H` |-> `H`,
         `es` |-> `mid`, `u` |-> `tp`, `s` |-> `t`]
        (INST_TYPE [``:'a`` |-> ``:256``, ``:'b`` |-> ``:256``]
          exprLoweringPropsTheory.stmt_state_rel_fields_transport)) >>
     (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  simp[]) >>

  suspend "topic_all_h"
QED
*)

Resume compile_log_frag_full[topic_all_h]:
  `local_ptrs_reserved cenv topic_sa` by
    (qspecl_then [`cenv`,`sm`,`topic_sa`] match_mp_tac
       exprLoweringPropsTheory.local_ptrs_reserved_next_var >> fs[ci_mono_def]) >>
  `allocas_from lo tp /\ lo <= tp.vs_alloca_next` by
    (fs[ptrDisciplineTheory.allocas_from_def] >> first_assum ACCEPT_TAC) >>
  `compile_alloc_buffer cap topic_sa = (src,s1)` by
    (fs[Abbr `cap`, Abbr `dtys`, Abbr `flags`] >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST
    [`n` |-> `cap`, `sa` |-> `topic_sa`, `sb` |-> `s1`, `buf` |-> `src`,
     `s` |-> `tp`, `G` |-> `Gp`, `tn` |-> `tnp`, `es` |-> `mid`,
     `H` |-> `storage_trace_horizon mid.storage_trace`,
     `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (INST_TYPE [``:'a`` |-> ``:256``, ``:'b`` |-> ``:256``]
      bodyFullAllocaFreshTheory.alloc_buffer_origin_ptr_path)) >>
  (impl_tac >- (rpt conj_tac >> (simp[]))) >>
  disch_then (qx_choosel_then [`q`,`bw`,`ta`,`Ga`,`tna`] strip_assume_tac) >>
  suspend "first_alloca"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[topic_all_h]:
(* 3. Actual first ALLOCA, with the actual src/s1 from the checked trace.
   local reservation advances by local_ptrs_reserved_next_var and
   cs_extends sm topic_sa. allocas_from/frontier transport across topics
   by the readonly fields above; source halt/cursor are helper outputs. *)
`local_ptrs_reserved cenv topic_sa` by
 (qspecl_then [`cenv`,`sm`,`topic_sa`] match_mp_tac
    exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
  fs[ci_mono_def]) >>
`allocas_from lo tp /\ lo <= tp.vs_alloca_next` by
  (fs[ptrDisciplineTheory.allocas_from_def] >> first_assum ACCEPT_TAC) >>
`compile_alloc_buffer cap topic_sa = (src,s1)` by
  (fs[Abbr `cap`, Abbr `dtys`, Abbr `flags`] >> first_assum ACCEPT_TAC) >>
mp_tac (Q.INST
  [`n` |-> `cap`, `sa` |-> `topic_sa`, `sb` |-> `s1`, `buf` |-> `src`,
   `s` |-> `tp`, `G` |-> `Gp`, `tn` |-> `tnp`, `es` |-> `mid`,
   `H` |-> `storage_trace_horizon mid.storage_trace`,
   `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
  (INST_TYPE [``:'a`` |-> ``:256``, ``:'b`` |-> ``:256``]
    bodyFullAllocaFreshTheory.alloc_buffer_origin_ptr_path)) >>
(impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
disch_then (qx_choosel_then [`q`,`bw`,`ta`,`Ga`,`tna`] strip_assume_tac) >>

  suspend "first_alloca"
QED
*)

Resume compile_log_frag_full[first_alloca]:
  `ta.vs_memory = t.vs_memory /\ t.vs_alloca_next <= ta.vs_alloca_next /\
   (!aid row. FLOOKUP t.vs_allocas aid = SOME row ==>
              FLOOKUP ta.vs_allocas aid = SOME row)` by
    (qpat_assum `ta with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = tp`
      (mp_tac o SIMP_RULE (srw_ss()) [venomStateTheory.venom_state_component_equality]) >>
     simp[] >> metis_tac[]) >>
  `!p. not_fresh_at sm p ==>
   lookup_var p ta = lookup_var p t /\ FLOOKUP Ga p = FLOOKUP G1 p /\
   op_taint tna (Var p) = op_taint tn1 (Var p)` by
    (rpt strip_tac >> `not_fresh_at topic_sa p` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >>
        fs[ci_mono_def]) >> metis_tac[]) >>
  `!i. i IN tna.t_mem ==> i IN tn1.t_mem \/ t.vs_alloca_next <= i` by
    (qpat_assum `!i. i IN tna.t_mem <=> _` (fn th => rewrite_tac[th]) >>
     rpt strip_tac >> fs[] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
   stmt_state_rel H ctx func cenv cx mid ta /\
   storage_well_formed_on cx mid (FST H) /\
   ghost_inv_at (DF H) lo d cenv cx mid Ga tna ta` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
         stmt_state_rel _ _ _ _ _ _ tp /\ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
     rpt conj_tac
     >- (qpat_assum `!H'. stmt_state_rel H' ctx func cenv cx mid tp ==>
           stmt_state_rel H' ctx func cenv cx mid ta`
           (qspec_then `H` mp_tac) >> simp[])
     >- first_assum ACCEPT_TAC >>
     mp_tac (Q.INST
       [`D` |-> `DF H`, `H` |-> `storage_trace_horizon mid.storage_trace`,
        `es` |-> `mid`, `s` |-> `tp`, `t` |-> `ta`, `sa` |-> `topic_sa`,
        `G` |-> `Gp`, `G'` |-> `Ga`, `tn` |-> `tnp`, `tn'` |-> `tna`,
        `e` |-> `w2n (bw:bytes32)+cap`]
       (INST_TYPE [``:'a`` |-> ``:256``]
         bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at)) >>
     impl_tac
     >- (simp[] >> rpt conj_tac >> rpt strip_tac >>
         irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >>
         fs[ci_mono_def] >> metis_tac[]) >> disch_then ACCEPT_TAC) >>
  `wb_frame cenv mid mid sm t ta` by
    (mp_tac (Q.SPECL [`cenv`,`mid`,`mid`,`sm`,`t`,`t`,`sm`,`ta`]
       exprSimWordArgsTheory.wb_frame_readonly_tail) >>
     impl_tac
     >- (simp[exprSimWordArgsTheory.wb_frame_refl] >> metis_tac[]) >>
     disch_then ACCEPT_TAC) >>
  `pure_frame cenv func mid sm t ta` by simp[pure_frame_def] >>
  suspend "allocation_frame"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[first_alloca]:
(* Allocate only this endpoint: no fresh-target existence is assumed.
   The actual allocation id is topic_sa.cs_next_id; it is NOT s1.next_id. *)
`ta.vs_memory = t.vs_memory /\
 t.vs_alloca_next <= ta.vs_alloca_next /\
 (!aid row. FLOOKUP t.vs_allocas aid = SOME row ==>
             FLOOKUP ta.vs_allocas aid = SOME row)` by
 (qpat_assum `ta with <|vs_vars := _; vs_allocas := _;
    vs_alloca_next := _; vs_inst_idx := _|> = tp`
    (mp_tac o SIMP_RULE (srw_ss()) [venomStateTheory.venom_state_component_equality]) >>
  simp[] >> metis_tac[]) >>
`!p. not_fresh_at sm p ==>
 lookup_var p ta = lookup_var p t /\ FLOOKUP Ga p = FLOOKUP G1 p /\
 op_taint tna (Var p) = op_taint tn1 (Var p)` by
 (rpt strip_tac >> `not_fresh_at topic_sa p` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >>
     fs[ci_mono_def]) >> metis_tac[]) >>
`!i. i IN tna.t_mem ==>
 i IN tn1.t_mem \/ t.vs_alloca_next <= i` by
 (qpat_assum `!i. i IN tna.t_mem <=> _` (fn th => rewrite_tac[th]) >>
  rpt strip_tac >> fs[] >> metis_tac[]) >>

(* The all-H callback reuses this exact ta/Ga/tna, not another ALLOCA. *)
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 stmt_state_rel H ctx func cenv cx mid ta /\
 storage_well_formed_on cx mid (FST H) /\
 ghost_inv_at (DF H) lo d cenv cx mid Ga tna ta` by
 (gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
      stmt_state_rel _ _ _ _ _ _ tp /\ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  rpt conj_tac
  >- (qpat_assum `!H'. stmt_state_rel H' ctx func cenv cx mid tp ==>
        stmt_state_rel H' ctx func cenv cx mid ta`
        (qspec_then `H` mp_tac) >> simp[])
  >- first_assum ACCEPT_TAC >>
  mp_tac (Q.INST
    [`D` |-> `DF H`, `H` |-> `storage_trace_horizon mid.storage_trace`,
     `es` |-> `mid`, `s` |-> `tp`, `t` |-> `ta`, `sa` |-> `topic_sa`,
     `G` |-> `Gp`, `G'` |-> `Ga`, `tn` |-> `tnp`, `tn'` |-> `tna`,
     `e` |-> `w2n (bw:bytes32)+cap`]
    (INST_TYPE [``:'a`` |-> ``:256``]
      bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at)) >>
  impl_tac
  >- (simp[] >> rpt conj_tac >> rpt strip_tac >>
      irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >>
      fs[ci_mono_def] >> metis_tac[]) >>
  disch_then ACCEPT_TAC) >>

(* 4. Frame once per packet, keeping the ORIGINAL capture bound sm. *)
`wb_frame cenv mid mid sm t ta` by
 (mp_tac (Q.SPECL [`cenv`,`mid`,`mid`,`sm`,`t`,`t`,`sm`,`ta`]
    exprSimWordArgsTheory.wb_frame_readonly_tail) >>
  impl_tac
  >- (simp[exprSimWordArgsTheory.wb_frame_refl] >> metis_tac[]) >>
  disch_then ACCEPT_TAC) >>
`pure_frame cenv func mid sm t ta` by simp[pure_frame_def] >>

  suspend "allocation_frame"
QED
*)

Resume compile_log_frag_full[allocation_frame]:
  `ci_mono topic_sa s1` by
    (mp_tac (Q.SPECL [`cap`,`topic_sa`]
      exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >> simp[]) >>
  `acyclic_struct_metadata cenv.ce_struct_fields /\
   sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv cx) fty = SOME tv ==>
        sz = type_memory_size tv) fields)` by
    (conj_tac >- fs[body_inv_def] >>
     qpat_assum `expr_sim_inv cenv cx env es`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `LENGTH flags = LENGTH args /\ LENGTH flags = LENGTH ops` by simp[Abbr `flags`] >>
  `select_log_args F flags (ZIP (MAP FST ops,args)) = ZIP (MAP FST data_ops,data_args)` by
    (`MAP FST (select_log_args F flags (ZIP (MAP FST ops,args))) = MAP FST data_ops /\
      MAP SND (select_log_args F flags (ZIP (MAP FST ops,args))) = data_args` by
       (qspecl_then [`flags`,`ops`] mp_tac eventLogSplitPropsTheory.split_log_ops_select >>
        (impl_tac >- simp[Abbr `flags`]) >>
        disch_then (fn th => simp[Abbr `data_ops`,Abbr `data_args`,th,
          GSYM select_log_args_MAP,MAP_ZIP])) >>
     metis_tac[listTheory.ZIP_UNZIP, listTheory.UNZIP_MAP]) >>
  `LIST_REL (\(op,e) v.
     expr_val_rel cx (expr_type e) v op t /\
     expr_val_at cenv cx (expr_type e) sa sm mid v op t /\
     expr_store_bound cx (expr_type e) v op t /\
     ptr_val_ok cx (expr_type e) v op G1 tn1 t /\
     (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G1 t) /\
     ?tv. evaluate_type (get_tenv cx) (expr_type e)=SOME tv /\ value_has_type tv v)
     (ZIP (MAP FST data_ops,data_args)) dvs` by
    (qpat_assum `select_log_args F flags (ZIP (MAP FST ops,args)) = ZIP (MAP FST data_ops,data_args)`
       (fn th => simp_tac bool_ss [Abbr `dvs`,log_non_indexed_values_select,GSYM th]) >>
     irule typedLogSplitCompleteTheory.select_log_args_list_rel >> simp[]) >>
  `EVERY (\p. (!x. FST p=Var x ==> not_fresh_at sm x) /\ (!lab. FST p<>Label lab)) data_ops` by
    (`data_ops=select_log_args F flags ops` by
       (qspecl_then [`flags`,`ops`] mp_tac eventLogSplitPropsTheory.split_log_ops_select >> simp[Abbr `data_ops`]) >>
     qpat_assum `data_ops=select_log_args F flags ops` (fn th => simp_tac bool_ss [th]) >>
     irule EVERY_select_log_args >> first_assum ACCEPT_TAC) >>
  suspend "field_sources"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[allocation_frame]:
`ci_mono topic_sa s1` by
  (mp_tac (Q.SPECL [`cap`,`topic_sa`]
    exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >> simp[]) >>
  `acyclic_struct_metadata cenv.ce_struct_fields /\
   sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv cx) fty = SOME tv ==>
        sz = type_memory_size tv) fields)` by
    (conj_tac >- fs[body_inv_def] >>
     qpat_assum `expr_sim_inv cenv cx env es`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
(* Select the original logical capture relation once. *)
`LENGTH flags = LENGTH args /\ LENGTH flags = LENGTH ops` by
  simp[Abbr `flags`] >>
`select_log_args F flags (ZIP (MAP FST ops,args)) =
 ZIP (MAP FST data_ops,data_args)` by
 (`MAP FST (select_log_args F flags (ZIP (MAP FST ops,args))) =
     MAP FST data_ops /\
   MAP SND (select_log_args F flags (ZIP (MAP FST ops,args))) = data_args` by
   (qspecl_then [`flags`,`ops`] mp_tac
      eventLogSplitPropsTheory.split_log_ops_select >>
    (impl_tac >- simp[Abbr `flags`]) >>
    disch_then (fn th => simp[Abbr `data_ops`,Abbr `data_args`,th,
      GSYM select_log_args_MAP,MAP_ZIP])) >>
  metis_tac[listTheory.ZIP_UNZIP, listTheory.UNZIP_MAP]) >>
`LIST_REL (\(op,e) v.
   expr_val_rel cx (expr_type e) v op t /\
   expr_val_at cenv cx (expr_type e) sa sm mid v op t /\
   expr_store_bound cx (expr_type e) v op t /\
   ptr_val_ok cx (expr_type e) v op G1 tn1 t /\
   (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G1 t) /\
   ?tv. evaluate_type (get_tenv cx) (expr_type e)=SOME tv /\
        value_has_type tv v)
   (ZIP (MAP FST data_ops,data_args)) dvs` by
 (qpat_assum `select_log_args F flags (ZIP (MAP FST ops,args)) =
      ZIP (MAP FST data_ops,data_args)`
    (fn th => simp_tac bool_ss [Abbr `dvs`,log_non_indexed_values_select,GSYM th]) >>
  irule typedLogSplitCompleteTheory.select_log_args_list_rel >> simp[]) >>
`EVERY (\p. (!x. FST p=Var x ==> not_fresh_at sm x) /\
            (!lab. FST p<>Label lab)) data_ops` by
 (`data_ops=select_log_args F flags ops` by
    (qspecl_then [`flags`,`ops`] mp_tac
      eventLogSplitPropsTheory.split_log_ops_select >>
     simp[Abbr `data_ops`]) >>
  qpat_assum `data_ops=select_log_args F flags ops`
    (fn th => simp_tac bool_ss [th]) >>
  irule EVERY_select_log_args >> first_assum ACCEPT_TAC) >>

  suspend "field_sources"
QED
*)

Resume compile_log_frag_full[field_sources]:
  `LENGTH data_ops = LENGTH data_args` by
    (qpat_assum `MAP SND data_ops = MAP (lowered_value_type cenv) data_args`
      (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `!local_name local_base local_size.
    local_region cenv mid.scopes ta local_name local_base local_size ==>
    local_base + local_size <= w2n bw \/ w2n bw + cap <= local_base` by
    (map_every qx_gen_tac [`local_name`,`local_base`,`local_size`] >> strip_tac >>
     qpat_assum `!name b len. local_region cenv mid.scopes ta name b len ==> regions_disjoint (w2n bw) cap b len`
       (qspecl_then [`local_name`,`local_base`,`local_size`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp_tac (srw_ss()) [loweringStateRelDefsTheory.regions_disjoint_def,DISJ_COMM]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid ta` by
    (qpat_assum `!H'. stmt_state_rel H' ctx func cenv cx mid tp ==> stmt_state_rel H' ctx func cenv cx mid ta`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  `!i. i < LENGTH data_ops ==>
   (\f dty dtv v.
    log_field_src cenv (get_tenv cx) (w2n bw) cap s1 Ga tna ta f dty dtv v \/
    (evaluate_type (get_tenv cx) dty = SOME dtv /\
     value_has_type dtv v /\ val_wf dtv v /\
     type_memory_bytes cenv dty = type_memory_size dtv /\
     (!x. FST f = Var x ==> not_fresh_at s1 x) /\
     is_bytestring_type dty /\ is_bytestring_type (SND f) /\
     (?xs stv sw len n. FST f = Var xs /\
      evaluate_type (get_tenv cx) (SND f) = SOME stv /\
      value_has_type stv v /\ val_wf stv v /\ lookup_var xs ta = SOME sw /\
      ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
       (?str. v = StringV str /\ len = LENGTH str)) /\
      n = 32 + 32 * word_size len /\ len + 31 < dimword(:256) /\
      n < dimword(:256) /\ n <= type_memory_size dtv /\
      w2n sw + n <= ta.vs_alloca_next /\ ptr_covers Ga tna xs ta n /\
      (!mem. mem_agree_outside tna.t_mem ta.vs_memory mem ==>
        val_in_memory stv v (w2n sw) mem) /\
      (!j. w2n sw <= j /\ j < w2n sw + val_footprint stv v ==>
        ~(w2n bw <= j /\ j < w2n bw + cap)))) \/
    (evaluate_type (get_tenv cx) dty = SOME dtv /\
     value_has_type dtv v /\ val_wf dtv v /\
     type_memory_bytes cenv dty = type_memory_size dtv /\
     type_memory_size dtv = 0 /\
     (!x. FST f = Var x ==> not_fresh_at s1 x) /\
     (!dst sc. compile_store_memory cenv (FST f) dst dty (SND f) sc = ((),sc)) /\
     (!p mem. val_in_memory dtv v p mem)))
     (EL i data_ops) (EL i dtys) (EL i dtvs) (EL i dvs)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. i < LENGTH data_ops ==> ?ltv ptv. _`
       (qspec_then `i` mp_tac) >> (impl_tac >- simp[]) >>
     disch_then (qx_choosel_then [`ltv`,`ptv`] strip_assume_tac) >>
     `i<LENGTH data_args /\ i<LENGTH dvs` by
       (qpat_assum `LIST_REL _ (ZIP (MAP FST data_ops,data_args)) dvs`
         (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
        qpat_assum `MAP SND data_ops = MAP (lowered_value_type cenv) data_args`
         (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
     qpat_assum `LIST_REL _ (ZIP (MAP FST data_ops,data_args)) dvs`
       (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     qpat_assum `EVERY (\p. (!x. FST p=Var x ==> not_fresh_at sm x) /\ (!lab. FST p<>Label lab)) data_ops`
       (mp_tac o Q.SPEC `i` o REWRITE_RULE [EVERY_EL]) >>
     simp[EL_ZIP,EL_MAP] >> rpt strip_tac >>
     qabbrev_tac `op=FST (EL i data_ops)` >>
     qabbrev_tac `sty=SND (EL i data_ops)` >>
     qabbrev_tac `lty=expr_type (EL i data_args)` >>
     qabbrev_tac `dty=EL i dtys` >> qabbrev_tac `dtv=EL i dtvs` >> qabbrev_tac `v=EL i dvs` >>
     `expr_val_rel cx lty v op ta` by
       (qspecl_then [`cenv`,`cx`,`func`,`lty`,`mid`,`mid`,`sa`,`sm`,`t`,`ta`,`v`,`op`]
         match_mp_tac bodyFullLogArgsTheory.pure_argument_value_kept >> simp[]) >>
     `expr_val_at cenv cx lty sa sm mid v op ta` by
       (mp_tac (Q.INST [`H` |-> `storage_trace_horizon mid.storage_trace`,
          `ty` |-> `lty`, `es` |-> `mid`, `es'` |-> `mid`, `ee` |-> `mid`,
          `sb` |-> `sm`, `sc` |-> `sm`, `s` |-> `t`, `t` |-> `ta`]
          (INST_TYPE [``:'a`` |-> ``:256``] stmtSimLogArgsTheory.log_frame_placement)) >>
        (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
     `!w. eval_operand op ta = SOME w <=> eval_operand op t = SOME w` by
       (Cases_on `op` >> simp_tac bool_ss [venomStateTheory.eval_operand_def] >> metis_tac[]) >>
     `expr_store_bound cx lty v op ta` by
       (qpat_assum `expr_store_bound cx lty v op t`
         (mp_tac o REWRITE_RULE [exprSimMemDefsTheory.expr_store_bound_def]) >>
        rewrite_tac [exprSimMemDefsTheory.expr_store_bound_def] >>
        rpt strip_tac >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
     `ptr_val_ok cx lty v op Ga tna ta` by
       (mp_tac (Q.SPECL [`cx`,`lty`,`v`,`op`,`G1`,`tn1`,`t`,`Ga`,`tna`,`ta`]
         logValueFramePtrTheory.ptr_val_ok_footprint_frame) >>
        impl_tac
        >- (rpt conj_tac
            >- first_assum ACCEPT_TAC
            >- (Cases_on `op`
                >- simp_tac (srw_ss()) [ptrDisciplineTheory.op_taint_def]
                >- metis_tac[] >> simp_tac (srw_ss()) [ptrDisciplineTheory.op_taint_def])
            >- metis_tac[] >- metis_tac[] >>
            map_every qx_gen_tac [`read_tv`,`read_w`] >> strip_tac >>
            `read_tv = ltv` by metis_tac[optionTheory.SOME_11] >>
            `val_wf read_tv v` by
              (irule (CONJUNCT1 exprSimAggregateChildrenTheory.typed_value_wf) >>
               qpat_assum `read_tv = ltv` (fn th => rewrite_tac [th]) >> first_assum ACCEPT_TAC) >>
            simp[] >> qx_gen_tac `byte_idx` >> rpt strip_tac >>
            `byte_idx < t.vs_alloca_next` by
              (match_mp_tac (Q.INST [`H` |-> `storage_trace_horizon mid.storage_trace`]
                (INST_TYPE [``:'a`` |-> ``:256``]
                  (Q.SPECL [`ctx`,`func`,`cenv`,`cx`,`lty`,`sa`,`sm`,`mid`,
                    `v`,`op`,`t`,`read_tv`,`read_w`,`byte_idx`]
                    allocationPtrTheory.expr_val_at_below_frontier))) >> simp[]) >>
            metis_tac[arithmeticTheory.NOT_LESS]) >> disch_then ACCEPT_TAC) >>
     `!x. op = Var x ==> not_fresh_at s1 x` by
       (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
        qexists_tac `sm` >> fs[ci_mono_def] >> decide_tac) >>
     `EL i data_ops = (op,sty)` by simp[Abbr `op`,Abbr `sty`] >>
     simp_tac bool_ss [pairTheory.FST, pairTheory.SND, Abbr `op`, Abbr `sty`, Abbr `dty`, Abbr `dtv`, Abbr `v`] >>
     drule_all log_full_field_capture_runtime >>
     simp[pairTheory.PAIR] >>
     disch_then (DISJ_CASES_THEN assume_tac)
     >- (disj1_tac >> first_assum ACCEPT_TAC) >>
     disj2_tac >> disj1_tac >> first_assum ACCEPT_TAC) >>
  suspend "packing_ready"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[field_sources]:
`LENGTH data_ops = LENGTH data_args` by
  (qpat_assum `MAP SND data_ops = MAP (lowered_value_type cenv) data_args`
    (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
`!local_name local_base local_size.
  local_region cenv mid.scopes ta local_name local_base local_size ==>
  local_base + local_size <= w2n bw \/ w2n bw + cap <= local_base` by
 (map_every qx_gen_tac [`local_name`,`local_base`,`local_size`] >> strip_tac >>
  qpat_assum `!name b len. local_region cenv mid.scopes ta name b len ==>
    regions_disjoint (w2n bw) cap b len`
    (qspecl_then [`local_name`,`local_base`,`local_size`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp_tac (srw_ss()) [loweringStateRelDefsTheory.regions_disjoint_def,DISJ_COMM]) >>
`stmt_state_rel (storage_trace_horizon mid.storage_trace)
    ctx func cenv cx mid ta` by
 (qpat_assum `!H'. stmt_state_rel H' ctx func cenv cx mid tp ==>
    stmt_state_rel H' ctx func cenv cx mid ta`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
(* One pointwise callback joins transport to the checked static packet. *)
`!i. i < LENGTH data_ops ==>
 log_field_src cenv (get_tenv cx) (w2n bw) cap s1 Ga tna ta
   (EL i data_ops) (EL i dtys) (EL i dtvs) (EL i dvs)` by
 (gen_tac >> strip_tac >>
  qpat_assum `!i. i < LENGTH data_ops ==> ?ltv ptv. _`
    (qspec_then `i` mp_tac) >> (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`ltv`,`ptv`] strip_assume_tac) >>
  `i<LENGTH data_args /\ i<LENGTH dvs` by
    (qpat_assum `LIST_REL _ (ZIP (MAP FST data_ops,data_args)) dvs`
      (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
     qpat_assum `MAP SND data_ops = MAP (lowered_value_type cenv) data_args`
      (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  qpat_assum `LIST_REL _ (ZIP (MAP FST data_ops,data_args)) dvs`
    (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  qpat_assum `EVERY (\p. (!x. FST p=Var x ==> not_fresh_at sm x) /\
                       (!lab. FST p<>Label lab)) data_ops`
    (mp_tac o Q.SPEC `i` o REWRITE_RULE [EVERY_EL]) >>
  simp[EL_ZIP,EL_MAP] >> rpt strip_tac >>
  qabbrev_tac `op=FST (EL i data_ops)` >>
  qabbrev_tac `sty=SND (EL i data_ops)` >>
  qabbrev_tac `lty=expr_type (EL i data_args)` >>
  qabbrev_tac `dty=EL i dtys` >>
  qabbrev_tac `dtv=EL i dtvs` >>
  qabbrev_tac `v=EL i dvs` >>
(* 5. Pointwise dynamic transport callback, after specializing that selected
   LIST_REL and capture freshness at one i; abbreviate
   op=FST(EL i data_ops),lty=expr_type(EL i data_args),v=EL i dvs.
   The callback's old placement is ALWAYS sa..sm, even at runtime ta. *)
`expr_val_rel cx lty v op ta` by
 (qspecl_then [`cenv`,`cx`,`func`,`lty`,`mid`,`mid`,`sa`,`sm`,`t`,`ta`,`v`,`op`]
    match_mp_tac bodyFullLogArgsTheory.pure_argument_value_kept >> simp[]) >>
`expr_val_at cenv cx lty sa sm mid v op ta` by
 (mp_tac (Q.INST [`H` |-> `storage_trace_horizon mid.storage_trace`,
    `ty` |-> `lty`, `es` |-> `mid`, `es'` |-> `mid`, `ee` |-> `mid`,
    `sb` |-> `sm`, `sc` |-> `sm`, `s` |-> `t`, `t` |-> `ta`]
    (INST_TYPE [``:'a`` |-> ``:256``]
      stmtSimLogArgsTheory.log_frame_placement)) >>
  impl_tac >- simp[] >> disch_then ACCEPT_TAC) >>
`!w. eval_operand op ta = SOME w <=> eval_operand op t = SOME w` by
 (Cases_on `op` >> simp_tac bool_ss [venomStateTheory.eval_operand_def] >>
  metis_tac[]) >>
`expr_store_bound cx lty v op ta` by
 (qpat_assum `expr_store_bound cx lty v op t`
    (mp_tac o REWRITE_RULE [exprSimMemDefsTheory.expr_store_bound_def]) >>
  rewrite_tac [exprSimMemDefsTheory.expr_store_bound_def] >>
  rpt strip_tac >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
`ptr_val_ok cx lty v op Ga tna ta` by
 (mp_tac (Q.SPECL [`cx`,`lty`,`v`,`op`,`G1`,`tn1`,`t`,`Ga`,`tna`,`ta`]
    logValueFramePtrTheory.ptr_val_ok_footprint_frame) >>
  impl_tac
  >- (rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- (Cases_on `op`
          >- simp_tac (srw_ss()) [ptrDisciplineTheory.op_taint_def]
          >- metis_tac[] >>
          simp_tac (srw_ss()) [ptrDisciplineTheory.op_taint_def])
      >- metis_tac[]
      >- metis_tac[] >>
      map_every qx_gen_tac [`read_tv`,`read_w`] >> strip_tac >>
      `read_tv = ltv` by
        (qpat_assum `evaluate_type (get_tenv cx) lty = SOME ltv`
          (fn left => qpat_assum
            `evaluate_type (get_tenv cx) lty = SOME read_tv`
            (fn right => ACCEPT_TAC (REWRITE_RULE [optionTheory.SOME_11]
              (TRANS (SYM right) left))))) >>
      `val_wf read_tv v` by
        (irule (CONJUNCT1 exprSimAggregateChildrenTheory.typed_value_wf) >>
         qpat_assum `read_tv = ltv` (fn th => rewrite_tac [th]) >>
         first_assum ACCEPT_TAC) >>
      simp[] >> qx_gen_tac `byte_idx` >> rpt strip_tac >>
      `byte_idx < t.vs_alloca_next` by
       (match_mp_tac (Q.INST
          [`H` |-> `storage_trace_horizon mid.storage_trace`]
          (INST_TYPE [``:'a`` |-> ``:256``]
            (Q.SPECL [`ctx`,`func`,`cenv`,`cx`,`lty`,`sa`,`sm`,`mid`,
              `v`,`op`,`t`,`read_tv`,`read_w`,`byte_idx`]
              allocationPtrTheory.expr_val_at_below_frontier))) >> simp[]) >>
      metis_tac[arithmeticTheory.NOT_LESS]) >>
  disch_then ACCEPT_TAC) >>

(* 6. Join this transported dynamic cut to the CHECKED static packet for i.
   No source positivity/Var/nominal bytes-capacity premise is introduced. *)
`!x. op = Var x ==> not_fresh_at s1 x` by
 (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
  qexists_tac `sm` >> fs[ci_mono_def] >> decide_tac) >>
`log_field_src cenv (get_tenv cx) (w2n bw) cap s1 Ga tna ta
   (op,sty) dty dtv v` by
 (mp_tac (Q.INST
    [`H` |-> `storage_trace_horizon mid.storage_trace`,
     `lty` |-> `lty`, `ltv` |-> `ltv`, `sty` |-> `sty`, `stv` |-> `ptv`,
     `dty` |-> `dty`, `dtv` |-> `dtv`, `v` |-> `v`, `op` |-> `op`,
     `sa` |-> `sa`, `sb` |-> `sm`, `packing_sa` |-> `s1`,
     `ee` |-> `mid`, `s` |-> `ta`, `G` |-> `Ga`, `tn` |-> `tna`,
     `b` |-> `w2n (bw:bytes32)`, `dest` |-> `topic_sa.cs_next_id`]
    (INST_TYPE [``:'a`` |-> ``:256``]
      logStoreDataFieldsOriginPtrTheory.log_field_src_from_capture)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC) >>

  fs[Abbr `op`,Abbr `sty`,Abbr `dty`,Abbr `dtv`,Abbr `v`,
    pairTheory.PAIR]) >>

  suspend "packing_ready"
QED
*)

Resume compile_log_frag_full[packing_ready]:
  `LENGTH data_args = LENGTH dtys /\ LENGTH dtys = LENGTH dtvs /\
   LENGTH dtys = LENGTH dvs` by
    (qpat_assum `MAP expr_type data_args = ltys` (mp_tac o Q.AP_TERM `LENGTH`) >>
     qpat_assum `arg_types_fit ltys dtys`
       (mp_tac o MATCH_MP LIST_REL_LENGTH o REWRITE_RULE [arg_types_fit_LIST_REL]) >>
     qpat_assum `OPT_MMAP _ dtys = SOME dtvs`
       (mp_tac o MATCH_MP LIST_REL_LENGTH o MATCH_MP vyperTypeABITheory.OPT_MMAP_LIST_REL) >>
     qpat_assum `LIST_REL _ dtys dvs` (mp_tac o MATCH_MP LIST_REL_LENGTH) >> simp[]) >>
  `~ta.vs_halted` by
    (qpat_assum `ta with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = tp`
       (mp_tac o Q.AP_TERM `\u. u.vs_halted`) >> simp[]) >>
  `LENGTH dtys = LENGTH data_ops /\ LENGTH dtvs = LENGTH data_ops /\
   LENGTH dvs = LENGTH data_ops` by metis_tac[] >>
  `lo <= ta.vs_alloca_next` by decide_tac >>
  `compile_log_store_data cenv data_ops dtys (Var q) 0 s1=((),s2)` by gvs[] >>
  qabbrev_tac `P = (\sa G tn s f dty dtv v.
    log_field_src cenv (get_tenv cx) (w2n bw) cap sa G tn s f dty dtv v \/
    (evaluate_type (get_tenv cx) dty = SOME dtv /\
     value_has_type dtv v /\ val_wf dtv v /\
     type_memory_bytes cenv dty = type_memory_size dtv /\
     (!x. FST f = Var x ==> not_fresh_at sa x) /\
     is_bytestring_type dty /\ is_bytestring_type (SND f) /\
     (?xs stv sw len n. FST f = Var xs /\
      evaluate_type (get_tenv cx) (SND f) = SOME stv /\
      value_has_type stv v /\ val_wf stv v /\ lookup_var xs s = SOME sw /\
      ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
       (?str. v = StringV str /\ len = LENGTH str)) /\
      n = 32 + 32 * word_size len /\ len + 31 < dimword(:256) /\
      n < dimword(:256) /\ n <= type_memory_size dtv /\
      w2n sw + n <= s.vs_alloca_next /\ ptr_covers G tn xs s n /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory stv v (w2n sw) mem) /\
      (!j. w2n sw <= j /\ j < w2n sw + val_footprint stv v ==>
        ~(w2n bw <= j /\ j < w2n bw + cap)))) \/
    (evaluate_type (get_tenv cx) dty = SOME dtv /\
     value_has_type dtv v /\ val_wf dtv v /\
     type_memory_bytes cenv dty = type_memory_size dtv /\
     type_memory_size dtv = 0 /\
     (!x. FST f = Var x ==> not_fresh_at sa x) /\
     (!dst sc. compile_store_memory cenv (FST f) dst dty (SND f) sc = ((),sc)) /\
     (!p mem. val_in_memory dtv v p mem)))` >>
  mp_tac (Q.INST
    [`cenv` |-> `cenv`, `tenv` |-> `get_tenv cx`, `xb` |-> `q`,
     `bw` |-> `bw`, `cap` |-> `cap`,
     `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (Q.SPEC `P` log_full_store_data_fold)) >>
  (impl_tac
   >- (conj_tac
       >- (rpt gen_tac >> simp_tac bool_ss [Abbr `P`] >>
           MATCH_ACCEPT_TAC (SIMP_RULE bool_ss [LET_THM] log_full_field_packet_frame)) >>
       conj_tac
       >- (rpt gen_tac >> simp_tac bool_ss [Abbr `P`] >>
           MATCH_ACCEPT_TAC (SIMP_RULE bool_ss [LET_THM] log_full_data_field_runtime_path)) >>
       rpt gen_tac >> simp_tac bool_ss [Abbr `P`] >>
       POP_ASSUM_LIST (K ALL_TAC) >>
       simp_tac bool_ss [log_field_src_def] >> metis_tac[])) >>
  disch_then drule >>
  disch_then (qspecl_then [`dtvs`,`dvs`,`ta`,`Ga`,`tna`] mp_tac) >>
  (impl_tac >- (simp_tac bool_ss [arithmeticTheory.ADD_CLAUSES] >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
      (simp_tac bool_ss [Abbr `P`] >>
       first_assum (ACCEPT_TAC o SIMP_RULE bool_ss []))])) >>
  disch_then (qx_choosel_then [`packed`,`Gpacked`,`tnpacked`] strip_assume_tac) >>
  suspend "packed"
QED

Resume compile_log_frag_full[packed]:
`local_ptrs_reserved cenv s1` by
 (qspecl_then [`cenv`,`topic_sa`,`s1`] match_mp_tac
    exprLoweringPropsTheory.local_ptrs_reserved_next_var >> fs[ci_mono_def]) >>
`typed_copy_state_frame s1 (w2n bw) cap ta packed` by
 (irule typedMemoryCopyTheory.typed_copy_state_frame_subinterval >>
  qexistsl_tac [`w2n (bw:bytes32)`,`type_memory_size_list dtvs`] >> simp[] >>
  qpat_assum `typed_copy_state_frame s1 (w2n bw + 0) _ ta packed`
    (ACCEPT_TAC o REWRITE_RULE [arithmeticTheory.ADD_CLAUSES])) >>
`copy_static packed = copy_static ta` by
 (qpat_assum `typed_copy_state_frame s1 (w2n bw) cap ta packed`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [typedMemoryCopyTheory.typed_copy_state_frame_def]) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[venomStateTheory.venom_state_component_equality] >> strip_tac >>
  simp[exprSimStorageCopyTheory.copy_static_def]) >>
`MEM (mk_inst topic_sa.cs_next_id ALLOCA [Lit (n2w cap)]
   [STRING #"%" (toString topic_sa.cs_next_var)]) (fn_insts func)` by
 (irule exprSimAllocTheory.buffer_alloc_code >>
  qexistsl_tac [`src`,`s1`] >> simp[]) >>
`!name lb len. local_region cenv mid.scopes ta name lb len ==>
  w2n bw + cap <= lb \/ lb + len <= w2n bw` by metis_tac[] >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 stmt_state_rel H ctx func cenv cx mid packed` by
 (gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid ta /\ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  mp_tac (Q.INST [`H` |-> `H`]
    (INST_TYPE [``:'a`` |-> ``:256``]
      (Q.SPECL [`ctx`,`func`,`cenv`,`cx`,`mid`,`s1`,`ta`,`packed`,
        `mk_inst topic_sa.cs_next_id ALLOCA [Lit (n2w cap)]
           [STRING #"%" (toString topic_sa.cs_next_var)]`,
        `w2n (bw:bytes32)`,`cap`]
        exprSimCopyTheory.copy_buffer_state_rel_frame))) >>
  (impl_tac >- (
    qpat_assum `typed_copy_state_frame s1 (w2n bw) cap ta packed`
      (strip_assume_tac o REWRITE_RULE
        [typedMemoryCopyTheory.typed_copy_state_frame_def,
         typedMemoryCopyTheory.typed_copy_frame_def]) >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
      simp_tac (srw_ss()) [venomInstTheory.mk_inst_def] >>
      first_assum ACCEPT_TAC])) >> disch_then ACCEPT_TAC) >>
suspend "packing_all_h"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[packing_ready]:
`LENGTH data_args = LENGTH dtys /\ LENGTH dtys = LENGTH dtvs /\
 LENGTH dtys = LENGTH dvs` by
 (qpat_assum `MAP expr_type data_args = ltys`
    (mp_tac o Q.AP_TERM `LENGTH`) >>
  qpat_assum `arg_types_fit ltys dtys`
    (mp_tac o MATCH_MP LIST_REL_LENGTH o REWRITE_RULE [arg_types_fit_LIST_REL]) >>
  qpat_assum `OPT_MMAP _ dtys = SOME dtvs`
    (mp_tac o MATCH_MP LIST_REL_LENGTH o MATCH_MP vyperTypeABITheory.OPT_MMAP_LIST_REL) >>
  qpat_assum `LIST_REL _ dtys dvs` (mp_tac o MATCH_MP LIST_REL_LENGTH) >> simp[]) >>
`~ta.vs_halted` by
 (qpat_assum `ta with <|vs_vars := _; vs_allocas := _;
    vs_alloca_next := _; vs_inst_idx := _|> = tp`
    (mp_tac o Q.AP_TERM `\u. u.vs_halted`) >> simp[]) >>
`LENGTH dtys = LENGTH data_ops /\ LENGTH dtvs = LENGTH data_ops /\
 LENGTH dvs = LENGTH data_ops` by metis_tac[] >>
`lo <= ta.vs_alloca_next` by decide_tac >>
`compile_log_store_data cenv data_ops dtys (Var q) 0 s1=((),s2)` by gvs[] >>
mp_tac (Q.INST
  [`cenv` |-> `cenv`, `tenv` |-> `get_tenv cx`,
   `xb` |-> `q`, `bw` |-> `bw`, `cap` |-> `cap`,
   `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
  (Q.SPECL [`data_ops`,`dtys`,`dtvs`,`dvs`,`0`,`s1`,`s2`,`ta`,`Ga`,`tna`]
    logStoreDataFieldsOriginPtrTheory.compile_log_store_data_origin_ptr_path)) >>
(impl_tac >- (rewrite_tac [arithmeticTheory.ADD_CLAUSES] >>
  rpt conj_tac >> first_assum ACCEPT_TAC)) >>
disch_then (qx_choosel_then [`packed`,`Gpacked`,`tnpacked`] strip_assume_tac) >>
suspend "packed"
QED
*)

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[packed]:
`local_ptrs_reserved cenv s1` by
 (qspecl_then [`cenv`,`topic_sa`,`s1`] match_mp_tac
    exprLoweringPropsTheory.local_ptrs_reserved_next_var >> fs[ci_mono_def]) >>
`typed_copy_state_frame s1 (w2n bw) cap ta packed` by
 (irule typedMemoryCopyTheory.typed_copy_state_frame_subinterval >>
  qexistsl_tac [`w2n (bw:bytes32)`,`type_memory_size_list dtvs`] >> simp[] >>
  qpat_assum `typed_copy_state_frame s1 (w2n bw + 0) _ ta packed`
    (ACCEPT_TAC o REWRITE_RULE [arithmeticTheory.ADD_CLAUSES])) >>
`copy_static packed = copy_static ta` by
 (qpat_assum `typed_copy_state_frame s1 (w2n bw) cap ta packed`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [typedMemoryCopyTheory.typed_copy_state_frame_def]) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[venomStateTheory.venom_state_component_equality] >> strip_tac >>
  simp[exprSimStorageCopyTheory.copy_static_def]) >>
`MEM (mk_inst topic_sa.cs_next_id ALLOCA [Lit (n2w cap)]
   [STRING #"%" (toString topic_sa.cs_next_var)]) (fn_insts func)` by
 (irule exprSimAllocTheory.buffer_alloc_code >>
  qexistsl_tac [`src`,`s1`] >> simp[]) >>
`!name lb len. local_region cenv mid.scopes ta name lb len ==>
  w2n bw + cap <= lb \/ lb + len <= w2n bw` by metis_tac[] >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 stmt_state_rel H ctx func cenv cx mid packed` by
 (gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid ta /\ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  mp_tac (Q.INST [`H` |-> `H`]
    (INST_TYPE [``:'a`` |-> ``:256``]
      (Q.SPECL [`ctx`,`func`,`cenv`,`cx`,`mid`,`s1`,`ta`,`packed`,
        `mk_inst topic_sa.cs_next_id ALLOCA [Lit (n2w cap)]
           [STRING #"%" (toString topic_sa.cs_next_var)]`,
        `w2n (bw:bytes32)`,`cap`]
        exprSimCopyTheory.copy_buffer_state_rel_frame))) >>
  (impl_tac >- (
    qpat_assum `typed_copy_state_frame s1 (w2n bw) cap ta packed`
      (strip_assume_tac o REWRITE_RULE
        [typedMemoryCopyTheory.typed_copy_state_frame_def,
         typedMemoryCopyTheory.typed_copy_frame_def]) >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
      simp_tac (srw_ss()) [venomInstTheory.mk_inst_def] >>
      first_assum ACCEPT_TAC])) >> disch_then ACCEPT_TAC) >>
suspend "packing_all_h"
QED
*)

Resume compile_log_frag_full[packing_all_h]:
`type_slot_size (TupleTV dtvs) <= dimword (:256)` by
 (mp_tac (Q.SPEC `dtvs` (CONJUNCT1 (CONJUNCT2
    valueEncodingPropsTheory.type_memory_size_slots))) >>
  simp_tac bool_ss [vyperValueTheory.type_slot_size_def] >> decide_tac) >>
`evaluate_type (get_tenv cx) (TupleT dtys) = SOME (TupleTV dtvs)` by
 (qpat_assum `type_slot_size (TupleTV dtvs) <= dimword (:256)` mp_tac >>
  qpat_assum `OPT_MMAP (evaluate_type (get_tenv cx)) dtys = SOME dtvs` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[Once vyperValueTheory.evaluate_type_def,
       vyperValueTheory.evaluate_types_OPT_MMAP,wordsTheory.dimword_def]) >>
`value_has_type (TupleTV dtvs) (ArrayV (TupleV dvs))` by
 (simp_tac bool_ss [vyperTypingTheory.value_has_type_def,
       vyperTypeDefaultsTheory.values_have_types_LIST_REL,LIST_REL_EL_EQN] >>
  conj_tac >- metis_tac[] >> qx_gen_tac `n` >> strip_tac >>
  qpat_assum `!i. i < LENGTH data_ops ==> ?ltv ptv. _`
    (qspec_then `n` mp_tac) >> (impl_tac >- decide_tac) >>
  disch_then (qx_choosel_then [`ltv`,`ptv`] strip_assume_tac) >>
  first_assum ACCEPT_TAC) >>
`dtys <> []` by
 (strip_tac >> `data_ops=[]` by fs[] >>
  fs[Abbr `data_ops`,Abbr `flags`]) >>
`abi_enc_plan (get_tenv cx) (TupleT dtys)
 (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys))` by
 (mp_tac (Q.INST [`env` |-> `env`, `es` |-> `es`,
    `tops` |-> `tops`, `ctx` |-> `ctx`, `tys` |-> `dtys`,
    `tv` |-> `TupleTV dtvs`]
    (SPEC_ALL bodySimLogArgsTheory.body_log_actual_tuple_abi_plan)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC) >>
`vyper_to_abi (get_tenv cx) (TupleT dtys) (ArrayV (TupleV dvs)) = SOME (ListV avs)` by
 simp[Once vyperABITheory.vyper_to_abi_def] >>
`!mem. mem_agree_outside tnpacked.t_mem packed.vs_memory mem ==>
 val_in_memory (TupleTV dtvs) (ArrayV (TupleV dvs)) (w2n bw) mem` by
 (simp[valueEncodingDefsTheory.val_in_memory_def] >>
  qpat_assum `!mem. mem_agree_outside tnpacked.t_mem packed.vs_memory mem ==>
    tuple_in_memory dvs dtvs (w2n bw + 0) mem`
    (mp_tac o REWRITE_RULE [arithmeticTheory.ADD_CLAUSES]) >> simp[]) >>
mp_tac (Q.INST [`env` |-> `get_tenv cx`, `ty` |-> `TupleT dtys`,
  `ei` |-> `type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys)`,
  `tv` |-> `TupleTV dtvs`, `v` |-> `ArrayV (TupleV dvs)`,
  `av` |-> `ListV avs`, `tainted` |-> `tnpacked.t_mem`,
  `initial_mem` |-> `packed.vs_memory`, `sb` |-> `w2n (bw:bytes32)`]
  abiEncoderSourceRobustTheory.abi_encoder_source_window_robust) >>
(impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
disch_then (qx_choosel_then [`enc_ty`,`enc_val`] strip_assume_tac) >>
suspend "abi_input"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[packing_all_h]:
(* Unbuilt continuation for the checked actual packed endpoint. *)
`type_slot_size (TupleTV dtvs) <= dimword (:256)` by
 (mp_tac (Q.SPEC `dtvs` (CONJUNCT1 (CONJUNCT2
    valueEncodingPropsTheory.type_memory_size_slots))) >>
  simp_tac bool_ss [vyperValueTheory.type_slot_size_def] >> decide_tac) >>
`evaluate_type (get_tenv cx) (TupleT dtys) = SOME (TupleTV dtvs)` by
 (qpat_assum `type_slot_size (TupleTV dtvs) <= dimword (:256)` mp_tac >>
  qpat_assum `OPT_MMAP (evaluate_type (get_tenv cx)) dtys = SOME dtvs` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[Once vyperValueTheory.evaluate_type_def,
       vyperValueTheory.evaluate_types_OPT_MMAP,wordsTheory.dimword_def]) >>
`value_has_type (TupleTV dtvs) (ArrayV (TupleV dvs))` by
 (simp_tac bool_ss [vyperTypingTheory.value_has_type_def,
       vyperTypeDefaultsTheory.values_have_types_LIST_REL,LIST_REL_EL_EQN] >>
  conj_tac >- metis_tac[] >> qx_gen_tac `n` >> strip_tac >>
  qpat_assum `!i. i < LENGTH data_ops ==> ?ltv ptv. _`
    (qspec_then `n` mp_tac) >> (impl_tac >- decide_tac) >>
  disch_then (qx_choosel_then [`ltv`,`ptv`] strip_assume_tac) >>
  first_assum ACCEPT_TAC) >>
`dtys <> []` by
 (strip_tac >> `data_ops=[]` by fs[] >>
  fs[Abbr `data_ops`,Abbr `flags`]) >>
`abi_enc_plan (get_tenv cx) (TupleT dtys)
 (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys))` by
 (mp_tac (Q.INST [`env` |-> `env`, `es` |-> `es`,
    `tops` |-> `tops`, `ctx` |-> `ctx`, `tys` |-> `dtys`,
    `tv` |-> `TupleTV dtvs`]
    (SPEC_ALL bodySimLogArgsTheory.body_log_actual_tuple_abi_plan)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC) >>
`vyper_to_abi (get_tenv cx) (TupleT dtys) (ArrayV (TupleV dvs)) = SOME (ListV avs)` by
 simp[Once vyperABITheory.vyper_to_abi_def] >>
`!mem. mem_agree_outside tnpacked.t_mem packed.vs_memory mem ==>
 val_in_memory (TupleTV dtvs) (ArrayV (TupleV dvs)) (w2n bw) mem` by
 (simp[valueEncodingDefsTheory.val_in_memory_def] >>
  qpat_assum `!mem. mem_agree_outside tnpacked.t_mem packed.vs_memory mem ==>
    tuple_in_memory dvs dtvs (w2n bw + 0) mem`
    (mp_tac o REWRITE_RULE [arithmeticTheory.ADD_CLAUSES]) >> simp[]) >>
mp_tac (Q.INST [`env` |-> `get_tenv cx`, `ty` |-> `TupleT dtys`,
  `ei` |-> `type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys)`,
  `tv` |-> `TupleTV dtvs`, `v` |-> `ArrayV (TupleV dvs)`,
  `av` |-> `ListV avs`, `tainted` |-> `tnpacked.t_mem`,
  `initial_mem` |-> `packed.vs_memory`, `sb` |-> `w2n (bw:bytes32)`]
  abiEncoderSourceRobustTheory.abi_encoder_source_window_robust) >>
(impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
disch_then (qx_choosel_then [`enc_ty`,`enc_val`] strip_assume_tac) >>
suspend "abi_input"
QED
*)

Resume compile_log_frag_full[abi_input]:
drule exprSimStorageCopyTheory.copy_static_fields >> strip_tac >>
`stmt_state_rel (storage_trace_horizon mid.storage_trace)
 ctx func cenv cx mid packed` by
 (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid packed`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
`gas_path_mem ctx func ta 0 (OK packed)` by
 (qpat_assum `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (ta,Ga,tna) [] (OK packed,Gpacked,tnpacked)`
    (qspec_then `DF (storage_trace_horizon mid.storage_trace)` mp_tac) >>
  disch_then (mp_tac o CONJUNCT1 o MATCH_MP
    fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
  disch_then (mp_tac o MATCH_MP fragGasOriginTheory.gas_origin_path_erase) >>
  simp[fragGasModeTheory.gas_marked_path_def]) >>
`alloca_inv ta` by
 (qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace)
    ctx func cenv cx mid ta`
    (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [stmt_state_rel_def])) >>
`!u. gas_path_mem ctx func ta 0 (OK u) ==> alloca_inv u` by
 (rpt strip_tac >>
  drule_all bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv >> simp[]) >>
`alloca_history func packed` by
 (drule_all fragGasPathFrameMemTheory.gas_path_mem_zero_history >> simp[]) >>
`allocas_from lo packed /\ lo <= packed.vs_alloca_next` by
 (fs[ptrDisciplineTheory.allocas_from_def] >> first_assum ACCEPT_TAC) >>
`ci_mono s1 s2` by
 (mp_tac (Q.SPECL [`cenv`,`data_ops`,`dtys`,`Var q`,`0`,`s1`]
    eventLoweringStructureTheory.compile_log_store_data_ci_mono) >> simp[]) >>
`local_ptrs_reserved cenv s2` by
 (qspecl_then [`cenv`,`s1`,`s2`] match_mp_tac
    exprLoweringPropsTheory.local_ptrs_reserved_next_var >> fs[ci_mono_def]) >>
qabbrev_tac `outcap=MAX 32 (abi_size_bound cenv.ce_struct_fields (TupleT dtys))` >>
`outcap < dimword (:256)` by
 (fs[Abbr `outcap`,Abbr `dtys`,log_alloc_ok_def] >>
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> decide_tac) >>
`compile_alloc_buffer outcap s2=(dst,s3)` by
 (fs[Abbr `outcap`,Abbr `dtys`,Abbr `flags`] >> first_assum ACCEPT_TAC) >>
mp_tac (Q.INST
 [`n` |-> `outcap`, `sa` |-> `s2`, `sb` |-> `s3`, `buf` |-> `dst`,
  `s` |-> `packed`, `G` |-> `Gpacked`, `tn` |-> `tnpacked`, `es` |-> `mid`,
  `H` |-> `storage_trace_horizon mid.storage_trace`,
  `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
 (INST_TYPE [``:'a`` |-> ``:256``, ``:'b`` |-> ``:256``]
   bodyFullAllocaFreshTheory.alloc_buffer_origin_ptr_path)) >>
(impl_tac >- (rpt conj_tac >> simp[])) >>
disch_then (qx_choosel_then [`out_q`,`out_bw`,`prepared`,`Gprep`,`tnprep`]
 strip_assume_tac) >>
suspend "output_alloca"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[abi_input]:
(* Unbuilt: the actual second ALLOCA after the fixed packed endpoint. *)
drule exprSimStorageCopyTheory.copy_static_fields >> strip_tac >>
`stmt_state_rel (storage_trace_horizon mid.storage_trace)
 ctx func cenv cx mid packed` by
 (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid packed`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
`gas_path_mem ctx func ta 0 (OK packed)` by
 (qpat_assum `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (ta,Ga,tna) [] (OK packed,Gpacked,tnpacked)`
    (qspec_then `DF (storage_trace_horizon mid.storage_trace)` mp_tac) >>
  disch_then (mp_tac o CONJUNCT1 o MATCH_MP
    fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
  disch_then (mp_tac o MATCH_MP fragGasOriginTheory.gas_origin_path_erase) >>
  simp[fragGasModeTheory.gas_marked_path_def]) >>
`alloca_inv ta` by
 (qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace)
    ctx func cenv cx mid ta`
    (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [stmt_state_rel_def])) >>
`!u. gas_path_mem ctx func ta 0 (OK u) ==> alloca_inv u` by
 (rpt strip_tac >>
  drule_all bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv >> simp[]) >>
`alloca_history func packed` by
 (drule_all fragGasPathFrameMemTheory.gas_path_mem_zero_history >> simp[]) >>
`allocas_from lo packed /\ lo <= packed.vs_alloca_next` by
 (fs[ptrDisciplineTheory.allocas_from_def] >> first_assum ACCEPT_TAC) >>
`ci_mono s1 s2` by
 (mp_tac (Q.SPECL [`cenv`,`data_ops`,`dtys`,`Var q`,`0`,`s1`]
    eventLoweringStructureTheory.compile_log_store_data_ci_mono) >> simp[]) >>
`local_ptrs_reserved cenv s2` by
 (qspecl_then [`cenv`,`s1`,`s2`] match_mp_tac
    exprLoweringPropsTheory.local_ptrs_reserved_next_var >> fs[ci_mono_def]) >>
qabbrev_tac `outcap=MAX 32 (abi_size_bound cenv.ce_struct_fields (TupleT dtys))` >>
`outcap < dimword (:256)` by
 (fs[Abbr `outcap`,Abbr `dtys`,log_alloc_ok_def] >>
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> decide_tac) >>
`compile_alloc_buffer outcap s2=(dst,s3)` by
 (fs[Abbr `outcap`,Abbr `dtys`,Abbr `flags`] >> first_assum ACCEPT_TAC) >>
mp_tac (Q.INST
 [`n` |-> `outcap`, `sa` |-> `s2`, `sb` |-> `s3`, `buf` |-> `dst`,
  `s` |-> `packed`, `G` |-> `Gpacked`, `tn` |-> `tnpacked`, `es` |-> `mid`,
  `H` |-> `storage_trace_horizon mid.storage_trace`,
  `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
 (INST_TYPE [``:'a`` |-> ``:256``, ``:'b`` |-> ``:256``]
   bodyFullAllocaFreshTheory.alloc_buffer_origin_ptr_path)) >>
(impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
disch_then (qx_choosel_then [`out_q`,`out_bw`,`prepared`,`Gprep`,`tnprep`]
 strip_assume_tac) >>
suspend "output_alloca"
QED
*)

Resume compile_log_frag_full[output_alloca]:
`prepared.vs_memory = packed.vs_memory` by
 (qpat_assum `prepared with <| vs_vars := _; vs_allocas := _;
    vs_alloca_next := _; vs_inst_idx := _|> = packed`
    (mp_tac o Q.AP_TERM `\u. u.vs_memory`) >> simp[]) >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 stmt_state_rel H ctx func cenv cx mid prepared` by
 (rpt strip_tac >>
  qpat_assum `!H'. stmt_state_rel H' ctx func cenv cx mid packed ==>
    stmt_state_rel H' ctx func cenv cx mid prepared`
    (qspec_then `H` match_mp_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid packed`
    (qspec_then `H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
`w2n bw + cap <= packed.vs_alloca_next` by
 (qpat_assum `copy_static packed = copy_static ta`
    (mp_tac o MATCH_MP exprSimStorageCopyTheory.copy_static_fields) >>
  strip_tac >> simp[]) >>
`val_footprint (TupleTV dtvs) (ArrayV (TupleV dvs)) <= cap` by
 simp[loweringPostsTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def] >>
`!i. i < val_footprint (TupleTV dtvs) (ArrayV (TupleV dvs)) ==>
  (w2n bw+i IN tnprep.t_mem <=> w2n bw+i IN tnpacked.t_mem)` by
 (rpt strip_tac >>
  `~(packed.vs_alloca_next <= w2n bw+i)` by decide_tac >>
  qpat_assum `!i. i IN tnprep.t_mem <=> _`
    (qspec_then `w2n (bw:bytes32)+i` mp_tac) >> simp[]) >>
`!mem. mem_agree_outside tnprep.t_mem prepared.vs_memory mem ==>
 abi_encoder_window_input
   (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys))
   enc_ty enc_val (w2n bw)
   (val_footprint (TupleTV dtvs) (ArrayV (TupleV dvs))) mem` by
 (qx_gen_tac `mem` >> strip_tac >>
  mp_tac (Q.SPECL [`tnpacked.t_mem`,`tnprep.t_mem`,`packed.vs_memory`,
    `prepared.vs_memory`,`w2n (bw:bytes32)`,`w2n (bw:bytes32)`,
    `val_footprint (TupleTV dtvs) (ArrayV (TupleV dvs))`,`mem`]
    robustCopyTransportPtrTheory.copied_window_agree_witness) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,simp[]])) >>
  disch_then (qx_choose_then `mix` strip_assume_tac) >>
  qpat_assum `!mem. mem_agree_outside tnpacked.t_mem packed.vs_memory mem ==>
    abi_encoder_window_input _ enc_ty enc_val _ _ mem`
    (qspec_then `mix` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (mp_tac o MATCH_MP abiEncoderWindowTheory.abi_encoder_window_input_mem_agree) >>
  disch_then (qspec_then `mem` match_mp_tac) >> first_assum ACCEPT_TAC) >>
suspend "prepared_abi_input"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[output_alloca]:
`prepared.vs_memory = packed.vs_memory` by
 (qpat_assum `prepared with <| vs_vars := _; vs_allocas := _;
    vs_alloca_next := _; vs_inst_idx := _|> = packed`
    (mp_tac o Q.AP_TERM `\u. u.vs_memory`) >> simp[]) >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 stmt_state_rel H ctx func cenv cx mid prepared` by
 (rpt strip_tac >>
  qpat_assum `!H'. stmt_state_rel H' ctx func cenv cx mid packed ==>
    stmt_state_rel H' ctx func cenv cx mid prepared`
    (qspec_then `H` match_mp_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid packed`
    (qspec_then `H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
`w2n bw + cap <= packed.vs_alloca_next` by
 (qpat_assum `copy_static packed = copy_static ta`
    (mp_tac o MATCH_MP exprSimStorageCopyTheory.copy_static_fields) >>
  strip_tac >> simp[]) >>
`val_footprint (TupleTV dtvs) (ArrayV (TupleV dvs)) <= cap` by
 simp[loweringPostsTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def] >>
`!i. i < val_footprint (TupleTV dtvs) (ArrayV (TupleV dvs)) ==>
  (w2n bw+i IN tnprep.t_mem <=> w2n bw+i IN tnpacked.t_mem)` by
 (rpt strip_tac >>
  `~(packed.vs_alloca_next <= w2n bw+i)` by decide_tac >>
  qpat_assum `!i. i IN tnprep.t_mem <=> _`
    (qspec_then `w2n (bw:bytes32)+i` mp_tac) >> simp[]) >>
`!mem. mem_agree_outside tnprep.t_mem prepared.vs_memory mem ==>
 abi_encoder_window_input
   (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys))
   enc_ty enc_val (w2n bw)
   (val_footprint (TupleTV dtvs) (ArrayV (TupleV dvs))) mem` by
 (qx_gen_tac `mem` >> strip_tac >>
  mp_tac (Q.SPECL [`tnpacked.t_mem`,`tnprep.t_mem`,`packed.vs_memory`,
    `prepared.vs_memory`,`w2n (bw:bytes32)`,`w2n (bw:bytes32)`,
    `val_footprint (TupleTV dtvs) (ArrayV (TupleV dvs))`,`mem`]
    robustCopyTransportPtrTheory.copied_window_agree_witness) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,simp[]])) >>
  disch_then (qx_choose_then `mix` strip_assume_tac) >>
  qpat_assum `!mem. mem_agree_outside tnpacked.t_mem packed.vs_memory mem ==>
    abi_encoder_window_input _ enc_ty enc_val _ _ mem`
    (qspec_then `mix` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (mp_tac o MATCH_MP abiEncoderWindowTheory.abi_encoder_window_input_mem_agree) >>
  disch_then (qspec_then `mem` match_mp_tac) >> first_assum ACCEPT_TAC) >>
suspend "prepared_abi_input"
QED
*)

Resume compile_log_frag_full[prepared_abi_input]:
`ci_mono s2 s3` by
 (mp_tac (Q.SPECL [`outcap`,`s2`] exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >> simp[]) >>
`not_fresh_at s2 q /\ not_fresh_at s3 q` by
 (qpat_assum `not_fresh_at s1 q` mp_tac >>
  qpat_assum `ci_mono s1 s2` mp_tac >>
  qpat_assum `ci_mono s2 s3` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp[ci_mono_def] >>
  rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
  qexists_tac `s1` >> simp[] >> decide_tac) >>
`ptr_covers Gpacked tnpacked q packed cap /\ lookup_var q packed = SOME bw` by
 (qpat_assum `typed_copy_state_frame s1 (w2n bw) cap ta packed`
    (strip_assume_tac o REWRITE_RULE [typedMemoryCopyTheory.typed_copy_state_frame_def]) >>
  `lookup_var q packed = lookup_var q ta` by
   (qpat_assum `!x. not_fresh_at s1 x ==> lookup_var x packed = lookup_var x ta`
     (qspec_then `q` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  `FLOOKUP Gpacked q = FLOOKUP Ga q /\
   op_taint tnpacked (Var q) = op_taint tna (Var q)` by
   (qpat_assum `!p. not_fresh_at s1 p ==> FLOOKUP Gpacked p = FLOOKUP Ga p /\ _`
     (qspec_then `q` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  conj_tac >-
   (mp_tac (Q.INST [`G` |-> `Ga`, `tn` |-> `tna`, `p` |-> `q`,
      `s` |-> `ta`, `n` |-> `cap`, `H` |-> `Gpacked`,
      `u` |-> `tnpacked`, `t` |-> `packed`]
      (SPEC_ALL decoderGhostFramePtrTheory.ptr_covers_frame)) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then ACCEPT_TAC) >> simp[]) >>
`ptr_covers Gprep tnprep q prepared cap /\ lookup_var q prepared = SOME bw` by
 (`lookup_var q prepared = lookup_var q packed /\
   FLOOKUP Gprep q = FLOOKUP Gpacked q /\
   op_taint tnprep (Var q) = op_taint tnpacked (Var q)` by
   (qpat_assum `!x. not_fresh_at s2 x ==> lookup_var x prepared = lookup_var x packed /\ _`
     (qspec_then `q` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  conj_tac >-
   (mp_tac (Q.INST [`G` |-> `Gpacked`, `tn` |-> `tnpacked`, `p` |-> `q`,
      `s` |-> `packed`, `n` |-> `cap`, `H` |-> `Gprep`,
      `u` |-> `tnprep`, `t` |-> `prepared`]
      (SPEC_ALL decoderGhostFramePtrTheory.ptr_covers_frame)) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then ACCEPT_TAC) >> simp[]) >>
`abi_size_bound cenv.ce_struct_fields (TupleT dtys) =
 vyper_abi_size_bound (get_tenv cx) (TupleT dtys)` by
 (drule_all abiTypeBoundPropsTheory.abi_props_vyper_typed >> simp[]) >>
`abi_size_bound cenv.ce_struct_fields (TupleT dtys) <= outcap` by
 simp[Abbr `outcap`] >>
`LENGTH (enc enc_ty enc_val) <= outcap` by decide_tac >>
`!mem. mem_agree_outside tnprep.t_mem prepared.vs_memory mem ==>
 abi_encoder_window_input
   (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys))
   enc_ty enc_val (w2n bw) cap mem` by
 (qx_gen_tac `mem` >> strip_tac >>
  irule abiEncoderWindowTheory.abi_encoder_window_input_capacity >>
  qexists_tac `val_footprint (TupleTV dtvs) (ArrayV (TupleV dvs))` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!mem. mem_agree_outside tnprep.t_mem prepared.vs_memory mem ==>
    abi_encoder_window_input _ enc_ty enc_val _
      (val_footprint (TupleTV dtvs) (ArrayV (TupleV dvs))) mem`
    (qspec_then `mem` match_mp_tac) >> first_assum ACCEPT_TAC) >>
suspend "prepared_resources"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[prepared_abi_input]:
`ci_mono s2 s3` by
 (mp_tac (Q.SPECL [`outcap`,`s2`] exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >> simp[]) >>
`not_fresh_at s2 q /\ not_fresh_at s3 q` by
 (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
  qexists_tac `s1` >> fs[ci_mono_def] >> decide_tac) >>
`ptr_covers Gpacked tnpacked q packed cap /\ lookup_var q packed = SOME bw` by
 (qpat_assum `typed_copy_state_frame s1 (w2n bw) cap ta packed`
    (strip_assume_tac o REWRITE_RULE [typedMemoryCopyTheory.typed_copy_state_frame_def]) >>
  `lookup_var q packed = lookup_var q ta` by
   (qpat_assum `!x. not_fresh_at s1 x ==> lookup_var x packed = lookup_var x ta`
     (qspec_then `q` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  `FLOOKUP Gpacked q = FLOOKUP Ga q /\
   op_taint tnpacked (Var q) = op_taint tna (Var q)` by
   (qpat_assum `!p. not_fresh_at s1 p ==> FLOOKUP Gpacked p = FLOOKUP Ga p /\ _`
     (qspec_then `q` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  conj_tac >-
   (mp_tac (Q.INST [`G` |-> `Ga`, `tn` |-> `tna`, `p` |-> `q`,
      `s` |-> `ta`, `n` |-> `cap`, `H` |-> `Gpacked`,
      `u` |-> `tnpacked`, `t` |-> `packed`]
      (SPEC_ALL decoderGhostFramePtrTheory.ptr_covers_frame)) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then ACCEPT_TAC) >> simp[]) >>
`ptr_covers Gprep tnprep q prepared cap /\ lookup_var q prepared = SOME bw` by
 (`lookup_var q prepared = lookup_var q packed /\
   FLOOKUP Gprep q = FLOOKUP Gpacked q /\
   op_taint tnprep (Var q) = op_taint tnpacked (Var q)` by
   (qpat_assum `!x. not_fresh_at s2 x ==> lookup_var x prepared = lookup_var x packed /\ _`
     (qspec_then `q` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  conj_tac >-
   (mp_tac (Q.INST [`G` |-> `Gpacked`, `tn` |-> `tnpacked`, `p` |-> `q`,
      `s` |-> `packed`, `n` |-> `cap`, `H` |-> `Gprep`,
      `u` |-> `tnprep`, `t` |-> `prepared`]
      (SPEC_ALL decoderGhostFramePtrTheory.ptr_covers_frame)) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then ACCEPT_TAC) >> simp[]) >>
`abi_size_bound cenv.ce_struct_fields (TupleT dtys) =
 vyper_abi_size_bound (get_tenv cx) (TupleT dtys)` by
 (qpat_assum `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)`
   (fn sf_th => qpat_assum
     `evaluate_type (get_tenv cx) (TupleT dtys) = SOME (TupleTV dtvs)`
     (fn eval_th => mp_tac (MATCH_MP
       abiTypeBoundPropsTheory.abi_props_vyper_typed (CONJ sf_th eval_th)))) >>
  simp[]) >>
`abi_size_bound cenv.ce_struct_fields (TupleT dtys) <= outcap` by
 simp[Abbr `outcap`] >>
`LENGTH (enc enc_ty enc_val) <= outcap` by decide_tac >>
`!mem. mem_agree_outside tnprep.t_mem prepared.vs_memory mem ==>
 abi_encoder_window_input
   (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys))
   enc_ty enc_val (w2n bw) cap mem` by
 (qx_gen_tac `mem` >> strip_tac >>
  irule abiEncoderWindowTheory.abi_encoder_window_input_capacity >>
  qexists_tac `val_footprint (TupleTV dtvs) (ArrayV (TupleV dvs))` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!mem. mem_agree_outside tnprep.t_mem prepared.vs_memory mem ==>
    abi_encoder_window_input _ enc_ty enc_val _
      (val_footprint (TupleTV dtvs) (ArrayV (TupleV dvs))) mem`
    (qspec_then `mem` match_mp_tac) >> first_assum ACCEPT_TAC) >>
suspend "prepared_resources"
QED
*)

Resume compile_log_frag_full[prepared_resources]:
`stmt_state_rel (storage_trace_horizon mid.storage_trace)
 ctx func cenv cx mid prepared` by
 (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid prepared`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
`alloca_inv prepared /\ alloca_room ctx func prepared` by
 (qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace)
    ctx func cenv cx mid prepared`
    (mp_tac o CONJUNCT2 o REWRITE_RULE [stmt_state_rel_def]) >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
`FLOOKUP prepared.vs_allocas topic_sa.cs_next_id = SOME (w2n bw,cap)` by
 (`FLOOKUP packed.vs_allocas topic_sa.cs_next_id = SOME (w2n bw,cap)` by simp[] >>
  qpat_assum `!aid e. FLOOKUP packed.vs_allocas aid = SOME e ==>
    FLOOKUP prepared.vs_allocas aid = SOME e`
    (qspecl_then [`topic_sa.cs_next_id`,`(w2n (bw:bytes32),cap)`] match_mp_tac) >>
  first_assum ACCEPT_TAC) >>
`topic_sa.cs_next_id < s2.cs_next_id /\ s2.cs_next_id < s3.cs_next_id` by
 (drule_all log_full_declared_data_allocation_sites >> simp[]) >>
`venomMemDefs$regions_disjoint (w2n bw,cap) (w2n out_bw,outcap)` by
 (mp_tac (Q.INST [`s` |-> `prepared`, `id` |-> `topic_sa.cs_next_id`,
    `other` |-> `s2.cs_next_id`, `b` |-> `w2n (bw:bytes32)`, `sz` |-> `cap`,
    `p` |-> `w2n (out_bw:bytes32)`, `n` |-> `outcap`]
    (SPEC_ALL allocaSiteResourceTheory.alloca_site_registered_disjoint)) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,decide_tac])) >>
  disch_then ACCEPT_TAC) >>
`w2n bw + cap <= prepared.vs_alloca_next /\
 w2n out_bw + LENGTH (enc enc_ty enc_val) <= prepared.vs_alloca_next /\
 venomMemDefs$regions_disjoint (w2n bw,cap)
   (w2n out_bw,LENGTH (enc enc_ty enc_val))` by
 (qpat_assum `venomMemDefs$regions_disjoint (w2n bw,cap) (w2n out_bw,outcap)` mp_tac >>
  simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
suspend "prepared_sites"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[prepared_resources]:
`stmt_state_rel (storage_trace_horizon mid.storage_trace)
 ctx func cenv cx mid prepared` by
 (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid prepared`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
`alloca_inv prepared /\ alloca_room ctx func prepared` by
 (qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace)
    ctx func cenv cx mid prepared`
    (mp_tac o CONJUNCT2 o REWRITE_RULE [stmt_state_rel_def]) >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
`FLOOKUP prepared.vs_allocas topic_sa.cs_next_id = SOME (w2n bw,cap)` by
 (`FLOOKUP packed.vs_allocas topic_sa.cs_next_id = SOME (w2n bw,cap)` by simp[] >>
  qpat_assum `!aid e. FLOOKUP packed.vs_allocas aid = SOME e ==>
    FLOOKUP prepared.vs_allocas aid = SOME e`
    (qspecl_then [`topic_sa.cs_next_id`,`(w2n (bw:bytes32),cap)`] match_mp_tac) >>
  first_assum ACCEPT_TAC) >>
`topic_sa.cs_next_id < s2.cs_next_id /\ s2.cs_next_id < s3.cs_next_id` by
 (drule_all stmtSimLogSuffixActualTheory.log_declared_data_allocation_sites >> simp[]) >>
`venomMemDefs$regions_disjoint (w2n bw,cap) (w2n out_bw,outcap)` by
 (mp_tac (Q.INST [`s` |-> `prepared`, `id` |-> `topic_sa.cs_next_id`,
    `other` |-> `s2.cs_next_id`, `b` |-> `w2n (bw:bytes32)`, `sz` |-> `cap`,
    `p` |-> `w2n (out_bw:bytes32)`, `n` |-> `outcap`]
    (SPEC_ALL allocaSiteResourceTheory.alloca_site_registered_disjoint)) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,decide_tac])) >>
  disch_then ACCEPT_TAC) >>
`w2n bw + cap <= prepared.vs_alloca_next /\
 w2n out_bw + LENGTH (enc enc_ty enc_val) <= prepared.vs_alloca_next /\
 venomMemDefs$regions_disjoint (w2n bw,cap)
   (w2n out_bw,LENGTH (enc enc_ty enc_val))` by
 (qpat_assum `venomMemDefs$regions_disjoint (w2n bw,cap) (w2n out_bw,outcap)` mp_tac >>
  simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
suspend "prepared_sites"
QED
*)

Resume compile_log_frag_full[prepared_sites]:
`topic_sa.cs_next_id NOTIN frag_ids s3 s4 /\
 s2.cs_next_id NOTIN frag_ids s3 s4 /\
 (!inst. MEM inst (fn_insts func) /\ inst.inst_id IN frag_ids s3 s4 /\
   inst.inst_opcode = ALLOCA ==>
   inst.inst_operands = [Lit 32w] /\
   ?p. inst.inst_outputs = [p] /\ ~not_fresh_at s3 p)` by
 (drule_all log_full_declared_data_encoder_sites >> simp[]) >>
`!inst b sz.
 MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
 inst.inst_id IN frag_ids s3 s4 /\
 FLOOKUP prepared.vs_allocas inst.inst_id = SOME (b,sz) ==>
 sz = 32 /\
 venomMemDefs$regions_disjoint (w2n bw,cap) (b,sz) /\
 venomMemDefs$regions_disjoint
   (w2n out_bw,LENGTH (enc enc_ty enc_val)) (b,sz)` by
 (map_every qx_gen_tac [`inst`,`b`,`sz`] >> strip_tac >>
  `inst.inst_operands = [Lit 32w]` by
   (qpat_assum `!inst. MEM inst (fn_insts func) /\ _ ==> _`
     (qspec_then `inst` mp_tac) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `sz = 32` by
   (qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace)
      ctx func cenv cx mid prepared`
      (mp_tac o List.last o CONJUNCTS o REWRITE_RULE [stmt_state_rel_def]) >>
    disch_then (qspecl_then [`inst`,`32w`,`b`,`sz`] mp_tac) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `venomMemDefs$regions_disjoint (w2n bw,cap) (b,sz)` by
   (mp_tac (Q.INST [`s` |-> `prepared`, `id` |-> `topic_sa.cs_next_id`,
      `other` |-> `inst.inst_id`, `b` |-> `w2n (bw:bytes32)`, `sz` |-> `cap`,
      `p` |-> `b`, `n` |-> `sz`]
      (SPEC_ALL allocaSiteResourceTheory.alloca_site_registered_disjoint)) >>
    (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,metis_tac[]])) >>
    disch_then ACCEPT_TAC) >>
  `venomMemDefs$regions_disjoint (w2n out_bw,outcap) (b,sz)` by
   (mp_tac (Q.INST [`s` |-> `prepared`, `id` |-> `s2.cs_next_id`,
      `other` |-> `inst.inst_id`, `b` |-> `w2n (out_bw:bytes32)`, `sz` |-> `outcap`,
      `p` |-> `b`, `n` |-> `sz`]
      (SPEC_ALL allocaSiteResourceTheory.alloca_site_registered_disjoint)) >>
    (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,metis_tac[]])) >>
    disch_then ACCEPT_TAC) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    qpat_assum `venomMemDefs$regions_disjoint (w2n out_bw,outcap) (b,sz)` mp_tac >>
    simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac]) >>
suspend "prepared_scratch"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[prepared_sites]:
`topic_sa.cs_next_id NOTIN frag_ids s3 s4 /\
 s2.cs_next_id NOTIN frag_ids s3 s4 /\
 (!inst. MEM inst (fn_insts func) /\ inst.inst_id IN frag_ids s3 s4 /\
   inst.inst_opcode = ALLOCA ==>
   inst.inst_operands = [Lit 32w] /\
   ?p. inst.inst_outputs = [p] /\ ~not_fresh_at s3 p)` by
 (drule_all stmtSimLogSuffixActualTheory.log_declared_data_encoder_sites >> simp[]) >>
`!inst b sz.
 MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
 inst.inst_id IN frag_ids s3 s4 /\
 FLOOKUP prepared.vs_allocas inst.inst_id = SOME (b,sz) ==>
 sz = 32 /\
 venomMemDefs$regions_disjoint (w2n bw,cap) (b,sz) /\
 venomMemDefs$regions_disjoint
   (w2n out_bw,LENGTH (enc enc_ty enc_val)) (b,sz)` by
 (map_every qx_gen_tac [`inst`,`b`,`sz`] >> strip_tac >>
  `inst.inst_operands = [Lit 32w]` by
   (qpat_assum `!inst. MEM inst (fn_insts func) /\ _ ==> _`
     (qspec_then `inst` mp_tac) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `sz = 32` by
   (qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace)
      ctx func cenv cx mid prepared`
      (mp_tac o List.last o CONJUNCTS o REWRITE_RULE [stmt_state_rel_def]) >>
    disch_then (qspecl_then [`inst`,`32w`,`b`,`sz`] mp_tac) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `venomMemDefs$regions_disjoint (w2n bw,cap) (b,sz)` by
   (mp_tac (Q.INST [`s` |-> `prepared`, `id` |-> `topic_sa.cs_next_id`,
      `other` |-> `inst.inst_id`, `b` |-> `w2n (bw:bytes32)`, `sz` |-> `cap`,
      `p` |-> `b`, `n` |-> `sz`]
      (SPEC_ALL allocaSiteResourceTheory.alloca_site_registered_disjoint)) >>
    (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,metis_tac[]])) >>
    disch_then ACCEPT_TAC) >>
  `venomMemDefs$regions_disjoint (w2n out_bw,outcap) (b,sz)` by
   (mp_tac (Q.INST [`s` |-> `prepared`, `id` |-> `s2.cs_next_id`,
      `other` |-> `inst.inst_id`, `b` |-> `w2n (out_bw:bytes32)`, `sz` |-> `outcap`,
      `p` |-> `b`, `n` |-> `sz`]
      (SPEC_ALL allocaSiteResourceTheory.alloca_site_registered_disjoint)) >>
    (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,metis_tac[]])) >>
    disch_then ACCEPT_TAC) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    qpat_assum `venomMemDefs$regions_disjoint (w2n out_bw,outcap) (b,sz)` mp_tac >>
    simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac]) >>
suspend "prepared_scratch"
QED
*)

Resume compile_log_frag_full[prepared_scratch]:
`abi_encoder_admissible
 (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys))` by
 irule abiEncoderAdmissibleTheory.abi_encoder_translation_admissible >>
`eval_operand src.buf_operand prepared = SOME (n2w (w2n bw)) /\
 eval_operand dst.buf_operand prepared = SOME (n2w (w2n out_bw))` by
 simp[venomStateTheory.eval_operand_def] >>
`!x. src.buf_operand = Var x \/ dst.buf_operand = Var x ==>
 not_fresh_at s3 x` by (rw[] >> first_assum ACCEPT_TAC) >>
`op_taint tnprep src.buf_operand = {} /\
 op_taint tnprep dst.buf_operand = {}` by
 (qpat_assum `ptr_covers Gprep tnprep q prepared cap`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [bodyPtrDefsTheory.ptr_covers_def]) >>
  qpat_assum `ptr_covers Gprep tnprep out_q prepared outcap`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [bodyPtrDefsTheory.ptr_covers_def]) >> simp[]) >>
`ptr_covers Gprep tnprep out_q prepared (LENGTH (enc enc_ty enc_val))` by
 (mp_tac (Q.INST [`G` |-> `Gprep`, `tn` |-> `tnprep`, `root` |-> `out_q`,
    `s` |-> `prepared`, `cap` |-> `outcap`, `sz` |-> `LENGTH (enc enc_ty enc_val)`]
    (SPEC_ALL reasonCopySourcePtrTheory.ptr_covers_mono)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
`~prepared.vs_halted` by
 (qpat_assum `prepared with <|vs_vars := _; vs_allocas := _;
    vs_alloca_next := _; vs_inst_idx := _|> = packed`
    (mp_tac o Q.AP_TERM `\u. u.vs_halted`) >> simp[]) >>
`lo <= prepared.vs_alloca_next` by decide_tac >>
`abi_encoder_window_input
 (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys))
 enc_ty enc_val (w2n bw) cap prepared.vs_memory` by
 (qpat_assum `!mem. mem_agree_outside tnprep.t_mem prepared.vs_memory mem ==>
    abi_encoder_window_input _ enc_ty enc_val _ cap mem`
    (qspec_then `prepared.vs_memory` match_mp_tac) >>
  simp_tac bool_ss [bodyPtrDefsTheory.mem_agree_outside_def]) >>
`abi_encoder_window_pre ctx func s3 s4 dst.buf_operand src.buf_operand
 (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys))
 enc_ty enc_val (w2n bw) cap (w2n out_bw) prepared` by
 (rewrite_tac [abiEncoderWindowContractTheory.abi_encoder_window_pre_def] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    rpt strip_tac >>
    qpat_assum `!inst b sz. MEM inst (fn_insts func) /\ _ ==> _`
      (qspecl_then [`inst`,`b`,`sz`] match_mp_tac) >>
    rpt conj_tac >> first_assum ACCEPT_TAC]) >>
suspend "encoder_entry"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[prepared_scratch]:
`abi_encoder_admissible
 (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys))` by
 irule abiEncoderAdmissibleTheory.abi_encoder_translation_admissible >>
`eval_operand src.buf_operand prepared = SOME (n2w (w2n bw)) /\
 eval_operand dst.buf_operand prepared = SOME (n2w (w2n out_bw))` by
 simp[venomStateTheory.eval_operand_def] >>
`!x. src.buf_operand = Var x \/ dst.buf_operand = Var x ==>
 not_fresh_at s3 x` by (rw[] >> first_assum ACCEPT_TAC) >>
`op_taint tnprep src.buf_operand = {} /\
 op_taint tnprep dst.buf_operand = {}` by
 (qpat_assum `ptr_covers Gprep tnprep q prepared cap`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [bodyPtrDefsTheory.ptr_covers_def]) >>
  qpat_assum `ptr_covers Gprep tnprep out_q prepared outcap`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [bodyPtrDefsTheory.ptr_covers_def]) >> simp[]) >>
`ptr_covers Gprep tnprep out_q prepared (LENGTH (enc enc_ty enc_val))` by
 (mp_tac (Q.INST [`G` |-> `Gprep`, `tn` |-> `tnprep`, `root` |-> `out_q`,
    `s` |-> `prepared`, `cap` |-> `outcap`, `sz` |-> `LENGTH (enc enc_ty enc_val)`]
    (SPEC_ALL reasonCopySourcePtrTheory.ptr_covers_mono)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
`~prepared.vs_halted` by
 (qpat_assum `prepared with <|vs_vars := _; vs_allocas := _;
    vs_alloca_next := _; vs_inst_idx := _|> = packed`
    (mp_tac o Q.AP_TERM `\u. u.vs_halted`) >> simp[]) >>
`lo <= prepared.vs_alloca_next` by decide_tac >>
`abi_encoder_window_input
 (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys))
 enc_ty enc_val (w2n bw) cap prepared.vs_memory` by
 (qpat_assum `!mem. mem_agree_outside tnprep.t_mem prepared.vs_memory mem ==>
    abi_encoder_window_input _ enc_ty enc_val _ cap mem`
    (qspec_then `prepared.vs_memory` match_mp_tac) >>
  simp_tac bool_ss [bodyPtrDefsTheory.mem_agree_outside_def]) >>
`abi_encoder_window_pre ctx func s3 s4 dst.buf_operand src.buf_operand
 (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys))
 enc_ty enc_val (w2n bw) cap (w2n out_bw) prepared` by
 (rewrite_tac [abiEncoderWindowContractTheory.abi_encoder_window_pre_def] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    rpt strip_tac >>
    qpat_assum `!inst b sz. MEM inst (fn_insts func) /\ _ ==> _`
      (qspecl_then [`inst`,`b`,`sz`] match_mp_tac) >>
    rpt conj_tac >> first_assum ACCEPT_TAC]) >>
suspend "encoder_entry"
QED
*)

Resume compile_log_frag_full[encoder_entry]:
qpat_assum `abi_encoder_window_pre ctx func s3 s4 dst.buf_operand src.buf_operand
 (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys))
 enc_ty enc_val (w2n bw) cap (w2n out_bw) prepared`
 (strip_assume_tac o REWRITE_RULE
   [abiEncoderWindowContractTheory.abi_encoder_window_pre_def]) >>
`0 < cap ==>
 w2n bw + cap <= prepared.vs_alloca_next /\
 venomMemDefs$regions_disjoint (w2n bw,cap)
   (w2n out_bw,LENGTH (enc enc_ty enc_val)) /\
 ?p. src.buf_operand = Var p /\ ptr_covers Gprep tnprep p prepared cap` by
 (strip_tac >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   qexists_tac `q` >> simp[]]) >>
`0 < LENGTH (enc enc_ty enc_val) ==>
 ?p. dst.buf_operand = Var p /\
 ptr_covers Gprep tnprep p prepared (LENGTH (enc enc_ty enc_val))` by
 (strip_tac >> qexists_tac `out_q` >> simp[]) >>
`!inst b sz.
 MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
 inst.inst_id IN frag_ids s3 s4 /\
 FLOOKUP prepared.vs_allocas inst.inst_id = SOME (b,sz) ==>
 sz = 32 /\
 (0 < cap ==> venomMemDefs$regions_disjoint (w2n bw,cap) (b,sz)) /\
 venomMemDefs$regions_disjoint
   (w2n out_bw,LENGTH (enc enc_ty enc_val)) (b,sz)` by
 (map_every qx_gen_tac [`inst`,`b`,`sz`] >> strip_tac >>
  qpat_assum `!inst b sz. MEM inst (fn_insts func) /\ _ ==> _`
    (qspecl_then [`inst`,`b`,`sz`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> rpt conj_tac >> TRY strip_tac >> first_assum ACCEPT_TAC) >>
mp_tac (Q.INST
 [`encoder_dst` |-> `dst.buf_operand`, `encoder_src` |-> `src.buf_operand`,
  `ei` |-> `type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys)`,
  `st` |-> `s3`, `en` |-> `s4`, `out` |-> `len`,
  `s` |-> `prepared`, `G` |-> `Gprep`, `tn` |-> `tnprep`,
  `at` |-> `enc_ty`, `av` |-> `enc_val`,
  `sb` |-> `w2n (bw:bytes32)`, `d` |-> `w2n (out_bw:bytes32)`, `cap` |-> `cap`,
  `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
 (Q.INST [`dst` |-> `encoder_dst`, `src` |-> `encoder_src`]
   (SPEC_ALL abiEncoderWindowJointTheory.compile_abi_encode_to_buf_window_joint))) >>
(impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
  simp_tac bool_ss [Abbr `dtys`] >> first_assum ACCEPT_TAC])) >>
disch_then (qx_choosel_then [`encoded`,`Genc`,`tnenc`] strip_assume_tac) >>
suspend "encoded_execution"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[encoder_entry]:
qpat_assum `abi_encoder_window_pre ctx func s3 s4 dst.buf_operand src.buf_operand
 (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys))
 enc_ty enc_val (w2n bw) cap (w2n out_bw) prepared`
 (strip_assume_tac o REWRITE_RULE
   [abiEncoderWindowContractTheory.abi_encoder_window_pre_def]) >>
`0 < cap ==>
 w2n bw + cap <= prepared.vs_alloca_next /\
 venomMemDefs$regions_disjoint (w2n bw,cap)
   (w2n out_bw,LENGTH (enc enc_ty enc_val)) /\
 ?p. src.buf_operand = Var p /\ ptr_covers Gprep tnprep p prepared cap` by
 (strip_tac >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   qexists_tac `q` >> simp[]]) >>
`0 < LENGTH (enc enc_ty enc_val) ==>
 ?p. dst.buf_operand = Var p /\
 ptr_covers Gprep tnprep p prepared (LENGTH (enc enc_ty enc_val))` by
 (strip_tac >> qexists_tac `out_q` >> simp[]) >>
`!inst b sz.
 MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
 inst.inst_id IN frag_ids s3 s4 /\
 FLOOKUP prepared.vs_allocas inst.inst_id = SOME (b,sz) ==>
 sz = 32 /\
 (0 < cap ==> venomMemDefs$regions_disjoint (w2n bw,cap) (b,sz)) /\
 venomMemDefs$regions_disjoint
   (w2n out_bw,LENGTH (enc enc_ty enc_val)) (b,sz)` by
 (map_every qx_gen_tac [`inst`,`b`,`sz`] >> strip_tac >>
  qpat_assum `!inst b sz. MEM inst (fn_insts func) /\ _ ==> _`
    (qspecl_then [`inst`,`b`,`sz`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> rpt conj_tac >> TRY strip_tac >> first_assum ACCEPT_TAC) >>
mp_tac (Q.INST
 [`encoder_dst` |-> `dst.buf_operand`, `encoder_src` |-> `src.buf_operand`,
  `ei` |-> `type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys)`,
  `st` |-> `s3`, `en` |-> `s4`, `out` |-> `len`,
  `s` |-> `prepared`, `G` |-> `Gprep`, `tn` |-> `tnprep`,
  `at` |-> `enc_ty`, `av` |-> `enc_val`,
  `sb` |-> `w2n (bw:bytes32)`, `d` |-> `w2n (out_bw:bytes32)`, `cap` |-> `cap`,
  `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
 (Q.INST [`dst` |-> `encoder_dst`, `src` |-> `encoder_src`]
   (SPEC_ALL abiEncoderWindowJointTheory.compile_abi_encode_to_buf_window_joint))) >>
(impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
  simp_tac bool_ss [Abbr `dtys`] >> first_assum ACCEPT_TAC])) >>
disch_then (qx_choosel_then [`encoded`,`Genc`,`tnenc`] strip_assume_tac) >>
suspend "encoded_execution"
QED
*)

Resume compile_log_frag_full[encoded_execution]:
`abi_encoder_window_result ctx func s3 s4 len enc_ty enc_val
 (w2n out_bw) prepared encoded` by
 (drule_all abiEncoderWindowContractTheory.window_strong_result_public >> simp[]) >>
qpat_assum `abi_encoder_window_result ctx func s3 s4 len enc_ty enc_val
 (w2n out_bw) prepared encoded`
 (strip_assume_tac o REWRITE_RULE
   [abiEncoderWindowContractTheory.abi_encoder_window_result_def]) >>
`window_alloca_growth prepared encoded` by
 (drule_all abiEncoderWindowContractTheory.window_strong_result_growth >> simp[]) >>
`encoded.vs_call_ctx = prepared.vs_call_ctx /\
 encoded.vs_fmp = prepared.vs_fmp /\
 encoded.vs_data_section = prepared.vs_data_section /\
 LENGTH prepared.vs_memory <= LENGTH encoded.vs_memory /\
 encoded.vs_alloca_next + pending_alloca_size func encoded <=
 prepared.vs_alloca_next + pending_alloca_size func prepared` by
 (qpat_assum `abi_encode_exec_frame func prepared encoded`
   (strip_assume_tac o REWRITE_RULE
     [exprSimAbiEncodeExecFrameTheory.abi_encode_exec_frame_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC) >>
`prepared.vs_alloca_next <= encoded.vs_alloca_next` by
 (qpat_assum `window_alloca_growth prepared encoded`
   (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE
     [abiEncoderWindowContractTheory.window_alloca_growth_def])) >>
`w2n out_bw + LENGTH (enc enc_ty enc_val) <= encoded.vs_alloca_next /\
 lo <= encoded.vs_alloca_next` by decide_tac >>
`gas_path_mem ctx func prepared 0 (OK encoded)` by
 (qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (prepared,Gprep,tnprep) [] (OK encoded,Genc,tnenc)`
   (qspec_then `DF (storage_trace_horizon mid.storage_trace)` mp_tac) >>
  disch_then (mp_tac o CONJUNCT1 o MATCH_MP
   fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
  disch_then (mp_tac o MATCH_MP fragGasOriginTheory.gas_origin_path_erase) >>
  simp[fragGasModeTheory.gas_marked_path_def]) >>
`!u. gas_path_mem ctx func prepared 0 (OK u) ==> alloca_inv u` by
 (rpt strip_tac >>
  drule_all bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv >> simp[]) >>
`alloca_history func encoded` by
 (drule_all fragGasPathFrameMemTheory.gas_path_mem_zero_history >> simp[]) >>
suspend "encoded_resources"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[encoded_execution]:
`abi_encoder_window_result ctx func s3 s4 len enc_ty enc_val
 (w2n out_bw) prepared encoded` by
 (drule_all abiEncoderWindowContractTheory.window_strong_result_public >> simp[]) >>
qpat_assum `abi_encoder_window_result ctx func s3 s4 len enc_ty enc_val
 (w2n out_bw) prepared encoded`
 (strip_assume_tac o REWRITE_RULE
   [abiEncoderWindowContractTheory.abi_encoder_window_result_def]) >>
`window_alloca_growth prepared encoded` by
 (drule_all abiEncoderWindowContractTheory.window_strong_result_growth >> simp[]) >>
`encoded.vs_call_ctx = prepared.vs_call_ctx /\
 encoded.vs_fmp = prepared.vs_fmp /\
 encoded.vs_data_section = prepared.vs_data_section /\
 LENGTH prepared.vs_memory <= LENGTH encoded.vs_memory /\
 encoded.vs_alloca_next + pending_alloca_size func encoded <=
 prepared.vs_alloca_next + pending_alloca_size func prepared` by
 (qpat_assum `abi_encode_exec_frame func prepared encoded`
   (strip_assume_tac o REWRITE_RULE
     [exprSimAbiEncodeExecFrameTheory.abi_encode_exec_frame_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC) >>
`prepared.vs_alloca_next <= encoded.vs_alloca_next` by
 (qpat_assum `window_alloca_growth prepared encoded`
   (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE
     [abiEncoderWindowContractTheory.window_alloca_growth_def])) >>
`w2n out_bw + LENGTH (enc enc_ty enc_val) <= encoded.vs_alloca_next /\
 lo <= encoded.vs_alloca_next` by decide_tac >>
`gas_path_mem ctx func prepared 0 (OK encoded)` by
 (qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (prepared,Gprep,tnprep) [] (OK encoded,Genc,tnenc)`
   (qspec_then `DF (storage_trace_horizon mid.storage_trace)` mp_tac) >>
  disch_then (mp_tac o CONJUNCT1 o MATCH_MP
   fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
  disch_then (mp_tac o MATCH_MP fragGasOriginTheory.gas_origin_path_erase) >>
  simp[fragGasModeTheory.gas_marked_path_def]) >>
`!u. gas_path_mem ctx func prepared 0 (OK u) ==> alloca_inv u` by
 (rpt strip_tac >>
  drule_all bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv >> simp[]) >>
`alloca_history func encoded` by
 (drule_all fragGasPathFrameMemTheory.gas_path_mem_zero_history >> simp[]) >>
suspend "encoded_resources"
QED
*)

Resume compile_log_frag_full[encoded_resources]:
`abi_encoder_registered_effect
 (window_alloca_sites func (frag_ids s3 s4))
 [(w2n out_bw,LENGTH (enc enc_ty enc_val))] prepared encoded` by
 (drule_all abiEncoderWindowContractTheory.window_strong_result_effect >>
  disch_then ACCEPT_TAC) >>
`!aid row. FLOOKUP prepared.vs_allocas aid = SOME row ==>
 FLOOKUP encoded.vs_allocas aid = SOME row` by
 (qpat_assum `abi_encoder_registered_effect _ _ prepared encoded`
   (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE
    [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def])) >>
`allocas_from lo encoded` by
 (rewrite_tac [ptrDisciplineTheory.allocas_from_def] >>
  qx_genl_tac [`aid`,`b`,`sz`] >> strip_tac >>
  Cases_on `FLOOKUP prepared.vs_allocas aid`
  >- (qpat_assum `window_alloca_growth prepared encoded`
       (mp_tac o CONJUNCT2 o REWRITE_RULE
        [abiEncoderWindowContractTheory.window_alloca_growth_def]) >>
      disch_then (qspecl_then [`aid`,`b`,`sz`] mp_tac) >>
      (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> decide_tac) >>
  rename1 `FLOOKUP prepared.vs_allocas aid = SOME row` >>
  `row = (b,sz)` by
   (qpat_assum `!aid row. FLOOKUP prepared.vs_allocas aid = SOME row ==> _`
     (qspecl_then [`aid`,`row`] mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    qpat_assum `FLOOKUP encoded.vs_allocas aid = SOME (b,sz)` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  qpat_assum `row = (b,sz)` (fn eq =>
    qpat_assum `FLOOKUP prepared.vs_allocas aid = SOME row`
      (assume_tac o PURE_REWRITE_RULE [eq])) >>
  qpat_assum `allocas_from lo prepared`
   (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
  disch_then (qspecl_then [`aid`,`b`,`sz`] match_mp_tac) >>
  first_assum ACCEPT_TAC) >>
`lookup_var out_q encoded = SOME out_bw` by
 (qpat_assum `!x w. not_fresh_at s3 x /\ lookup_var x prepared = SOME w ==> _`
   (qspecl_then [`out_q`,`out_bw`] match_mp_tac) >>
  conj_tac >> first_assum ACCEPT_TAC) >>
`FLOOKUP Genc out_q = FLOOKUP Gprep out_q /\
 op_taint tnenc (Var out_q) = op_taint tnprep (Var out_q)` by
 (qpat_assum `!x. not_fresh_at s3 x ==> FLOOKUP Genc x = _ /\ _`
   (qspec_then `out_q` match_mp_tac) >> first_assum ACCEPT_TAC) >>
`ptr_covers Genc tnenc out_q encoded (LENGTH (enc enc_ty enc_val))` by
 (match_mp_tac (Q.INST [`G` |-> `Gprep`, `tn` |-> `tnprep`,
    `s` |-> `prepared`] decoderGhostFramePtrTheory.ptr_covers_frame) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   qpat_assum `lookup_var out_q encoded = SOME out_bw` mp_tac >>
   qpat_assum `lookup_var out_q prepared = SOME out_bw` mp_tac >>
   POP_ASSUM_LIST (K ALL_TAC) >> simp[]]) >>
suspend "encoded_pointer"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[encoded_resources]:
`abi_encoder_registered_effect
 (window_alloca_sites func (frag_ids s3 s4))
 [(w2n out_bw,LENGTH (enc enc_ty enc_val))] prepared encoded` by
 (drule_all abiEncoderWindowContractTheory.window_strong_result_effect >>
  disch_then ACCEPT_TAC) >>
`!aid row. FLOOKUP prepared.vs_allocas aid = SOME row ==>
 FLOOKUP encoded.vs_allocas aid = SOME row` by
 (qpat_assum `abi_encoder_registered_effect _ _ prepared encoded`
   (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE
    [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def])) >>
`allocas_from lo encoded` by
 (rewrite_tac [ptrDisciplineTheory.allocas_from_def] >>
  qx_genl_tac [`aid`,`b`,`sz`] >> strip_tac >>
  Cases_on `FLOOKUP prepared.vs_allocas aid`
  >- (qpat_assum `window_alloca_growth prepared encoded`
       (mp_tac o CONJUNCT2 o REWRITE_RULE
        [abiEncoderWindowContractTheory.window_alloca_growth_def]) >>
      disch_then (qspecl_then [`aid`,`b`,`sz`] mp_tac) >>
      (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> decide_tac) >>
  rename1 `FLOOKUP prepared.vs_allocas aid = SOME row` >>
  `row = (b,sz)` by
   (qpat_assum `!aid row. FLOOKUP prepared.vs_allocas aid = SOME row ==> _`
     (qspecl_then [`aid`,`row`] mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    qpat_assum `FLOOKUP encoded.vs_allocas aid = SOME (b,sz)` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  qpat_assum `row = (b,sz)` (fn eq =>
    qpat_assum `FLOOKUP prepared.vs_allocas aid = SOME row`
      (assume_tac o PURE_REWRITE_RULE [eq])) >>
  qpat_assum `allocas_from lo prepared`
   (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
  disch_then (qspecl_then [`aid`,`b`,`sz`] match_mp_tac) >>
  first_assum ACCEPT_TAC) >>
`lookup_var out_q encoded = SOME out_bw` by
 (qpat_assum `!x w. not_fresh_at s3 x /\ lookup_var x prepared = SOME w ==> _`
   (qspecl_then [`out_q`,`out_bw`] match_mp_tac) >>
  conj_tac >> first_assum ACCEPT_TAC) >>
`FLOOKUP Genc out_q = FLOOKUP Gprep out_q /\
 op_taint tnenc (Var out_q) = op_taint tnprep (Var out_q)` by
 (qpat_assum `!x. not_fresh_at s3 x ==> FLOOKUP Genc x = _ /\ _`
   (qspec_then `out_q` match_mp_tac) >> first_assum ACCEPT_TAC) >>
`ptr_covers Genc tnenc out_q encoded (LENGTH (enc enc_ty enc_val))` by
 (match_mp_tac (Q.INST [`G` |-> `Gprep`, `tn` |-> `tnprep`,
    `s` |-> `prepared`] decoderGhostFramePtrTheory.ptr_covers_frame) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   qpat_assum `lookup_var out_q encoded = SOME out_bw` mp_tac >>
   qpat_assum `lookup_var out_q prepared = SOME out_bw` mp_tac >>
   POP_ASSUM_LIST (K ALL_TAC) >> simp[]]) >>
suspend "encoded_pointer"
QED
*)

Resume compile_log_frag_full[encoded_pointer]:
`EVERY (\arg. (!x. FST arg = Var x ==> not_fresh_at sm x) /\
 (!lab. FST arg <> Label lab)) topic_args` by
 (qpat_assum `LIST_REL (\arg v. ?j. j < LENGTH args /\ v = EL j vs /\
    FST arg = FST (EL j ops) /\ SND arg = expr_type (EL j args))
    topic_args topic_vals` mp_tac >>
  qpat_assum `EVERY (\p. (!x. FST p = Var x ==> not_fresh_at sm x) /\
    (!lab. FST p <> Label lab)) ops` mp_tac >>
  qpat_assum `LENGTH ops = LENGTH fields` mp_tac >>
  qpat_assum `LENGTH args = LENGTH fields` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [LIST_REL_EL_EQN,EVERY_EL] >>
  rpt strip_tac >> metis_tac[]) >>
`EVERY (\p. (!x. FST p = Var x ==> not_fresh_at sm x) /\
 (!lab. FST p <> Label lab))
 (MAP (\p. (FST p,is_bytestring_type (SND p))) topic_args)` by
 (simp_tac bool_ss [EVERY_MAP,pairTheory.FST] >> first_assum ACCEPT_TAC) >>
mp_tac (Q.SPECL
 [`MAP (\p. (FST p,is_bytestring_type (SND p))) topic_args`,
  `sm`,`topic_ops`,`topic_sa`]
 stmtSimLogTopicsTheory.compile_log_topic_ops_frontier) >>
(impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
`ci_mono topic_sa s1` by
 (mp_tac (Q.SPECL [`cap`,`topic_sa`]
   exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >> simp[]) >>
`!x w. not_fresh_at topic_sa x /\ lookup_var x tp = SOME w ==>
 lookup_var x encoded = SOME w /\
 FLOOKUP Genc x = FLOOKUP Gp x /\
 op_taint tnenc (Var x) = op_taint tnp (Var x)` by
 (qx_genl_tac [`x`,`w`] >> strip_tac >>
  `not_fresh_at s1 x /\ not_fresh_at s2 x /\ not_fresh_at s3 x` by
   (rpt conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
    qexists_tac `topic_sa` >>
    qpat_assum `ci_mono topic_sa s1`
     (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
    qpat_assum `ci_mono s1 s2`
     (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
    qpat_assum `ci_mono s2 s3`
     (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,decide_tac]) >>
  `lookup_var x ta = lookup_var x tp /\ FLOOKUP Ga x = FLOOKUP Gp x /\
   op_taint tna (Var x) = op_taint tnp (Var x)` by
   (qpat_assum `!x. not_fresh_at topic_sa x ==> lookup_var x ta = _ /\ _`
     (qspec_then `x` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  `lookup_var x packed = lookup_var x ta` by
   (qpat_assum `typed_copy_state_frame s1 (w2n bw) cap ta packed`
     (strip_assume_tac o REWRITE_RULE
      [typedMemoryCopyTheory.typed_copy_state_frame_def]) >>
    qpat_assum `!x. not_fresh_at s1 x ==> lookup_var x packed = _`
     (qspec_then `x` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  `FLOOKUP Gpacked x = FLOOKUP Ga x /\
   op_taint tnpacked (Var x) = op_taint tna (Var x)` by
   (qpat_assum `!p. not_fresh_at s1 p ==> FLOOKUP Gpacked p = _ /\ _`
     (qspec_then `x` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  `lookup_var x prepared = lookup_var x packed /\
   FLOOKUP Gprep x = FLOOKUP Gpacked x /\
   op_taint tnprep (Var x) = op_taint tnpacked (Var x)` by
   (qpat_assum `!x. not_fresh_at s2 x ==> lookup_var x prepared = _ /\ _`
     (qspec_then `x` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  `lookup_var x prepared = SOME w` by asm_rewrite_tac[] >>
  `lookup_var x encoded = SOME w` by
   (qpat_assum `!x w. not_fresh_at s3 x /\ lookup_var x prepared = SOME w ==> _`
     (qspecl_then [`x`,`w`] match_mp_tac) >>
    conj_tac >> first_assum ACCEPT_TAC) >>
  `FLOOKUP Genc x = FLOOKUP Gprep x /\
   op_taint tnenc (Var x) = op_taint tnprep (Var x)` by
   (qpat_assum `!x. not_fresh_at s3 x ==> FLOOKUP Genc x = _ /\ _`
     (qspec_then `x` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[]) >>
suspend "encoded_topic_frame"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[encoded_pointer]:
`EVERY (\arg. (!x. FST arg = Var x ==> not_fresh_at sm x) /\
 (!lab. FST arg <> Label lab)) topic_args` by
 (qpat_assum `LIST_REL (\arg v. ?j. j < LENGTH args /\ v = EL j vs /\
    FST arg = FST (EL j ops) /\ SND arg = expr_type (EL j args))
    topic_args topic_vals` mp_tac >>
  qpat_assum `EVERY (\p. (!x. FST p = Var x ==> not_fresh_at sm x) /\
    (!lab. FST p <> Label lab)) ops` mp_tac >>
  qpat_assum `LENGTH ops = LENGTH args` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [LIST_REL_EL_EQN,EVERY_EL] >>
  rpt strip_tac >> metis_tac[]) >>
`EVERY (\p. (!x. FST p = Var x ==> not_fresh_at sm x) /\
 (!lab. FST p <> Label lab))
 (MAP (\p. (FST p,is_bytestring_type (SND p))) topic_args)` by
 (simp_tac bool_ss [EVERY_MAP,pairTheory.FST] >> first_assum ACCEPT_TAC) >>
mp_tac (Q.SPECL
 [`MAP (\p. (FST p,is_bytestring_type (SND p))) topic_args`,
  `sm`,`topic_ops`,`topic_sa`]
 stmtSimLogTopicsTheory.compile_log_topic_ops_frontier) >>
(impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
`ci_mono topic_sa s1` by
 (mp_tac (Q.SPECL [`cap`,`topic_sa`]
   exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >> simp[]) >>
`!x w. not_fresh_at topic_sa x /\ lookup_var x tp = SOME w ==>
 lookup_var x encoded = SOME w /\
 FLOOKUP Genc x = FLOOKUP Gp x /\
 op_taint tnenc (Var x) = op_taint tnp (Var x)` by
 (qx_genl_tac [`x`,`w`] >> strip_tac >>
  `not_fresh_at s1 x /\ not_fresh_at s2 x /\ not_fresh_at s3 x` by
   (rpt conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
    qexists_tac `topic_sa` >>
    qpat_assum `ci_mono topic_sa s1`
     (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
    qpat_assum `ci_mono s1 s2`
     (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
    qpat_assum `ci_mono s2 s3`
     (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,decide_tac]) >>
  `lookup_var x ta = lookup_var x tp /\ FLOOKUP Ga x = FLOOKUP Gp x /\
   op_taint tna (Var x) = op_taint tnp (Var x)` by
   (qpat_assum `!x. not_fresh_at topic_sa x ==> lookup_var x ta = _ /\ _`
     (qspec_then `x` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  `lookup_var x packed = lookup_var x ta` by
   (qpat_assum `typed_copy_state_frame s1 (w2n bw) cap ta packed`
     (strip_assume_tac o REWRITE_RULE
      [typedMemoryCopyTheory.typed_copy_state_frame_def]) >>
    qpat_assum `!x. not_fresh_at s1 x ==> lookup_var x packed = _`
     (qspec_then `x` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  `FLOOKUP Gpacked x = FLOOKUP Ga x /\
   op_taint tnpacked (Var x) = op_taint tna (Var x)` by
   (qpat_assum `!p. not_fresh_at s1 p ==> FLOOKUP Gpacked p = _ /\ _`
     (qspec_then `x` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  `lookup_var x prepared = lookup_var x packed /\
   FLOOKUP Gprep x = FLOOKUP Gpacked x /\
   op_taint tnprep (Var x) = op_taint tnpacked (Var x)` by
   (qpat_assum `!x. not_fresh_at s2 x ==> lookup_var x prepared = _ /\ _`
     (qspec_then `x` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  `lookup_var x prepared = SOME w` by asm_rewrite_tac[] >>
  `lookup_var x encoded = SOME w` by
   (qpat_assum `!x w. not_fresh_at s3 x /\ lookup_var x prepared = SOME w ==> _`
     (qspecl_then [`x`,`w`] match_mp_tac) >>
    conj_tac >> first_assum ACCEPT_TAC) >>
  `FLOOKUP Genc x = FLOOKUP Gprep x /\
   op_taint tnenc (Var x) = op_taint tnprep (Var x)` by
   (qpat_assum `!x. not_fresh_at s3 x ==> FLOOKUP Genc x = _ /\ _`
     (qspec_then `x` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[]) >>
suspend "encoded_topic_frame"
QED
*)

Resume compile_log_frag_full[encoded_topic_frame]:
`!op w. MEM op topic_ops /\ eval_operand op tp = SOME w ==>
 eval_operand op encoded = SOME w /\ op_taint tnenc op = {}` by
 (qpat_assum `!x w. not_fresh_at topic_sa x /\ lookup_var x tp = SOME w ==>
    lookup_var x encoded = SOME w /\ _` mp_tac >>
  qpat_assum `EVERY (\op. (!z. op = Var z ==> not_fresh_at topic_sa z) /\
    (!l. op <> Label l)) topic_ops` mp_tac >>
  qpat_assum `EVERY (\op. op_taint tnp op = {}) topic_ops` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [EVERY_MEM] >> rpt disch_tac >>
  qx_genl_tac [`op`,`w`] >> strip_tac >>
  qpat_x_assum `!op. MEM op topic_ops ==> op_taint tnp op = {}`
    (qspec_then `op` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `!op. MEM op topic_ops ==>
    (!z. op = Var z ==> not_fresh_at topic_sa z) /\ (!l. op <> Label l)`
    (qspec_then `op` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  Cases_on `op` >>
  gvs[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def] >>
  metis_tac[]) >>
`LIST_REL (\op w. eval_operand op encoded = SOME w) topic_ops topics /\
 EVERY (\op. op_taint tnenc op = {}) topic_ops` by
 (qpat_assum `!op w. MEM op topic_ops /\ eval_operand op tp = SOME w ==> _`
   mp_tac >>
  qpat_assum `LIST_REL (\op w. eval_operand op tp = SOME w) topic_ops topics`
   mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [LIST_REL_EL_EQN,EVERY_EL] >>
  rpt strip_tac >> metis_tac[MEM_EL]) >>
suspend "encoded_topics"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[encoded_topic_frame]:
`!op w. MEM op topic_ops /\ eval_operand op tp = SOME w ==>
 eval_operand op encoded = SOME w /\ op_taint tnenc op = {}` by
 (qpat_assum `!x w. not_fresh_at topic_sa x /\ lookup_var x tp = SOME w ==>
    lookup_var x encoded = SOME w /\ _` mp_tac >>
  qpat_assum `EVERY (\op. (!z. op = Var z ==> not_fresh_at topic_sa z) /\
    (!l. op <> Label l)) topic_ops` mp_tac >>
  qpat_assum `EVERY (\op. op_taint tnp op = {}) topic_ops` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [EVERY_MEM] >> rpt disch_tac >>
  qx_genl_tac [`op`,`w`] >> strip_tac >>
  qpat_x_assum `!op. MEM op topic_ops ==> op_taint tnp op = {}`
    (qspec_then `op` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `!op. MEM op topic_ops ==>
    (!z. op = Var z ==> not_fresh_at topic_sa z) /\ (!l. op <> Label l)`
    (qspec_then `op` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  Cases_on `op` >>
  gvs[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def] >>
  metis_tac[]) >>
`LIST_REL (\op w. eval_operand op encoded = SOME w) topic_ops topics /\
 EVERY (\op. op_taint tnenc op = {}) topic_ops` by
 (qpat_assum `!op w. MEM op topic_ops /\ eval_operand op tp = SOME w ==> _`
   mp_tac >>
  qpat_assum `LIST_REL (\op w. eval_operand op tp = SOME w) topic_ops topics`
   mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [LIST_REL_EL_EQN,EVERY_EL] >>
  rpt strip_tac >> metis_tac[MEM_EL]) >>
suspend "encoded_topics"
QED
*)

Resume compile_log_frag_full[encoded_topics]:
`LENGTH (Lit (n2w h)::topic_ops) <= 4` by
 (mp_tac (Q.INST
   [`xs` |-> `lops`, `flags` |-> `flags`,
    `sa` |-> `sm`, `sb` |-> `topic_sa`, `emitted_topic_ops` |-> `topic_ops`,
    `first_topic` |-> `Lit (n2w h)`]
   (Q.INST [`ops` |-> `emitted_topic_ops`, `h` |-> `first_topic`]
     (SPEC_ALL stmtSimLogTopicsTheory.log_emitted_topic_count_exact))) >>
  (impl_tac >-
   (conj_tac >-
     (simp_tac bool_ss [Abbr `flags`,Abbr `lops`,LENGTH_MAP,LENGTH_ZIP] >>
      qpat_assum `LENGTH ops = LENGTH fields` mp_tac >>
      qpat_assum `LENGTH args = LENGTH fields` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
    conj_tac >> first_assum ACCEPT_TAC)) >>
  simp_tac bool_ss []) >>
`LENGTH (Lit (n2w h)::topic_ops) < dimword (:256)` by
 (`4 < dimword (:256)` by
   simp_tac (srw_ss()) [wordsTheory.dimword_def] >> decide_tac) >>
`eval_operands (Lit (n2w h)::topic_ops) encoded = SOME (n2w h::topics)` by
 (qpat_assum `LIST_REL (\op w. eval_operand op encoded = SOME w) topic_ops topics`
   (mp_tac o MATCH_MP stmtSimLogSuffixTheory.log_operands_values) >>
  simp_tac (srw_ss()) [venomStateTheory.eval_operands_def,
    venomStateTheory.eval_operand_def]) >>
`LENGTH (enc enc_ty enc_val) < dimword (:256)` by decide_tac >>
`w2n (n2w (LENGTH (enc enc_ty enc_val)) : bytes32) =
 LENGTH (enc enc_ty enc_val)` by
 (qpat_assum `LENGTH (enc enc_ty enc_val) < dimword (:256)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
  asm_simp_tac bool_ss [wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD]) >>
`eval_operand dst.buf_operand encoded = SOME out_bw /\
 op_taint tnenc dst.buf_operand = {}` by
 (qpat_assum `ptr_covers Genc tnenc out_q encoded (LENGTH (enc enc_ty enc_val))`
   (mp_tac o CONJUNCT1 o REWRITE_RULE [ptr_covers_def]) >>
  qpat_assum `lookup_var out_q encoded = SOME out_bw` mp_tac >>
  qpat_assum `dst.buf_operand = Var out_q` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [venomStateTheory.eval_operand_def]) >>
`EVERY (\op. op_taint tnenc op = {})
 (dst.buf_operand::len::Lit (n2w h)::topic_ops)` by
 (qpat_assum `EVERY (\op. op_taint tnenc op = {}) topic_ops` mp_tac >>
  qpat_assum `op_taint tnenc dst.buf_operand = {}` mp_tac >>
  qpat_assum `op_taint tnenc len = {}` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [EVERY_DEF,ptrDisciplineTheory.op_taint_def]) >>
Cases_on `encoded.vs_call_ctx.cc_static`
>- suspend "encoded_static" >>
mp_tac (Q.INST
 [`topic_ops` |-> `Lit (n2w h)::topic_ops`, `topics` |-> `n2w h::topics`,
  `ptr_op` |-> `dst.buf_operand`, `len_op` |-> `len`,
  `off` |-> `out_bw:bytes32`,
  `encoded_length_word` |-> `n2w (LENGTH (enc enc_ty enc_val)):bytes32`,
  `s` |-> `encoded`, `G` |-> `Genc`, `tn` |-> `tnenc`,
  `sa` |-> `s4`, `sb` |-> `sb`,
  `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
 (Q.INST [`len` |-> `encoded_length_word`]
   (SPEC_ALL bodyFullLogSuffixTheory.compile_log_emit_origin_ptr_path))) >>
(impl_tac >-
 (qpat_assum `w2n (n2w (LENGTH (enc enc_ty enc_val)) : bytes32) =
    LENGTH (enc enc_ty enc_val)` (fn len_th => rewrite_tac[len_th]) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   (qpat_assum `emit_inst LOG _ [] s4 = ((),sb)` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> NO_TAC),
   DISJ2_TAC >> first_assum ACCEPT_TAC,
   strip_tac >> qexists_tac `out_q` >>
   conj_tac >> first_assum ACCEPT_TAC])) >>
strip_tac >>
suspend "encoded_log"
QED

Resume compile_log_frag_full[encoded_static]:
mp_tac (Q.INST
 [`topic_ops` |-> `Lit (n2w h)::topic_ops`, `topics` |-> `n2w h::topics`,
  `ptr_op` |-> `dst.buf_operand`, `len_op` |-> `len`,
  `off` |-> `out_bw:bytes32`,
  `encoded_length_word` |-> `n2w (LENGTH (enc enc_ty enc_val)):bytes32`,
  `s` |-> `encoded`, `G` |-> `Genc`, `tn` |-> `tnenc`,
  `sa` |-> `s4`, `sb` |-> `sb`,
  `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
 (Q.INST [`len` |-> `encoded_length_word`]
   (SPEC_ALL compile_log_emit_static_origin_ptr_path))) >>
(impl_tac >-
 (qpat_assum `w2n (n2w (LENGTH (enc enc_ty enc_val)) : bytes32) =
    LENGTH (enc enc_ty enc_val)` (fn len_th => rewrite_tac[len_th]) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   (qpat_assum `emit_inst LOG _ [] s4 = ((),sb)` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> NO_TAC),
   DISJ2_TAC >> first_assum ACCEPT_TAC,
   strip_tac >> qexists_tac `out_q` >>
   conj_tac >> first_assum ACCEPT_TAC])) >>
strip_tac >>
suspend "static_path"
QED

Resume compile_log_frag_full[static_path]:
`cx.txn.is_static` by
 (qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace)
    ctx func cenv cx mid prepared`
   (mp_tac o CONJUNCT1 o REWRITE_RULE [stmt_state_rel_def]) >>
  qpat_assum `encoded.vs_call_ctx = prepared.vs_call_ctx` mp_tac >>
  qpat_assum `encoded.vs_call_ctx.cc_static` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [state_rel_def,call_ctx_rel_def] >> metis_tac[]) >>
`!D. gas_origin_ptr_path
 (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
 (t,G1,tn1) []
 (Abort ExHalt_abort (halt_state (set_returndata [] encoded)),Genc,tnenc)` by
 (qx_gen_tac `path_D` >>
  qpat_assum `!D. gas_origin_ptr_path _ (t,G1,tn1) [] (OK tp,Gp,tnp)`
   (qspec_then `path_D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path _ (tp,Gp,tnp) [] (OK ta,Ga,tna)`
   (qspec_then `path_D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path _ (ta,Ga,tna) [] (OK packed,Gpacked,tnpacked)`
   (qspec_then `path_D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path _ (packed,Gpacked,tnpacked) [] (OK prepared,Gprep,tnprep)`
   (qspec_then `path_D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path _ (prepared,Gprep,tnprep) [] (OK encoded,Genc,tnenc)`
   (qspec_then `path_D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path _ (encoded,Genc,tnenc) [] (Abort _ _,Genc,tnenc)`
   (qspec_then `path_D` mp_tac) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,APPEND_NIL]) >>
`!tail. bind (lift_option
 (encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs)
 "Log encode event")
 (\event. ignore_bind (check_not_static cx) (push_log event))
 (mid with gas_obs := tail) =
 (INR (Error (RuntimeError "write in static context")),mid with gas_obs := tail)` by
 (qpat_assum `encode_source_event _ _ _ _ _ = SOME log_ev` mp_tac >>
  qpat_assum `cx.txn.is_static` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[log_full_source_suffix_result]) >>
irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >>
reverse conj_tac >- first_assum ACCEPT_TAC >>
qexistsl_tac [`Genc`,`mid`,
 `Abort ExHalt_abort (halt_state (set_returndata [] encoded))`,
 `INR (Error (RuntimeError "write in static context"))`,`tnenc`] >>
conj_tac >-
 (qpat_assum `cx.txn.is_static` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
  simp[bind_def,ignore_bind_def,lift_option_def,check_not_static_eq,
       return_def,raise_def]) >>
reverse conj_tac >- simp[exit_result_def] >>
qx_gen_tac `post_H` >> strip_tac >> BETA_TAC >>
conj_tac >-
 (qpat_assum `!D. gas_origin_ptr_path _ (t,G1,tn1) [] (Abort _ _,Genc,tnenc)`
   (qspec_then `DF post_H` ACCEPT_TAC)) >>
simp[stmt_exit_ptr_def,expr_exit_def,halt_exit_def]
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[encoded_topics]:
`LENGTH (Lit (n2w h)::topic_ops) <= 4` by
 (mp_tac (Q.INST
   [`xs` |-> `ops`, `flags` |-> `flags`,
    `sa` |-> `sm`, `sb` |-> `topic_sa`, `emitted_topic_ops` |-> `topic_ops`,
    `first_topic` |-> `Lit (n2w h)`]
   (Q.INST [`ops` |-> `emitted_topic_ops`, `h` |-> `first_topic`]
     (SPEC_ALL stmtSimLogTopicsTheory.log_emitted_topic_count_exact))) >>
  (impl_tac >-
   (conj_tac >-
     (simp_tac bool_ss [Abbr `flags`,LENGTH_MAP] >>
      qpat_assum `LENGTH ops = LENGTH fields` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      metis_tac[]) >>
    conj_tac >> first_assum ACCEPT_TAC)) >>
  simp_tac bool_ss []) >>
`LENGTH (Lit (n2w h)::topic_ops) < dimword (:256)` by
 (`4 < dimword (:256)` by
   simp_tac (srw_ss()) [wordsTheory.dimword_def] >> decide_tac) >>
`eval_operands (Lit (n2w h)::topic_ops) encoded = SOME (n2w h::topics)` by
 (qpat_assum `LIST_REL (\op w. eval_operand op encoded = SOME w) topic_ops topics`
   (mp_tac o MATCH_MP stmtSimLogSuffixTheory.log_operands_values) >>
  simp_tac (srw_ss()) [venomStateTheory.eval_operands_def,
    venomStateTheory.eval_operand_def]) >>
`LENGTH (enc enc_ty enc_val) < dimword (:256)` by decide_tac >>
`w2n (n2w (LENGTH (enc enc_ty enc_val)) : bytes32) =
 LENGTH (enc enc_ty enc_val)` by
 (qpat_assum `LENGTH (enc enc_ty enc_val) < dimword (:256)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
  asm_simp_tac bool_ss [wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD]) >>
`eval_operand dst.buf_operand encoded = SOME out_bw /\
 op_taint tnenc dst.buf_operand = {}` by
 (qpat_assum `ptr_covers Genc tnenc out_q encoded (LENGTH (enc enc_ty enc_val))`
   (mp_tac o CONJUNCT1 o REWRITE_RULE [ptr_covers_def]) >>
  qpat_assum `lookup_var out_q encoded = SOME out_bw` mp_tac >>
  qpat_assum `dst.buf_operand = Var out_q` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [venomStateTheory.eval_operand_def]) >>
`EVERY (\op. op_taint tnenc op = {})
 (dst.buf_operand::len::Lit (n2w h)::topic_ops)` by
 (qpat_assum `EVERY (\op. op_taint tnenc op = {}) topic_ops` mp_tac >>
  qpat_assum `op_taint tnenc dst.buf_operand = {}` mp_tac >>
  qpat_assum `op_taint tnenc len = {}` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [EVERY_DEF,ptrDisciplineTheory.op_taint_def]) >>
`~encoded.vs_call_ctx.cc_static` by
 (qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace)
    ctx func cenv cx mid prepared`
   (mp_tac o CONJUNCT1 o REWRITE_RULE [stmt_state_rel_def]) >>
  qpat_assum `encoded.vs_call_ctx = prepared.vs_call_ctx` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [state_rel_def] >> metis_tac[]) >>
mp_tac (Q.INST
 [`topic_ops` |-> `Lit (n2w h)::topic_ops`, `topics` |-> `n2w h::topics`,
  `ptr_op` |-> `dst.buf_operand`, `len_op` |-> `len`,
  `off` |-> `out_bw:bytes32`,
  `encoded_length_word` |-> `n2w (LENGTH (enc enc_ty enc_val)):bytes32`,
  `s` |-> `encoded`, `G` |-> `Genc`, `tn` |-> `tnenc`,
  `sa` |-> `s4`, `sb` |-> `sb`,
  `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
 (Q.INST [`len` |-> `encoded_length_word`]
   (SPEC_ALL bodyFullLogSuffixTheory.compile_log_emit_origin_ptr_path))) >>
(impl_tac >-
 (qpat_assum `w2n (n2w (LENGTH (enc enc_ty enc_val)) : bytes32) =
    LENGTH (enc enc_ty enc_val)` (fn len_th => rewrite_tac[len_th]) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   DISJ2_TAC >> first_assum ACCEPT_TAC,
   strip_tac >> qexists_tac `out_q` >>
   conj_tac >> first_assum ACCEPT_TAC])) >>
strip_tac >>
suspend "encoded_log"
QED
*)

Resume compile_log_frag_full[encoded_log]:
`encoded.vs_call_ctx.cc_address = cx.txn.target` by
 (qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace)
    ctx func cenv cx mid prepared`
   (mp_tac o CONJUNCT1 o REWRITE_RULE [stmt_state_rel_def]) >>
  qpat_assum `encoded.vs_call_ctx = prepared.vs_call_ctx` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [state_rel_def,call_ctx_rel_def] >> metis_tac[]) >>
`enc enc_ty enc_val = log_ev.data` by
 (qpat_assum `enc enc_ty enc_val = _` mp_tac >>
  simp_tac (srw_ss()) [Abbr `log_ev`,vyperABITheory.vyper_to_abi_type_def]) >>
`<|logger := w2w encoded.vs_call_ctx.cc_address;
   topics := n2w h::topics;
   data := mem_bytes_at (w2n out_bw)
     (w2n (n2w (LENGTH (enc enc_ty enc_val)) : bytes32)) encoded.vs_memory|>
 = log_ev` by
 (qpat_assum `mem_bytes_at (w2n out_bw) (LENGTH (enc enc_ty enc_val))
    encoded.vs_memory = enc enc_ty enc_val` mp_tac >>
  qpat_assum `w2n (n2w (LENGTH (enc enc_ty enc_val)) : bytes32) =
    LENGTH (enc enc_ty enc_val)` mp_tac >>
  qpat_assum `encoded.vs_call_ctx.cc_address = cx.txn.target` mp_tac >>
  qpat_assum `enc enc_ty enc_val = log_ev.data` mp_tac >>
  simp_tac (srw_ss()) [Abbr `log_ev`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> asm_rewrite_tac[]) >>
qabbrev_tac `fin = encoded with
 <|vs_logs := encoded.vs_logs ++ [log_ev];
   vs_inst_idx := LENGTH sb.cs_current_insts|>` >>
`!D. gas_origin_ptr_path
 (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
 (encoded,Genc,tnenc) [] (OK fin,Genc,tnenc)` by
 (qpat_assum `!D. gas_origin_ptr_path
    (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (encoded,Genc,tnenc) [] _` mp_tac >>
  qpat_assum `<|logger := w2w encoded.vs_call_ctx.cc_address;
    topics := n2w h::topics; data := _|> = log_ev` mp_tac >>
  simp_tac bool_ss [Abbr `fin`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> asm_rewrite_tac[]) >>
suspend "logged_event"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[encoded_log]:
`encoded.vs_call_ctx.cc_address = cx.txn.target` by
 (qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace)
    ctx func cenv cx mid prepared`
   (mp_tac o CONJUNCT1 o REWRITE_RULE [stmt_state_rel_def]) >>
  qpat_assum `encoded.vs_call_ctx = prepared.vs_call_ctx` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [state_rel_def,call_ctx_rel_def] >> metis_tac[]) >>
`enc enc_ty enc_val = log_ev.data` by
 (qpat_assum `enc enc_ty enc_val = _` mp_tac >>
  simp_tac (srw_ss()) [Abbr `log_ev`,vyperABITheory.vyper_to_abi_type_def]) >>
`<|logger := w2w encoded.vs_call_ctx.cc_address;
   topics := n2w h::topics;
   data := mem_bytes_at (w2n out_bw)
     (w2n (n2w (LENGTH (enc enc_ty enc_val)) : bytes32)) encoded.vs_memory|>
 = log_ev` by
 (qpat_assum `mem_bytes_at (w2n out_bw) (LENGTH (enc enc_ty enc_val))
    encoded.vs_memory = enc enc_ty enc_val` mp_tac >>
  qpat_assum `w2n (n2w (LENGTH (enc enc_ty enc_val)) : bytes32) =
    LENGTH (enc enc_ty enc_val)` mp_tac >>
  qpat_assum `encoded.vs_call_ctx.cc_address = cx.txn.target` mp_tac >>
  qpat_assum `enc enc_ty enc_val = log_ev.data` mp_tac >>
  simp_tac (srw_ss()) [Abbr `log_ev`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> asm_rewrite_tac[]) >>
qabbrev_tac `fin = encoded with
 <|vs_logs := encoded.vs_logs ++ [log_ev];
   vs_inst_idx := LENGTH sb.cs_current_insts|>` >>
`!D. gas_origin_ptr_path
 (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
 (encoded,Genc,tnenc) [] (OK fin,Genc,tnenc)` by
 (qpat_assum `!D. gas_origin_ptr_path
    (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (encoded,Genc,tnenc) [] _` mp_tac >>
  qpat_assum `<|logger := w2w encoded.vs_call_ctx.cc_address;
    topics := n2w h::topics; data := _|> = log_ev` mp_tac >>
  simp_tac bool_ss [Abbr `fin`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> asm_rewrite_tac[]) >>
suspend "logged_event"
QED
*)

Resume compile_log_frag_full[logged_event]:
`local_ptrs_rel func cenv mid.scopes prepared` by
 (qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace)
    ctx func cenv cx mid prepared`
   (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [state_rel_def] o
    CONJUNCT1 o REWRITE_RULE [stmt_state_rel_def])) >>
`s2.cs_next_var <= s3.cs_next_var` by
 (qpat_assum `ci_mono s2 s3`
   (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  first_assum ACCEPT_TAC) >>
`local_ptrs_reserved cenv s3` by
 (qspecl_then [`cenv`,`s2`,`s3`] match_mp_tac
   exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
  conj_tac >> first_assum ACCEPT_TAC) >>
`!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
 not_fresh_at s3 p` by
 (qpat_assum `local_ptrs_reserved cenv s3` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [local_ptrs_reserved_def] >> metis_tac[]) >>
`!name entry local_p sz.
 lookup_scopes name mid.scopes = SOME entry /\
 FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var local_p) sz) ==>
 lookup_var local_p encoded = lookup_var local_p prepared` by
 (rpt gen_tac >> strip_tac >>
  `not_fresh_at s3 local_p` by
   (qpat_assum `!name p sz. FLOOKUP cenv.ce_vars name = _ ==> _`
     (qspecl_then [`name`,`local_p`,`sz`] match_mp_tac) >>
    first_assum ACCEPT_TAC) >>
  qpat_assum `local_ptrs_rel func cenv mid.scopes prepared`
   (mp_tac o Q.SPECL [`name`,`entry`,`local_p`,`sz`] o CONJUNCT1 o
    REWRITE_RULE [local_ptrs_rel_def]) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `lookup_var local_p encoded = SOME w` by
   (qpat_assum `!x w. not_fresh_at s3 x /\ lookup_var x prepared = SOME w ==> _`
     (qspecl_then [`local_p`,`w`] match_mp_tac) >>
    conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `lookup_var local_p encoded = SOME w` mp_tac >>
  qpat_assum `lookup_var local_p prepared = SOME w` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
`!name b n. local_region cenv mid.scopes encoded name b n <=>
 local_region cenv mid.scopes prepared name b n` by
 (rpt gen_tac >> match_mp_tac local_region_lookup_cong >>
  first_assum ACCEPT_TAC) >>
suspend "encoded_local_registers"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[logged_event]:
`local_ptrs_rel func cenv mid.scopes prepared` by
 (qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace)
    ctx func cenv cx mid prepared`
   (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [state_rel_def] o
    CONJUNCT1 o REWRITE_RULE [stmt_state_rel_def])) >>
`s2.cs_next_var <= s3.cs_next_var` by
 (qpat_assum `ci_mono s2 s3`
   (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  first_assum ACCEPT_TAC) >>
`local_ptrs_reserved cenv s3` by
 (qspecl_then [`cenv`,`s2`,`s3`] match_mp_tac
   exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
  conj_tac >> first_assum ACCEPT_TAC) >>
`!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
 not_fresh_at s3 p` by
 (qpat_assum `local_ptrs_reserved cenv s3` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [local_ptrs_reserved_def] >> metis_tac[]) >>
`!name entry local_p sz.
 lookup_scopes name mid.scopes = SOME entry /\
 FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var local_p) sz) ==>
 lookup_var local_p encoded = lookup_var local_p prepared` by
 (rpt gen_tac >> strip_tac >>
  `not_fresh_at s3 local_p` by
   (qpat_assum `!name p sz. FLOOKUP cenv.ce_vars name = _ ==> _`
     (qspecl_then [`name`,`local_p`,`sz`] match_mp_tac) >>
    first_assum ACCEPT_TAC) >>
  qpat_assum `local_ptrs_rel func cenv mid.scopes prepared`
   (mp_tac o Q.SPECL [`name`,`entry`,`local_p`,`sz`] o CONJUNCT1 o
    REWRITE_RULE [local_ptrs_rel_def]) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `lookup_var local_p encoded = SOME w` by
   (qpat_assum `!x w. not_fresh_at s3 x /\ lookup_var x prepared = SOME w ==> _`
     (qspecl_then [`local_p`,`w`] match_mp_tac) >>
    conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `lookup_var local_p encoded = SOME w` mp_tac >>
  qpat_assum `lookup_var local_p prepared = SOME w` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
`!name b n. local_region cenv mid.scopes encoded name b n <=>
 local_region cenv mid.scopes prepared name b n` by
 (rpt gen_tac >> match_mp_tac local_region_lookup_cong >>
  first_assum ACCEPT_TAC) >>
suspend "encoded_local_registers"
QED
*)

Resume compile_log_frag_full[encoded_local_registers]:
`!aid b k. FLOOKUP encoded.vs_allocas aid = SOME (b,k) /\
 FLOOKUP prepared.vs_allocas aid = NONE ==> prepared.vs_alloca_next <= b` by
 (qpat_assum `window_alloca_growth prepared encoded` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [abiEncoderWindowContractTheory.window_alloca_growth_def] >>
  metis_tac[]) >>
`!name entry local_p sz.
 lookup_scopes name mid.scopes = SOME entry /\
 FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var local_p) sz) ==>
 !inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
 inst.inst_outputs = [local_p] ==>
 inst.inst_id NOTIN window_alloca_sites func (frag_ids s3 s4)` by
 (rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL
   [`dst.buf_operand`,`src.buf_operand`,
    `type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys)`,
    `s3`,`len`,`s4`,`func`,`func`,`cenv`,`s3`,`mid.scopes`,
    `name`,`entry`,`local_p`,`sz`]
   exprSimAbiEncodeCallerFrameTheory.abi_encode_scratch_local_id_exclusion) >>
  (impl_tac >-
   (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    simp_tac bool_ss [Abbr `dtys`] >> first_assum ACCEPT_TAC,
    rpt strip_tac >> first_assum ACCEPT_TAC,decide_tac])) >>
  disch_then ACCEPT_TAC) >>
suspend "encoded_scratch_ids"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[encoded_local_registers]:
`!aid b k. FLOOKUP encoded.vs_allocas aid = SOME (b,k) /\
 FLOOKUP prepared.vs_allocas aid = NONE ==> prepared.vs_alloca_next <= b` by
 (qpat_assum `window_alloca_growth prepared encoded` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [abiEncoderWindowContractTheory.window_alloca_growth_def] >>
  metis_tac[]) >>
`!name entry local_p sz.
 lookup_scopes name mid.scopes = SOME entry /\
 FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var local_p) sz) ==>
 !inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
 inst.inst_outputs = [local_p] ==>
 inst.inst_id NOTIN window_alloca_sites func (frag_ids s3 s4)` by
 (rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL
   [`dst.buf_operand`,`src.buf_operand`,
    `type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT dtys)`,
    `s3`,`len`,`s4`,`func`,`func`,`cenv`,`s3`,`mid.scopes`,
    `name`,`entry`,`local_p`,`sz`]
   exprSimAbiEncodeCallerFrameTheory.abi_encode_scratch_local_id_exclusion) >>
  (impl_tac >-
   (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    simp_tac bool_ss [Abbr `dtys`] >> first_assum ACCEPT_TAC,
    rpt strip_tac >> first_assum ACCEPT_TAC,decide_tac])) >>
  disch_then ACCEPT_TAC) >>
suspend "encoded_scratch_ids"
QED
*)

Resume compile_log_frag_full[encoded_scratch_ids]:
`alloca_inv encoded` by
 (qpat_assum `!u. gas_path_mem ctx func prepared 0 (OK u) ==> alloca_inv u`
   (qspec_then `encoded` match_mp_tac) >> first_assum ACCEPT_TAC) >>
`!name b n. local_region cenv mid.scopes prepared name b n ==>
 !aid q k. aid IN window_alloca_sites func (frag_ids s3 s4) /\
 FLOOKUP encoded.vs_allocas aid = SOME (q,k) ==> b+n <= q \/ q+k <= b` by
 (rpt gen_tac >>
  simp_tac bool_ss [local_region_def] >>
  disch_then (qx_choosel_then [`entry`,`local_p`,`local_w`] strip_assume_tac) >>
  qpat_assum `b = w2n local_w` (fn th => rewrite_tac [th]) >>
  match_mp_tac (Q.SPECL
   [`func`,`cenv`,`mid.scopes`,`prepared`,`encoded`,
    `window_alloca_sites func (frag_ids s3 s4)`,`name`,`entry`,`local_p`,`n`,`local_w`]
   exprSimAbiEncodeCallerFrameTheory.abi_encode_local_ptr_separation) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   qpat_assum `!name entry local_p sz.
    lookup_scopes name mid.scopes = SOME entry /\ _ ==> _`
    (qspecl_then [`name`,`entry`,`local_p`,`n`] match_mp_tac) >>
   conj_tac >> first_assum ACCEPT_TAC]) >>
`!name b n. local_region cenv mid.scopes prepared name b n ==>
 b+n <= w2n out_bw \/ w2n out_bw + LENGTH (enc enc_ty enc_val) <= b` by
 (rpt gen_tac >> strip_tac >>
  qpat_assum `!name b len. local_region cenv mid.scopes prepared name b len ==>
    loweringStateRelDefs$regions_disjoint (w2n out_bw) outcap b len`
   (qspecl_then [`name`,`b`,`n`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  rewrite_tac [loweringStateRelDefsTheory.regions_disjoint_def] >>
  qpat_assum `LENGTH (enc enc_ty enc_val) <= outcap` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
`!name b n. local_region cenv mid.scopes prepared name b n ==>
 mem_bytes_at b n encoded.vs_memory = mem_bytes_at b n prepared.vs_memory` by
 (rpt gen_tac >> strip_tac >>
  match_mp_tac abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
  rpt gen_tac >> strip_tac >>
  match_mp_tac (Q.INST
   [`ids` |-> `window_alloca_sites func (frag_ids s3 s4)`,
    `outs` |-> `[(w2n (out_bw:bytes32),LENGTH (enc enc_ty enc_val))]`,
    `s` |-> `prepared`,`t` |-> `encoded`,`lo` |-> `b`,`n` |-> `n`]
   exprSimAbiEncodeFrameTransferTheory.abi_encode_registered_protected_byte) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   simp_tac (srw_ss()) [EVERY_DEF] >>
    qpat_assum `!name b n. local_region cenv mid.scopes prepared name b n ==>
     b+n <= w2n out_bw \/ _`
     (qspecl_then [`name`,`b`,`n`] match_mp_tac) >> first_assum ACCEPT_TAC,
   qpat_assum `!name b n. local_region cenv mid.scopes prepared name b n ==>
    !aid q k. _`
    (qspecl_then [`name`,`b`,`n`] match_mp_tac) >> first_assum ACCEPT_TAC]) >>
suspend "encoded_local_bytes"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[encoded_scratch_ids]:
`alloca_inv encoded` by
 (qpat_assum `!u. gas_path_mem ctx func prepared 0 (OK u) ==> alloca_inv u`
   (qspec_then `encoded` match_mp_tac) >> first_assum ACCEPT_TAC) >>
`!name b n. local_region cenv mid.scopes prepared name b n ==>
 !aid q k. aid IN window_alloca_sites func (frag_ids s3 s4) /\
 FLOOKUP encoded.vs_allocas aid = SOME (q,k) ==> b+n <= q \/ q+k <= b` by
 (rpt gen_tac >>
  simp_tac bool_ss [local_region_def] >>
  disch_then (qx_choosel_then [`entry`,`local_p`,`local_w`] strip_assume_tac) >>
  qpat_assum `b = w2n local_w` (fn th => rewrite_tac [th]) >>
  match_mp_tac (Q.SPECL
   [`func`,`cenv`,`mid.scopes`,`prepared`,`encoded`,
    `window_alloca_sites func (frag_ids s3 s4)`,`name`,`entry`,`local_p`,`n`,`local_w`]
   exprSimAbiEncodeCallerFrameTheory.abi_encode_local_ptr_separation) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   qpat_assum `!name entry local_p sz.
    lookup_scopes name mid.scopes = SOME entry /\ _ ==> _`
    (qspecl_then [`name`,`entry`,`local_p`,`n`] match_mp_tac) >>
   conj_tac >> first_assum ACCEPT_TAC]) >>
`!name b n. local_region cenv mid.scopes prepared name b n ==>
 b+n <= w2n out_bw \/ w2n out_bw + LENGTH (enc enc_ty enc_val) <= b` by
 (rpt gen_tac >> strip_tac >>
  qpat_assum `!name b len. local_region cenv mid.scopes prepared name b len ==>
    loweringStateRelDefs$regions_disjoint (w2n out_bw) outcap b len`
   (qspecl_then [`name`,`b`,`n`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  rewrite_tac [loweringStateRelDefsTheory.regions_disjoint_def] >>
  qpat_assum `LENGTH (enc enc_ty enc_val) <= outcap` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
`!name b n. local_region cenv mid.scopes prepared name b n ==>
 mem_bytes_at b n encoded.vs_memory = mem_bytes_at b n prepared.vs_memory` by
 (rpt gen_tac >> strip_tac >>
  match_mp_tac abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
  rpt gen_tac >> strip_tac >>
  match_mp_tac (Q.INST
   [`ids` |-> `window_alloca_sites func (frag_ids s3 s4)`,
    `outs` |-> `[(w2n (out_bw:bytes32),LENGTH (enc enc_ty enc_val))]`,
    `s` |-> `prepared`,`t` |-> `encoded`,`lo` |-> `b`,`n` |-> `n`]
   exprSimAbiEncodeFrameTransferTheory.abi_encode_registered_protected_byte) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   simp_tac (srw_ss()) [EVERY_DEF] >>
    qpat_assum `!name b n. local_region cenv mid.scopes prepared name b n ==>
     b+n <= w2n out_bw \/ _`
     (qspecl_then [`name`,`b`,`n`] match_mp_tac) >> first_assum ACCEPT_TAC,
   qpat_assum `!name b n. local_region cenv mid.scopes prepared name b n ==>
    !aid q k. _`
    (qspecl_then [`name`,`b`,`n`] match_mp_tac) >> first_assum ACCEPT_TAC]) >>
suspend "encoded_local_bytes"
QED
*)

Resume compile_log_frag_full[encoded_local_bytes]:
qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace)
 ctx func cenv cx mid prepared`
 (strip_assume_tac o REWRITE_RULE [stmt_state_rel_def]) >>
`!aid. aid IN window_alloca_sites func (frag_ids s3 s4) ==>
 ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid` by
 (POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [abiEncoderWindowContractTheory.window_alloca_sites_def] >>
  metis_tac[]) >>
`MEM (mk_inst s2.cs_next_id ALLOCA [Lit (n2w outcap)]
 [STRING #"%" (toString s2.cs_next_var)]) (fn_insts func)` by
 (irule exprSimAllocTheory.buffer_alloc_code >>
  qexistsl_tac [`dst`,`s3`] >> conj_tac >> first_assum ACCEPT_TAC) >>
`cenv.ce_is_ctor ==> !name tv v off.
 FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
 FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
  | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
 !aid q k. aid IN window_alloca_sites func (frag_ids s3 s4) /\
 FLOOKUP encoded.vs_allocas aid = SOME (q,k) ==>
 off+type_memory_size tv <= q \/ q+k <= off` by
 (strip_tac >> rpt gen_tac >> strip_tac >>
  match_mp_tac (Q.INST
   [`func` |-> `func`,`cenv` |-> `cenv`,`cx` |-> `cx`,`vs` |-> `mid`,
    `initial` |-> `prepared`,`actual` |-> `encoded`,
    `ids` |-> `window_alloca_sites func (frag_ids s3 s4)`]
   exprSimAbiEncodeCallerFrameTheory.abi_encode_immutable_region_separation) >>
  rpt conj_tac >> first_assum ACCEPT_TAC) >>
`cenv.ce_is_ctor ==> !name tv v off.
 FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
 FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
  | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
 off+type_memory_size tv <= w2n out_bw \/
 w2n out_bw + LENGTH (enc enc_ty enc_val) <= off` by
 (strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `immutable_alloca_sep func cenv cx mid prepared`
   (mp_tac o CONJUNCT2 o REWRITE_RULE [immutable_alloca_sep_def]) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`name`,`tv`,`v`,`off`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (mp_tac o CONJUNCT1 o CONJUNCT2) >>
  disch_then (qspecl_then
   [`mk_inst s2.cs_next_id ALLOCA [Lit (n2w outcap)]
     [STRING #"%" (toString s2.cs_next_var)]`,`w2n (out_bw:bytes32)`,`outcap`] mp_tac) >>
  (impl_tac >-
   (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    simp_tac (srw_ss()) [venomInstTheory.mk_inst_def] >>
    first_assum ACCEPT_TAC])) >>
  rewrite_tac [loweringStateRelDefsTheory.regions_disjoint_def] >>
  qpat_assum `LENGTH (enc enc_ty enc_val) <= outcap` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
`cenv.ce_is_ctor ==> !name tv v off.
 FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
 FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
  | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
 mem_bytes_at off (type_memory_size tv) encoded.vs_memory =
 mem_bytes_at off (type_memory_size tv) prepared.vs_memory` by
 (strip_tac >> rpt gen_tac >> strip_tac >>
  match_mp_tac abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
  rpt gen_tac >> strip_tac >>
  match_mp_tac (Q.INST
   [`ids` |-> `window_alloca_sites func (frag_ids s3 s4)`,
    `outs` |-> `[(w2n (out_bw:bytes32),LENGTH (enc enc_ty enc_val))]`,
    `s` |-> `prepared`,`t` |-> `encoded`,`lo` |-> `off`,`n` |-> `type_memory_size tv`]
   exprSimAbiEncodeFrameTransferTheory.abi_encode_registered_protected_byte) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   simp_tac (srw_ss()) [EVERY_DEF] >>
    qpat_assum `cenv.ce_is_ctor ==> !name tv v off. _ ==>
     off+type_memory_size tv <= w2n out_bw \/ _` mp_tac >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (qspecl_then [`name`,`tv`,`v`,`off`] match_mp_tac) >>
    conj_tac >> first_assum ACCEPT_TAC,
   qpat_assum `cenv.ce_is_ctor ==> !name tv v off. _ ==> !aid q k. _` mp_tac >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (qspecl_then [`name`,`tv`,`v`,`off`] match_mp_tac) >>
    conj_tac >> first_assum ACCEPT_TAC]) >>
suspend "encoded_immutable_bytes"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[encoded_local_bytes]:
qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace)
 ctx func cenv cx mid prepared`
 (strip_assume_tac o REWRITE_RULE [stmt_state_rel_def]) >>
`!aid. aid IN window_alloca_sites func (frag_ids s3 s4) ==>
 ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid` by
 (POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [abiEncoderWindowContractTheory.window_alloca_sites_def] >>
  metis_tac[]) >>
`MEM (mk_inst s2.cs_next_id ALLOCA [Lit (n2w outcap)]
 [STRING #"%" (toString s2.cs_next_var)]) (fn_insts func)` by
 (irule exprSimAllocTheory.buffer_alloc_code >>
  qexistsl_tac [`dst`,`s3`] >> conj_tac >> first_assum ACCEPT_TAC) >>
`cenv.ce_is_ctor ==> !name tv v off.
 FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
 FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
  | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
 !aid q k. aid IN window_alloca_sites func (frag_ids s3 s4) /\
 FLOOKUP encoded.vs_allocas aid = SOME (q,k) ==>
 off+type_memory_size tv <= q \/ q+k <= off` by
 (strip_tac >> rpt gen_tac >> strip_tac >>
  match_mp_tac (Q.INST
   [`func` |-> `func`,`cenv` |-> `cenv`,`cx` |-> `cx`,`vs` |-> `mid`,
    `initial` |-> `prepared`,`actual` |-> `encoded`,
    `ids` |-> `window_alloca_sites func (frag_ids s3 s4)`]
   exprSimAbiEncodeCallerFrameTheory.abi_encode_immutable_region_separation) >>
  rpt conj_tac >> first_assum ACCEPT_TAC) >>
`cenv.ce_is_ctor ==> !name tv v off.
 FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
 FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
  | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
 off+type_memory_size tv <= w2n out_bw \/
 w2n out_bw + LENGTH (enc enc_ty enc_val) <= off` by
 (strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `immutable_alloca_sep func cenv cx mid prepared`
   (mp_tac o CONJUNCT2 o REWRITE_RULE [immutable_alloca_sep_def]) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`name`,`tv`,`v`,`off`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (mp_tac o CONJUNCT1 o CONJUNCT2) >>
  disch_then (qspecl_then
   [`mk_inst s2.cs_next_id ALLOCA [Lit (n2w outcap)]
     [STRING #"%" (toString s2.cs_next_var)]`,`w2n (out_bw:bytes32)`,`outcap`] mp_tac) >>
  (impl_tac >-
   (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    simp_tac (srw_ss()) [venomInstTheory.mk_inst_def] >>
    first_assum ACCEPT_TAC])) >>
  rewrite_tac [loweringStateRelDefsTheory.regions_disjoint_def] >>
  qpat_assum `LENGTH (enc enc_ty enc_val) <= outcap` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
`cenv.ce_is_ctor ==> !name tv v off.
 FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
 FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
  | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
 mem_bytes_at off (type_memory_size tv) encoded.vs_memory =
 mem_bytes_at off (type_memory_size tv) prepared.vs_memory` by
 (strip_tac >> rpt gen_tac >> strip_tac >>
  match_mp_tac abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
  rpt gen_tac >> strip_tac >>
  match_mp_tac (Q.INST
   [`ids` |-> `window_alloca_sites func (frag_ids s3 s4)`,
    `outs` |-> `[(w2n (out_bw:bytes32),LENGTH (enc enc_ty enc_val))]`,
    `s` |-> `prepared`,`t` |-> `encoded`,`lo` |-> `off`,`n` |-> `type_memory_size tv`]
   exprSimAbiEncodeFrameTransferTheory.abi_encode_registered_protected_byte) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   simp_tac (srw_ss()) [EVERY_DEF] >>
    qpat_assum `cenv.ce_is_ctor ==> !name tv v off. _ ==>
     off+type_memory_size tv <= w2n out_bw \/ _` mp_tac >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (qspecl_then [`name`,`tv`,`v`,`off`] match_mp_tac) >>
    conj_tac >> first_assum ACCEPT_TAC,
   qpat_assum `cenv.ce_is_ctor ==> !name tv v off. _ ==> !aid q k. _` mp_tac >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (qspecl_then [`name`,`tv`,`v`,`off`] match_mp_tac) >>
    conj_tac >> first_assum ACCEPT_TAC]) >>
suspend "encoded_immutable_bytes"
QED
*)

Resume compile_log_frag_full[encoded_immutable_bytes]:
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 state_rel H func cenv cx mid encoded` by
 (gen_tac >> strip_tac >>
  `state_rel H func cenv cx mid prepared` by
   (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid prepared`
     (qspec_then `H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [stmt_state_rel_def])) >>
  match_mp_tac (Q.INST
   [`initial` |-> `prepared`,`prepared` |-> `prepared`,`actual` |-> `encoded`,
    `observer` |-> `func`,`ids` |-> `window_alloca_sites func (frag_ids s3 s4)`,
    `outs` |-> `[(w2n (out_bw:bytes32),LENGTH (enc enc_ty enc_val))]`]
   exprSimAbiEncodeStateTransportTheory.abi_encode_caller_state_rel) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,REFL_TAC]) >>
`immutable_alloca_sep func cenv cx mid encoded` by
 (match_mp_tac (Q.INST [`initial` |-> `prepared`]
   exprSimAbiEncodeStateTransportTheory.abi_encode_caller_immutable_separation) >>
  rpt conj_tac >> first_assum ACCEPT_TAC) >>
`alloca_room ctx func encoded /\ fmp_room ctx func encoded` by
 (match_mp_tac (Q.INST [`initial` |-> `prepared`,`observer` |-> `func`]
   exprSimAbiEncodeStateTransportTheory.abi_encode_caller_resource_room) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   rpt strip_tac >> FIRST [REFL_TAC,first_assum ACCEPT_TAC]]) >>
suspend "encoded_state_fields"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[encoded_immutable_bytes]:
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 state_rel H func cenv cx mid encoded` by
 (gen_tac >> strip_tac >>
  `state_rel H func cenv cx mid prepared` by
   (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid prepared`
     (qspec_then `H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [stmt_state_rel_def])) >>
  match_mp_tac (Q.INST
   [`initial` |-> `prepared`,`prepared` |-> `prepared`,`actual` |-> `encoded`,
    `observer` |-> `func`,`ids` |-> `window_alloca_sites func (frag_ids s3 s4)`,
    `outs` |-> `[(w2n (out_bw:bytes32),LENGTH (enc enc_ty enc_val))]`]
   exprSimAbiEncodeStateTransportTheory.abi_encode_caller_state_rel) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,REFL_TAC]) >>
`immutable_alloca_sep func cenv cx mid encoded` by
 (match_mp_tac (Q.INST [`initial` |-> `prepared`]
   exprSimAbiEncodeStateTransportTheory.abi_encode_caller_immutable_separation) >>
  rpt conj_tac >> first_assum ACCEPT_TAC) >>
`alloca_room ctx func encoded /\ fmp_room ctx func encoded` by
 (match_mp_tac (Q.INST [`initial` |-> `prepared`,`observer` |-> `func`]
   exprSimAbiEncodeStateTransportTheory.abi_encode_caller_resource_room) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   rpt strip_tac >> FIRST [REFL_TAC,first_assum ACCEPT_TAC]]) >>
suspend "encoded_state_fields"
QED
*)

Resume compile_log_frag_full[encoded_state_fields]:
`encoded.vs_labels = prepared.vs_labels` by
 (drule_all abiEncoderWindowContractTheory.window_strong_result_labels >> simp[]) >>
`!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at s3 x` by
 (qpat_assum `local_ptrs_reserved cenv s3`
   (mp_tac o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE [local_ptrs_reserved_def]) >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
`immutable_base_zero cenv encoded` by
 (match_mp_tac (Q.INST [`initial` |-> `prepared`]
   exprSimAbiEncodeStateTransportTheory.abi_encode_caller_immutable_base) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   rpt gen_tac >> strip_tac >>
   `not_fresh_at s3 x` by
    (qpat_assum `!x. cenv.ce_imm_alloca = SOME (Var x) ==> _`
      (qspec_then `x` match_mp_tac) >> first_assum ACCEPT_TAC) >>
   qpat_assum `!x w. not_fresh_at s3 x /\ lookup_var x prepared = SOME w ==> _`
    (qspecl_then [`x`,`v`] match_mp_tac) >> conj_tac >> first_assum ACCEPT_TAC]) >>
`!aid b sz. aid IN window_alloca_sites func (frag_ids s3 s4) /\
 FLOOKUP encoded.vs_allocas aid = SOME (b,sz) ==> sz = 32` by
 (qpat_assum `window_strong_result ctx func s3 s4 len enc_ty enc_val
   (w2n out_bw) prepared encoded`
   (mp_tac o REWRITE_RULE [abiEncoderWindowContractTheory.window_strong_result_def]) >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
`!aid. aid NOTIN window_alloca_sites func (frag_ids s3 s4) ==>
 FLOOKUP encoded.vs_allocas aid = FLOOKUP prepared.vs_allocas aid` by
 (qpat_assum `abi_encoder_registered_effect
   (window_alloca_sites func (frag_ids s3 s4)) _ prepared encoded`
   (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE
    [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def])) >>
`!row_inst row_word row_base row_size.
 MEM row_inst (fn_insts func) /\ row_inst.inst_opcode = ALLOCA /\
 row_inst.inst_operands = [Lit row_word] /\
 FLOOKUP encoded.vs_allocas row_inst.inst_id = SOME (row_base,row_size) ==> row_size = w2n row_word` by
 (map_every qx_gen_tac [`row_inst`,`row_word`,`row_base`,`row_size`] >> strip_tac >>
  Cases_on `row_inst.inst_id IN window_alloca_sites func (frag_ids s3 s4)`
  >- (`row_size = 32` by
       (qpat_assum `!aid b row_size. aid IN window_alloca_sites func (frag_ids s3 s4) /\
         FLOOKUP encoded.vs_allocas aid = SOME (b,row_size) ==> row_size = 32`
         (qspecl_then [`row_inst.inst_id`,`row_base`,`row_size`] match_mp_tac) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
      `row_inst.inst_id IN frag_ids s3 s4` by
       (qpat_assum `row_inst.inst_id IN window_alloca_sites func (frag_ids s3 s4)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac (srw_ss()) [abiEncoderWindowContractTheory.window_alloca_sites_def]) >>
      `row_inst.inst_operands = [Lit 32w]` by
       (qpat_assum `!row_inst. MEM row_inst (fn_insts func) /\ row_inst.inst_id IN frag_ids s3 s4 /\
         row_inst.inst_opcode = ALLOCA ==> _`
         (qspec_then `row_inst` mp_tac) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
        disch_then (ACCEPT_TAC o CONJUNCT1)) >>
      qpat_assum `row_inst.inst_operands = [Lit row_word]` mp_tac >>
      qpat_assum `row_inst.inst_operands = [Lit 32w]` mp_tac >>
      qpat_assum `row_size = 32` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [wordsTheory.dimword_def]) >>
  `FLOOKUP prepared.vs_allocas row_inst.inst_id = SOME (row_base,row_size)` by
   (qpat_assum `!aid. aid NOTIN window_alloca_sites func (frag_ids s3 s4) ==> _`
     (qspec_then `row_inst.inst_id` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    qpat_assum `FLOOKUP encoded.vs_allocas row_inst.inst_id = SOME (row_base,row_size)` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  qpat_assum `!row_inst row_word row_base row_size. MEM row_inst (fn_insts func) /\
    row_inst.inst_opcode = ALLOCA /\ row_inst.inst_operands = [Lit row_word] /\
    FLOOKUP prepared.vs_allocas row_inst.inst_id = SOME (row_base,row_size) ==> row_size = w2n row_word`
    (qspecl_then [`row_inst`,`row_word`,`row_base`,`row_size`] match_mp_tac) >>
  rpt conj_tac >> first_assum ACCEPT_TAC) >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 stmt_state_rel H ctx func cenv cx mid encoded` by
 (gen_tac >> strip_tac >> rewrite_tac [stmt_state_rel_def] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
    state_rel H func cenv cx mid encoded`
    (qspec_then `H` match_mp_tac) >> first_assum ACCEPT_TAC]) >>
suspend "encoded_stmt_state"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[encoded_state_fields]:
`encoded.vs_labels = prepared.vs_labels` by
 (drule_all abiEncoderWindowContractTheory.window_strong_result_labels >> simp[]) >>
`!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at s3 x` by
 (qpat_assum `local_ptrs_reserved cenv s3`
   (mp_tac o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE [local_ptrs_reserved_def]) >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
`immutable_base_zero cenv encoded` by
 (match_mp_tac (Q.INST [`initial` |-> `prepared`]
   exprSimAbiEncodeStateTransportTheory.abi_encode_caller_immutable_base) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   rpt gen_tac >> strip_tac >>
   `not_fresh_at s3 x` by
    (qpat_assum `!x. cenv.ce_imm_alloca = SOME (Var x) ==> _`
      (qspec_then `x` match_mp_tac) >> first_assum ACCEPT_TAC) >>
   qpat_assum `!x w. not_fresh_at s3 x /\ lookup_var x prepared = SOME w ==> _`
    (qspecl_then [`x`,`v`] match_mp_tac) >> conj_tac >> first_assum ACCEPT_TAC]) >>
`!aid b sz. aid IN window_alloca_sites func (frag_ids s3 s4) /\
 FLOOKUP encoded.vs_allocas aid = SOME (b,sz) ==> sz = 32` by
 (qpat_assum `window_strong_result ctx func s3 s4 len enc_ty enc_val
   (w2n out_bw) prepared encoded`
   (mp_tac o REWRITE_RULE [abiEncoderWindowContractTheory.window_strong_result_def]) >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
`!aid. aid NOTIN window_alloca_sites func (frag_ids s3 s4) ==>
 FLOOKUP encoded.vs_allocas aid = FLOOKUP prepared.vs_allocas aid` by
 (qpat_assum `abi_encoder_registered_effect
   (window_alloca_sites func (frag_ids s3 s4)) _ prepared encoded`
   (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE
    [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def])) >>
`!row_inst row_word row_base row_size.
 MEM row_inst (fn_insts func) /\ row_inst.inst_opcode = ALLOCA /\
 row_inst.inst_operands = [Lit row_word] /\
 FLOOKUP encoded.vs_allocas row_inst.inst_id = SOME (row_base,row_size) ==> row_size = w2n row_word` by
 (map_every qx_gen_tac [`row_inst`,`row_word`,`row_base`,`row_size`] >> strip_tac >>
  Cases_on `row_inst.inst_id IN window_alloca_sites func (frag_ids s3 s4)`
  >- (`row_size = 32` by
       (qpat_assum `!aid b row_size. aid IN window_alloca_sites func (frag_ids s3 s4) /\
         FLOOKUP encoded.vs_allocas aid = SOME (b,row_size) ==> row_size = 32`
         (qspecl_then [`row_inst.inst_id`,`row_base`,`row_size`] match_mp_tac) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
      `row_inst.inst_id IN frag_ids s3 s4` by
       (qpat_assum `row_inst.inst_id IN window_alloca_sites func (frag_ids s3 s4)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac (srw_ss()) [abiEncoderWindowContractTheory.window_alloca_sites_def]) >>
      `row_inst.inst_operands = [Lit 32w]` by
       (qpat_assum `!row_inst. MEM row_inst (fn_insts func) /\ row_inst.inst_id IN frag_ids s3 s4 /\
         row_inst.inst_opcode = ALLOCA ==> _`
         (qspec_then `row_inst` mp_tac) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
        disch_then (ACCEPT_TAC o CONJUNCT1)) >>
      qpat_assum `row_inst.inst_operands = [Lit row_word]` mp_tac >>
      qpat_assum `row_inst.inst_operands = [Lit 32w]` mp_tac >>
      qpat_assum `row_size = 32` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [wordsTheory.dimword_def]) >>
  `FLOOKUP prepared.vs_allocas row_inst.inst_id = SOME (row_base,row_size)` by
   (qpat_assum `!aid. aid NOTIN window_alloca_sites func (frag_ids s3 s4) ==> _`
     (qspec_then `row_inst.inst_id` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    qpat_assum `FLOOKUP encoded.vs_allocas row_inst.inst_id = SOME (row_base,row_size)` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  qpat_assum `!row_inst row_word row_base row_size. MEM row_inst (fn_insts func) /\
    row_inst.inst_opcode = ALLOCA /\ row_inst.inst_operands = [Lit row_word] /\
    FLOOKUP prepared.vs_allocas row_inst.inst_id = SOME (row_base,row_size) ==> row_size = w2n row_word`
    (qspecl_then [`row_inst`,`row_word`,`row_base`,`row_size`] match_mp_tac) >>
  rpt conj_tac >> first_assum ACCEPT_TAC) >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 stmt_state_rel H ctx func cenv cx mid encoded` by
 (gen_tac >> strip_tac >> rewrite_tac [stmt_state_rel_def] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
    state_rel H func cenv cx mid encoded`
    (qspec_then `H` match_mp_tac) >> first_assum ACCEPT_TAC]) >>
suspend "encoded_stmt_state"
QED
*)

Resume compile_log_frag_full[encoded_stmt_state]:
`!name b n i. local_region cenv mid.scopes prepared name b n /\
 b <= i /\ i < b+n ==> (i IN tnenc.t_mem <=> i IN tnprep.t_mem)` by
 (map_every qx_gen_tac [`local_name`,`local_b`,`local_n`,`local_i`] >> strip_tac >>
  qpat_assum `!i. (_ \/ _) /\
   (!id b sz. id IN window_alloca_sites func (frag_ids s3 s4) /\
    FLOOKUP encoded.vs_allocas id = SOME (b,sz) ==> _ \/ _) ==>
   (i IN tnenc.t_mem <=> i IN tnprep.t_mem)`
   (qspec_then `local_i` match_mp_tac) >> conj_tac
  >- (qpat_assum `!name b n. local_region cenv mid.scopes prepared name b n ==>
       b+n <= w2n out_bw \/ _`
       (qspecl_then [`local_name`,`local_b`,`local_n`] mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      qpat_assum `local_b <= local_i` mp_tac >>
      qpat_assum `local_i < local_b+local_n` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  map_every qx_gen_tac [`scratch_id`,`scratch_b`,`scratch_n`] >> strip_tac >>
  qpat_assum `!name b n. local_region cenv mid.scopes prepared name b n ==>
   !aid q k. _`
   (qspecl_then [`local_name`,`local_b`,`local_n`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`scratch_id`,`scratch_b`,`scratch_n`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `local_b <= local_i` mp_tac >>
  qpat_assum `local_i < local_b+local_n` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
`!aid b sz. FLOOKUP encoded.vs_allocas aid = SOME (b,sz) ==> lo <= b` by
 (qpat_assum `allocas_from lo encoded`
   (ACCEPT_TAC o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def])) >>
`lo <= w2n out_bw` by
 (qpat_assum `allocas_from lo prepared`
   (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
  disch_then (qspecl_then
   [`s2.cs_next_id`,`w2n (out_bw:bytes32)`,`outcap`] match_mp_tac) >>
  first_assum ACCEPT_TAC) >>
`mem_bytes_at 0 lo encoded.vs_memory = mem_bytes_at 0 lo prepared.vs_memory` by
 (match_mp_tac abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
  map_every qx_gen_tac [`prefix_i`] >> strip_tac >>
  match_mp_tac (Q.INST
   [`ids` |-> `window_alloca_sites func (frag_ids s3 s4)`,
    `outs` |-> `[(w2n (out_bw:bytes32),LENGTH (enc enc_ty enc_val))]`,
    `s` |-> `prepared`,`t` |-> `encoded`,`lo` |-> `0`,`n` |-> `lo`]
   exprSimAbiEncodeFrameTransferTheory.abi_encode_registered_protected_byte) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   simp_tac (srw_ss()) [EVERY_DEF] >>
    FIRST [first_assum ACCEPT_TAC,DISJ1_TAC >> first_assum ACCEPT_TAC],
   simp_tac bool_ss [arithmeticTheory.ADD_CLAUSES] >>
   map_every qx_gen_tac [`scratch_id`,`scratch_b`,`scratch_n`] >> strip_tac >>
   DISJ1_TAC >>
   qpat_assum `!aid b sz. FLOOKUP encoded.vs_allocas aid = SOME (b,sz) ==> lo <= b`
    (qspecl_then [`scratch_id`,`scratch_b`,`scratch_n`] match_mp_tac) >>
   first_assum ACCEPT_TAC,decide_tac]) >>
suspend "encoded_ghost_regions"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[encoded_stmt_state]:
`!name b n i. local_region cenv mid.scopes prepared name b n /\
 b <= i /\ i < b+n ==> (i IN tnenc.t_mem <=> i IN tnprep.t_mem)` by
 (map_every qx_gen_tac [`local_name`,`local_b`,`local_n`,`local_i`] >> strip_tac >>
  qpat_assum `!i. (_ \/ _) /\
   (!id b sz. id IN window_alloca_sites func (frag_ids s3 s4) /\
    FLOOKUP encoded.vs_allocas id = SOME (b,sz) ==> _ \/ _) ==>
   (i IN tnenc.t_mem <=> i IN tnprep.t_mem)`
   (qspec_then `local_i` match_mp_tac) >> conj_tac
  >- (qpat_assum `!name b n. local_region cenv mid.scopes prepared name b n ==>
       b+n <= w2n out_bw \/ _`
       (qspecl_then [`local_name`,`local_b`,`local_n`] mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      qpat_assum `local_b <= local_i` mp_tac >>
      qpat_assum `local_i < local_b+local_n` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  map_every qx_gen_tac [`scratch_id`,`scratch_b`,`scratch_n`] >> strip_tac >>
  qpat_assum `!name b n. local_region cenv mid.scopes prepared name b n ==>
   !aid q k. _`
   (qspecl_then [`local_name`,`local_b`,`local_n`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`scratch_id`,`scratch_b`,`scratch_n`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `local_b <= local_i` mp_tac >>
  qpat_assum `local_i < local_b+local_n` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
`!aid b sz. FLOOKUP encoded.vs_allocas aid = SOME (b,sz) ==> lo <= b` by
 (qpat_assum `allocas_from lo encoded`
   (ACCEPT_TAC o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def])) >>
`lo <= w2n out_bw` by
 (qpat_assum `allocas_from lo prepared`
   (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
  disch_then (qspecl_then
   [`s2.cs_next_id`,`w2n (out_bw:bytes32)`,`outcap`] match_mp_tac) >>
  first_assum ACCEPT_TAC) >>
`mem_bytes_at 0 lo encoded.vs_memory = mem_bytes_at 0 lo prepared.vs_memory` by
 (match_mp_tac abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
  map_every qx_gen_tac [`prefix_i`] >> strip_tac >>
  match_mp_tac (Q.INST
   [`ids` |-> `window_alloca_sites func (frag_ids s3 s4)`,
    `outs` |-> `[(w2n (out_bw:bytes32),LENGTH (enc enc_ty enc_val))]`,
    `s` |-> `prepared`,`t` |-> `encoded`,`lo` |-> `0`,`n` |-> `lo`]
   exprSimAbiEncodeFrameTransferTheory.abi_encode_registered_protected_byte) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   simp_tac (srw_ss()) [EVERY_DEF] >>
    FIRST [first_assum ACCEPT_TAC,DISJ1_TAC >> first_assum ACCEPT_TAC],
   simp_tac bool_ss [arithmeticTheory.ADD_CLAUSES] >>
   map_every qx_gen_tac [`scratch_id`,`scratch_b`,`scratch_n`] >> strip_tac >>
   DISJ1_TAC >>
   qpat_assum `!aid b sz. FLOOKUP encoded.vs_allocas aid = SOME (b,sz) ==> lo <= b`
    (qspecl_then [`scratch_id`,`scratch_b`,`scratch_n`] match_mp_tac) >>
   first_assum ACCEPT_TAC,decide_tac]) >>
suspend "encoded_ghost_regions"
QED
*)

Resume compile_log_frag_full[encoded_ghost_regions]:
`!i. i < lo ==> (i IN tnenc.t_mem <=> i IN tnprep.t_mem)` by
 (qx_gen_tac `prefix_i` >> strip_tac >>
  qpat_assum `!i. (_ \/ _) /\
   (!id b sz. id IN window_alloca_sites func (frag_ids s3 s4) /\
    FLOOKUP encoded.vs_allocas id = SOME (b,sz) ==> _ \/ _) ==>
   (i IN tnenc.t_mem <=> i IN tnprep.t_mem)`
   (qspec_then `prefix_i` match_mp_tac) >> conj_tac
  >- (DISJ1_TAC >> qpat_assum `lo <= w2n out_bw` mp_tac >>
      qpat_assum `prefix_i < lo` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  map_every qx_gen_tac [`scratch_id`,`scratch_b`,`scratch_n`] >> strip_tac >>
  DISJ1_TAC >>
  `lo <= scratch_b` by
   (qpat_assum `!aid b sz. FLOOKUP encoded.vs_allocas aid = SOME (b,sz) ==> lo <= b`
    (qspecl_then [`scratch_id`,`scratch_b`,`scratch_n`] match_mp_tac) >>
    first_assum ACCEPT_TAC) >>
  qpat_assum `prefix_i < lo` mp_tac >>
  qpat_assum `lo <= scratch_b` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
`!old_p old_n. not_fresh_at s3 old_p /\
 ptr_covers Gprep tnprep old_p prepared old_n ==>
 ptr_covers Genc tnenc old_p encoded old_n` by
 (map_every qx_gen_tac [`old_p`,`old_n`] >> strip_tac >>
  qpat_assum `!x w. not_fresh_at s3 x /\ lookup_var x prepared = SOME w ==>
   lookup_var x encoded = SOME w` mp_tac >>
  qpat_assum `!x. not_fresh_at s3 x ==>
   FLOOKUP Genc x = FLOOKUP Gprep x /\
   op_taint tnenc (Var x) = op_taint tnprep (Var x)` mp_tac >>
  qpat_assum `ptr_covers Gprep tnprep old_p prepared old_n` mp_tac >>
  qpat_assum `not_fresh_at s3 old_p` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  rewrite_tac [bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
suspend "encoded_ghost_pointers"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[encoded_ghost_regions]:
`!i. i < lo ==> (i IN tnenc.t_mem <=> i IN tnprep.t_mem)` by
 (qx_gen_tac `prefix_i` >> strip_tac >>
  qpat_assum `!i. (_ \/ _) /\
   (!id b sz. id IN window_alloca_sites func (frag_ids s3 s4) /\
    FLOOKUP encoded.vs_allocas id = SOME (b,sz) ==> _ \/ _) ==>
   (i IN tnenc.t_mem <=> i IN tnprep.t_mem)`
   (qspec_then `prefix_i` match_mp_tac) >> conj_tac
  >- (DISJ1_TAC >> qpat_assum `lo <= w2n out_bw` mp_tac >>
      qpat_assum `prefix_i < lo` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  map_every qx_gen_tac [`scratch_id`,`scratch_b`,`scratch_n`] >> strip_tac >>
  DISJ1_TAC >>
  `lo <= scratch_b` by
   (qpat_assum `!aid b sz. FLOOKUP encoded.vs_allocas aid = SOME (b,sz) ==> lo <= b`
    (qspecl_then [`scratch_id`,`scratch_b`,`scratch_n`] match_mp_tac) >>
    first_assum ACCEPT_TAC) >>
  qpat_assum `prefix_i < lo` mp_tac >>
  qpat_assum `lo <= scratch_b` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
`!old_p old_n. not_fresh_at s3 old_p /\
 ptr_covers Gprep tnprep old_p prepared old_n ==>
 ptr_covers Genc tnenc old_p encoded old_n` by
 (map_every qx_gen_tac [`old_p`,`old_n`] >> strip_tac >>
  qpat_assum `!x w. not_fresh_at s3 x /\ lookup_var x prepared = SOME w ==>
   lookup_var x encoded = SOME w` mp_tac >>
  qpat_assum `!x. not_fresh_at s3 x ==>
   FLOOKUP Genc x = FLOOKUP Gprep x /\
   op_taint tnenc (Var x) = op_taint tnprep (Var x)` mp_tac >>
  qpat_assum `ptr_covers Gprep tnprep old_p prepared old_n` mp_tac >>
  qpat_assum `not_fresh_at s3 old_p` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  rewrite_tac [bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
suspend "encoded_ghost_pointers"
QED
*)

Resume compile_log_frag_full[encoded_ghost_pointers]:
`!local_name local_entry local_p local_sz local_word.
 lookup_scopes local_name mid.scopes = SOME local_entry /\
 FLOOKUP cenv.ce_vars local_name = SOME (PtrVar (Var local_p) local_sz) /\
 lookup_var local_p prepared = SOME local_word /\
 (!mem. mem_agree_outside tnprep.t_mem prepared.vs_memory mem ==>
   val_in_memory local_entry.type local_entry.value (w2n local_word) mem) ==>
 !mem. mem_agree_outside tnenc.t_mem encoded.vs_memory mem ==>
   val_in_memory local_entry.type local_entry.value (w2n local_word) mem` by
 (map_every qx_gen_tac
   [`local_name`,`local_entry`,`local_p`,`local_sz`,`local_word`] >> strip_tac >>
  `val_wf local_entry.type local_entry.value /\
   type_memory_size local_entry.type <= local_sz` by
   (qpat_assum `local_ptrs_rel func cenv mid.scopes prepared`
     (mp_tac o Q.SPECL [`local_name`,`local_entry`,`local_p`,`local_sz`] o
      CONJUNCT1 o REWRITE_RULE [local_ptrs_rel_def]) >>
    (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
    POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `val_footprint local_entry.type local_entry.value <= local_sz` by
   (qspecl_then [`local_entry.type`,`local_entry.value`] mp_tac
      exprSimPropsTheory.val_footprint_le >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    qpat_assum `type_memory_size local_entry.type <= local_sz` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `local_region cenv mid.scopes prepared local_name
    (w2n local_word) local_sz` by
   (rewrite_tac [local_region_def] >>
    qexistsl_tac [`local_entry`,`local_p`,`local_word`] >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,REFL_TAC]) >>
  match_mp_tac (Q.INST
   [`tv` |-> `local_entry.type`,`v` |-> `local_entry.value`,
    `src` |-> `w2n (local_word:bytes32)`,
    `dst` |-> `w2n (local_word:bytes32)`,`n` |-> `local_sz`,
    `tn` |-> `tnprep.t_mem`,`tn'` |-> `tnenc.t_mem`,
    `mem` |-> `prepared.vs_memory`,`mem'` |-> `encoded.vs_memory`]
   (SPEC_ALL robustCopyTransportPtrTheory.robust_val_in_memory_copy_transport)) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   qpat_assum `!name b n. local_region cenv mid.scopes prepared name b n ==>
    mem_bytes_at b n encoded.vs_memory = mem_bytes_at b n prepared.vs_memory`
    (qspecl_then [`local_name`,`w2n (local_word:bytes32)`,`local_sz`]
     match_mp_tac) >> first_assum ACCEPT_TAC,
   qx_gen_tac `local_i` >> strip_tac >>
   qpat_assum `!name b n i. local_region cenv mid.scopes prepared name b n /\
    b <= i /\ i < b+n ==> (i IN tnenc.t_mem <=> i IN tnprep.t_mem)`
    (qspecl_then [`local_name`,`w2n (local_word:bytes32)`,`local_sz`,
      `w2n (local_word:bytes32)+local_i`] match_mp_tac) >>
   rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,decide_tac]]) >>
suspend "encoded_robust_locals"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[encoded_ghost_pointers]:
`!local_name local_entry local_p local_sz local_word.
 lookup_scopes local_name mid.scopes = SOME local_entry /\
 FLOOKUP cenv.ce_vars local_name = SOME (PtrVar (Var local_p) local_sz) /\
 lookup_var local_p prepared = SOME local_word /\
 (!mem. mem_agree_outside tnprep.t_mem prepared.vs_memory mem ==>
   val_in_memory local_entry.type local_entry.value (w2n local_word) mem) ==>
 !mem. mem_agree_outside tnenc.t_mem encoded.vs_memory mem ==>
   val_in_memory local_entry.type local_entry.value (w2n local_word) mem` by
 (map_every qx_gen_tac
   [`local_name`,`local_entry`,`local_p`,`local_sz`,`local_word`] >> strip_tac >>
  `val_wf local_entry.type local_entry.value /\
   type_memory_size local_entry.type <= local_sz` by
   (qpat_assum `local_ptrs_rel func cenv mid.scopes prepared`
     (mp_tac o Q.SPECL [`local_name`,`local_entry`,`local_p`,`local_sz`] o
      CONJUNCT1 o REWRITE_RULE [local_ptrs_rel_def]) >>
    (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
    POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `val_footprint local_entry.type local_entry.value <= local_sz` by
   (qspecl_then [`local_entry.type`,`local_entry.value`] mp_tac
      exprSimPropsTheory.val_footprint_le >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    qpat_assum `type_memory_size local_entry.type <= local_sz` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `local_region cenv mid.scopes prepared local_name
    (w2n local_word) local_sz` by
   (rewrite_tac [local_region_def] >>
    qexistsl_tac [`local_entry`,`local_p`,`local_word`] >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,REFL_TAC]) >>
  match_mp_tac (Q.INST
   [`tv` |-> `local_entry.type`,`v` |-> `local_entry.value`,
    `src` |-> `w2n (local_word:bytes32)`,
    `dst` |-> `w2n (local_word:bytes32)`,`n` |-> `local_sz`,
    `tn` |-> `tnprep.t_mem`,`tn'` |-> `tnenc.t_mem`,
    `mem` |-> `prepared.vs_memory`,`mem'` |-> `encoded.vs_memory`]
   (SPEC_ALL robustCopyTransportPtrTheory.robust_val_in_memory_copy_transport)) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   qpat_assum `!name b n. local_region cenv mid.scopes prepared name b n ==>
    mem_bytes_at b n encoded.vs_memory = mem_bytes_at b n prepared.vs_memory`
    (qspecl_then [`local_name`,`w2n (local_word:bytes32)`,`local_sz`]
     match_mp_tac) >> first_assum ACCEPT_TAC,
   qx_gen_tac `local_i` >> strip_tac >>
   qpat_assum `!name b n i. local_region cenv mid.scopes prepared name b n /\
    b <= i /\ i < b+n ==> (i IN tnenc.t_mem <=> i IN tnprep.t_mem)`
    (qspecl_then [`local_name`,`w2n (local_word:bytes32)`,`local_sz`,
      `w2n (local_word:bytes32)+local_i`] match_mp_tac) >>
   rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,decide_tac]]) >>
suspend "encoded_robust_locals"
QED
*)

Resume compile_log_frag_full[encoded_robust_locals]:
`!x. not_fresh_at sm x ==> not_fresh_at s3 x` by
 (qx_gen_tac `old_x` >> strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >>
  qpat_assum `sm.cs_next_var <= topic_sa.cs_next_var` mp_tac >>
  qpat_assum `ci_mono topic_sa s1` mp_tac >>
  qpat_assum `ci_mono s1 s2` mp_tac >>
  qpat_assum `ci_mono s2 s3` mp_tac >>
  qpat_assum `not_fresh_at sm old_x` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [ci_mono_def] >> rpt strip_tac >> decide_tac) >>
`(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
   not_fresh_at s3 x) /\
 (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
   not_fresh_at s3 x)` by
 (qpat_assum `!x. not_fresh_at sm x ==> not_fresh_at s3 x` mp_tac >>
  qpat_assum `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
   not_fresh_at sm x` mp_tac >>
  qpat_assum `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
   not_fresh_at sm x` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
`encoded.vs_accounts = prepared.vs_accounts /\
 encoded.vs_transient = prepared.vs_transient /\
 encoded.vs_immutables = prepared.vs_immutables` by
 (qpat_assum `abi_encoder_registered_effect _ _ prepared encoded`
   (mp_tac o REWRITE_RULE
    [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def]) >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
`!D. ghost_inv_at D lo d cenv cx mid Gprep tnprep prepared ==>
 ghost_inv_at D lo d cenv cx mid Genc tnenc encoded` by
 (qx_gen_tac `enc_dead` >> strip_tac >>
  qpat_x_assum `ghost_inv_at enc_dead lo d cenv cx mid Gprep tnprep prepared`
   (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
  rewrite_tac [bodyPtrDefsTheory.ghost_inv_at_def] >> rpt conj_tac
  >- (map_every qx_gen_tac [`local_name`,`local_entry`,`local_p`,`local_sz`] >>
      strip_tac >>
      qpat_assum `!name entry p sz. _ ==>
       ptr_covers Gprep tnprep p prepared sz /\ _`
       (qspecl_then [`local_name`,`local_entry`,`local_p`,`local_sz`] mp_tac) >>
      (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
      conj_tac
      >- (qpat_assum `!old_p old_n. not_fresh_at s3 old_p /\ _ ==> _`
           (qspecl_then [`local_p`,`local_sz`] match_mp_tac) >>
          conj_tac >- (qpat_assum `!name p sz. FLOOKUP cenv.ce_vars name = _ ==> _`
           (qspecl_then [`local_name`,`local_p`,`local_sz`] match_mp_tac) >>
           first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
      map_every qx_gen_tac [`local_word`,`local_mem`] >> strip_tac >>
      `lookup_var local_p prepared = SOME local_word` by
       (qpat_assum `!name entry local_p sz. _ ==>
          lookup_var local_p encoded = lookup_var local_p prepared`
         (qspecl_then [`local_name`,`local_entry`,`local_p`,`local_sz`] mp_tac) >>
        (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
        qpat_assum `lookup_var local_p encoded = SOME local_word` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
      qpat_assum `!local_name local_entry local_p local_sz local_word. _ ==>
       !mem. mem_agree_outside tnenc.t_mem encoded.vs_memory mem ==> _`
       (qspecl_then [`local_name`,`local_entry`,`local_p`,`local_sz`,
         `local_word`] mp_tac) >>
      (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       qx_gen_tac `local_old_mem` >> strip_tac >>
       qpat_assum `!w mem. lookup_var local_p prepared = SOME w /\ _ ==> _`
        (qspecl_then [`local_word`,`local_old_mem`] match_mp_tac) >>
       conj_tac >> first_assum ACCEPT_TAC])) >>
      disch_then (qspec_then `local_mem` match_mp_tac) >> first_assum ACCEPT_TAC)
  >- (Cases_on `d` >- simp_tac bool_ss [bodyPtrDefsTheory.return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb) cenv Genc tnenc encoded` >>
      PairCases_on `rb` >>
      qpat_assum `return_buf_ptr (SOME _) cenv Gprep tnprep prepared` mp_tac >>
      qpat_assum `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at s3 x` mp_tac >>
      qpat_assum `!old_p old_n. not_fresh_at s3 old_p /\ _ ==> _` mp_tac >>
      qpat_assum `!x w. not_fresh_at s3 x /\ lookup_var x prepared = SOME w ==> _`
       mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
      rewrite_tac [bodyPtrDefsTheory.return_buf_ptr_def] >> metis_tac[])
  >- (qpat_assum `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at s3 x` mp_tac >>
      qpat_assum `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
       op_taint tnprep (Var x) = {}` mp_tac >>
      qpat_assum `!x. not_fresh_at s3 x ==> FLOOKUP Genc x = _ /\ _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
  >- (qpat_assum `stor_taint_ok_at enc_dead tnprep prepared` mp_tac >>
      qpat_assum `encoded.vs_accounts = prepared.vs_accounts` mp_tac >>
      qpat_assum `encoded.vs_transient = prepared.vs_transient` mp_tac >>
      qpat_assum `encoded.vs_immutables = prepared.vs_immutables` mp_tac >>
      qpat_assum `encoded.vs_call_ctx = prepared.vs_call_ctx` mp_tac >>
      qpat_assum `tnenc.t_stor = tnprep.t_stor` mp_tac >>
      qpat_assum `tnenc.t_trans = tnprep.t_trans` mp_tac >>
      qpat_assum `tnenc.t_imm = tnprep.t_imm` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp_tac bool_ss [bodyPtrDefsTheory.stor_taint_ok_at_def])
  >- (qpat_assum `!i. i < lo ==> (i IN tnenc.t_mem <=> i IN tnprep.t_mem)` mp_tac >>
      qpat_assum `mem_bytes_at 0 lo encoded.vs_memory =
       mem_bytes_at 0 lo prepared.vs_memory` mp_tac >>
      qpat_assum `!i. i < lo /\ i IN tnprep.t_mem ==> _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
  >- (qpat_assum `!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at s3 x`
       mp_tac >>
      qpat_assum `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==>
       FLOOKUP Gprep x = NONE /\ _` mp_tac >>
      qpat_assum `!x. not_fresh_at s3 x ==> FLOOKUP Genc x = _ /\ _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
  >> first_assum ACCEPT_TAC) >>
suspend "encoded_ghost_frame"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[encoded_robust_locals]:
`!x. not_fresh_at sm x ==> not_fresh_at s3 x` by
 (qx_gen_tac `old_x` >> strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >>
  qpat_assum `sm.cs_next_var <= topic_sa.cs_next_var` mp_tac >>
  qpat_assum `ci_mono topic_sa s1` mp_tac >>
  qpat_assum `ci_mono s1 s2` mp_tac >>
  qpat_assum `ci_mono s2 s3` mp_tac >>
  qpat_assum `not_fresh_at sm old_x` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [ci_mono_def] >> rpt strip_tac >> decide_tac) >>
`(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
   not_fresh_at s3 x) /\
 (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
   not_fresh_at s3 x)` by
 (qpat_assum `!x. not_fresh_at sm x ==> not_fresh_at s3 x` mp_tac >>
  qpat_assum `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
   not_fresh_at sm x` mp_tac >>
  qpat_assum `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
   not_fresh_at sm x` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
`encoded.vs_accounts = prepared.vs_accounts /\
 encoded.vs_transient = prepared.vs_transient /\
 encoded.vs_immutables = prepared.vs_immutables` by
 (qpat_assum `abi_encoder_registered_effect _ _ prepared encoded`
   (mp_tac o REWRITE_RULE
    [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def]) >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
`!D. ghost_inv_at D lo d cenv cx mid Gprep tnprep prepared ==>
 ghost_inv_at D lo d cenv cx mid Genc tnenc encoded` by
 (qx_gen_tac `enc_dead` >> strip_tac >>
  qpat_x_assum `ghost_inv_at enc_dead lo d cenv cx mid Gprep tnprep prepared`
   (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
  rewrite_tac [bodyPtrDefsTheory.ghost_inv_at_def] >> rpt conj_tac
  >- (map_every qx_gen_tac [`local_name`,`local_entry`,`local_p`,`local_sz`] >>
      strip_tac >>
      qpat_assum `!name entry p sz. _ ==>
       ptr_covers Gprep tnprep p prepared sz /\ _`
       (qspecl_then [`local_name`,`local_entry`,`local_p`,`local_sz`] mp_tac) >>
      (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
      conj_tac
      >- (qpat_assum `!old_p old_n. not_fresh_at s3 old_p /\ _ ==> _`
           (qspecl_then [`local_p`,`local_sz`] match_mp_tac) >>
          conj_tac >- (qpat_assum `!name p sz. FLOOKUP cenv.ce_vars name = _ ==> _`
           (qspecl_then [`local_name`,`local_p`,`local_sz`] match_mp_tac) >>
           first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
      map_every qx_gen_tac [`local_word`,`local_mem`] >> strip_tac >>
      `lookup_var local_p prepared = SOME local_word` by
       (qpat_assum `!name entry local_p sz. _ ==>
          lookup_var local_p encoded = lookup_var local_p prepared`
         (qspecl_then [`local_name`,`local_entry`,`local_p`,`local_sz`] mp_tac) >>
        (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
        qpat_assum `lookup_var local_p encoded = SOME local_word` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
      qpat_assum `!local_name local_entry local_p local_sz local_word. _ ==>
       !mem. mem_agree_outside tnenc.t_mem encoded.vs_memory mem ==> _`
       (qspecl_then [`local_name`,`local_entry`,`local_p`,`local_sz`,
         `local_word`] mp_tac) >>
      (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       qx_gen_tac `local_old_mem` >> strip_tac >>
       qpat_assum `!w mem. lookup_var local_p prepared = SOME w /\ _ ==> _`
        (qspecl_then [`local_word`,`local_old_mem`] match_mp_tac) >>
       conj_tac >> first_assum ACCEPT_TAC])) >>
      disch_then (qspec_then `local_mem` match_mp_tac) >> first_assum ACCEPT_TAC)
  >- (Cases_on `d` >- simp_tac bool_ss [bodyPtrDefsTheory.return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb) cenv Genc tnenc encoded` >>
      PairCases_on `rb` >>
      qpat_assum `return_buf_ptr (SOME _) cenv Gprep tnprep prepared` mp_tac >>
      qpat_assum `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at s3 x` mp_tac >>
      qpat_assum `!old_p old_n. not_fresh_at s3 old_p /\ _ ==> _` mp_tac >>
      qpat_assum `!x w. not_fresh_at s3 x /\ lookup_var x prepared = SOME w ==> _`
       mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
      rewrite_tac [bodyPtrDefsTheory.return_buf_ptr_def] >> metis_tac[])
  >- (qpat_assum `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at s3 x` mp_tac >>
      qpat_assum `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
       op_taint tnprep (Var x) = {}` mp_tac >>
      qpat_assum `!x. not_fresh_at s3 x ==> FLOOKUP Genc x = _ /\ _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
  >- (qpat_assum `stor_taint_ok_at enc_dead tnprep prepared` mp_tac >>
      qpat_assum `encoded.vs_accounts = prepared.vs_accounts` mp_tac >>
      qpat_assum `encoded.vs_transient = prepared.vs_transient` mp_tac >>
      qpat_assum `encoded.vs_immutables = prepared.vs_immutables` mp_tac >>
      qpat_assum `encoded.vs_call_ctx = prepared.vs_call_ctx` mp_tac >>
      qpat_assum `tnenc.t_stor = tnprep.t_stor` mp_tac >>
      qpat_assum `tnenc.t_trans = tnprep.t_trans` mp_tac >>
      qpat_assum `tnenc.t_imm = tnprep.t_imm` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp_tac bool_ss [bodyPtrDefsTheory.stor_taint_ok_at_def])
  >- (qpat_assum `!i. i < lo ==> (i IN tnenc.t_mem <=> i IN tnprep.t_mem)` mp_tac >>
      qpat_assum `mem_bytes_at 0 lo encoded.vs_memory =
       mem_bytes_at 0 lo prepared.vs_memory` mp_tac >>
      qpat_assum `!i. i < lo /\ i IN tnprep.t_mem ==> _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
  >- (qpat_assum `!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at s3 x`
       mp_tac >>
      qpat_assum `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==>
       FLOOKUP Gprep x = NONE /\ _` mp_tac >>
      qpat_assum `!x. not_fresh_at s3 x ==> FLOOKUP Genc x = _ /\ _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
  >> first_assum ACCEPT_TAC) >>
suspend "encoded_ghost_frame"
QED
*)

Resume compile_log_frag_full[encoded_ghost_frame]:
`(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
   not_fresh_at s1 x) /\
 (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
   not_fresh_at s1 x)` by
 (rpt conj_tac >> map_every qx_gen_tac [`ret_x`,`ret_sz`] >> strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >>
  `not_fresh_at sm ret_x` by
   (FIRST [qpat_assum `!x sz. cenv.ce_return_buf = _ ==> not_fresh_at sm x`
      (qspecl_then [`ret_x`,`ret_sz`] match_mp_tac) >> first_assum ACCEPT_TAC,
     qpat_assum `!x sz. cenv.ce_return_pc = _ ==> not_fresh_at sm x`
      (qspecl_then [`ret_x`,`ret_sz`] match_mp_tac) >> first_assum ACCEPT_TAC]) >>
  qpat_assum `sm.cs_next_var <= topic_sa.cs_next_var` mp_tac >>
  qpat_assum `ci_mono topic_sa s1` mp_tac >>
  qpat_assum `not_fresh_at sm ret_x` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [ci_mono_def] >>
  rpt strip_tac >> FIRST [first_assum ACCEPT_TAC,decide_tac]) >>
`lo <= w2n bw` by
 (qpat_assum `allocas_from lo ta`
   (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
  disch_then (qspecl_then
   [`topic_sa.cs_next_id`,`w2n (bw:bytes32)`,`cap`] match_mp_tac) >>
  first_assum ACCEPT_TAC) >>
`!j. j < w2n bw \/ w2n bw+cap <= j ==>
 (j IN tnpacked.t_mem <=> j IN tna.t_mem)` by
 (qx_gen_tac `pack_i` >> disch_tac >>
  qpat_assum `!i. ~(w2n bw + 0 <= i /\
   i < w2n bw + 0 + type_memory_size_list dtvs) ==>
   (i IN tnpacked.t_mem <=> i IN tna.t_mem)`
   (qspec_then `pack_i` match_mp_tac) >>
  qpat_assum `type_memory_size_list dtvs <= cap` mp_tac >>
  qpat_assum `pack_i < w2n bw \/ w2n bw+cap <= pack_i` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
qpat_assum `typed_copy_state_frame s1 (w2n bw) cap ta packed`
 (strip_assume_tac o REWRITE_RULE
  [typedMemoryCopyTheory.typed_copy_state_frame_def,
   typedMemoryCopyTheory.typed_copy_frame_def]) >>
`packed.vs_accounts = ta.vs_accounts /\
 packed.vs_transient = ta.vs_transient /\
 packed.vs_call_ctx = ta.vs_call_ctx /\
 packed.vs_immutables = ta.vs_immutables` by
 (qpat_assum `packed with <|vs_vars := _; vs_memory := _;
   vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = ta`
   (mp_tac o SIMP_RULE (srw_ss())
    [venomStateTheory.venom_state_component_equality]) >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [] >> metis_tac[]) >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 ghost_inv_at (DF H) lo d cenv cx mid Gpacked tnpacked packed` by
 (qx_gen_tac `pack_H` >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
   stmt_state_rel H ctx func cenv cx mid ta /\ _`
   (qspec_then `pack_H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `local_ptrs_rel func cenv mid.scopes ta` by
   (qpat_assum `stmt_state_rel pack_H ctx func cenv cx mid ta` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    simp_tac bool_ss [stmt_state_rel_def,state_rel_def] >> metis_tac[]) >>
  `stor_taint_ok_at (DF pack_H) tnpacked packed` by
   (qpat_assum `ghost_inv_at (DF pack_H) lo d cenv cx mid Ga tna ta`
     (mp_tac o el 4 o CONJUNCTS o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
    qpat_assum `packed.vs_accounts = ta.vs_accounts` mp_tac >>
    qpat_assum `packed.vs_transient = ta.vs_transient` mp_tac >>
    qpat_assum `packed.vs_call_ctx = ta.vs_call_ctx` mp_tac >>
    qpat_assum `packed.vs_immutables = ta.vs_immutables` mp_tac >>
    qpat_assum `tnpacked.t_stor = tna.t_stor` mp_tac >>
    qpat_assum `tnpacked.t_trans = tna.t_trans` mp_tac >>
    qpat_assum `tnpacked.t_imm = tna.t_imm` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    simp_tac bool_ss [bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
  match_mp_tac (Q.INST
   [`D` |-> `DF pack_H`,`s` |-> `ta`,`z` |-> `packed`,`sa` |-> `s1`,
    `G` |-> `Ga`,`tn` |-> `tna`,`H` |-> `Gpacked`,`tf` |-> `tnpacked`,
    `start` |-> `w2n (bw:bytes32)`,`nb` |-> `cap`,`func` |-> `func`]
   bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_inv_at) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   qx_gen_tac `old_x` >> strip_tac >>
   qpat_assum `!p. not_fresh_at s1 p ==>
    FLOOKUP Gpacked p = FLOOKUP Ga p /\ _`
    (qspec_then `old_x` mp_tac) >>
   (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
   rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    qpat_assum `!x. not_fresh_at s1 x ==> lookup_var x packed = lookup_var x ta`
     (qspec_then `old_x` match_mp_tac) >> first_assum ACCEPT_TAC]]) >>
suspend "packed_ghost"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[encoded_ghost_frame]:
`(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
   not_fresh_at s1 x) /\
 (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
   not_fresh_at s1 x)` by
 (rpt conj_tac >> map_every qx_gen_tac [`ret_x`,`ret_sz`] >> strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >>
  `not_fresh_at sm ret_x` by
   (FIRST [qpat_assum `!x sz. cenv.ce_return_buf = _ ==> not_fresh_at sm x`
      (qspecl_then [`ret_x`,`ret_sz`] match_mp_tac) >> first_assum ACCEPT_TAC,
     qpat_assum `!x sz. cenv.ce_return_pc = _ ==> not_fresh_at sm x`
      (qspecl_then [`ret_x`,`ret_sz`] match_mp_tac) >> first_assum ACCEPT_TAC]) >>
  qpat_assum `sm.cs_next_var <= topic_sa.cs_next_var` mp_tac >>
  qpat_assum `ci_mono topic_sa s1` mp_tac >>
  qpat_assum `not_fresh_at sm ret_x` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [ci_mono_def] >>
  rpt strip_tac >> FIRST [first_assum ACCEPT_TAC,decide_tac]) >>
`lo <= w2n bw` by
 (qpat_assum `allocas_from lo ta`
   (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
  disch_then (qspecl_then
   [`topic_sa.cs_next_id`,`w2n (bw:bytes32)`,`cap`] match_mp_tac) >>
  first_assum ACCEPT_TAC) >>
`!j. j < w2n bw \/ w2n bw+cap <= j ==>
 (j IN tnpacked.t_mem <=> j IN tna.t_mem)` by
 (qx_gen_tac `pack_i` >> disch_tac >>
  qpat_assum `!i. ~(w2n bw + 0 <= i /\
   i < w2n bw + 0 + type_memory_size_list dtvs) ==>
   (i IN tnpacked.t_mem <=> i IN tna.t_mem)`
   (qspec_then `pack_i` match_mp_tac) >>
  qpat_assum `type_memory_size_list dtvs <= cap` mp_tac >>
  qpat_assum `pack_i < w2n bw \/ w2n bw+cap <= pack_i` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
qpat_assum `typed_copy_state_frame s1 (w2n bw) cap ta packed`
 (strip_assume_tac o REWRITE_RULE
  [typedMemoryCopyTheory.typed_copy_state_frame_def,
   typedMemoryCopyTheory.typed_copy_frame_def]) >>
`packed.vs_accounts = ta.vs_accounts /\
 packed.vs_transient = ta.vs_transient /\
 packed.vs_call_ctx = ta.vs_call_ctx /\
 packed.vs_immutables = ta.vs_immutables` by
 (qpat_assum `packed with <|vs_vars := _; vs_memory := _;
   vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = ta`
   (mp_tac o SIMP_RULE (srw_ss())
    [venomStateTheory.venom_state_component_equality]) >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [] >> metis_tac[]) >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 ghost_inv_at (DF H) lo d cenv cx mid Gpacked tnpacked packed` by
 (qx_gen_tac `pack_H` >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
   stmt_state_rel H ctx func cenv cx mid ta /\ _`
   (qspec_then `pack_H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `local_ptrs_rel func cenv mid.scopes ta` by
   (qpat_assum `stmt_state_rel pack_H ctx func cenv cx mid ta` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    simp_tac bool_ss [stmt_state_rel_def,state_rel_def] >> metis_tac[]) >>
  `stor_taint_ok_at (DF pack_H) tnpacked packed` by
   (qpat_assum `ghost_inv_at (DF pack_H) lo d cenv cx mid Ga tna ta`
     (mp_tac o el 4 o CONJUNCTS o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
    qpat_assum `packed.vs_accounts = ta.vs_accounts` mp_tac >>
    qpat_assum `packed.vs_transient = ta.vs_transient` mp_tac >>
    qpat_assum `packed.vs_call_ctx = ta.vs_call_ctx` mp_tac >>
    qpat_assum `packed.vs_immutables = ta.vs_immutables` mp_tac >>
    qpat_assum `tnpacked.t_stor = tna.t_stor` mp_tac >>
    qpat_assum `tnpacked.t_trans = tna.t_trans` mp_tac >>
    qpat_assum `tnpacked.t_imm = tna.t_imm` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    simp_tac bool_ss [bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
  match_mp_tac (Q.INST
   [`D` |-> `DF pack_H`,`s` |-> `ta`,`z` |-> `packed`,`sa` |-> `s1`,
    `G` |-> `Ga`,`tn` |-> `tna`,`H` |-> `Gpacked`,`tf` |-> `tnpacked`,
    `start` |-> `w2n (bw:bytes32)`,`nb` |-> `cap`,`func` |-> `func`]
   bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_inv_at) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
   qx_gen_tac `old_x` >> strip_tac >>
   qpat_assum `!p. not_fresh_at s1 p ==>
    FLOOKUP Gpacked p = FLOOKUP Ga p /\ _`
    (qspec_then `old_x` mp_tac) >>
   (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
   rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    qpat_assum `!x. not_fresh_at s1 x ==> lookup_var x packed = lookup_var x ta`
     (qspec_then `old_x` match_mp_tac) >> first_assum ACCEPT_TAC]]) >>
suspend "packed_ghost"
QED
*)

Resume compile_log_frag_full[packed_ghost]:
`(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
   not_fresh_at s2 x) /\
 (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
   not_fresh_at s2 x)` by
 (rpt conj_tac >> map_every qx_gen_tac [`ret_x`,`ret_sz`] >> strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `s1` >>
  `not_fresh_at s1 ret_x` by
   (FIRST [qpat_assum `!x sz. cenv.ce_return_buf = _ ==> not_fresh_at s1 x`
      (qspecl_then [`ret_x`,`ret_sz`] match_mp_tac) >> first_assum ACCEPT_TAC,
     qpat_assum `!x sz. cenv.ce_return_pc = _ ==> not_fresh_at s1 x`
      (qspecl_then [`ret_x`,`ret_sz`] match_mp_tac) >> first_assum ACCEPT_TAC]) >>
  qpat_assum `ci_mono s1 s2` mp_tac >>
  qpat_assum `not_fresh_at s1 ret_x` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [ci_mono_def] >>
  rpt strip_tac >> first_assum ACCEPT_TAC) >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 ghost_inv_at (DF H) lo d cenv cx mid Gprep tnprep prepared` by
 (qx_gen_tac `prep_H` >> strip_tac >>
  `ghost_inv_at (DF prep_H) lo d cenv cx mid Gpacked tnpacked packed` by
   (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx mid Gpacked tnpacked packed`
    (qspec_then `prep_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST
   [`D` |-> `DF (prep_H : (bool # bytes32 # type_value) list # num list)`,
    `H` |-> `storage_trace_horizon mid.storage_trace`,
    `es` |-> `mid`,`s` |-> `packed`,`t` |-> `prepared`,`sa` |-> `s2`,
    `G` |-> `Gpacked`,`G'` |-> `Gprep`,`tn` |-> `tnpacked`,`tn'` |-> `tnprep`,
    `e` |-> `w2n (out_bw:bytes32)+outcap`]
   (INST_TYPE [``:'a`` |-> ``:256``]
    bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC) >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 ghost_inv_at (DF H) lo d cenv cx mid Genc tnenc encoded` by
 (qx_gen_tac `enc_H` >> strip_tac >>
  qpat_assum `!D. ghost_inv_at D lo d cenv cx mid Gprep tnprep prepared ==>
   ghost_inv_at D lo d cenv cx mid Genc tnenc encoded`
   (qspec_then `DF enc_H` match_mp_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
   ghost_inv_at (DF H) lo d cenv cx mid Gprep tnprep prepared`
   (qspec_then `enc_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
suspend "encoded_all_h_ghost"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[packed_ghost]:
`(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
   not_fresh_at s2 x) /\
 (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
   not_fresh_at s2 x)` by
 (rpt conj_tac >> map_every qx_gen_tac [`ret_x`,`ret_sz`] >> strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `s1` >>
  `not_fresh_at s1 ret_x` by
   (FIRST [qpat_assum `!x sz. cenv.ce_return_buf = _ ==> not_fresh_at s1 x`
      (qspecl_then [`ret_x`,`ret_sz`] match_mp_tac) >> first_assum ACCEPT_TAC,
     qpat_assum `!x sz. cenv.ce_return_pc = _ ==> not_fresh_at s1 x`
      (qspecl_then [`ret_x`,`ret_sz`] match_mp_tac) >> first_assum ACCEPT_TAC]) >>
  qpat_assum `ci_mono s1 s2` mp_tac >>
  qpat_assum `not_fresh_at s1 ret_x` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [ci_mono_def] >>
  rpt strip_tac >> first_assum ACCEPT_TAC) >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 ghost_inv_at (DF H) lo d cenv cx mid Gprep tnprep prepared` by
 (qx_gen_tac `prep_H` >> strip_tac >>
  `ghost_inv_at (DF prep_H) lo d cenv cx mid Gpacked tnpacked packed` by
   (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx mid Gpacked tnpacked packed`
    (qspec_then `prep_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST
   [`D` |-> `DF (prep_H : (bool # bytes32 # type_value) list # num list)`,
    `H` |-> `storage_trace_horizon mid.storage_trace`,
    `es` |-> `mid`,`s` |-> `packed`,`t` |-> `prepared`,`sa` |-> `s2`,
    `G` |-> `Gpacked`,`G'` |-> `Gprep`,`tn` |-> `tnpacked`,`tn'` |-> `tnprep`,
    `e` |-> `w2n (out_bw:bytes32)+outcap`]
   (INST_TYPE [``:'a`` |-> ``:256``]
    bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC) >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 ghost_inv_at (DF H) lo d cenv cx mid Genc tnenc encoded` by
 (qx_gen_tac `enc_H` >> strip_tac >>
  qpat_assum `!D. ghost_inv_at D lo d cenv cx mid Gprep tnprep prepared ==>
   ghost_inv_at D lo d cenv cx mid Genc tnenc encoded`
   (qspec_then `DF enc_H` match_mp_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
   ghost_inv_at (DF H) lo d cenv cx mid Gprep tnprep prepared`
   (qspec_then `enc_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
suspend "encoded_all_h_ghost"
QED
*)

Resume compile_log_frag_full[encoded_all_h_ghost]:
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 ghost_inv_at (DF H) lo d cenv cx mid Genc tnenc fin` by
 (qx_gen_tac `fin_H` >> strip_tac >>
  simp_tac bool_ss [Abbr `fin`,bodyFullLogSuffixTheory.ghost_inv_at_logs_idx] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
   ghost_inv_at (DF H) lo d cenv cx mid Genc tnenc encoded`
   (qspec_then `fin_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 stmt_state_rel H ctx func cenv cx
  (mid with logs := mid.logs ++ [log_ev]) fin` by
 (qx_gen_tac `fin_H` >> strip_tac >>
  `stmt_state_rel fin_H ctx func cenv cx
    (mid with logs := mid.logs ++ [log_ev])
    (encoded with vs_logs := encoded.vs_logs ++ [log_ev])` by
   (match_mp_tac stmtSimLogEmitTheory.log_append_stmt_state_rel >>
    qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid encoded`
     (qspec_then `fin_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  qpat_assum `stmt_state_rel fin_H ctx func cenv cx _
   (encoded with vs_logs := _)` mp_tac >>
  simp_tac (srw_ss()) [Abbr `fin`,exprLoweringPropsTheory.stmt_state_rel_inst_idx]) >>
`!D. gas_origin_ptr_path
 (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
 (t,G1,tn1) [] (OK fin,Genc,tnenc)` by
 (qx_gen_tac `path_D` >>
  qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (t,G1,tn1) [] (OK tp,Gp,tnp)` (qspec_then `path_D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (tp,Gp,tnp) [] (OK ta,Ga,tna)` (qspec_then `path_D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (ta,Ga,tna) [] (OK packed,Gpacked,tnpacked)` (qspec_then `path_D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (packed,Gpacked,tnpacked) [] (OK prepared,Gprep,tnprep)` (qspec_then `path_D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (prepared,Gprep,tnprep) [] (OK encoded,Genc,tnenc)` (qspec_then `path_D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (encoded,Genc,tnenc) [] (OK fin,Genc,tnenc)` (qspec_then `path_D` mp_tac) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,APPEND_NIL]) >>
suspend "logged_joint_frame"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[encoded_all_h_ghost]:
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 ghost_inv_at (DF H) lo d cenv cx mid Genc tnenc fin` by
 (qx_gen_tac `fin_H` >> strip_tac >>
  simp_tac bool_ss [Abbr `fin`,bodyFullLogSuffixTheory.ghost_inv_at_logs_idx] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
   ghost_inv_at (DF H) lo d cenv cx mid Genc tnenc encoded`
   (qspec_then `fin_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 stmt_state_rel H ctx func cenv cx
  (mid with logs := mid.logs ++ [log_ev]) fin` by
 (qx_gen_tac `fin_H` >> strip_tac >>
  `stmt_state_rel fin_H ctx func cenv cx
    (mid with logs := mid.logs ++ [log_ev])
    (encoded with vs_logs := encoded.vs_logs ++ [log_ev])` by
   (match_mp_tac stmtSimLogEmitTheory.log_append_stmt_state_rel >>
    qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid encoded`
     (qspec_then `fin_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
  qpat_assum `stmt_state_rel fin_H ctx func cenv cx _
   (encoded with vs_logs := _)` mp_tac >>
  simp_tac (srw_ss()) [Abbr `fin`,exprLoweringPropsTheory.stmt_state_rel_inst_idx]) >>
`!D. gas_origin_ptr_path
 (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
 (t,G1,tn1) [] (OK fin,Genc,tnenc)` by
 (qx_gen_tac `path_D` >>
  qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (t,G1,tn1) [] (OK tp,Gp,tnp)` (qspec_then `path_D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (tp,Gp,tnp) [] (OK ta,Ga,tna)` (qspec_then `path_D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (ta,Ga,tna) [] (OK packed,Gpacked,tnpacked)` (qspec_then `path_D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (packed,Gpacked,tnpacked) [] (OK prepared,Gprep,tnprep)` (qspec_then `path_D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (prepared,Gprep,tnprep) [] (OK encoded,Genc,tnenc)` (qspec_then `path_D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (encoded,Genc,tnenc) [] (OK fin,Genc,tnenc)` (qspec_then `path_D` mp_tac) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,APPEND_NIL]) >>
suspend "logged_joint_frame"
QED
*)

Resume compile_log_frag_full[logged_joint_frame]:
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 ghost_inv_at (DF H) lo d cenv cx
  (mid with logs := mid.logs ++ [log_ev]) Genc tnenc fin` by
 (qx_gen_tac `fin_H` >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
   ghost_inv_at (DF H) lo d cenv cx mid Genc tnenc fin`
   (qspec_then `fin_H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [bodyPtrDefsTheory.ghost_inv_at_def] >>
  strip_tac >> asm_rewrite_tac []) >>
`gas_path_mem ctx func encoded 0 (OK fin)` by
 (qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (encoded,Genc,tnenc) [] (OK fin,Genc,tnenc)`
   (qspec_then `DF (storage_trace_horizon mid.storage_trace)` mp_tac) >>
  disch_then (mp_tac o CONJUNCT1 o MATCH_MP
   fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
  disch_then (mp_tac o MATCH_MP fragGasOriginTheory.gas_origin_path_erase) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [fragGasModeTheory.gas_marked_path_def]) >>
`!u. gas_path_mem ctx func encoded 0 (OK u) ==> alloca_inv u` by
 (rpt strip_tac >>
  drule_all bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv >> simp[]) >>
`alloca_history func fin` by
 (drule_all fragGasPathFrameMemTheory.gas_path_mem_zero_history >> simp[]) >>
`sb.cs_current_bb = s4.cs_current_bb` by
 (qpat_assum `emit_inst LOG _ [] s4 = ((),sb)`
   (mp_tac o MATCH_MP emitHelperPropsTheory.emit_inst_extends) >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss []) >>
`~block_is_terminated sb` by
 (qpat_assum `emit_inst LOG _ [] s4 = ((),sb)`
   (ACCEPT_TAC o MATCH_MP logComposeFactsTheory.log_emit_not_terminated)) >>
`stmt_lands lctx sb (INL ()) fin /\ ~fin.vs_halted` by
 (qpat_assum `encoded.vs_current_bb = s4.cs_current_bb` mp_tac >>
  qpat_assum `sb.cs_current_bb = s4.cs_current_bb` mp_tac >>
  qpat_assum `~encoded.vs_halted` mp_tac >>
  simp_tac (srw_ss()) [Abbr `fin`,stmt_lands_def]) >>
suspend "logged_final_resources"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[logged_joint_frame]:
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 ghost_inv_at (DF H) lo d cenv cx
  (mid with logs := mid.logs ++ [log_ev]) Genc tnenc fin` by
 (qx_gen_tac `fin_H` >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
   ghost_inv_at (DF H) lo d cenv cx mid Genc tnenc fin`
   (qspec_then `fin_H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [bodyPtrDefsTheory.ghost_inv_at_def] >>
  strip_tac >> asm_rewrite_tac []) >>
`gas_path_mem ctx func encoded 0 (OK fin)` by
 (qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (encoded,Genc,tnenc) [] (OK fin,Genc,tnenc)`
   (qspec_then `DF (storage_trace_horizon mid.storage_trace)` mp_tac) >>
  disch_then (mp_tac o CONJUNCT1 o MATCH_MP
   fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
  disch_then (mp_tac o MATCH_MP fragGasOriginTheory.gas_origin_path_erase) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [fragGasModeTheory.gas_marked_path_def]) >>
`!u. gas_path_mem ctx func encoded 0 (OK u) ==> alloca_inv u` by
 (rpt strip_tac >>
  drule_all bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv >> simp[]) >>
`alloca_history func fin` by
 (drule_all fragGasPathFrameMemTheory.gas_path_mem_zero_history >> simp[]) >>
`sb.cs_current_bb = s4.cs_current_bb` by
 (qpat_assum `emit_inst LOG _ [] s4 = ((),sb)`
   (mp_tac o MATCH_MP emitHelperPropsTheory.emit_inst_extends) >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss []) >>
`~block_is_terminated sb` by
 (qpat_assum `emit_inst LOG _ [] s4 = ((),sb)`
   (ACCEPT_TAC o MATCH_MP logComposeFactsTheory.log_emit_not_terminated)) >>
`stmt_lands lctx sb (INL ()) fin /\ ~fin.vs_halted` by
 (qpat_assum `encoded.vs_current_bb = s4.cs_current_bb` mp_tac >>
  qpat_assum `sb.cs_current_bb = s4.cs_current_bb` mp_tac >>
  qpat_assum `~encoded.vs_halted` mp_tac >>
  simp_tac (srw_ss()) [Abbr `fin`,stmt_lands_def]) >>
suspend "logged_final_resources"
QED
*)

Resume compile_log_frag_full[logged_final_resources]:
`ci_mono sm topic_sa` by
 (qpat_assum `compile_log_topic_ops _ sm = (topic_ops,topic_sa)`
   (fn topic_code => ACCEPT_TAC (SIMP_RULE bool_ss [topic_code,pairTheory.SND]
     (ISPECL [rand (rator (lhs (concl topic_code))),``sm:compile_state``]
       eventLoweringStructureTheory.compile_log_topic_ops_ci_mono)))) >>
`!x. not_fresh_at sm x ==> not_fresh_at topic_sa x /\
 not_fresh_at s1 x /\ not_fresh_at s2 x /\ not_fresh_at s3 x` by
 (qx_gen_tac `frame_x` >> strip_tac >>
  qpat_assum `ci_mono sm topic_sa` mp_tac >>
  qpat_assum `ci_mono topic_sa s1` mp_tac >>
  qpat_assum `ci_mono s1 s2` mp_tac >>
  qpat_assum `ci_mono s2 s3` mp_tac >>
  qpat_assum `not_fresh_at sm frame_x` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [ci_mono_def] >> rpt strip_tac >>
  rpt conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
  qexists_tac `sm` >> conj_tac >> FIRST [first_assum ACCEPT_TAC,decide_tac]) >>
`!x. not_fresh_at sm x ==>
 FLOOKUP Genc x = FLOOKUP G1 x /\
 op_taint tnenc (Var x) = op_taint tn1 (Var x)` by
 (qx_gen_tac `frame_x` >> strip_tac >>
  qpat_assum `!x. not_fresh_at sm x ==> not_fresh_at topic_sa x /\ _`
   (qspec_then `frame_x` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!p. not_fresh_at sm p ==> lookup_var p ta = _ /\ _`
   (qspec_then `frame_x` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!p. not_fresh_at s1 p ==> FLOOKUP Gpacked p = _ /\ _`
   (qspec_then `frame_x` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!x. not_fresh_at s2 x ==> lookup_var x prepared = _ /\ _`
   (qspec_then `frame_x` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!x. not_fresh_at s3 x ==> FLOOKUP Genc x = _ /\ _`
   (qspec_then `frame_x` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  asm_rewrite_tac []) >>
`!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==>
 lookup_var x fin = SOME w` by
 (qx_genl_tac [`frame_x`,`frame_w`] >> strip_tac >>
  `not_fresh_at topic_sa frame_x` by
   (qpat_assum `!x. not_fresh_at sm x ==> not_fresh_at topic_sa x /\ _`
     (qspec_then `frame_x` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> first_assum ACCEPT_TAC) >>
  `lookup_var frame_x tp = SOME frame_w` by
   (qpat_assum `!p. not_fresh_at sm p ==> lookup_var p tp = _ /\ _`
     (qspec_then `frame_x` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> asm_rewrite_tac []) >>
  `lookup_var frame_x encoded = SOME frame_w` by
   (qpat_assum `!x w. not_fresh_at topic_sa x /\ lookup_var x tp = SOME w ==> _`
     (qspecl_then [`frame_x`,`frame_w`] mp_tac) >>
    (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
    strip_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `lookup_var frame_x encoded = SOME frame_w` mp_tac >>
  simp_tac (srw_ss()) [Abbr `fin`,venomStateTheory.lookup_var_def]) >>
`t.vs_alloca_next <= fin.vs_alloca_next` by
 (qpat_assum `t.vs_alloca_next <= ta.vs_alloca_next` mp_tac >>
  qpat_assum `packed.vs_alloca_next = ta.vs_alloca_next` mp_tac >>
  qpat_assum `packed.vs_alloca_next <= prepared.vs_alloca_next` mp_tac >>
  qpat_assum `prepared.vs_alloca_next <= encoded.vs_alloca_next` mp_tac >>
  simp_tac (srw_ss()) [Abbr `fin`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
`!aid row. FLOOKUP t.vs_allocas aid = SOME row ==>
 FLOOKUP fin.vs_allocas aid = SOME row` by
 (qpat_assum `!aid row. FLOOKUP t.vs_allocas aid = SOME row ==>
   FLOOKUP ta.vs_allocas aid = SOME row` mp_tac >>
  qpat_assum `packed.vs_allocas = ta.vs_allocas` mp_tac >>
  qpat_assum `!aid e. FLOOKUP packed.vs_allocas aid = SOME e ==>
   FLOOKUP prepared.vs_allocas aid = SOME e` mp_tac >>
  qpat_assum `!aid row. FLOOKUP prepared.vs_allocas aid = SOME row ==>
   FLOOKUP encoded.vs_allocas aid = SOME row` mp_tac >>
  simp_tac (srw_ss()) [Abbr `fin`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac []) >>
suspend "logged_suffix_frame"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[logged_final_resources]:
`ci_mono sm topic_sa` by
 (qpat_assum `compile_log_topic_ops _ sm = (topic_ops,topic_sa)`
   (fn topic_code => ACCEPT_TAC (SIMP_RULE bool_ss [topic_code,pairTheory.SND]
     (ISPECL [rand (rator (lhs (concl topic_code))),``sm:compile_state``]
       eventLoweringStructureTheory.compile_log_topic_ops_ci_mono)))) >>
`!x. not_fresh_at sm x ==> not_fresh_at topic_sa x /\
 not_fresh_at s1 x /\ not_fresh_at s2 x /\ not_fresh_at s3 x` by
 (qx_gen_tac `frame_x` >> strip_tac >>
  qpat_assum `ci_mono sm topic_sa` mp_tac >>
  qpat_assum `ci_mono topic_sa s1` mp_tac >>
  qpat_assum `ci_mono s1 s2` mp_tac >>
  qpat_assum `ci_mono s2 s3` mp_tac >>
  qpat_assum `not_fresh_at sm frame_x` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [ci_mono_def] >> rpt strip_tac >>
  rpt conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
  qexists_tac `sm` >> conj_tac >> FIRST [first_assum ACCEPT_TAC,decide_tac]) >>
`!x. not_fresh_at sm x ==>
 FLOOKUP Genc x = FLOOKUP G1 x /\
 op_taint tnenc (Var x) = op_taint tn1 (Var x)` by
 (qx_gen_tac `frame_x` >> strip_tac >>
  qpat_assum `!x. not_fresh_at sm x ==> not_fresh_at topic_sa x /\ _`
   (qspec_then `frame_x` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!p. not_fresh_at sm p ==> lookup_var p ta = _ /\ _`
   (qspec_then `frame_x` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!p. not_fresh_at s1 p ==> FLOOKUP Gpacked p = _ /\ _`
   (qspec_then `frame_x` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!x. not_fresh_at s2 x ==> lookup_var x prepared = _ /\ _`
   (qspec_then `frame_x` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!x. not_fresh_at s3 x ==> FLOOKUP Genc x = _ /\ _`
   (qspec_then `frame_x` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  asm_rewrite_tac []) >>
`!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==>
 lookup_var x fin = SOME w` by
 (qx_genl_tac [`frame_x`,`frame_w`] >> strip_tac >>
  `not_fresh_at topic_sa frame_x` by
   (qpat_assum `!x. not_fresh_at sm x ==> not_fresh_at topic_sa x /\ _`
     (qspec_then `frame_x` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> first_assum ACCEPT_TAC) >>
  `lookup_var frame_x tp = SOME frame_w` by
   (qpat_assum `!p. not_fresh_at sm p ==> lookup_var p tp = _ /\ _`
     (qspec_then `frame_x` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> asm_rewrite_tac []) >>
  `lookup_var frame_x encoded = SOME frame_w` by
   (qpat_assum `!x w. not_fresh_at topic_sa x /\ lookup_var x tp = SOME w ==> _`
     (qspecl_then [`frame_x`,`frame_w`] mp_tac) >>
    (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
    strip_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `lookup_var frame_x encoded = SOME frame_w` mp_tac >>
  simp_tac (srw_ss()) [Abbr `fin`,venomStateTheory.lookup_var_def]) >>
`t.vs_alloca_next <= fin.vs_alloca_next` by
 (qpat_assum `t.vs_alloca_next <= ta.vs_alloca_next` mp_tac >>
  qpat_assum `packed.vs_alloca_next = ta.vs_alloca_next` mp_tac >>
  qpat_assum `packed.vs_alloca_next <= prepared.vs_alloca_next` mp_tac >>
  qpat_assum `prepared.vs_alloca_next <= encoded.vs_alloca_next` mp_tac >>
  simp_tac (srw_ss()) [Abbr `fin`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
`!aid row. FLOOKUP t.vs_allocas aid = SOME row ==>
 FLOOKUP fin.vs_allocas aid = SOME row` by
 (qpat_assum `!aid row. FLOOKUP t.vs_allocas aid = SOME row ==>
   FLOOKUP ta.vs_allocas aid = SOME row` mp_tac >>
  qpat_assum `packed.vs_allocas = ta.vs_allocas` mp_tac >>
  qpat_assum `!aid e. FLOOKUP packed.vs_allocas aid = SOME e ==>
   FLOOKUP prepared.vs_allocas aid = SOME e` mp_tac >>
  qpat_assum `!aid row. FLOOKUP prepared.vs_allocas aid = SOME row ==>
   FLOOKUP encoded.vs_allocas aid = SOME row` mp_tac >>
  simp_tac (srw_ss()) [Abbr `fin`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac []) >>
suspend "logged_suffix_frame"
QED
*)

Resume compile_log_frag_full[logged_suffix_frame]:
`!x. not_fresh_at sa x ==> not_fresh_at sm x` by
 (qx_gen_tac `caller_x` >> strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
  conj_tac >> first_assum ACCEPT_TAC) >>
`!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
 lookup_var x fin = SOME w` by
 (qpat_assum `wb_frame cenv es mid sa s0 t`
   (mp_tac o CONJUNCT1 o REWRITE_RULE [wb_frame_def]) >>
  qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sm x` mp_tac >>
  qpat_assum `!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==>
   lookup_var x fin = SOME w` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac []) >>
`!x. not_fresh_at sa x ==>
 FLOOKUP Genc x = FLOOKUP G0 x /\
 op_taint tnenc (Var x) = op_taint tn0 (Var x)` by
 (qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1`
   (mp_tac o CONJUNCT1 o REWRITE_RULE [ghost_kept_at_def]) >>
  qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sm x` mp_tac >>
  qpat_assum `!x. not_fresh_at sm x ==> FLOOKUP Genc x = FLOOKUP G1 x /\ _`
   mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac []) >>
`!aid row. FLOOKUP s0.vs_allocas aid = SOME row ==>
 FLOOKUP fin.vs_allocas aid = SOME row` by
 (qpat_assum `wb_frame cenv es mid sa s0 t`
   (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [wb_frame_def]) >>
  qpat_assum `!aid row. FLOOKUP t.vs_allocas aid = SOME row ==>
   FLOOKUP fin.vs_allocas aid = SOME row` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac []) >>
`s0.vs_alloca_next <= fin.vs_alloca_next` by
 (qpat_assum `s0.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
  qpat_assum `t.vs_alloca_next <= fin.vs_alloca_next` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
`sa.cs_next_var <= sb.cs_next_var` by
 (qpat_assum `compile_stmt cenv lctx ret_ty (Log id args) sa = ((),sb)`
   (fn stmt_code => mp_tac (SIMP_RULE bool_ss [stmt_code,pairTheory.SND,ci_mono_def]
     (Q.SPECL [`cenv`,`lctx`,`ret_ty`,`Log id args`,`sa`]
       (CONJUNCT1 stmtLoweringMonoTheory.compile_stmt_ci_mono)))) >>
  strip_tac >> first_assum ACCEPT_TAC) >>
`return_buf_frame d cenv sb fin` by
 (match_mp_tac (Q.SPECL [`d`,`cenv`,`cenv`,`sa`,`sb`,`s0`,`fin`]
   bodyMemoryDefsTheory.return_buf_frame_frame) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,REFL_TAC]) >>
suspend "logged_caller_frame"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[logged_suffix_frame]:
`!x. not_fresh_at sa x ==> not_fresh_at sm x` by
 (qx_gen_tac `caller_x` >> strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
  conj_tac >> first_assum ACCEPT_TAC) >>
`!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
 lookup_var x fin = SOME w` by
 (qpat_assum `wb_frame cenv es mid sa s0 t`
   (mp_tac o CONJUNCT1 o REWRITE_RULE [wb_frame_def]) >>
  qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sm x` mp_tac >>
  qpat_assum `!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==>
   lookup_var x fin = SOME w` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac []) >>
`!x. not_fresh_at sa x ==>
 FLOOKUP Genc x = FLOOKUP G0 x /\
 op_taint tnenc (Var x) = op_taint tn0 (Var x)` by
 (qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1`
   (mp_tac o CONJUNCT1 o REWRITE_RULE [ghost_kept_at_def]) >>
  qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sm x` mp_tac >>
  qpat_assum `!x. not_fresh_at sm x ==> FLOOKUP Genc x = FLOOKUP G1 x /\ _`
   mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac []) >>
`!aid row. FLOOKUP s0.vs_allocas aid = SOME row ==>
 FLOOKUP fin.vs_allocas aid = SOME row` by
 (qpat_assum `wb_frame cenv es mid sa s0 t`
   (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [wb_frame_def]) >>
  qpat_assum `!aid row. FLOOKUP t.vs_allocas aid = SOME row ==>
   FLOOKUP fin.vs_allocas aid = SOME row` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac []) >>
`s0.vs_alloca_next <= fin.vs_alloca_next` by
 (qpat_assum `s0.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
  qpat_assum `t.vs_alloca_next <= fin.vs_alloca_next` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
`sa.cs_next_var <= sb.cs_next_var` by
 (qpat_assum `compile_stmt cenv lctx ret_ty (Log id args) sa = ((),sb)`
   (fn stmt_code => mp_tac (SIMP_RULE bool_ss [stmt_code,pairTheory.SND,ci_mono_def]
     (Q.SPECL [`cenv`,`lctx`,`ret_ty`,`Log id args`,`sa`]
       (CONJUNCT1 stmtLoweringMonoTheory.compile_stmt_ci_mono)))) >>
  strip_tac >> first_assum ACCEPT_TAC) >>
`return_buf_frame d cenv sb fin` by
 (match_mp_tac (Q.SPECL [`d`,`cenv`,`cenv`,`sa`,`sb`,`s0`,`fin`]
   bodyMemoryDefsTheory.return_buf_frame_frame) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,REFL_TAC]) >>
suspend "logged_caller_frame"
QED
*)

Resume compile_log_frag_full[logged_caller_frame]:
qabbrev_tac `done_es = mid with logs := mid.logs ++ [log_ev]` >>
`~cx.txn.is_static` by
 (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
   state_rel H func cenv cx mid encoded`
   (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `~encoded.vs_call_ctx.cc_static` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [loweringStateRelDefsTheory.state_rel_def,
    loweringStateRelDefsTheory.call_ctx_rel_def] >> metis_tac []) >>
`!tail. bind (lift_option
 (encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs)
 "Log encode event")
 (\event. ignore_bind (check_not_static cx) (push_log event))
 (mid with gas_obs := tail) =
 (INL (),done_es with gas_obs := tail)` by
 (simp_tac bool_ss [Abbr `done_es`] >>
  qpat_assum `encode_source_event _ _ _ _ _ = SOME log_ev` mp_tac >>
  qpat_assum `~cx.txn.is_static` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
  asm_simp_tac (srw_ss()) [bind_def, ignore_bind_def, lift_option_def,
    return_def, check_not_static_eq, push_log_def]) >>
`!H. valid_horizon cx st0 H done_es.storage_trace ==>
 stmt_state_rel H ctx func cenv cx (done_es with gas_obs := []) fin` by
 (simp_tac (srw_ss()) [Abbr `done_es`,exprSimWordArgsTheory.stmt_state_rel_gas_obs] >>
  first_assum ACCEPT_TAC) >>
`!H. valid_horizon cx st0 H done_es.storage_trace ==>
 ghost_inv_at (DF H) lo d cenv cx (done_es with gas_obs := []) Genc tnenc fin` by
 (qx_gen_tac `post_H` >> simp_tac (srw_ss()) [Abbr `done_es`] >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
   ghost_inv_at (DF H) lo d cenv cx
    (mid with logs := mid.logs ++ [log_ev]) Genc tnenc fin`
   (qspec_then `post_H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [bodyPtrDefsTheory.ghost_inv_at_def] >>
  strip_tac >> asm_rewrite_tac []) >>
`!H. valid_horizon cx st0 H done_es.storage_trace ==>
 storage_well_formed_on cx (done_es with gas_obs := []) (FST H)` by
 (qx_gen_tac `post_H` >> simp_tac (srw_ss()) [Abbr `done_es`] >> strip_tac >>
  `storage_well_formed_on cx mid (FST post_H)` by
   (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid ta /\ _`
     (qspec_then `post_H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> first_assum ACCEPT_TAC) >>
  `storage_well_formed_on cx
    ((mid with logs := mid.logs ++ [log_ev]) with gas_obs := []) (FST post_H) <=>
   storage_well_formed_on cx mid (FST post_H)` by
   (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >>
    simp_tac (srw_ss()) []) >>
  pop_assum mp_tac >>
  qpat_assum `storage_well_formed_on cx mid (FST post_H)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [] >> metis_tac []) >>
irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
reverse conj_tac >- first_assum ACCEPT_TAC >>
qexistsl_tac [`Genc`,`done_es`,`INL ()`,`fin`,`tnenc`] >>
conj_tac >-
 (qpat_assum `!tail. bind _ _ (mid with gas_obs := tail) =
   (INL (),done_es with gas_obs := tail)` mp_tac >>
  qpat_assum `encode_source_event _ _ _ _ _ = SOME log_ev` mp_tac >>
  qpat_assum `encode_source_event _ _ _ _ _ = SOME <| logger := _; topics := _; data := _ |>` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac [optionTheory.SOME_11]) >>
qx_gen_tac `post_H` >> strip_tac >> BETA_TAC >>
conj_tac >-
 (qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (t,G1,tn1) [] (OK fin,Genc,tnenc)`
   (qspec_then `DF post_H` ACCEPT_TAC)) >>
suspend "logged_outcome_post"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[logged_caller_frame]:
qabbrev_tac `done_es = mid with logs := mid.logs ++ [log_ev]` >>
`!tail. bind (lift_option
 (encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs)
 "Log encode event") push_log (mid with gas_obs := tail) =
 (INL (),done_es with gas_obs := tail)` by
 (simp_tac bool_ss [Abbr `done_es`] >> first_assum ACCEPT_TAC) >>
`!H. valid_horizon cx st0 H done_es.storage_trace ==>
 stmt_state_rel H ctx func cenv cx (done_es with gas_obs := []) fin` by
 (simp_tac (srw_ss()) [Abbr `done_es`,exprSimWordArgsTheory.stmt_state_rel_gas_obs] >>
  first_assum ACCEPT_TAC) >>
`!H. valid_horizon cx st0 H done_es.storage_trace ==>
 ghost_inv_at (DF H) lo d cenv cx (done_es with gas_obs := []) Genc tnenc fin` by
 (qx_gen_tac `post_H` >> simp_tac (srw_ss()) [Abbr `done_es`] >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
   ghost_inv_at (DF H) lo d cenv cx
    (mid with logs := mid.logs ++ [log_ev]) Genc tnenc fin`
   (qspec_then `post_H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [bodyPtrDefsTheory.ghost_inv_at_def] >>
  strip_tac >> asm_rewrite_tac []) >>
`!H. valid_horizon cx st0 H done_es.storage_trace ==>
 storage_well_formed_on cx (done_es with gas_obs := []) (FST H)` by
 (qx_gen_tac `post_H` >> simp_tac (srw_ss()) [Abbr `done_es`] >> strip_tac >>
  `storage_well_formed_on cx mid (FST post_H)` by
   (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid ta /\ _`
     (qspec_then `post_H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> first_assum ACCEPT_TAC) >>
  `storage_well_formed_on cx
    ((mid with logs := mid.logs ++ [log_ev]) with gas_obs := []) (FST post_H) <=>
   storage_well_formed_on cx mid (FST post_H)` by
   (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >>
    simp_tac (srw_ss()) []) >>
  pop_assum mp_tac >>
  qpat_assum `storage_well_formed_on cx mid (FST post_H)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [] >> metis_tac []) >>
irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
reverse conj_tac >- first_assum ACCEPT_TAC >>
qexistsl_tac [`Genc`,`done_es`,`INL ()`,`fin`,`tnenc`] >>
conj_tac >- first_assum ACCEPT_TAC >>
qx_gen_tac `post_H` >> strip_tac >> BETA_TAC >>
conj_tac >-
 (qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (t,G1,tn1) [] (OK fin,Genc,tnenc)`
   (qspec_then `DF post_H` ACCEPT_TAC)) >>
suspend "logged_outcome_post"
QED
*)

Resume compile_log_frag_full[logged_outcome_post]:
`stmt_state_rel post_H ctx func cenv cx (done_es with gas_obs := []) fin` by
 (qpat_assum `!H. valid_horizon cx st0 H done_es.storage_trace ==>
   stmt_state_rel H ctx func cenv cx (done_es with gas_obs := []) fin`
   (qspec_then `post_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
`storage_well_formed_on cx (done_es with gas_obs := []) (FST post_H)` by
 (qpat_assum `!H. valid_horizon cx st0 H done_es.storage_trace ==>
   storage_well_formed_on cx (done_es with gas_obs := []) (FST H)`
   (qspec_then `post_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
`ghost_inv_at (DF post_H) lo d cenv cx
 (done_es with gas_obs := []) Genc tnenc fin` by
 (qpat_assum `!H. valid_horizon cx st0 H done_es.storage_trace ==>
   ghost_inv_at (DF H) lo d cenv cx (done_es with gas_obs := []) Genc tnenc fin`
   (qspec_then `post_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
qexists_tac `cenv` >>
simp_tac bool_ss [stmtSimPropsTheory.cenv_top_ext_refl] >>
rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[logged_outcome_post]:
`stmt_state_rel post_H ctx func cenv cx (done_es with gas_obs := []) fin` by
 (qpat_assum `!H. valid_horizon cx st0 H done_es.storage_trace ==>
   stmt_state_rel H ctx func cenv cx (done_es with gas_obs := []) fin`
   (qspec_then `post_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
`storage_well_formed_on cx (done_es with gas_obs := []) (FST post_H)` by
 (qpat_assum `!H. valid_horizon cx st0 H done_es.storage_trace ==>
   storage_well_formed_on cx (done_es with gas_obs := []) (FST H)`
   (qspec_then `post_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
`ghost_inv_at (DF post_H) lo d cenv cx
 (done_es with gas_obs := []) Genc tnenc fin` by
 (qpat_assum `!H. valid_horizon cx st0 H done_es.storage_trace ==>
   ghost_inv_at (DF H) lo d cenv cx (done_es with gas_obs := []) Genc tnenc fin`
   (qspec_then `post_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
qexists_tac `cenv` >>
simp_tac bool_ss [stmtSimPropsTheory.cenv_top_ext_refl] >>
rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)

Resume compile_log_frag_full[empty_data]:
  qabbrev_tac `flags = MAP SND fields` >>
  `SND (split_log_ops lops flags) = []` by
    (drule_all stmtSimLogTraceTheory.split_log_ops_view >>
     disch_then (qspec_then `flags` mp_tac) >>
     qpat_assum `SND (split_log_ops ops flags) = []` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [MAP_EQ_NIL] >> metis_tac[]) >>
  `emit_inst LOG
    (Lit (n2w (LENGTH (Lit (n2w h)::topic_ops))) ::
      REVERSE (Lit (n2w h)::topic_ops) ++ [Lit 0w; Lit 0w]) []
    topic_sa = ((),sb)` by
    (mp_tac (Q.INST
      [`xs` |-> `lops`, `topics` |-> `topic_ops`,
       `st` |-> `topic_sa`, `tys` |-> `MAP (SND o FST) (fields : ((string # type) # bool) list)`,
       `flags` |-> `flags`, `ty` |-> `ret_ty`]
      (SPEC_ALL stmtSimLogTraceTheory.compile_log_empty_trace)) >>
     (impl_tac >- simp[Abbr `flags`]) >>
     qpat_assum `compile_stmt cenv lctx ret_ty (Log id args) sa = ((),sb)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `cs_extends topic_sa sb` by
    (qpat_assum `emit_inst LOG _ [] topic_sa = ((),sb)`
       (ACCEPT_TAC o MATCH_MP fragExecTheory.cs_extends_emit_inst)) >>
  qabbrev_tac `topic_args = select_log_args T flags lops` >>
  qabbrev_tac `topic_vals = select_log_args T flags vs` >>
  `LIST_REL (\arg v. ?j. j < LENGTH args /\ v = EL j vs /\
       FST arg = FST (EL j ops) /\ SND arg = expr_type (EL j args))
     topic_args topic_vals` by
    (simp_tac bool_ss [Abbr `topic_args`, Abbr `topic_vals`] >>
     irule typedLogSplitCompleteTheory.select_log_args_list_rel >>
     conj_tac >- simp[Abbr `flags`, Abbr `lops`] >>
     simp[LIST_REL_EL_EQN, Abbr `lops`, EL_ZIP, EL_MAP] >>
     rpt strip_tac >> qexists_tac `n` >> simp[]) >>
  `MAP (\p. (FST p,is_bytestring_type (SND p))) topic_args =
     FST (split_log_ops lops flags)` by
    (mp_tac (Q.SPECL [`flags`, `lops`]
       eventLogSplitPropsTheory.split_log_ops_select) >>
     (impl_tac >- simp[Abbr `flags`, Abbr `lops`]) >>
     disch_then (mp_tac o Q.AP_TERM `FST`) >>
     simp[Abbr `topic_args`, pairTheory.LAMBDA_PROD]) >>
  `compile_log_topic_ops
     (MAP (\p. (FST p,is_bytestring_type (SND p))) topic_args) sm =
     (topic_ops,topic_sa)` by simp[Abbr `flags`] >>
  `MAP SND topic_args = select_log_args T flags (MAP expr_type args)` by
    simp[Abbr `topic_args`, Abbr `lops`, GSYM select_log_args_MAP,
      MAP_ZIP] >>
  `encode_indexed_event_topics (REPLICATE (LENGTH topic_args) T)
       (MAP SND topic_args) topic_vals = SOME topics` by
    (mp_tac (Q.SPECL [`flags`,`MAP expr_type args`,`vs`]
       eventLogSplitPropsTheory.encode_indexed_event_topics_select) >>
     (impl_tac >- simp[Abbr `flags`]) >>
     `LENGTH topic_args = LENGTH (select_log_args T flags (MAP expr_type args))` by
       metis_tac[LENGTH_MAP] >>
     simp[Abbr `topic_vals`, Abbr `flags`]) >>
  `LIST_REL (\arg f. supported_scalar_type (SND arg)) topic_args
      (select_log_args T flags fields)` by
    (simp_tac bool_ss [Abbr `topic_args`] >>
     irule eventLogSplitPropsTheory.select_log_args_rel >>
     conj_tac >- simp[Abbr `flags`, Abbr `lops`] >>
     simp[LIST_REL_EL_EQN, EL_ZIP, Abbr `lops`, Abbr `flags`, EL_MAP] >>
     rpt strip_tac >>
     `supported_scalar_type (SND (FST (EL n fields)))` by
       (qpat_assum `EVERY (\f. if SND f then _ else _) fields`
          (mp_tac o Q.SPEC `n` o REWRITE_RULE [EVERY_EL]) >> simp[]) >>
     `event_arg_compatible (SND (FST (EL n fields))) (expr_type (EL n args))` by
       (qpat_assum `LIST_REL event_arg_compatible _ _`
          (mp_tac o Q.SPEC `n` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
        simp[EL_MAP, combinTheory.o_THM]) >>
     metis_tac[whitelistLogWidenTheory.scalar_event_arg_compatible]) >>
  `EVERY (\arg. supported_scalar_type (SND arg)) topic_args` by
    (qpat_assum `LIST_REL (\arg f. supported_scalar_type (SND arg)) _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]) >>
  `LIST_REL (\arg v. supported_scalar_type (SND arg) /\
       ?j. j < LENGTH args /\ v = EL j vs /\
       FST arg = FST (EL j ops) /\ SND arg = expr_type (EL j args))
     topic_args topic_vals` by
    (fs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]) >>
  suspend "empty_topic_producer"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[empty_data]:
  qabbrev_tac `flags = MAP SND fields` >>
  `SND (split_log_ops lops flags) = []` by
    (drule_all stmtSimLogTraceTheory.split_log_ops_view >>
     disch_then (qspec_then `flags` mp_tac) >>
     qpat_assum `SND (split_log_ops ops flags) = []` mp_tac >>
     simp_tac bool_ss [Abbr `flags`] >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [MAP_EQ_NIL] >> metis_tac[]) >>
  `emit_inst LOG
    (Lit (n2w (LENGTH (Lit (n2w h)::topic_ops))) ::
      REVERSE (Lit (n2w h)::topic_ops) ++ [Lit 0w; Lit 0w]) []
    topic_sa = ((),sb)` by
    (mp_tac (Q.INST
      [`xs` |-> `lops`, `topics` |-> `topic_ops`,
       `st` |-> `topic_sa`, `tys` |-> `MAP (SND o FST) (fields : ((string # type) # bool) list)`,
       `flags` |-> `flags`, `ty` |-> `ret_ty`]
      (SPEC_ALL stmtSimLogTraceTheory.compile_log_empty_trace)) >>
     impl_tac >- simp[Abbr `flags`] >>
     disch_then (fn th => ACCEPT_TAC (EQ_MP th
       (ASSUME ``compile_stmt cenv lctx ret_ty (Log id args) sa = ((),sb)``)))) >>
  `cs_extends topic_sa sb` by
    (qpat_assum `emit_inst LOG _ [] topic_sa = ((),sb)`
      (fn code => mp_tac (SIMP_RULE bool_ss [code,pairTheory.SND,ci_mono_def]
        (ISPECL [``LOG:opcode``,rand (rator (rator (lhs (concl code)))),
          ``[]:string list``,``topic_sa:compile_state``]
          exprLoweringPropsTheory.ci_mono_emit_inst))) >>
     simp_tac bool_ss []) >>
  qabbrev_tac `topic_args = select_log_args T flags lops` >>
  qabbrev_tac `topic_vals = select_log_args T flags vs` >>
  `LIST_REL (\arg v. ?j. j < LENGTH args /\ v = EL j vs /\
       FST arg = FST (EL j ops) /\ SND arg = expr_type (EL j args))
     topic_args topic_vals` by
    (simp_tac bool_ss [Abbr `topic_args`, Abbr `topic_vals`] >>
     irule typedLogSplitCompleteTheory.select_log_args_list_rel >>
     conj_tac >- simp[Abbr `flags`, Abbr `lops`] >>
     simp[LIST_REL_EL_EQN, Abbr `lops`, EL_ZIP, EL_MAP] >>
     rpt strip_tac >> qexists_tac `n` >> simp[]) >>
  `MAP (\p. (FST p,is_bytestring_type (SND p))) topic_args =
     FST (split_log_ops lops flags)` by
    (mp_tac (Q.SPECL [`flags`, `lops`]
       eventLogSplitPropsTheory.split_log_ops_select) >>
     impl_tac >- simp[Abbr `flags`, Abbr `lops`] >>
     disch_then (mp_tac o Q.AP_TERM `FST`) >>
     simp[Abbr `topic_args`, pairTheory.LAMBDA_PROD]) >>
  `compile_log_topic_ops
     (MAP (\p. (FST p,is_bytestring_type (SND p))) topic_args) sm =
     (topic_ops,topic_sa)` by simp[Abbr `flags`] >>
  `MAP SND topic_args = select_log_args T flags (MAP expr_type args)` by
    simp[Abbr `topic_args`, Abbr `lops`, GSYM select_log_args_MAP,
      MAP_ZIP] >>
  `encode_indexed_event_topics (REPLICATE (LENGTH topic_args) T)
       (MAP SND topic_args) topic_vals = SOME topics` by
    (mp_tac (Q.SPECL [`flags`,`MAP expr_type args`,`vs`]
       eventLogSplitPropsTheory.encode_indexed_event_topics_select) >>
     impl_tac >- simp[Abbr `flags`] >>
     `LENGTH topic_args = LENGTH (select_log_args T flags (MAP expr_type args))` by
       metis_tac[LENGTH_MAP] >>
     simp[Abbr `topic_vals`, Abbr `flags`]) >>
  `LIST_REL (\arg f. supported_scalar_type (SND arg)) topic_args
      (select_log_args T flags fields)` by
    (simp_tac bool_ss [Abbr `topic_args`] >>
     irule eventLogSplitPropsTheory.select_log_args_rel >>
     conj_tac >- simp[Abbr `flags`, Abbr `lops`] >>
     simp[LIST_REL_EL_EQN, EL_ZIP, Abbr `lops`, Abbr `flags`, EL_MAP] >>
     rpt strip_tac >>
     `supported_scalar_type (SND (FST (EL n fields)))` by
       (qpat_assum `EVERY (\f. if SND f then _ else _) fields`
          (mp_tac o Q.SPEC `n` o REWRITE_RULE [EVERY_EL]) >> simp[]) >>
     `event_arg_compatible (SND (FST (EL n fields))) (expr_type (EL n args))` by
       (qpat_assum `LIST_REL event_arg_compatible _ _`
          (mp_tac o Q.SPEC `n` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
        simp[EL_MAP, combinTheory.o_THM]) >>
     metis_tac[stmtSimLogSourceTheory.scalar_event_arg_compatible]) >>
  `EVERY (\arg. supported_scalar_type (SND arg)) topic_args` by
    (qpat_assum `LIST_REL (\arg f. supported_scalar_type (SND arg)) _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]) >>
  `LIST_REL (\arg v. supported_scalar_type (SND arg) /\
       ?j. j < LENGTH args /\ v = EL j vs /\
       FST arg = FST (EL j ops) /\ SND arg = expr_type (EL j args))
     topic_args topic_vals` by
    (fs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]) >>
  suspend "empty_topic_producer"
QED
*)

Resume compile_log_frag_full[empty_topic_producer]:
  `log_full_post DF lo d ctx func cenv cx es sa sm s0 G0 tn0 args ops
     (storage_trace_horizon mid.storage_trace) (INL vs : value list + exception)
     mid G1 tn1 t` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id` by
    (mp_tac (cj 1 stmtLoweringMonoTheory.ci_mono_list_helpers) >>
     disch_then (qspecl_then [`cenv`,`args`,`sa`] mp_tac) >> simp[ci_mono_def]) >>
  `local_ptrs_reserved cenv sm` by
    (qspecl_then [`cenv`,`sa`,`sm`] match_mp_tac
       exprLoweringPropsTheory.local_ptrs_reserved_next_var >> fs[cs_extends_def]) >>
  `cs_extends sm topic_sa /\ sm.cs_next_var <= topic_sa.cs_next_var /\
   sm.cs_next_id <= topic_sa.cs_next_id` by
    (mp_tac (cj 2 stmtLoweringMonoTheory.ci_mono_list_helpers) >>
     disch_then (qspecl_then
       [`MAP (\p. (FST p,is_bytestring_type (SND p))) topic_args`,`sm`] mp_tac) >>
     simp[ci_mono_def]) >>
  `fn_has_code sm topic_sa func` by
    (qspecl_then [`sm`,`sm`,`topic_sa`,`sb`,`func`] match_mp_tac
       fragExecTheory.fn_has_code_mid >> simp[cs_extends_refl]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ lo d cenv cx mid G1 tn1 t`
       (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >> simp[]) >>
  drule_all bodyFullLogScalarTopicsTheory.compile_log_scalar_topics_from_capture >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`tp`,`Gp`,`tnp`] strip_assume_tac)) >>
  suspend "empty_topic_endpoint"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[empty_topic_producer]:
  `log_full_post DF lo d ctx func cenv cx es sa sm s0 G0 tn0 args ops
     (storage_trace_horizon mid.storage_trace) (INL vs : value list + exception)
     mid G1 tn1 t` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
`cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
 sa.cs_next_id <= sm.cs_next_id` by
 (mp_tac (cj 1 stmtLoweringMonoTheory.ci_mono_list_helpers) >>
  disch_then (qspecl_then [`cenv`,`args`,`sa`] mp_tac) >>
  simp[ci_mono_def]) >>
`local_ptrs_reserved cenv sm` by
 (qspecl_then [`cenv`,`sa`,`sm`] match_mp_tac
    exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
  fs[cs_extends_def]) >>
`cs_extends sm topic_sa /\ sm.cs_next_var <= topic_sa.cs_next_var /\
 sm.cs_next_id <= topic_sa.cs_next_id` by
 (mp_tac (cj 2 stmtLoweringMonoTheory.ci_mono_list_helpers) >>
  disch_then (qspecl_then
    [`MAP (\p. (FST p,is_bytestring_type (SND p))) topic_args`,`sm`] mp_tac) >>
  simp[ci_mono_def]) >>
`fn_has_code sm topic_sa func` by
 (qspecl_then [`sm`,`sm`,`topic_sa`,`sb`,`func`] match_mp_tac
    fragExecTheory.fn_has_code_mid >> simp[cs_extends_refl]) >>
`allocas_from lo t /\ lo <= t.vs_alloca_next` by
 (qpat_assum `ghost_inv_at _ lo d cenv cx mid G1 tn1 t`
   (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >> simp[]) >>
mp_tac (Q.INST
  [`captured` |-> `ops`, `xs` |-> `topic_args`, `ivs` |-> `topic_vals`,
   `result_ops` |-> `topic_ops`, `sb` |-> `topic_sa`, `ee` |-> `mid`,
   `inv_es` |-> `es`, `s` |-> `t`, `G` |-> `G1`, `tn` |-> `tn1`,
   `H` |-> `storage_trace_horizon mid.storage_trace`,
   `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
  (INST_TYPE [``:'a`` |-> ``:256``, ``:'b`` |-> ``:exception``]
    (INST [{redex=mk_var ("ops", ``:operand list``),
            residue=mk_var ("result_ops", ``:operand list``)}]
      bodyFullLogScalarTopicsTheory.compile_log_scalar_topics_from_capture))) >>
(impl_tac
>- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
disch_then (qx_choosel_then [`tp`,`Gp`,`tnp`] strip_assume_tac) >>

  suspend "empty_topic_endpoint"
QED
*)

Resume compile_log_frag_full[empty_topic_endpoint]:
  `tp.vs_memory = t.vs_memory /\ tp.vs_allocas = t.vs_allocas /\
   tp.vs_alloca_next = t.vs_alloca_next /\
   tp.vs_accounts = t.vs_accounts /\ tp.vs_transient = t.vs_transient /\
   tp.vs_requests = t.vs_requests /\ tp.vs_call_ctx = t.vs_call_ctx` by
    (qpat_assum `tp with <|vs_vars := _; vs_inst_idx := _|> = t`
      (mp_tac o SIMP_RULE (srw_ss()) [venomStateTheory.venom_state_component_equality]) >> simp[]) >>
  `gas_path_mem ctx func t 0 (OK tp)` by
    (qpat_assum `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t,G1,tn1) [] (OK tp,Gp,tnp)`
      (qspec_then `DF (storage_trace_horizon mid.storage_trace)` mp_tac) >>
     disch_then (mp_tac o CONJUNCT1 o MATCH_MP
       fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
     disch_then (mp_tac o MATCH_MP fragGasOriginTheory.gas_origin_path_erase) >>
     simp[fragGasModeTheory.gas_marked_path_def]) >>
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  `!u. gas_path_mem ctx func t 0 (OK u) ==> alloca_inv u` by
    (rpt strip_tac >>
     drule_all bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv >> simp[]) >>
  `alloca_history func tp` by
    (drule_all fragGasPathFrameMemTheory.gas_path_mem_zero_history >> simp[]) >>
  suspend "empty_topic_frame"
QED

Resume compile_log_frag_full[empty_topic_frame]:
  `(!x sz. cenv.ce_return_buf=SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc=SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    (rpt conj_tac >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
     fs[ci_mono_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
   stmt_state_rel H ctx func cenv cx mid tp /\
   storage_well_formed_on cx mid (FST H) /\
   ghost_inv_at (DF H) lo d cenv cx mid Gp tnp tp` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >>
     disch_then (strip_assume_tac o BETA_RULE o
       REWRITE_RULE [bodyFullLogArgsTheory.log_full_post_def]) >> gvs[] >>
     `stmt_state_rel H ctx func cenv cx mid tp` by
       (mp_tac (Q.INST
         [`H0` |-> `storage_trace_horizon mid.storage_trace`, `H` |-> `H`,
          `es` |-> `mid`, `u` |-> `tp`, `s` |-> `t`]
         (INST_TYPE [``:'a`` |-> ``:256``, ``:'b`` |-> ``:256``]
           exprLoweringPropsTheory.stmt_state_rel_fields_transport)) >>
        (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >> simp[]) >>
  suspend "empty_topic_all_h"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[empty_topic_endpoint]:
(* Project readonly fields once; leave the original equality available. *)
`tp.vs_memory = t.vs_memory /\ tp.vs_allocas = t.vs_allocas /\
 tp.vs_alloca_next = t.vs_alloca_next /\
 tp.vs_accounts = t.vs_accounts /\ tp.vs_transient = t.vs_transient /\
 tp.vs_requests = t.vs_requests /\ tp.vs_call_ctx = t.vs_call_ctx`
 by (qpat_assum `tp with <|vs_vars := _; vs_inst_idx := _|> = t`
      (mp_tac o SIMP_RULE (srw_ss()) [venomStateTheory.venom_state_component_equality]) >>
     simp[]) >>

(* alloca_history is sensitive to the cursor, so a state-field equality
   alone cannot transport it. Project the SAME topic path; no re-execution
   and no second endpoint are selected. *)
`gas_path_mem ctx func t 0 (OK tp)` by
 (qpat_assum `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t,G1,tn1) [] (OK tp,Gp,tnp)`
    (qspec_then `DF (storage_trace_horizon mid.storage_trace)` mp_tac) >>
  disch_then (mp_tac o CONJUNCT1 o MATCH_MP
    fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
  disch_then (mp_tac o MATCH_MP fragGasOriginTheory.gas_origin_path_erase) >>
  simp[fragGasModeTheory.gas_marked_path_def]) >>
`alloca_inv t` by fs[stmt_state_rel_def] >>
`!u. gas_path_mem ctx func t 0 (OK u) ==> alloca_inv u` by
 (rpt strip_tac >>
  drule_all bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv >> simp[]) >>
`alloca_history func tp` by
 (drule_all fragGasPathFrameMemTheory.gas_path_mem_zero_history >> simp[]) >>

  suspend "empty_topic_frame"
QED
*)

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[empty_topic_frame]:
(* 2. Preserve original all-H facts at the one chosen topic endpoint.
   Return freshness comes from stmt_frag_full / ret_pc_ok at sa;
   local_ptrs_reserved deliberately does NOT contain these two facts. *)
`(!x sz. cenv.ce_return_buf=SOME (PtrVar (Var x) sz) ==>
   not_fresh_at sm x) /\
 (!x sz. cenv.ce_return_pc=SOME (PtrVar (Var x) sz) ==>
   not_fresh_at sm x)` by
 (rpt conj_tac >> rpt strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
  fs[ci_mono_def] >> metis_tac[]) >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 stmt_state_rel H ctx func cenv cx mid tp /\
 storage_well_formed_on cx mid (FST H) /\
 ghost_inv_at (DF H) lo d cenv cx mid Gp tnp tp` by
 (gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >>
  disch_then (strip_assume_tac o BETA_RULE o
    REWRITE_RULE [bodyFullLogArgsTheory.log_full_post_def]) >> gvs[] >>
  `stmt_state_rel H ctx func cenv cx mid tp` by
    (mp_tac (Q.INST
        [`H0` |-> `storage_trace_horizon mid.storage_trace`, `H` |-> `H`,
         `es` |-> `mid`, `u` |-> `tp`, `s` |-> `t`]
        (INST_TYPE [``:'a`` |-> ``:256``, ``:'b`` |-> ``:256``]
          exprLoweringPropsTheory.stmt_state_rel_fields_transport)) >>
     (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  simp[]) >>

  suspend "empty_topic_all_h"
QED
*)

Resume compile_log_frag_full[empty_topic_all_h]:
`ltys = []` by
 (mp_tac (Q.SPECL [`lops`,`flags`]
   stmtSimLogTopicsTheory.split_log_ops_data_types) >>
  (impl_tac >- simp[Abbr `lops`,Abbr `flags`]) >>
  simp[Abbr `ltys`,Abbr `lops`,Abbr `flags`,MAP_ZIP]) >>
`dtys = [] /\ dvs = []` by fs[arg_types_fit_LIST_REL] >>
`avs = []` by
 (qpat_assum `vyper_to_abi_list _ dtys dvs = SOME avs` mp_tac >>
  qpat_assum `dtys = []` mp_tac >> qpat_assum `dvs = []` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [vyperABITheory.vyper_to_abi_def]) >>
qabbrev_tac `log_ev = <|logger := cx.txn.target;
  topics := n2w h::topics; data := []|>` >>
`encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs = SOME log_ev` by
 (qpat_assum `encode_source_event _ _ _ _ _ = SOME _` mp_tac >>
  qpat_assum `dtys = []` mp_tac >> qpat_assum `avs = []` mp_tac >>
  simp_tac bool_ss [Abbr `log_ev`] >> POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [contractABITheory.enc_def,listTheory.REV_DEF,LET_THM]) >>
`LENGTH (Lit (n2w h)::topic_ops) <= 4` by
 (mp_tac (Q.INST
   [`xs` |-> `lops`, `flags` |-> `flags`,
    `sa` |-> `sm`, `sb` |-> `topic_sa`, `emitted_topic_ops` |-> `topic_ops`,
    `first_topic` |-> `Lit (n2w h)`]
   (Q.INST [`ops` |-> `emitted_topic_ops`, `h` |-> `first_topic`]
     (SPEC_ALL stmtSimLogTopicsTheory.log_emitted_topic_count_exact))) >>
  (impl_tac >-
   (conj_tac >-
     (simp_tac bool_ss [Abbr `flags`,Abbr `lops`,LENGTH_MAP,LENGTH_ZIP] >>
      qpat_assum `LENGTH ops = LENGTH fields` mp_tac >>
      qpat_assum `LENGTH args = LENGTH fields` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
    conj_tac >> first_assum ACCEPT_TAC)) >> simp_tac bool_ss []) >>
`LENGTH (Lit (n2w h)::topic_ops) < dimword (:256)` by
 (`4 < dimword (:256)` by simp[wordsTheory.dimword_def] >> decide_tac) >>
`eval_operands (Lit (n2w h)::topic_ops) tp = SOME (n2w h::topics)` by
 (qpat_assum `LIST_REL (\op w. eval_operand op tp = SOME w) topic_ops topics`
   (mp_tac o MATCH_MP stmtSimLogSuffixTheory.log_operands_values) >>
  simp[venomStateTheory.eval_operands_def,venomStateTheory.eval_operand_def]) >>
`tp.vs_call_ctx.cc_address = cx.txn.target /\
 (tp.vs_call_ctx.cc_static <=> cx.txn.is_static)` by
 (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid tp /\ _`
   (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [stmt_state_rel_def,state_rel_def,call_ctx_rel_def] >>
  metis_tac[]) >>
`fn_has_code topic_sa sb func` by
 (qspecl_then [`sm`,`topic_sa`,`sb`,`sb`,`func`] match_mp_tac
   fragExecTheory.fn_has_code_mid >> simp[cs_extends_refl]) >>
`allocas_from lo tp /\ lo <= tp.vs_alloca_next` by
 (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
   stmt_state_rel H ctx func cenv cx mid tp /\ _`
   (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp_tac bool_ss [bodyPtrDefsTheory.ghost_inv_at_def] >>
  strip_tac >> asm_rewrite_tac[]) >>
Cases_on `tp.vs_call_ctx.cc_static`
>- suspend "empty_static" >>
mp_tac (Q.INST
 [`topic_ops` |-> `Lit (n2w h)::topic_ops`, `topics` |-> `n2w h::topics`,
  `ptr_op` |-> `Lit 0w`, `len_op` |-> `Lit 0w`,
  `off` |-> `0w:bytes32`, `len` |-> `0w:bytes32`,
  `s` |-> `tp`, `G` |-> `Gp`, `tn` |-> `tnp`,
  `sa` |-> `topic_sa`, `sb` |-> `sb`,
  `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
 (SPEC_ALL bodyFullLogSuffixTheory.compile_log_emit_origin_ptr_path)) >>
(impl_tac >-
 (asm_simp_tac (srw_ss()) [venomStateTheory.eval_operand_def,
   ptrDisciplineTheory.op_taint_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC)) >>
strip_tac >> suspend "empty_emit"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[empty_topic_all_h]:
`ltys = []` by
 (mp_tac (Q.SPECL [`lops`,`flags`]
   stmtSimLogTopicsTheory.split_log_ops_data_types) >>
  impl_tac >- simp[Abbr `lops`,Abbr `flags`] >>
  simp[Abbr `ltys`,Abbr `lops`,Abbr `flags`,MAP_ZIP]) >>
`dtys = [] /\ dvs = []` by
 (fs[arg_types_fit_LIST_REL]) >>
`avs = []` by
 (qpat_assum `vyper_to_abi_list _ dtys dvs = SOME avs` mp_tac >>
  qpat_assum `dtys = []` mp_tac >> qpat_assum `dvs = []` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [vyperABITheory.vyper_to_abi_def]) >>
qabbrev_tac `log_ev = <|logger := cx.txn.target;
  topics := n2w h::topics; data := []|>` >>
`encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs = SOME log_ev` by
 (qpat_assum `encode_source_event _ _ _ _ _ = SOME _` mp_tac >>
  qpat_assum `dtys = []` mp_tac >> qpat_assum `avs = []` mp_tac >>
  simp_tac bool_ss [Abbr `log_ev`] >> POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [contractABITheory.enc_def,listTheory.REV_DEF,LET_THM]) >>
`LENGTH (Lit (n2w h)::topic_ops) <= 4` by
 (mp_tac (Q.INST
   [`xs` |-> `ops`, `flags` |-> `flags`,
    `sa` |-> `sm`, `sb` |-> `topic_sa`, `emitted_topic_ops` |-> `topic_ops`,
    `first_topic` |-> `Lit (n2w h)`]
   (Q.INST [`ops` |-> `emitted_topic_ops`, `h` |-> `first_topic`]
     (SPEC_ALL stmtSimLogTopicsTheory.log_emitted_topic_count_exact))) >>
  (impl_tac >-
   (conj_tac >- simp[Abbr `flags`] >>
    conj_tac >> first_assum ACCEPT_TAC)) >> simp_tac bool_ss []) >>
`LENGTH (Lit (n2w h)::topic_ops) < dimword (:256)` by
 (`4 < dimword (:256)` by simp[wordsTheory.dimword_def] >> decide_tac) >>
`eval_operands (Lit (n2w h)::topic_ops) tp = SOME (n2w h::topics)` by
 (qpat_assum `LIST_REL (\op w. eval_operand op tp = SOME w) topic_ops topics`
   (mp_tac o MATCH_MP stmtSimLogSuffixTheory.log_operands_values) >>
  simp[venomStateTheory.eval_operands_def,venomStateTheory.eval_operand_def]) >>
`~tp.vs_call_ctx.cc_static /\ tp.vs_call_ctx.cc_address = cx.txn.target` by
 (qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace)
   ctx func cenv cx mid tp` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [stmt_state_rel_def,state_rel_def,call_ctx_rel_def] >>
  metis_tac[]) >>
`fn_has_code topic_sa sb func` by
 (qspecl_then [`sm`,`topic_sa`,`sb`,`sb`,`func`] match_mp_tac
   fragExecTheory.fn_has_code_mid >> simp[cs_extends_refl]) >>
`allocas_from lo tp /\ lo <= tp.vs_alloca_next` by
 (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
   stmt_state_rel H ctx func cenv cx mid tp /\ _`
   (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  simp_tac bool_ss [bodyPtrDefsTheory.ghost_inv_at_def] >>
  strip_tac >> asm_rewrite_tac[]) >>
mp_tac (Q.INST
 [`topic_ops` |-> `Lit (n2w h)::topic_ops`, `topics` |-> `n2w h::topics`,
  `ptr_op` |-> `Lit 0w`, `len_op` |-> `Lit 0w`,
  `off` |-> `0w:bytes32`, `len` |-> `0w:bytes32`,
  `s` |-> `tp`, `G` |-> `Gp`, `tn` |-> `tnp`,
  `sa` |-> `topic_sa`, `sb` |-> `sb`,
  `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
 (SPEC_ALL bodyFullLogSuffixTheory.compile_log_emit_origin_ptr_path)) >>
(impl_tac >-
 (asm_simp_tac (srw_ss()) [venomStateTheory.eval_operand_def,
   ptrDisciplineTheory.op_taint_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC)) >>
strip_tac >> suspend "empty_emit"
QED
*)

Resume compile_log_frag_full[empty_static]:
mp_tac (Q.INST
 [`topic_ops` |-> `Lit (n2w h)::topic_ops`, `topics` |-> `n2w h::topics`,
  `ptr_op` |-> `Lit 0w`, `len_op` |-> `Lit 0w`,
  `off` |-> `0w:bytes32`, `len` |-> `0w:bytes32`,
  `s` |-> `tp`, `G` |-> `Gp`, `tn` |-> `tnp`,
  `sa` |-> `topic_sa`, `sb` |-> `sb`,
  `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
 (SPEC_ALL compile_log_emit_static_origin_ptr_path)) >>
(impl_tac >-
 (asm_simp_tac (srw_ss()) [venomStateTheory.eval_operand_def,
   ptrDisciplineTheory.op_taint_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
`cx.txn.is_static` by metis_tac[] >>
`!D. gas_origin_ptr_path
 (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
 (t,G1,tn1) []
 (Abort ExHalt_abort (halt_state (set_returndata [] tp)),Gp,tnp)` by
 (qx_gen_tac `path_D` >>
  qpat_assum `!D. gas_origin_ptr_path _ (t,G1,tn1) [] (OK tp,Gp,tnp)`
   (qspec_then `path_D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path _ (tp,Gp,tnp) [] (Abort _ _,Gp,tnp)`
   (qspec_then `path_D` mp_tac) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,APPEND_NIL]) >>
`!tail. bind (lift_option
 (encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs)
 "Log encode event")
 (\event. ignore_bind (check_not_static cx) (push_log event))
 (mid with gas_obs := tail) =
 (INR (Error (RuntimeError "write in static context")),mid with gas_obs := tail)` by
 (qpat_assum `encode_source_event _ _ _ _ _ = SOME log_ev` mp_tac >>
  qpat_assum `cx.txn.is_static` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[log_full_source_suffix_result]) >>
irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >>
reverse conj_tac >- first_assum ACCEPT_TAC >>
qexistsl_tac [`Gp`,`mid`,
 `Abort ExHalt_abort (halt_state (set_returndata [] tp))`,
 `INR (Error (RuntimeError "write in static context"))`,`tnp`] >>
conj_tac >- first_assum ACCEPT_TAC >>
reverse conj_tac >- simp[exit_result_def] >>
qx_gen_tac `post_H` >> strip_tac >> BETA_TAC >>
conj_tac >-
 (qpat_assum `!D. gas_origin_ptr_path _ (t,G1,tn1) [] (Abort _ _,Gp,tnp)`
   (qspec_then `DF post_H` ACCEPT_TAC)) >>
simp[stmt_exit_ptr_def,expr_exit_def,halt_exit_def]
QED

Resume compile_log_frag_full[empty_emit]:
qabbrev_tac `fin = tp with <|vs_logs := tp.vs_logs ++ [log_ev];
  vs_inst_idx := LENGTH sb.cs_current_insts|>` >>
`!D. gas_origin_ptr_path
 (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
 (tp,Gp,tnp) [] (OK fin,Gp,tnp)` by
 (qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (tp,Gp,tnp) [] _` mp_tac >>
  qpat_assum `tp.vs_call_ctx.cc_address = cx.txn.target` mp_tac >>
  simp_tac bool_ss [Abbr `fin`,Abbr `log_ev`] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [mem_bytes_at_def]) >>
`!D. gas_origin_ptr_path
 (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
 (t,G1,tn1) [] (OK fin,Gp,tnp)` by
 (qx_gen_tac `path_D` >>
  qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (t,G1,tn1) [] (OK tp,Gp,tnp)` (qspec_then `path_D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (tp,Gp,tnp) [] (OK fin,Gp,tnp)` (qspec_then `path_D` mp_tac) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,APPEND_NIL]) >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 stmt_state_rel H ctx func cenv cx
  (mid with logs := mid.logs ++ [log_ev]) fin` by
 (qx_gen_tac `fin_H` >> strip_tac >>
  `stmt_state_rel fin_H ctx func cenv cx mid tp` by
   (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid tp /\ _`
     (qspec_then `fin_H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel fin_H ctx func cenv cx
    (mid with logs := mid.logs ++ [log_ev])
    (tp with vs_logs := tp.vs_logs ++ [log_ev])` by
   (match_mp_tac stmtSimLogEmitTheory.log_append_stmt_state_rel >>
    first_assum ACCEPT_TAC) >>
  pop_assum mp_tac >>
  simp_tac (srw_ss()) [Abbr `fin`,exprLoweringPropsTheory.stmt_state_rel_inst_idx]) >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 ghost_inv_at (DF H) lo d cenv cx
  (mid with logs := mid.logs ++ [log_ev]) Gp tnp fin` by
 (qx_gen_tac `fin_H` >> strip_tac >>
  `ghost_inv_at (DF fin_H) lo d cenv cx mid Gp tnp tp` by
   (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid tp /\ _`
     (qspec_then `fin_H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> first_assum ACCEPT_TAC) >>
  pop_assum mp_tac >> simp_tac bool_ss [Abbr `fin`,ghost_inv_at_logs_idx] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [bodyPtrDefsTheory.ghost_inv_at_def] >>
  strip_tac >> asm_rewrite_tac[]) >>
`gas_path_mem ctx func tp 0 (OK fin)` by
 (qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (tp,Gp,tnp) [] (OK fin,Gp,tnp)`
   (qspec_then `DF (storage_trace_horizon mid.storage_trace)` mp_tac) >>
  disch_then (mp_tac o CONJUNCT1 o MATCH_MP
   fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
  disch_then (mp_tac o MATCH_MP fragGasOriginTheory.gas_origin_path_erase) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [fragGasModeTheory.gas_marked_path_def]) >>
`alloca_inv tp` by
 (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
   stmt_state_rel H ctx func cenv cx mid tp /\ _`
   (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp_tac bool_ss [stmt_state_rel_def] >>
  strip_tac >> asm_rewrite_tac[]) >>
`!u. gas_path_mem ctx func tp 0 (OK u) ==> alloca_inv u` by
 (rpt strip_tac >>
  drule_all bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv >> simp[]) >>
`alloca_history func fin` by
 (drule_all fragGasPathFrameMemTheory.gas_path_mem_zero_history >> simp[]) >>
`sb.cs_current_bb = topic_sa.cs_current_bb` by
 (qpat_assum `emit_inst LOG _ [] topic_sa = ((),sb)`
   (mp_tac o MATCH_MP emitHelperPropsTheory.emit_inst_extends) >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss []) >>
`~block_is_terminated sb` by
 (qpat_assum `emit_inst LOG _ [] topic_sa = ((),sb)`
   (ACCEPT_TAC o MATCH_MP logComposeFactsTheory.log_emit_not_terminated)) >>
`stmt_lands lctx sb (INL ()) fin /\ ~fin.vs_halted` by
 (qpat_assum `tp.vs_current_bb = topic_sa.cs_current_bb` mp_tac >>
  qpat_assum `sb.cs_current_bb = topic_sa.cs_current_bb` mp_tac >>
  qpat_assum `~tp.vs_halted` mp_tac >>
  simp_tac (srw_ss()) [Abbr `fin`,stmt_lands_def]) >>
suspend "empty_final_frame"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[empty_emit]:
qabbrev_tac `fin = tp with <|vs_logs := tp.vs_logs ++ [log_ev];
  vs_inst_idx := LENGTH sb.cs_current_insts|>` >>
`!D. gas_origin_ptr_path
 (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
 (tp,Gp,tnp) [] (OK fin,Gp,tnp)` by
 (qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (tp,Gp,tnp) [] _` mp_tac >>
  qpat_assum `tp.vs_call_ctx.cc_address = cx.txn.target` mp_tac >>
  simp_tac bool_ss [Abbr `fin`,Abbr `log_ev`] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [mem_bytes_at_def]) >>
`!D. gas_origin_ptr_path
 (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
 (t,G1,tn1) [] (OK fin,Gp,tnp)` by
 (qx_gen_tac `path_D` >>
  qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (t,G1,tn1) [] (OK tp,Gp,tnp)` (qspec_then `path_D` mp_tac) >>
  qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (tp,Gp,tnp) [] (OK fin,Gp,tnp)` (qspec_then `path_D` mp_tac) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,APPEND_NIL]) >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 stmt_state_rel H ctx func cenv cx
  (mid with logs := mid.logs ++ [log_ev]) fin` by
 (qx_gen_tac `fin_H` >> strip_tac >>
  `stmt_state_rel fin_H ctx func cenv cx mid tp` by
   (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid tp /\ _`
     (qspec_then `fin_H` mp_tac) >>
    impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel fin_H ctx func cenv cx
    (mid with logs := mid.logs ++ [log_ev])
    (tp with vs_logs := tp.vs_logs ++ [log_ev])` by
   (match_mp_tac stmtSimLogEmitTheory.log_append_stmt_state_rel >>
    first_assum ACCEPT_TAC) >>
  pop_assum mp_tac >>
  simp_tac (srw_ss()) [Abbr `fin`,exprLoweringPropsTheory.stmt_state_rel_inst_idx]) >>
`!H. valid_horizon cx st0 H mid.storage_trace ==>
 ghost_inv_at (DF H) lo d cenv cx
  (mid with logs := mid.logs ++ [log_ev]) Gp tnp fin` by
 (qx_gen_tac `fin_H` >> strip_tac >>
  `ghost_inv_at (DF fin_H) lo d cenv cx mid Gp tnp tp` by
   (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid tp /\ _`
     (qspec_then `fin_H` mp_tac) >>
    impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> first_assum ACCEPT_TAC) >>
  pop_assum mp_tac >> simp_tac bool_ss [Abbr `fin`,ghost_inv_at_logs_idx] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [bodyPtrDefsTheory.ghost_inv_at_def] >>
  strip_tac >> asm_rewrite_tac[]) >>
`gas_path_mem ctx func tp 0 (OK fin)` by
 (qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (tp,Gp,tnp) [] (OK fin,Gp,tnp)`
   (qspec_then `DF (storage_trace_horizon mid.storage_trace)` mp_tac) >>
  disch_then (mp_tac o CONJUNCT1 o MATCH_MP
   fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
  disch_then (mp_tac o MATCH_MP fragGasOriginTheory.gas_origin_path_erase) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [fragGasModeTheory.gas_marked_path_def]) >>
`alloca_inv tp` by
 (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
   stmt_state_rel H ctx func cenv cx mid tp /\ _`
   (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  simp_tac bool_ss [stmt_state_rel_def] >>
  strip_tac >> asm_rewrite_tac[]) >>
`!u. gas_path_mem ctx func tp 0 (OK u) ==> alloca_inv u` by
 (rpt strip_tac >>
  drule_all bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv >> simp[]) >>
`alloca_history func fin` by
 (drule_all fragGasPathFrameMemTheory.gas_path_mem_zero_history >> simp[]) >>
`sb.cs_current_bb = topic_sa.cs_current_bb` by
 (qpat_assum `emit_inst LOG _ [] topic_sa = ((),sb)`
   (mp_tac o MATCH_MP emitHelperPropsTheory.emit_inst_extends) >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss []) >>
`~block_is_terminated sb` by
 (qpat_assum `emit_inst LOG _ [] topic_sa = ((),sb)`
   (ACCEPT_TAC o MATCH_MP logComposeFactsTheory.log_emit_not_terminated)) >>
`stmt_lands lctx sb (INL ()) fin /\ ~fin.vs_halted` by
 (qpat_assum `tp.vs_current_bb = topic_sa.cs_current_bb` mp_tac >>
  qpat_assum `sb.cs_current_bb = topic_sa.cs_current_bb` mp_tac >>
  qpat_assum `~tp.vs_halted` mp_tac >>
  simp_tac (srw_ss()) [Abbr `fin`,stmt_lands_def]) >>
suspend "empty_final_frame"
QED
*)

Resume compile_log_frag_full[empty_final_frame]:
`!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==>
 lookup_var x fin = SOME w` by
 (qx_genl_tac [`frame_x`,`frame_w`] >> strip_tac >>
  qpat_assum `!p. not_fresh_at sm p ==> lookup_var p tp = _ /\ _`
   (qspec_then `frame_x` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `lookup_var frame_x t = SOME frame_w` mp_tac >>
  simp_tac bool_ss [Abbr `fin`,venomStateTheory.lookup_var_def] >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [] >> metis_tac[]) >>
`!x. not_fresh_at sm x ==>
 FLOOKUP Gp x = FLOOKUP G1 x /\
 op_taint tnp (Var x) = op_taint tn1 (Var x)` by
 (qx_gen_tac `frame_x` >> strip_tac >>
  qpat_assum `!p. not_fresh_at sm p ==> lookup_var p tp = _ /\ _`
   (qspec_then `frame_x` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
`t.vs_alloca_next <= fin.vs_alloca_next` by
 (qpat_assum `tp.vs_alloca_next = t.vs_alloca_next` mp_tac >>
  simp_tac (srw_ss()) [Abbr `fin`]) >>
`!aid row. FLOOKUP t.vs_allocas aid = SOME row ==>
 FLOOKUP fin.vs_allocas aid = SOME row` by
 (qpat_assum `tp.vs_allocas = t.vs_allocas` mp_tac >>
  simp_tac (srw_ss()) [Abbr `fin`]) >>
`!x. not_fresh_at sa x ==> not_fresh_at sm x` by
 (qx_gen_tac `caller_x` >> strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
  conj_tac >> first_assum ACCEPT_TAC) >>
`!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
 lookup_var x fin = SOME w` by
 (qpat_assum `wb_frame cenv es mid sa s0 t`
   (mp_tac o CONJUNCT1 o REWRITE_RULE [wb_frame_def]) >>
  qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sm x` mp_tac >>
  qpat_assum `!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==>
   lookup_var x fin = SOME w` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac []) >>
`!x. not_fresh_at sa x ==>
 FLOOKUP Gp x = FLOOKUP G0 x /\
 op_taint tnp (Var x) = op_taint tn0 (Var x)` by
 (qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1`
   (mp_tac o CONJUNCT1 o REWRITE_RULE [ghost_kept_at_def]) >>
  qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sm x` mp_tac >>
  qpat_assum `!x. not_fresh_at sm x ==> FLOOKUP Gp x = FLOOKUP G1 x /\ _`
   mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac []) >>
`!aid row. FLOOKUP s0.vs_allocas aid = SOME row ==>
 FLOOKUP fin.vs_allocas aid = SOME row` by
 (qpat_assum `wb_frame cenv es mid sa s0 t`
   (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [wb_frame_def]) >>
  qpat_assum `!aid row. FLOOKUP t.vs_allocas aid = SOME row ==>
   FLOOKUP fin.vs_allocas aid = SOME row` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac []) >>
`s0.vs_alloca_next <= fin.vs_alloca_next` by
 (qpat_assum `s0.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
  qpat_assum `t.vs_alloca_next <= fin.vs_alloca_next` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
`sa.cs_next_var <= sb.cs_next_var` by
 (qpat_assum `compile_stmt cenv lctx ret_ty (Log id args) sa = ((),sb)`
   (fn stmt_code => mp_tac (SIMP_RULE bool_ss [stmt_code,pairTheory.SND,ci_mono_def]
     (Q.SPECL [`cenv`,`lctx`,`ret_ty`,`Log id args`,`sa`]
       (CONJUNCT1 stmtLoweringMonoTheory.compile_stmt_ci_mono)))) >>
  strip_tac >> first_assum ACCEPT_TAC) >>
`return_buf_frame d cenv sb fin` by
 (match_mp_tac (Q.SPECL [`d`,`cenv`,`cenv`,`sa`,`sb`,`s0`,`fin`]
   bodyMemoryDefsTheory.return_buf_frame_frame) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,REFL_TAC]) >>
suspend "empty_caller_frame"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[empty_final_frame]:
`!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==>
 lookup_var x fin = SOME w` by
 (qx_genl_tac [`frame_x`,`frame_w`] >> strip_tac >>
  qpat_assum `!p. not_fresh_at sm p ==> lookup_var p tp = _ /\ _`
   (qspec_then `frame_x` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `lookup_var frame_x t = SOME frame_w` mp_tac >>
  simp_tac bool_ss [Abbr `fin`,venomStateTheory.lookup_var_def] >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [] >> metis_tac[]) >>
`!x. not_fresh_at sm x ==>
 FLOOKUP Gp x = FLOOKUP G1 x /\
 op_taint tnp (Var x) = op_taint tn1 (Var x)` by
 (qx_gen_tac `frame_x` >> strip_tac >>
  qpat_assum `!p. not_fresh_at sm p ==> lookup_var p tp = _ /\ _`
   (qspec_then `frame_x` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
`t.vs_alloca_next <= fin.vs_alloca_next` by
 (qpat_assum `tp.vs_alloca_next = t.vs_alloca_next` mp_tac >>
  simp_tac (srw_ss()) [Abbr `fin`]) >>
`!aid row. FLOOKUP t.vs_allocas aid = SOME row ==>
 FLOOKUP fin.vs_allocas aid = SOME row` by
 (qpat_assum `tp.vs_allocas = t.vs_allocas` mp_tac >>
  simp_tac (srw_ss()) [Abbr `fin`]) >>
`!x. not_fresh_at sa x ==> not_fresh_at sm x` by
 (qx_gen_tac `caller_x` >> strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
  conj_tac >> first_assum ACCEPT_TAC) >>
`!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
 lookup_var x fin = SOME w` by
 (qpat_assum `wb_frame cenv es mid sa s0 t`
   (mp_tac o CONJUNCT1 o REWRITE_RULE [wb_frame_def]) >>
  qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sm x` mp_tac >>
  qpat_assum `!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==>
   lookup_var x fin = SOME w` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac []) >>
`!x. not_fresh_at sa x ==>
 FLOOKUP Gp x = FLOOKUP G0 x /\
 op_taint tnp (Var x) = op_taint tn0 (Var x)` by
 (qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1`
   (mp_tac o CONJUNCT1 o REWRITE_RULE [ghost_kept_at_def]) >>
  qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sm x` mp_tac >>
  qpat_assum `!x. not_fresh_at sm x ==> FLOOKUP Gp x = FLOOKUP G1 x /\ _`
   mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac []) >>
`!aid row. FLOOKUP s0.vs_allocas aid = SOME row ==>
 FLOOKUP fin.vs_allocas aid = SOME row` by
 (qpat_assum `wb_frame cenv es mid sa s0 t`
   (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [wb_frame_def]) >>
  qpat_assum `!aid row. FLOOKUP t.vs_allocas aid = SOME row ==>
   FLOOKUP fin.vs_allocas aid = SOME row` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac []) >>
`s0.vs_alloca_next <= fin.vs_alloca_next` by
 (qpat_assum `s0.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
  qpat_assum `t.vs_alloca_next <= fin.vs_alloca_next` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
`sa.cs_next_var <= sb.cs_next_var` by
 (qpat_assum `compile_stmt cenv lctx ret_ty (Log id args) sa = ((),sb)`
   (fn stmt_code => mp_tac (SIMP_RULE bool_ss [stmt_code,pairTheory.SND,ci_mono_def]
     (Q.SPECL [`cenv`,`lctx`,`ret_ty`,`Log id args`,`sa`]
       (CONJUNCT1 stmtLoweringMonoTheory.compile_stmt_ci_mono)))) >>
  strip_tac >> first_assum ACCEPT_TAC) >>
`return_buf_frame d cenv sb fin` by
 (match_mp_tac (Q.SPECL [`d`,`cenv`,`cenv`,`sa`,`sb`,`s0`,`fin`]
   bodyMemoryDefsTheory.return_buf_frame_frame) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,REFL_TAC]) >>
suspend "empty_caller_frame"
QED
*)

Resume compile_log_frag_full[empty_caller_frame]:
qabbrev_tac `done_es = mid with logs := mid.logs ++ [log_ev]` >>
`~cx.txn.is_static` by metis_tac[] >>
`!tail. bind (lift_option
 (encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs)
 "Log encode event")
 (\event. ignore_bind (check_not_static cx) (push_log event))
 (mid with gas_obs := tail) =
 (INL (),done_es with gas_obs := tail)` by
 (simp_tac bool_ss [Abbr `done_es`] >>
  qpat_assum `encode_source_event _ _ _ _ _ = SOME log_ev` mp_tac >>
  qpat_assum `~cx.txn.is_static` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
  asm_simp_tac (srw_ss()) [bind_def, ignore_bind_def, lift_option_def,
    return_def, check_not_static_eq, push_log_def]) >>
`!H. valid_horizon cx st0 H done_es.storage_trace ==>
 stmt_state_rel H ctx func cenv cx (done_es with gas_obs := []) fin` by
 (simp_tac (srw_ss()) [Abbr `done_es`,exprSimWordArgsTheory.stmt_state_rel_gas_obs] >>
  first_assum ACCEPT_TAC) >>
`!H. valid_horizon cx st0 H done_es.storage_trace ==>
 ghost_inv_at (DF H) lo d cenv cx (done_es with gas_obs := []) Gp tnp fin` by
 (qx_gen_tac `post_H` >> simp_tac (srw_ss()) [Abbr `done_es`] >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
   ghost_inv_at (DF H) lo d cenv cx
    (mid with logs := mid.logs ++ [log_ev]) Gp tnp fin`
   (qspec_then `post_H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [bodyPtrDefsTheory.ghost_inv_at_def] >>
  strip_tac >> asm_rewrite_tac []) >>
`!H. valid_horizon cx st0 H done_es.storage_trace ==>
 storage_well_formed_on cx (done_es with gas_obs := []) (FST H)` by
 (qx_gen_tac `post_H` >> simp_tac (srw_ss()) [Abbr `done_es`] >> strip_tac >>
  `storage_well_formed_on cx mid (FST post_H)` by
   (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid tp /\ _`
     (qspec_then `post_H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> first_assum ACCEPT_TAC) >>
  `storage_well_formed_on cx
    ((mid with logs := mid.logs ++ [log_ev]) with gas_obs := []) (FST post_H) <=>
   storage_well_formed_on cx mid (FST post_H)` by
   (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >>
    simp_tac (srw_ss()) []) >>
  pop_assum mp_tac >>
  qpat_assum `storage_well_formed_on cx mid (FST post_H)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [] >> metis_tac []) >>
irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
reverse conj_tac >- first_assum ACCEPT_TAC >>
qexistsl_tac [`Gp`,`done_es`,`INL ()`,`fin`,`tnp`] >>
conj_tac >- first_assum ACCEPT_TAC >>
qx_gen_tac `post_H` >> strip_tac >> BETA_TAC >>
conj_tac >-
 (qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (t,G1,tn1) [] (OK fin,Gp,tnp)`
   (qspec_then `DF post_H` ACCEPT_TAC)) >>
suspend "empty_outcome_post"
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[empty_caller_frame]:
qabbrev_tac `done_es = mid with logs := mid.logs ++ [log_ev]` >>
`!tail. bind (lift_option
 (encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs)
 "Log encode event") push_log (mid with gas_obs := tail) =
 (INL (),done_es with gas_obs := tail)` by
 (asm_simp_tac (srw_ss()) [Abbr `done_es`,vyperStateTheory.lift_option_def,
   vyperStateTheory.bind_def,vyperStateTheory.push_log_def,vyperStateTheory.return_def]) >>
`!H. valid_horizon cx st0 H done_es.storage_trace ==>
 stmt_state_rel H ctx func cenv cx (done_es with gas_obs := []) fin` by
 (simp_tac (srw_ss()) [Abbr `done_es`,exprSimWordArgsTheory.stmt_state_rel_gas_obs] >>
  first_assum ACCEPT_TAC) >>
`!H. valid_horizon cx st0 H done_es.storage_trace ==>
 ghost_inv_at (DF H) lo d cenv cx (done_es with gas_obs := []) Gp tnp fin` by
 (qx_gen_tac `post_H` >> simp_tac (srw_ss()) [Abbr `done_es`] >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
   ghost_inv_at (DF H) lo d cenv cx
    (mid with logs := mid.logs ++ [log_ev]) Gp tnp fin`
   (qspec_then `post_H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [bodyPtrDefsTheory.ghost_inv_at_def] >>
  strip_tac >> asm_rewrite_tac []) >>
`!H. valid_horizon cx st0 H done_es.storage_trace ==>
 storage_well_formed_on cx (done_es with gas_obs := []) (FST H)` by
 (qx_gen_tac `post_H` >> simp_tac (srw_ss()) [Abbr `done_es`] >> strip_tac >>
  `storage_well_formed_on cx mid (FST post_H)` by
   (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid tp /\ _`
     (qspec_then `post_H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> first_assum ACCEPT_TAC) >>
  `storage_well_formed_on cx
    ((mid with logs := mid.logs ++ [log_ev]) with gas_obs := []) (FST post_H) <=>
   storage_well_formed_on cx mid (FST post_H)` by
   (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >>
    simp_tac (srw_ss()) []) >>
  pop_assum mp_tac >>
  qpat_assum `storage_well_formed_on cx mid (FST post_H)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [] >> metis_tac []) >>
irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
reverse conj_tac >- first_assum ACCEPT_TAC >>
qexistsl_tac [`Gp`,`done_es`,`INL ()`,`fin`,`tnp`] >>
conj_tac >- first_assum ACCEPT_TAC >>
qx_gen_tac `post_H` >> strip_tac >> BETA_TAC >>
conj_tac >-
 (qpat_assum `!D. gas_origin_ptr_path
   (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (t,G1,tn1) [] (OK fin,Gp,tnp)`
   (qspec_then `DF post_H` ACCEPT_TAC)) >>
suspend "empty_outcome_post"
QED
*)

Resume compile_log_frag_full[empty_outcome_post]:
`stmt_state_rel post_H ctx func cenv cx (done_es with gas_obs := []) fin` by
 (qpat_assum `!H. valid_horizon cx st0 H done_es.storage_trace ==>
   stmt_state_rel H ctx func cenv cx (done_es with gas_obs := []) fin`
   (qspec_then `post_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
`storage_well_formed_on cx (done_es with gas_obs := []) (FST post_H)` by
 (qpat_assum `!H. valid_horizon cx st0 H done_es.storage_trace ==>
   storage_well_formed_on cx (done_es with gas_obs := []) (FST H)`
   (qspec_then `post_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
`ghost_inv_at (DF post_H) lo d cenv cx
 (done_es with gas_obs := []) Gp tnp fin` by
 (qpat_assum `!H. valid_horizon cx st0 H done_es.storage_trace ==>
   ghost_inv_at (DF H) lo d cenv cx (done_es with gas_obs := []) Gp tnp fin`
   (qspec_then `post_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
qexists_tac `cenv` >>
simp_tac bool_ss [stmtSimPropsTheory.cenv_top_ext_refl] >>
rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Historical receiver proof retained (inactive).
Resume compile_log_frag_full[empty_outcome_post]:
`stmt_state_rel post_H ctx func cenv cx (done_es with gas_obs := []) fin` by
 (qpat_assum `!H. valid_horizon cx st0 H done_es.storage_trace ==>
   stmt_state_rel H ctx func cenv cx (done_es with gas_obs := []) fin`
   (qspec_then `post_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
`storage_well_formed_on cx (done_es with gas_obs := []) (FST post_H)` by
 (qpat_assum `!H. valid_horizon cx st0 H done_es.storage_trace ==>
   storage_well_formed_on cx (done_es with gas_obs := []) (FST H)`
   (qspec_then `post_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
`ghost_inv_at (DF post_H) lo d cenv cx
 (done_es with gas_obs := []) Gp tnp fin` by
 (qpat_assum `!H. valid_horizon cx st0 H done_es.storage_trace ==>
   ghost_inv_at (DF H) lo d cenv cx (done_es with gas_obs := []) Gp tnp fin`
   (qspec_then `post_H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
qexists_tac `cenv` >>
simp_tac bool_ss [stmtSimPropsTheory.cenv_top_ext_refl] >>
rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)

Finalise compile_log_frag_full

Theorem body_log_aggregate_full:
  !cx id args fields DF lo d PG tops ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    body_exprs_full_ok cx args /\
    body_inv tops ctx cenv cx /\
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

(* Historical aggregate projection retained (inactive).
Proof
  rpt gen_tac >> strip_tac >>
  irule compile_log_frag_full >>
  asm_simp_tac bool_ss [] >> conj_tac >-
    (qexistsl_tac [`[]`, `tops`] >>
     asm_simp_tac bool_ss [supported_stmt_def]) >>
  qexistsl_tac [`env`, `env'`] >> asm_simp_tac bool_ss []
QED
*)
