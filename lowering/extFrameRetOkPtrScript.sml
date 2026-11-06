(*
 * The pointer twin of S1's external_frame_ret_ok, admitted.
 *
 * TOP-LEVEL:
 *   external_frame_ret_ok_ptr
 *)
Theory extFrameRetOkPtr
Ancestors
  vyperCompiler selectorDispatch moduleLoweringProps stmtLoweringProps
  exprLoweringProps vyperInterpreter vyperContext venomExecSemantics
  venomState compileEnv e2eDefs supportedProgram compileVyper fragExec
  venomInst contextCodegenRel ptrDiscipline ptrSafeRun vyperLoweringCorrect
  loweringRuntimeCorrect bodyPtrDefs stmtSimDefs stmtSimProps loweringPosts bodySim moduleLowering
  stmtLowering vyperTypeSystem vyperState emitHelper vyperTypeSelectedEntrySoundness
  stmtLoweringMono venomWf memSafeRun allocaFrontierBound unitTransformDefs
  unitShapeDefs o1PassContract extRetScalarCopyCountedPtr extRetBytesCopyCountedPtr
  extRetBulkCopyCountedPtr extRetWordStmtPtr extRetCopySuffixPtr extRetCopyInputsPtr
  extRetOperandBoundaryPtr extRetDispatchProtectionPtr extRetDispatchResultPtr
  extRetStaticStmtPtr extRetStaticReservedPtr extRetStaticFrameMetadataPtr
  extRetStaticFrameConsumerPtr extRetStaticCapacityPtr extRetStaticBoundedConsumerPtr
  extRetTypedStaticConsumerPtr extRetStaticLoweredFramePtr extRetStaticPlanSelectionPtr
  extRetStaticUnrestrictedProbePtr extRetZeroStmtPtr extRetRecursiveDomainProbePtr
  extRetRecursiveDynamicProbePtr extRetEvaluatedStaticPtr
  extRetRecursiveInterfacePtr extRetRecursivePlanPtr extRetSupportedShapePtr
  extRetPointwiseSourcePtr extRetRobustSourceChildrenPtr extRetRecursiveContractAuditPtr
  extRetRawValuePtr extRetRawStmtPtr extRetAbiReadCleanPtr extRetAbiReadBoundsPtr
  extRetAbiBytesHeaderPtr extRetAbiBytesCountedPtr extRetAbiStaticCountedPtr
  extRetAbiArrayStaticBodyPtr extRetAbiArrayInitPtr extRetAbiArrayBackedgePtr
  extRetAbiArrayStaticLoopPtr extRetAbiArrayStaticCountedPtr extRetAbiSourceInputPtr
  extRetAbiWrappedSourcePtr extRetAbiSingletonCountedPtr extRetAbiSingletonWrapperPtr
  extRetAbiChildBoundaryPtr extRetScratchInitPtr extRetSourceWindowPtr
  extRetAbiStorageFramePtr extRetAbiSingletonReturnPtr extRetBufferAllocCountedPtr
  extRetAbiReturnConsumerPtr extRetAbiBytesLivePtr extRetAbiSingletonLivePtr
  extRetBufferStatePtr extRetCursorResourcePtr extRetBufferCursorStatePtr
  extRetSingletonCapacityPtr extRetSourceAllocationPtr extRetCapacityAuditPtr
  extRetCapacityFrameProbePtr extRetSingletonWordCapacityPtr extRetSingletonStmtPtr
  extRetFrameFactsPtr extRetNoneFramePtr extRetWordFramePtr extRetRawFramePtr
  extRetSignatureFramePtr extRetLoweredBytesFramePtr extRetSingletonFramePtr returnMetadataPtr vyperTypeCallGraph

val _ = Parse.hide "body";

(* ADMITTED: external_frame_ret_ok with the ghost, for any outcome of the
   return: every return sequence halts pointer-safely, its return data
   untainted.

   Why it should hold: the frame has no return PC or buffer and no
   nonreentrant lock (supported_program forces nr = F), so the lowered
   Return is the returned expression's code (expr_sim_ptr /
   expr_vv_sim_ptr, given) and then one of compile_external_return's
   branches: STOP; ALLOCA 32, MSTORE, RETURN 32 of an untainted word; a raw
   return of a Bytes value's data; or ALLOCA of the max return size, the
   ABI encoder, RETURN of the encoded length, possibly after a widening
   copy into a fresh buffer.  Fresh ALLOCA bytes start tainted, so the
   point is that the encoder writes every byte it returns, from the value's
   pinned (hence untainted, by ptr_mem_ok) bytes or from literals, and
   returns exactly what it wrote. *)
Theorem external_frame_ret_ok_ptr:
  !tops rpolicy unit am tx ret vs mut args fbody env lbl cenv0 pos_args
   min_cds is_payable nkey ut' iv rt st cenv sa func.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
         (mut, F, lookup_raw_return_or_F (NONE : num option)
                     tx.function_name External tops,
          tx.function_name, args, [], ret, fbody)) =
      (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
       rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) ==>
    frame_ret_ok_ptr NONE unit.cu_context [] func
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (\v es gt r. T) cenv ret
Proof
  rpt gen_tac >> strip_tac >> rw[frame_ret_ok_ptr_def] >>
  drule_all external_frame_control_metadata >> strip_tac >>
  Cases_on `eo`
  >- (irule external_return_none_stmt_frag_ptr >> simp[] >> metis_tac[]) >>
  Cases_on `is_word_type ret`
  >- (`~cenv'.ce_raw_return` by
        (strip_tac >>
         `lookup_raw_return_or_F (NONE : num option) tx.function_name External tops` by metis_tac[] >>
         drule_all source_typing_raw_return_type >> strip_tac >>
         gvs[is_word_type_def]) >>
      irule external_return_word_frame_stmt_frag_ptr >> simp[] >>
      qexists_tac `env'` >> simp[] >> metis_tac[]) >>
  Cases_on `cenv'.ce_raw_return`
  >- (`lookup_raw_return_or_F (NONE : num option) tx.function_name External tops` by metis_tac[] >>
      drule_all source_typing_raw_return_type >> strip_tac >> gvs[] >>
      irule external_return_raw_frame_stmt_frag_ptr >> simp[] >>
      reverse conj_tac >- (qexists_tac `env'` >> simp[]) >>
      drule typed_dynamic_bytes_return_source >> strip_tac >>
      irule typed_lowered_value_bytestring >> simp[] >>
      qexists_tac `env'` >> simp[] >>
      rpt strip_tac >> irule external_frame_signature_return_map >>
      goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >>
      metis_tac[]) >>
  drule_all external_frame_runtime_flags >> strip_tac >>
  Cases_on `?n. ret = BaseT (BytesT (Dynamic n))`
  >- (gvs[] >>
      drule_all source_external_return_contract >> strip_tac >>
      drule source_typing_distinct_type_keys >> strip_tac >>
      irule external_return_singleton_bytes_frame_stmt_frag_ptr >> simp[] >>
      conj_tac
      >- (drule typed_dynamic_bytes_return_source >> strip_tac >>
          irule typed_lowered_value_bytestring >> simp[] >>
          qexists_tac `env'` >> simp[] >>
          rpt strip_tac >> irule external_frame_signature_return_map >>
          goal_assum (drule_at Any) >>
          goal_assum (drule_at Any) >>
          goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      reverse conj_tac >- (qexists_tac `env'` >> simp[]) >>
      goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `?n. ret = BaseT (StringT n)`
  >- (gvs[] >>
      drule_all source_external_return_contract >> strip_tac >>
      drule source_typing_distinct_type_keys >> strip_tac >>
      irule external_return_singleton_string_frame_stmt_frag_ptr >> simp[] >>
      conj_tac
      >- (drule typed_string_return_source >> strip_tac >>
          irule typed_lowered_value_bytestring >> simp[is_bytestring_type_def] >>
          qexists_tac `env'` >> simp[] >>
          rpt strip_tac >> irule external_frame_signature_return_map >>
          goal_assum (drule_at Any) >>
          goal_assum (drule_at Any) >>
          goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      reverse conj_tac >- (qexists_tac `env'` >> simp[]) >>
      goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `~is_abi_dynamic cenv'.ce_struct_fields ret`
  >- (drule_all source_external_return_contract >> strip_tac >>
      `?tv. evaluate_type (type_env tops) ret = SOME tv` by
        fs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
      drule source_deployment_context >> strip_tac >>
      `expr_type x = ret` by
        (drule_all typed_abi_static_return_annotation >> simp[]) >>
      `well_typed_expr env' x /\ expr_type x <> NoneT` by
        fs[typedCopyPtrTheory.type_stmt_return_some_iff] >>
      `ret <> NoneT` by metis_tac[] >>
      `lowered_value_type cenv' x = ret` by
        (irule external_frame_typed_static_lowered_return >>
         goal_assum (drule_at Any) >>
         goal_assum (drule_at Any) >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      irule external_frame_evaluated_static_stmt_frag_ptr >> simp[] >>
      conj_tac >- fs[int_calls_stmt_def, int_calls_expr_def] >>
      reverse conj_tac >- (qexists_tac `env'` >> simp[]) >>
      goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  Cases_on `assignable_type (type_env tops) ret /\
            (?m. cenv'.ce_ret_enc_info = AbiCopy m) /\
            expr_type x = ret /\ lowered_value_type cenv' x = ret`
  >- (gvs[] >>
      drule source_deployment_context >> strip_tac >>
      `well_typed_expr env' x /\ expr_type x <> NoneT` by
        fs[typedCopyPtrTheory.type_stmt_return_some_iff] >>
      irule external_frame_equal_static_copy_stmt_frag_ptr_bounded >> simp[] >>
      conj_tac >- fs[int_calls_stmt_def, int_calls_expr_def] >>
      reverse conj_tac >- (qexists_tac `env'` >> simp[]) >>
      goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  cheat
QED
