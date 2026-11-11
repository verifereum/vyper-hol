(*
 * Seam of bodyPtrStructLit: a struct literal every element of which has
 * its post at its annotated type (no widened internal-call element).
 *
 * TOP-LEVEL:
 *   body_struct_lit_uniform_ptr
 *)
Theory bodyPtrStructLitSeamUniform
Ancestors
  bodyPtrStructLitUniformAllocated bodyPtrStructLitUniformFinalEndpoint
  bodyPtrMakeArrayConsInvariant bodyPtrMakeArrayAllocBuffer
  exprSimAggregateLayout exprSimAggregateSource gasSummaryComposePtr argsTailPtr
  exprSimHypsDefs allocLimits loweringPosts compileEnv exprLowering vyperTypeSystem
  bodyPtrStructLitCallPath bodyPtrStructLitCompiledContext
  bodyPtrStructLitCopyPath bodyPtrStructLitCreationFrames
  bodyPtrStructLitEmpty bodyPtrStructLitEndpointAllocation
  bodyPtrStructLitEntryStoreFrame bodyPtrStructLitIdentityRead
  bodyPtrStructLitInvoke bodyPtrStructLitLayoutTransfer
  bodyPtrStructLitOldWordFrame bodyPtrStructLitOwnershipAbiWrappers
  bodyPtrStructLitOwnershipBuiltinBody
  bodyPtrStructLitOwnershipConstructorEntry
  bodyPtrStructLitOwnershipConstructorTail
  bodyPtrStructLitOwnershipDeclarationRoute bodyPtrStructLitOwnershipDispatch
  bodyPtrStructLitOwnershipEntryPc bodyPtrStructLitOwnershipExprBody
  bodyPtrStructLitOwnershipExtraction bodyPtrStructLitOwnershipInitial
  bodyPtrStructLitOwnershipModuleEntry bodyPtrStructLitOwnershipRestrictions
  bodyPtrStructLitOwnershipSelectedPackages bodyPtrStructLitOwnershipStmtLoops
  bodyPtrStructLitOwnershipStructLoop bodyPtrStructLitOwnershipTypeCases
  bodyPtrStructLitPathBoundary bodyPtrStructLitPhaseInvariant
  bodyPtrStructLitRequestFrame bodyPtrStructLitResourceHandoff
  bodyPtrStructLitReturnBoundary bodyPtrStructLitReturnCertificate
  bodyPtrStructLitReturnShape bodyPtrStructLitRobustOldBuffer
  bodyPtrStructLitStagingWrites bodyPtrStructLitTupleFrame
  bodyPtrStructLitUnwrapFrame bodyPtrStructLitUnwrapSeparation
  bodyPtrStructLitWordCapacity bodyPtrStructLitWordStoreHandoff
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

(* A struct literal lowers like a tuple literal (bodyPtrMakeArray's
   literal_tuple_vv_sim_ptr on the s3-ptr tip): allocate the struct's
   buffer, then for each field compile the element, add the field's
   offset to the buffer and store the element's value there
   (compile_struct_lit, compile_store_memory at the element's
   lowered_value_type), and return the buffer's base pointer.
   S1's proof of the same case is exprSimAggregates' compile_struct_lit_case
   (compile_struct_lit_vv_case); the fields' expr_body_pre is
   exprSimAggregateSource's expr_body_pre_struct_field.
   S1's split there is int_calls_expr e = [] \/ lowered_value_type = expr_type
   per element; its loop uses that only to get lowered_value_type = expr_type
   \/ is_bytestring_type (expr_type e), and post_value_type = expr_type
   (exprSimAggregateLoops' aggregate_elem_lowered_type and its uses), both of
   which follow from this statement's hypothesis.
   Why it holds for the elements this adds (bytestring-typed widened calls,
   Concat/AbiEncode with calls): a bytestring field is stored by
   compile_store_bytestring, which ignores the source type and copies
   32 + ceil32(len) bytes, inside the source's ptr_mem_ok coverage and the
   field's slot (val_wf bounds len).  A non-word, non-bytestring element has
   lowered_value_type = expr_type here, so its copy is at the field's size
   and ptr_buf_ok covers the read.  The struct's own post_value_type is its
   expr_type, so its vv_post asks no vv_own; vv_storage_live is trivial for
   its LocMemory value.  Typing puts the keys in declaration order without
   duplicates, and alloc_limits_expr bounds the buffer size. *)
Theorem body_struct_lit_uniform_ptr:
  !cx v7 src_id_opt id kes d PG tops ctx func cenv env ty es.
    body_exprs_ptr_ok cx (MAP SND kes) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (StructLit v7 (src_id_opt,id) kes) es /\
    EVERY (\e. post_value_type cenv e = expr_type e) (MAP SND kes) ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es
Proof
  rpt gen_tac >> strip_tac >> rw[expr_vv_sim_ptr_def] >>
  drule compile_struct_literal_inv >> strip_tac >> gvs[] >>
  drule struct_literal_lookup_types >> strip_tac >>
  drule struct_literal_evaluated_layout >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `!e st. MEM e (MAP SND kes) /\ expr_sim_inv cenv cx env st ==>
    expr_body_pre cenv cx env e st` by metis_tac[expr_body_pre_struct_field] >>
  `v7 = StructT (src_id_opt,id)` by fs[expr_body_pre_def, well_typed_expr_def] >>
  `type_memory_size_list tvs < dimword(:256)` by
    (fs[expr_body_pre_def, alloc_limits_expr_def, type_memory_bytes_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `?root. ba.buf_operand = Var root` by metis_tac[alloc_buffer_emitted] >>
  `compile_alloc_buffer (type_memory_size_list tvs) sa = (ba,sm)` by metis_tac[] >>
  fs[EVERY_MEM] >>
  drule_at (Pat `compile_struct_lit _ _ _ _ _ _ _ = _`)
    structlit_uniform_allocated_fields_outcome_ptr >>
  simp[EVERY_MEM] >> disch_then drule_all >>
  disch_then (qspec_then `PG` strip_assume_tac) >> gvs[] >>
  dxrule structlit_uniform_outcome_source_run >> strip_tac >>
  simp[structlit_uniform_action, combinTheory.o_DEF] >>
  drule (gas_outcome_ptr_return_map
    |> Q.GEN `f` |> Q.ISPEC `\(vs : value list). Value (StructV (ZIP (MAP FST (kes : (string # expr) list),vs)))`
    |> REWRITE_RULE [GSYM boolTheory.AND_IMP_INTRO]) >>
  disch_then (match_mp_tac o BETA_RULE o SPEC_ALL) >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      drule literal_loop_frame_runtime >> strip_tac >>
      `addr < dimword(:256)` by decide_tac >>
      `LENGTH (MAP FST kes) = LENGTH tvs` by
        (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
      `eval_expr cx (StructLit (StructT (src_id_opt,id)) (src_id_opt,id) kes)
         (es with gas_obs := gs) =
         (INL (Value (StructV (ZIP (MAP FST kes,vs)))),ee)` by
        (drule aggregate_eval_struct >> simp[]) >>
      `val_wf (StructTV (ZIP (MAP FST kes,tvs))) (StructV (ZIP (MAP FST kes,vs)))` by
        (irule aggregate_materialised_child_wf >>
         goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
         simp[expr_type_def, read_result_def, return_def] >>
         goal_assum (drule_at Any) >> simp[]) >>
      drule_at (Pat `literal_loop_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
        (Q.INST [`e` |-> `StructLit (StructT (src_id_opt,id)) (src_id_opt,id) kes`]
          structlit_uniform_endpoint_posts) >>
      simp[expr_type_def, lowered_value_type_def, post_value_type_def, type_memory_bytes_def] >>
      disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >> simp[] >>
      disch_then drule_all >> disch_then (qspec_then `kes` mp_tac) >>
      strip_tac >> simp[contextTheory.base_ptr_def] >>
      irule structlit_uniform_pointer_posts_cong >>
      goal_assum (drule_at Any) >> simp[contextTheory.base_ptr_def, contextTheory.mk_ptr_def]) >>
  gen_tac >> Cases_on `rr` >> simp[]
QED
