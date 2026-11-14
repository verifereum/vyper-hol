(* Internal-call tuple producer checkpoint.  Metadata selection is separated
   from runtime allocation ownership: the latter is not an expr_post fact. *)
Theory tupleAssignImmutableDeployIntCallBoundary
Ancestors
  bodySim bodyIntCallSource internalReturnMetadata
  externalReturnIntcallProducer typedMemoryCopy
  exprSimHypsDefs vyperTypeInvariants vyperTypeSystem
  supportedDecls supportedProgram memoryLocalRhsProps supportedNames intCallStep intCallFrame
  intCallResult intCallReturnMem compileEnv

Theorem tuple_immutable_intcall_decl[local]:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es /\
  well_typed_expr env (Call (TupleT tys) (IntCall (NONE,name)) xs NONE) /\
  IS_SOME (supported_function_decl tops (NONE,name) Internal) ==>
  ?mut nr rr args dflts ret body.
    supported_function_decl tops (NONE,name) Internal =
      SOME (mut,nr,rr,args,dflts,ret,body) /\
    type_widens_to env.type_defs ret (TupleT tys)
Proof
  strip_tac >>
  `fn_sigs_consistent env.fn_sigs cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  drule_all typed_intcall_source_signature >> strip_tac >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops` by
    fs[body_inv_def] >>
  gvs[] >> drule_all supported_internal_callable >> strip_tac >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `supported_function_decl tops (NONE,name) Internal = SOME decl` >>
  PairCases_on `decl` >>
  drule supported_internal_lookup >> strip_tac >>
  gvs[vyperInterpreterTheory.lookup_callable_function_def] >>
  metis_tac[]
QED

Theorem tuple_immutable_intcall_metadata:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es /\
  well_typed_expr env (Call (TupleT tys) (IntCall (NONE,name)) xs NONE) /\
  IS_SOME (supported_function_decl tops (NONE,name) Internal) ==>
  ?stys ats.
    ce.ce_func_return_type (nsid_to_string (NONE,name)) = TupleT stys /\
    type_widens_to env.type_defs (TupleT stys) (TupleT tys) /\
    ce.ce_func_info (nsid_to_string (NONE,name)) =
      compute_func_info (\n. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields n))
        (TupleT stys) (type_memory_bytes ce (TupleT stys)) ats
Proof
  strip_tac >> drule_all tuple_immutable_intcall_decl >> strip_tac >>
  drule typed_copy_tuple_widening >> strip_tac >> gvs[] >>
  `ce.ce_func_info = build_func_info (get_struct_fields (make_struct_fields_map tops)) tops /\
   ce.ce_struct_fields = make_struct_fields_map tops /\ supported_program tops` by
    fs[body_inv_def] >>
  drule_all supported_internal_call_info >> strip_tac >>
  `ce.ce_func_return_type (nsid_to_string (NONE,name)) = TupleT stys` by
    (drule supported_internal_function_lookup >> strip_tac >>
     `ALL_DISTINCT (supported_function_names tops)` by
       metis_tac[supported_program_names, supported_declaration_names_unique] >>
     drule_at (Pos last) memoryLocalRhsPropsTheory.build_func_return_type_distinct >>
     fs[body_inv_def, nsid_to_string_def]) >>
  qexistsl_tac [`stys`,`MAP SND args`] >> simp[]
QED

(* Zero-sized declared tuples need not allocate; positive declared layouts
   cannot take compile_call's bufferless result branch. *)
Theorem tuple_immutable_intcall_buffer_selection[local]:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es /\
  well_typed_expr env (Call (TupleT tys) (IntCall (NONE,name)) xs NONE) /\
  IS_SOME (supported_function_decl tops (NONE,name) Internal) /\
  compile_expr ce ct (Call (TupleT tys) (IntCall (NONE,name)) xs NONE) sa = (vv,sb) ==>
  ?stys. ce.ce_func_return_type (nsid_to_string (NONE,name)) = TupleT stys /\
    type_widens_to env.type_defs (TupleT stys) (TupleT tys) /\
    (type_memory_bytes ce (TupleT stys) = 0 \/
     ?p. vv = LocatedValue (TupleT stys) p /\ p.ptr_location = LocMemory)
Proof
  strip_tac >> drule_all tuple_immutable_intcall_metadata >> strip_tac >>
  qexists_tac `stys` >> simp[] >>
  Cases_on `type_memory_bytes ce (TupleT stys) = 0` >> simp[] >>
  drule return_compile_intcall_output >> strip_tac >> gvs[] >>
  fs[compute_func_info_def, AllCaseEqs()]
QED

Theorem tuple_immutable_intcall_caller_selection:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es /\
  supported_stmt tops bindings
    (Assign (TupleTarget gs) (Call (TupleT tys) (IntCall (NONE,name)) xs NONE)) /\
  type_stmt env ret_ty
    (Assign (TupleTarget gs) (Call (TupleT tys) (IntCall (NONE,name)) xs NONE)) = SOME env' /\
  compile_expr ce ct (Call (TupleT tys) (IntCall (NONE,name)) xs NONE) sa = (vv,sb) ==>
  ?stys. ce.ce_func_return_type (nsid_to_string (NONE,name)) = TupleT stys /\
    type_widens_to env.type_defs (TupleT stys) (TupleT tys) /\
    (type_memory_bytes ce (TupleT stys) = 0 \/
     ?p. vv = LocatedValue (TupleT stys) p /\ p.ptr_location = LocMemory)
Proof
  strip_tac >> irule tuple_immutable_intcall_buffer_selection >>
  `well_typed_expr env (Call (TupleT tys) (IntCall (NONE,name)) xs NONE)` by
    gvs[Once type_stmt_def, AllCaseEqs()] >>
  `IS_SOME (supported_function_decl tops (NONE,name) Internal)` by
    gvs[supportedStmtsTheory.supported_stmt_def,
        supportedStmtsTheory.supported_assignment_def,
        supportedExprsTheory.supported_expr_def,
        supportedExprsTheory.supported_pure_expr_def,
        supportedExprsTheory.supported_effect_expr_def] >>
  metis_tac[]
QED

(* Caller/producer ledger (not a proof of owned pending tuple storage).

   DISCHARGED: body_inv supplies function-info and struct metadata maps and
   the single source module. expr_sim_inv supplies fn_sigs_consistent and
   declared return agreement; assignment typing supplies well_typed_expr.
   supported_stmt supplies the internal declaration. The checked selection
   above combines these to exclude a bufferless *positive physical layout*.
   The declared layout is TupleT stys, possibly narrower than the annotation;
   its empty case must not be replaced by an annotation-size assertion.

   REUSE for the compiler prefix: intCallStep.compile_call_intcall_shape
   identifies compile_multi_vvs, compile_alloc_buffer (32*ret_count or rbs),
   compile_stage_intcall_args, INVOKE, and (for stack returns)
   store_multi_results. Its output is base_ptr of exactly that return buffer,
   not an arbitrary callee pointer. No call-safety proof is duplicated here.

   RUNTIME AUDIT: loweringHalt.compile_alloc_buffer_fresh_frag establishes
   the new allocation at the buffer point. intCallFrame.invoke_return_frame
   preserves the caller's allocation map and frontier across INVOKE, but
   takes memory from the callee. Thus allocation persistence alone is not
   byte preservation. intCallReturnMem.intret_mem_q supplies val_in_memory
   at a memory return; intCallResult.store_multi_results_frag supplies the
   stack-return representation. Neither is a producer theorem carrying the
   fresh buffer's interval through argument staging, INVOKE and final stores.

   STILL REQUIRED: from actual successful compile_expr execution, retain the
   allocation id created after argument evaluation, sa.cs_next_id <= aid <
   sb.cs_next_id, final eval_operand/base pointer identity, containment of the
   complete *declared* tuple envelope, and separation from final local_region
   entries. Connect allocation runtime/capacity and callee return hypotheses
   to the frozen caller and gas prefix; call_evaluation_safe alone is not an
   allocation geometry contract. The required zero-size disjunct is physical
   layout size zero. Same-layout expr_post/vv_post ownership is conditional
   and does not discharge this missing producer interface. No counterexample
   to the frozen theorem or external missing premise has been established.
*)
