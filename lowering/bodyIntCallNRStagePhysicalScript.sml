(* Physical tags at the interleaved staging boundary. *)
Theory bodyIntCallNRStagePhysical
Ancestors
  bodyIntCallCompilerTags exprSimHyps exprLowering loweringPosts compileEnv context

Theorem intcall_stage_internal_call_tag:
  vv_type (FST (compile_call cfn ce rty ty (IntCall fid) args drv st)) =
    ce.ce_func_return_type (nsid_to_string fid)
Proof
  simp[compile_call_def, pairTheory.ELIM_UNCURRY, vv_type_def] >>
  rpt (pairarg_tac >> simp[]) >>
  rpt IF_CASES_TAC >> simp[vv_type_def, pairTheory.ELIM_UNCURRY] >>
  rpt (pairarg_tac >> simp[vv_type_def]) >>
  Cases_on `return_buf` >> simp[vv_type_def, pairTheory.ELIM_UNCURRY]
QED

Theorem intcall_stage_pop_tag:
  vv_type (FST (compile_expr ce ty (Pop ann target) st)) = ann
Proof
  once_rewrite_tac[compile_expr_raw_def] >>
  simp[compile_expr_body_def, pairTheory.ELIM_UNCURRY, vv_type_def,
       vyperASTTheory.expr_type_def]
QED

Theorem intcall_stage_intcall_tag:
  vv_type (FST (compile_expr ce ty (Call ann (IntCall fid) args drv) st)) =
    lowered_value_type ce (Call ann (IntCall fid) args drv)
Proof
  once_rewrite_tac[compile_expr_raw_def] >>
  simp[compile_expr_body_def, intcall_stage_internal_call_tag,
       lowered_value_type_def]
QED

Theorem intcall_stage_external_call_tag:
  (!fid. target <> IntCall fid) ==>
  vv_type (FST (compile_call cfn ce ann ty target args drv st)) = ann
Proof
  strip_tac >> Cases_on `target` >>
  gvs[compile_call_def, pairTheory.ELIM_UNCURRY, vv_type_def]
  >~ [`compile_call _ _ _ _ (ExtCall _ _ triple _) _ _ _`]
  >- (PairCases_on `triple` >>
      simp[compile_call_def, pairTheory.ELIM_UNCURRY, vv_type_def] >>
      rpt (IF_CASES_TAC >> simp[pairTheory.ELIM_UNCURRY, vv_type_def]) >>
      rpt (CASE_TAC >> simp[pairTheory.ELIM_UNCURRY, vv_type_def])) >>
  rpt (IF_CASES_TAC >> simp[pairTheory.ELIM_UNCURRY, vv_type_def]) >>
  rpt (CASE_TAC >> simp[pairTheory.ELIM_UNCURRY, vv_type_def])
QED

(* Effectful children do not alter an enclosing non-call's physical tag.
   Internal calls are the sole exception: they use the callee's layout. *)
Theorem intcall_stage_physical_type:
  vv_type (FST (compile_expr ce ty e st)) =
    (case e of Call ann (IntCall fid) args drv =>
       ce.ce_func_return_type (nsid_to_string fid)
     | _ => expr_type e)
Proof
  Cases_on `expr_effect_root e`
  >- (Cases_on `e` >>
      gvs[supportedExprTraverseTheory.expr_effect_root_def,
          intcall_stage_pop_tag, vyperASTTheory.expr_type_def] >>
      rename1 `Call ann target args drv` >> Cases_on `target` >>
      simp[intcall_stage_intcall_tag, lowered_value_type_def] >>
      once_rewrite_tac[compile_expr_raw_def] >>
      simp[compile_expr_body_def, vyperASTTheory.expr_type_def] >>
      irule intcall_stage_external_call_tag >> simp[]) >>
  `vv_type (FST (compile_expr ce ty e st)) = expr_type e` by
    (once_rewrite_tac[compile_expr_raw_def] >>
     irule intcall_expr_body_tag >> simp[] >> conj_tac >> rpt gen_tac >>
     IF_CASES_TAC >>
     simp[exprCallBoundsTheory.invalid_expr_call_def, vv_type_def] >>
     once_rewrite_tac[compile_expr_raw_def] >>
     simp[intcall_builtin_dispatch_body_tag, intcall_type_dispatch_body_tag,
          pairTheory.ELIM_UNCURRY, vv_type_def]) >>
  Cases_on `e` >>
  gvs[supportedExprTraverseTheory.expr_effect_root_def]
QED

Theorem intcall_stage_aggregate_physical_type:
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  compile_expr ce ty e sa = (vv,sb) ==>
  vv_type vv = post_value_type ce e
Proof
  strip_tac >>
  mp_tac (Q.INST [`st` |-> `sa`] intcall_stage_physical_type) >>
  simp[] >> Cases_on `e` >>
  gvs[post_value_type_def, vyperASTTheory.expr_type_def] >>
  rename1 `Call ann target args drv` >> Cases_on `target` >>
  gvs[post_value_type_def, lowered_value_type_def, vyperASTTheory.expr_type_def]
QED

(* Head-premise provenance (no additional caller invariant).
   - Semantic source/destination typing and widening: NRStageTypes exports
     intcall_stage_declared_layout/word/bytes, using expr_body_pre and the
     well-typed call's parameter widening.
   - Source forcing capacity: aggregateEvaluatedLayout's public
     body_post_type_allocation_bound, not expr_body_pre_copy_ok at the
     annotation (an internal call may return a smaller physical aggregate).
     Destination capacity: intcall_stage_declared_capacity at the callee's
     FunctionDecl.  MAX 32 preserves the allocation limit.
   - Unequal aggregate metadata: acyclic_struct_metadata is in body_inv;
     sfields_tenv_consistent and field distinctness/sizes are in expr_sim_inv,
     obtained from expr_body_pre.  expr_sim_inv_memory_size supplies the
     universal evaluated-size equation.  These facts concern ce/cx and are
     independent of the moving source evaluation state.
   - Only the aggregate branch passes vv_type to compile_store_memory.
     A word destination emits MSTORE directly; a bytes destination uses
     compile_store_bytestring directly.  Their semantic representations use
     intcall_stage_declared_word/bytes, not equality of physical and post tags.
   - Source memory bounds/ownership are producer outputs.  Allocation and
     forcing transport them; disjointness from the new destination and from
     old snapshots remains a runtime head-execution obligation, not a type
     fact.  NRStageFragments exports the guarded allocation/forcing frames.
*)
