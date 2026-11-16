(* Body boundaries for aggregate storage Append. *)
Theory bodyMemAppendAggregateFacts
Ancestors
  bodyAppendStorageAdapter bodyAppendStorageFacts bodyMemAssignTopCopyFacts
  supportedStmts supportedExprs loweringPosts exprSimMemDefs
  valueEncodingProps vyperAST bodySim bodyStorageMetadata supportedProgram
  supportedDecls supportedTypes compileEnv exprSimHyps whitelistVisibility
  vyperValue vyperTypeValues
  bodyAppendStorageLayoutFacts

Theorem append_pure_post_type:
  supported_pure_expr tops e ==> post_value_type cenv e = expr_type e
Proof
  strip_tac >> irule post_value_type_not_int_call >>
  rpt strip_tac >> gvs[supported_pure_expr_def]
QED

Theorem append_aggregate_rhs_memory:
  supported_pure_expr tops e /\
  expr_post H ctx func cenv cx e es sa sm s0 es1 v op s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  expr_store_bound cx (expr_type e) v op s ==>
  ?w. eval_operand op s = SOME w /\
    val_in_memory tv v (w2n w) s.vs_memory /\
    (type_slot_size tv = 0 \/
     w2n w + 32 * type_slot_size tv <= s.vs_alloca_next)
Proof
  strip_tac >> drule append_pure_post_type >> strip_tac >>
  `expr_val_rel cx (expr_type e) v op s` by fs[expr_post_def] >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  simp[expr_val_rel_def] >> strip_tac >>
  qexists_tac `w` >> simp[] >>
  drule_all topcopy_val_store_size >> strip_tac >>
  gvs[expr_store_bound_def, type_memory_size_slots]
QED
