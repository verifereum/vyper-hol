(* Source invariant landing shared by both nonlocal AugAssign backends. *)
Theory bodyIntCallFamStmtMutationAugPlaceSourceLanding
Ancestors
  bodyExprPreFacts loweringPosts stmtLowering compileEnv vyperTypeCallGraph

Theorem intcall_aug_place_source_landing:
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  supported_stmt tops bindings (AugAssign ty bt bop e) /\
  expr_sim_inv ce cx env es /\ ce.ce_alloca_locals /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign ty bt bop e)) /\
  eval_stmt cx (AugAssign ty bt bop e) es = (INL (),ff) ==>
  expr_sim_inv ce cx env ff
Proof
  strip_tac >>
  `?unit sb. compile_stmt ce lctx ret_ty (AugAssign ty bt bop e) sa = (unit,sb)` by
    metis_tac[pairTheory.PAIR] >>
  `stmt_env ce lctx ret_ty (AugAssign ty bt bop e) sa = (ce,sb)` by
    simp[stmt_env_def,declare_stmt_local_def,comp_bind_def,comp_return_def,
         comp_ignore_bind_def] >>
  drule_all expr_sim_inv_stmt >> simp[]
QED
