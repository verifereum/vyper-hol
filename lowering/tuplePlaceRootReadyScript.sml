(* Frozen-root premise adapters for arbitrary-place tuple assignment. *)
Theory tuplePlaceRootReady
Ancestors
  tuplePlaceBounds tuplePlaceReachable tuplePlaceRhsCert exprSimHyps
  exprSimSource exprSimHypsDefs vyperTypeExprSoundness
  vyperTypeEvalSoundness allocLimits list
Libs
  monadsyntax

Theorem tuple_place_root_static_ready:
  expr_body_pre cenv cx env e es /\ expr_type e = TupleT tys /\
  EVERY (\g. ?bt. g = BaseTarget bt /\ supported_target_pure tops bt /\
    target_case F ctx func cenv cx bt /\ ~immutable_root cx bt /\
    target_indices_pre cenv cx env bt) gs ==>
  type_alloc_ok cenv (TupleT tys) /\
  EVERY (\g. ?bt. g = BaseTarget bt /\ supported_target_pure tops bt /\
    target_case F ctx func cenv cx bt /\ ~immutable_root cx bt /\
    target_indices_pre cenv cx env bt /\
    call_evaluation_safe cx (int_calls_target bt)) gs
Proof
  strip_tac >> conj_tac
  >- (fs[expr_body_pre_def] >>
      drule alloc_limits_expr_type_alloc_ok >> simp[]) >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexists `bt` >> simp[] >>
  metis_tac[tuple_place_rhs_target_call_safe]
QED

Theorem tuple_place_root_layout_ready:
  expr_sim_inv cenv cx env es /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) ==>
  LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) ltys ltvs
Proof
  strip_tac >>
  fs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  drule vyperTypeABITheory.evaluate_types_LIST_REL >>
  simp[LIST_REL_EL_EQN] >> strip_tac >> simp[] >>
  rpt strip_tac >> irule expr_sim_inv_memory_size >> metis_tac[]
QED

Theorem tuple_place_root_rhs_ready:
  expr_body_pre cenv cx env e es /\
  expr_type e = TupleT tys /\ lowered_value_type cenv e = TupleT ltys /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) ==>
  expr_sim_inv cenv cx env (ee with gas_obs := []) /\
  ?vs. v = ArrayV (TupleV vs) /\
    value_has_type (TupleTV ltvs) (ArrayV (TupleV vs))
Proof
  strip_tac >>
  drule_all expr_body_pre_eval >> strip_tac >>
  drule_all memory_rhs_read_post_typed >>
  `post_value_type cenv e = TupleT ltys` by
    metis_tac[tuple_place_post_tuple_type] >>
  simp[value_runtime_typed_def] >> strip_tac >>
  `env.type_defs = get_tenv cx` by fs[expr_sim_inv_def,
    vyperTypeInvariantsTheory.env_consistent_def,
    vyperTypeInvariantsTheory.env_context_consistent_def] >>
  gvs[] >>
  drule_all stmtSimReturnTheory.tuple_type_value >>
  strip_tac >> gvs[]
QED
