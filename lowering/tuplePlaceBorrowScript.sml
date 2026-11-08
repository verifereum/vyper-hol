(* Borrowed tuple bytes: pointer evaluation is distinct from writes. *)
Theory tuplePlaceBorrow
Ancestors
  tuplePlaceSnapshot tuplePlaceSource supportedTargets bodySimAugPlaceScopes
  vyperPlaceFrames vyperInterpreter vyperState vyperMisc vyperValue
  vyperScopePreservation vyperPlaceStatePreservation exprSimSource loweringPosts

Theorem tuple_place_pure_target_scopes:
  !bt tops cx es res ee.
    supported_target_pure tops bt /\
    eval_base_place cx bt es = (res,ee) ==> ee.scopes = es.scopes
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >> rpt gen_tac
  >- (simp[Once evaluate_def, get_scopes_def, bind_def, ignore_bind_def,
           type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >- (PairCases_on `p` >> simp[Once evaluate_def] >>
      metis_tac[lookup_global_scopes])
  >- (qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
      simp[vyperASTTheory.expr_size_def] >> strip_tac >> rpt strip_tac >>
      qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      strip_tac >> gvs[supported_target_pure_def] >>
      imp_res_tac read_result_state >> imp_res_tac extend_place_state >>
      imp_res_tac aug_place_pure_expr_scopes >> gvs[] >> metis_tac[])
  >> (qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
      simp[vyperASTTheory.expr_size_def] >> strip_tac >> rpt strip_tac >>
      qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      strip_tac >> gvs[supported_target_pure_def] >>
      imp_res_tac extend_place_state >> gvs[] >> metis_tac[])
QED

Theorem tuple_place_pure_target_borrow_bytes:
  supported_target_pure tops bt /\
  eval_base_place cx bt es = (res,ee) /\
  target_post ctx func cenv cx es sa sb s0 ee pv vt r s /\
  local_region cenv es.scopes s0 n b sz ==>
  mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory
Proof
  rpt strip_tac >>
  drule_all tuple_place_pure_target_scopes >> strip_tac >>
  irule tuple_place_target_unchanged_local >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem tuple_place_borrowed_tuple_path:
  local_val_at cenv cx n k (TupleTV tvs) (ArrayV (TupleV vs)) ==>
  local_path_at cenv cx n k (TupleTV tvs)
Proof
  simp[local_val_at_def]
QED
