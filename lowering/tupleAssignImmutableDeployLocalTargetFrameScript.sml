(* Target evaluation preserves borrowed local bytes, including effectful
   supported subscript keys. This boundary says nothing about earlier stores. *)
Theory tupleAssignImmutableDeployLocalTargetFrame
Ancestors
  tuplePlaceSnapshot tuplePlaceBorrow bodySimAugPlaceScopes supportedStmts
  vyperInterpreter vyperState vyperMisc vyperValue vyperPlaceStatePreservation
  valueEncodingProps vyperPlaceFrames vyperScopePreservation

Theorem tuple_immutable_local_target_pending:
  target_post ctx func cenv cx es sa sb s0 ee pv vt r s /\
  ee.scopes = es.scopes /\
  local_region cenv es.scopes s0 n b sz /\
  b <= a /\ a + type_memory_size tv <= b + sz /\
  val_wf tv v /\ val_in_memory tv v a s0.vs_memory ==>
  val_in_memory tv v a s.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory` by
    (irule tuple_place_target_unchanged_local >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule val_in_memory_mem_agree >> conj_tac >- simp[] >>
  qexistsl [`type_memory_size tv`, `s0.vs_memory`] >> simp[] >>
  drule mem_bytes_at_translated_window >>
  disch_then (qspecl_then [`a - b`, `type_memory_size tv`] mp_tac) >> simp[]
QED

Theorem tuple_immutable_supported_target_scopes:
  !bt tops bindings cx es res ee.
    supported_target tops bindings bt /\
    eval_base_place cx bt es = (res,ee) ==> ee.scopes = es.scopes
Proof
  Cases_on `bt` >> rpt gen_tac
  >- (simp[Once evaluate_def, get_scopes_def, bind_def, ignore_bind_def,
           type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >- (PairCases_on `p` >> simp[Once evaluate_def] >>
      metis_tac[lookup_global_scopes])
  >- (Cases_on `b` >> simp[supported_target_def] >> rpt strip_tac >>
      qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      strip_tac >>
      imp_res_tac read_result_state >> imp_res_tac extend_place_state >>
      imp_res_tac aug_place_supported_expr_scopes >>
      PairCases_on `p` >> gvs[Once evaluate_def] >>
      metis_tac[lookup_global_scopes])
  >> (Cases_on `b` >> simp[supported_target_def] >> rpt strip_tac >>
      qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      strip_tac >> imp_res_tac extend_place_state >>
      PairCases_on `p` >> gvs[Once evaluate_def] >>
      metis_tac[lookup_global_scopes])
QED

(* Caller discharge ledger (target evaluation only).
   supported_stmt ... (Assign (TupleTarget gs) e), through
   supported_stmt_def and supported_assignment_def, gives supported_target
   for every BaseTarget in gs. The source step supplies eval_base_place.
   Thus tuple_immutable_supported_target_scopes needs neither key purity nor
   an exclusion of internal calls: supported_expr is enough for each key.

   tuple_immutable_local_target_pending takes target_post from the target
   simulation; the preceding source boundary supplies its exact scope equality.
   local_region, containment, val_wf and the initial val_in_memory still have
   to be supplied by a local-backed RHS snapshot at the actual target entry.
   This theorem does NOT establish those facts for every RHS producer, and
   does NOT transport the snapshot across any preceding element stores.
   In particular unchanged scope domains alone would not prove this frame. *)
