(* Captured source reads across effect-free operand suffixes. *)
Theory exprExtRequestSuffix
Ancestors
  exprExtRequestSourceFrame exprExtRequestSourceProbe exprExtRequestReadProbe
  exprExtRequestDelayed vyperCallOutcomeFrame vyperState
  supportedExprTraverse vyperInterpreter loweringPosts exprSimProps
  compileEnv accountsRelProps exprLoweringProps vyperStorageBackend
  vyperStatePreservation

Theorem extrequest_read_after_pure_expr:
  ~expr_has_effect e /\ eval_expr cx e es = (res,ee) ==>
  read_result cx captured ee = (FST (read_result cx captured es),ee)
Proof
  strip_tac >> irule extrequest_read_result_frame >>
  drule extrequest_pure_expr_read_frame >>
  simp[state_rel_frame_result] >> metis_tac[]
QED

Theorem extrequest_read_after_pure_exprs:
  EVERY (\e. ~expr_has_effect e) es /\ eval_exprs cx es s = (res,t) ==>
  read_result cx captured t = (FST (read_result cx captured s),t)
Proof
  strip_tac >> irule extrequest_read_result_frame >>
  drule extrequest_pure_exprs_read_frame >>
  simp[state_rel_frame_result] >> metis_tac[]
QED

Theorem extrequest_read_after_pure_results:
  EVERY (\e. ~expr_has_effect e) es /\ eval_expr_results cx es s = (res,t) ==>
  read_result cx captured t = (FST (read_result cx captured s),t)
Proof
  strip_tac >> irule extrequest_read_result_frame >>
  drule extrequest_pure_results_read_frame >>
  simp[state_rel_frame_result] >> metis_tac[]
QED

Theorem extrequest_read_results_frame:
  !captured. extrequest_read_frame cx s t ==>
  read_results cx captured t = (FST (read_results cx captured s),t)
Proof
  Induct >> simp[read_results_def, return_def] >> rpt strip_tac >>
  drule extrequest_read_result_frame >>
  disch_then (qspec_then `h` mp_tac) >>
  Cases_on `read_result cx h s` >> Cases_on `q` >> simp[bind_def] >>
  strip_tac >>
  `r = s` by metis_tac[read_result_state] >> gvs[] >>
  qmatch_goalsub_abbrev_tac `read_results cx captured start` >>
  Cases_on `read_results cx captured start` >> Cases_on `q` >>
  simp[bind_def, return_def]
QED

Theorem extrequest_reads_after_pure_exprs:
  EVERY (\e. ~expr_has_effect e) es /\ eval_exprs cx es s = (res,t) ==>
  read_results cx captured t = (FST (read_results cx captured s),t)
Proof
  strip_tac >> irule extrequest_read_results_frame >>
  drule extrequest_pure_exprs_read_frame >>
  simp[state_rel_frame_result] >> metis_tac[]
QED

Theorem extrequest_memory_holds_kept:
  vv_at cenv cx ty sa sm ee captured (LocatedValue ty p) s0 /\
  vv_holds cenv cx ty captured (LocatedValue ty p) ee s0 /\
  p.ptr_location = LocMemory /\
  read_result cx captured ee = (INL v,ee) /\
  extrequest_read_frame cx ee ee' /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  eval_operand p.ptr_operand s0 = SOME w /\
  eval_operand p.ptr_operand s = SOME w /\
  vv_post ctx func cenv cx e ee sm sn s0 ee' result' vv s /\
  (!n b sz. local_region cenv ee.scopes s0 n b sz ==>
    mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory) ==>
  vv_holds cenv cx ty captured (LocatedValue ty p) ee' s
Proof
  strip_tac >>
  `val_in_memory tv v (w2n w) s.vs_memory` by
    (irule extrequest_memory_read_kept >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `read_result cx captured ee' = (INL v,ee')` by
    (drule extrequest_read_result_frame >> simp[]) >>
  simp[vv_holds_def] >>
  metis_tac[val_in_memory_word_type]
QED

Theorem extrequest_storage_projection_kept:
  extrequest_read_frame cx es ee ==>
  get_storage cx es tr = get_storage cx ee tr
Proof
  Cases_on `tr` >>
  simp[extrequest_read_frame_def, get_storage_def,
       vfmExecutionTheory.lookup_transient_storage_def,
       vfmStateTheory.lookup_account_def]
QED

Theorem extrequest_storage_holds_kept:
  storage_holds cx tr ty captured w es s0 /\
  extrequest_read_frame cx es ee /\
  stmt_state_rel ctx func cenv cx ee s /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    storage_read_live cx tr (get_storage cx es tr) w tv) ==>
  storage_holds cx tr ty captured w ee s
Proof
  strip_tac >>
  `get_storage cx es tr = get_storage cx ee tr` by
    metis_tac[extrequest_storage_projection_kept] >>
  gvs[storage_holds_def] >>
  `read_result cx captured ee = (INL v,ee)` by
    (drule extrequest_read_result_frame >> simp[]) >>
  `read_result cx (PlaceR (StoragePlace tr w tvt)) ee = (INL v,ee)` by
    (drule extrequest_read_result_frame >>
     disch_then (qspec_then `PlaceR (StoragePlace tr w tvt)` mp_tac) >>
     simp[read_result_def, read_place_def]) >>
  simp[] >> conj_tac
  >- gvs[read_result_def, read_place_def] >>
  irule storage_range_agree_of_live >>
  conj_tac >- gvs[storage_range_agree_def] >>
  qexistsl_tac [`cx`, `tr`] >> simp[] >>
  Cases_on `tr` >>
  gvs[stmt_state_rel_def, state_rel_def, storage_rel_def,
      transient_rel_def, get_storage_def,
      vfmStateTheory.lookup_account_def]
QED
