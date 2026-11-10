(* Frame one immutable binding, rather than the whole immutable store. *)
Theory whitelistForIterImmFrame
Ancestors
  vyperBareGlobalName vyperPlaceFrames vyperState vyperTypeSystem
  stmtSimForArrayFrame vyperStatePreservation supportedExprs supportedExprForms supportedExprTraverse
  vyperTypeInvariants vyperInterpreter vyperCallOutcomeFrame vyperAST list rich_list finite_map alist
  supportedStmts supportedStmtTraverse

Theorem lookup_immutable_set_other:
  (src',name') <> (src,name) /\
  set_immutable cx src' name' tv v es = (r,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  simp[set_immutable_def, get_address_immutables_def,
       set_address_immutables_def, bind_def, lift_option_type_def,
       return_def, raise_def] >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  simp[return_def, raise_def] >>
  rpt strip_tac >> gvs[lookup_immutable_def] >>
  Cases_on `src' = src` >>
  gvs[set_source_immutables_def, get_source_immutables_def, FLOOKUP_UPDATE,
      ALOOKUP_ADELKEY]
QED

Theorem lookup_immutable_write_other:
  write_place cx p v es = (r,es') /\
  (!src' name' path. p = ImmutablePlace src' name' path ==>
                      (src',name') <> (src,name)) ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  Cases_on `p`
  >- (strip_tac >> drule write_storage_place_immutables >>
      simp[lookup_immutable_def])
  >- (strip_tac >> drule write_memory_place_immutables >>
      simp[lookup_immutable_def]) >>
  rename1 `write_place cx (ImmutablePlace other_src other_name path)` >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  simp[write_place_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def] >>
  rename1 `ALOOKUP es.immutables cx.txn.target = SOME imms` >>
  Cases_on `FLOOKUP (get_source_immutables other_src imms) other_name` >>
  simp[return_def, raise_def] >>
  rename1 `FLOOKUP _ _ = SOME tva` >>
  Cases_on `assign_subscripts (FST tva) (SND tva) path (Replace v)` >>
  simp[return_def, raise_def] >>
  rpt strip_tac >> irule lookup_immutable_set_other >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Relate the semantic immutable root to the syntactic write guard. *)
Theorem lookup_global_immutable_root:
  lookup_global cx src id es =
    (INL (PlaceR (ImmutablePlace other_src other_id path)),es') ==>
  other_src = src /\ other_id = id /\ path = []
Proof
  simp[lookup_global_def, vyperMiscTheory.option_CASE_rator,
       vyperMiscTheory.prod_CASE_rator, var_decl_info_CASE_rator,
       bind_def, lift_option_type_def, return_def, raise_def,
       get_immutables_def, get_address_immutables_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[AllCaseEqs(), bind_def, return_def, raise_def]
QED

Theorem extend_place_immutable_root:
  extend_place cx pv sb es =
    (INL (PlaceR (ImmutablePlace src id path)),es') ==>
  ?oldpath. pv = PlaceR (ImmutablePlace src id oldpath)
Proof
  Cases_on `pv` >> Cases_on `sb` >>
  simp[oneline extend_place_def, bind_def, ignore_bind_def,
       lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[bind_def, return_def, raise_def, lift_sum_def,
      value_type_CASE_rator, place_CASE_rator, vyperMiscTheory.sum_CASE_rator,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs(), extend_memory_place_def] >>
  Cases_on `tv` >>
  gvs[oneline extend_storage_place_def, vyperValueTheory.value_CASE_rator,
      bind_def, ignore_bind_def, check_def, assert_def,
      lift_option_type_def, lift_sum_def, return_def, raise_def, AllCaseEqs()] >>
  pairarg_tac >> gvs[return_def]
QED

Theorem immutable_place_access_root_attrs[local]:
  !target attrs. FST (place_access target attrs) = FST (place_access target [])
Proof
  measureInduct_on `base_assignment_target_size target` >>
  Cases_on `target` >> simp[place_access_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem eval_base_place_immutable_root:
  !target cx es src id path es'.
    eval_base_place cx target es =
      (INL (PlaceR (ImmutablePlace src id path)),es') ==>
    FST (place_access target []) = TopLevelNameTarget (src,id)
Proof
  measureInduct_on `base_assignment_target_size target` >>
  Cases_on `target` >> rpt strip_tac
  >~ [`eval_base_place _ (NameTarget _) _ = _`]
  >- gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
         type_check_def, assert_def, return_def, raise_def, AllCaseEqs(),
         place_access_def]
  >~ [`eval_base_place _ (TopLevelNameTarget _) _ = _`]
  >- (rename1 `eval_base_place cx (TopLevelNameTarget nsid) es = _` >>
      PairCases_on `nsid` >> gvs[Once evaluate_def] >>
      drule lookup_global_immutable_root >> simp[place_access_def]) >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  drule extend_place_immutable_root >> strip_tac >> gvs[] >>
  rename1 `eval_base_place cx inner _ = _` >>
  first_x_assum (qspec_then `inner` mp_tac) >> simp[] >>
  disch_then drule >> simp[place_access_def, immutable_place_access_root_attrs]
QED

Theorem eval_target_place_immutable_root:
  eval_target_place cx target es = (INL (ImmutablePlace src id path),es') ==>
  FST (place_access target []) = TopLevelNameTarget (src,id)
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, get_place_def, return_def,
      raise_def, AllCaseEqs()] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  metis_tac[eval_base_place_immutable_root]
QED

Theorem typed_guarded_immutable_target_write:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) =
     SOME (Type (ArrayT elem bound))) /\
  type_place_target env target = SOME vt /\
  ~place_contains target (TopLevelNameTarget (src,name)) /\
  eval_target_place cx target es = (INL p,es1) /\
  write_place cx p v es1 = (r,es2) ==>
  lookup_immutable cx es2 src name = lookup_immutable cx es1 src name
Proof
  rpt strip_tac >> irule lookup_immutable_write_other >>
  goal_assum (drule_at Any) >> rpt strip_tac >> gvs[] >>
  drule eval_target_place_immutable_root >> strip_tac >>
  drule_at (Pat `type_place_target env target`) typed_guarded_array_root >>
  simp[] >> metis_tac[]
QED

Theorem append_guarded_immutable_frame:
  append_place cx p v es = (res,es') /\
  (!other_src other_name path. p = ImmutablePlace other_src other_name path ==>
     (other_src,other_name) <> (src,name)) ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  Cases_on `p` >> rpt strip_tac
  >~ [`append_place _ (StoragePlace _ _ _) _ _ = _`]
  >- (drule vyperScopePreservationTheory.append_storage_place_scopes_immutables >>
      simp[lookup_immutable_def]) >>
  gvs[append_place_def, bind_def, AllCaseEqs()] >>
  imp_res_tac read_place_state >> imp_res_tac place_type_value_state >>
  imp_res_tac lift_sum_state >> gvs[] >>
  irule lookup_immutable_write_other >> goal_assum (drule_at Any) >> simp[]
QED

Theorem same_immutables_observation[local]:
  t.immutables = s.immutables ==>
  lookup_immutable cx t src name = lookup_immutable cx s src name
Proof
  simp[lookup_immutable_def]
QED

Theorem pop_place_immutable_other[local]:
  (!other_src other_name path. p = ImmutablePlace other_src other_name path ==>
     (other_src,other_name) <> (src,name)) /\
  pop_place cx p es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  Cases_on `p` >> strip_tac
  >- (drule vyperScopePreservationTheory.pop_storage_place_scopes_immutables >>
      simp[lookup_immutable_def])
  >- (rename1 `MemoryPlace id path` >>
      Cases_on `find_containing_scope id es.scopes` >>
      gvs[pop_place_def, bind_def, get_scopes_def, lift_option_type_def,
          return_def, raise_def] >>
      PairCases_on `x` >>
      gvs[bind_def, ignore_bind_def, lift_sum_def, type_check_def, assert_def,
          check_def, set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
      fs[GSYM lift_sum_def, GSYM lift_option_type_def] >>
      imp_res_tac vyperStatePreservationTheory.lift_sum_state >>
      imp_res_tac vyperStatePreservationTheory.lift_option_type_state >>
      gvs[lookup_immutable_def] >>
      pairarg_tac >>
      gvs[bind_def, ignore_bind_def, set_scopes_def, return_def,
          lookup_immutable_def]) >>
  gvs[pop_place_def, bind_def, ignore_bind_def, get_immutables_def,
      get_address_immutables_def, lift_option_type_def, lift_sum_def,
      return_def, raise_def, AllCaseEqs()] >>
  gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator,
      return_def, raise_def, AllCaseEqs()] >>
  irule lookup_immutable_set_other >> goal_assum (drule_at Any) >> simp[]
QED

(* The immutable instance of the evaluator frame: no write lands on the
   protected immutable and no internal call can reach the constructor. *)
Theorem eval_immutable_frame[local]:
  (!cx e st res st'.
     expr_writes_ok (\w. FST (place_access w []) <> TopLevelNameTarget (src,name)) e /\
     ~supported_expr_exists expr_internal_call_root e /\
     eval_expr cx e st = (res,st') ==>
     lookup_immutable cx st' src name = lookup_immutable cx st src name) /\
  (!cx es st res st'.
     EVERY (expr_writes_ok
       (\w. FST (place_access w []) <> TopLevelNameTarget (src,name))) es /\
     ~supported_exprs_exists expr_internal_call_root es /\
     eval_exprs cx es st = (res,st') ==>
     lookup_immutable cx st' src name = lookup_immutable cx st src name) /\
  (!cx t st res st'.
     target_writes_ok (\w. FST (place_access w []) <> TopLevelNameTarget (src,name)) t /\
     ~supported_target_exists expr_internal_call_root t /\
     eval_target_place cx t st = (res,st') ==>
     lookup_immutable cx st' src name = lookup_immutable cx st src name)
Proof
  qspecl_then [`\c st. lookup_immutable c st src name`,
               `\w. FST (place_access w []) <> TopLevelNameTarget (src,name)`]
    mp_tac eval_observation_frame_mutual >>
  impl_tac
  >- (conj_tac >- simp[lookup_immutable_def] >>
      simp[] >> rpt strip_tac >>
      irule pop_place_immutable_other >> goal_assum (drule_at Any) >>
      rpt strip_tac >> gvs[] >>
      drule eval_target_place_immutable_root >> simp[]) >>
  BETA_TAC >> strip_tac >> rpt conj_tac >> rpt strip_tac >> metis_tac[]
QED

Theorem immutable_root_writes_ok[local]:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) =
     SOME (Type (ArrayT elem bound))) ==>
  (!e. well_typed_expr env e /\
       expr_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) e ==>
       expr_writes_ok (\w. FST (place_access w []) <> TopLevelNameTarget (src,name)) e) /\
  (!es. well_typed_exprs env es /\
       EVERY (expr_writes_ok
         (\w. ~place_contains w (TopLevelNameTarget (src,name)))) es ==>
       EVERY (expr_writes_ok
         (\w. FST (place_access w []) <> TopLevelNameTarget (src,name))) es) /\
  (!t. IS_SOME (type_place_target env t) /\
       target_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) t ==>
       target_writes_ok (\w. FST (place_access w []) <> TopLevelNameTarget (src,name)) t)
Proof
  disch_then assume_tac >>
  `!w vt. type_place_target env w = SOME vt /\
          ~place_contains w (TopLevelNameTarget (src,name)) ==>
          FST (place_access w []) <> TopLevelNameTarget (src,name)` by
    (rpt strip_tac >>
     qspecl_then [`env`, `TopLevelNameTarget (src,name)`, `elem`, `bound`,
                  `w`, `vt`] mp_tac typed_guarded_array_root >>
     simp[]) >>
  rpt strip_tac
  >- (drule_then irule (cj 1 writes_ok_typed_mono) >>
      qexists_tac `\w. ~place_contains w (TopLevelNameTarget (src,name))` >>
      simp[])
  >- (drule_then irule (cj 4 writes_ok_typed_mono) >>
      qexists_tac `\w. ~place_contains w (TopLevelNameTarget (src,name))` >>
      simp[]) >>
  drule_then irule (cj 3 writes_ok_typed_mono) >>
  qexists_tac `\w. ~place_contains w (TopLevelNameTarget (src,name))` >>
  simp[]
QED

Theorem typed_expr_immutable[local]:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) =
     SOME (Type (ArrayT elem bound))) /\
  well_typed_expr env e /\
  expr_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) e /\
  ~supported_expr_exists expr_internal_call_root e /\
  eval_expr cx e st = (res,st') ==>
  lookup_immutable cx st' src name = lookup_immutable cx st src name
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule immutable_root_writes_ok >> strip_tac >>
  `expr_writes_ok (\w. FST (place_access w []) <> TopLevelNameTarget (src,name)) e`
    by (first_x_assum irule >> simp[]) >>
  drule_all (cj 1 eval_immutable_frame) >> simp[]
QED

Theorem typed_exprs_immutable[local]:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) =
     SOME (Type (ArrayT elem bound))) /\
  well_typed_exprs env es /\
  EVERY (expr_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name)))) es /\
  ~supported_exprs_exists expr_internal_call_root es /\
  eval_exprs cx es st = (res,st') ==>
  lookup_immutable cx st' src name = lookup_immutable cx st src name
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule immutable_root_writes_ok >> strip_tac >>
  `EVERY (expr_writes_ok
     (\w. FST (place_access w []) <> TopLevelNameTarget (src,name))) es`
    by (first_x_assum irule >> simp[]) >>
  drule_all (cj 2 eval_immutable_frame) >> simp[]
QED

Theorem typed_custom_error_immutable[local]:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) =
     SOME (Type (ArrayT elem bound))) /\
  well_typed_custom_error env err /\
  EVERY (expr_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))))
    (custom_error_exprs err) /\
  EVERY (\e. ~supported_expr_exists expr_internal_call_root e)
    (custom_error_exprs err) /\
  order_custom_error_args params err = SOME es /\
  eval_exprs cx es st = (res,st') ==>
  lookup_immutable cx st' src name = lookup_immutable cx st src name
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule immutable_root_writes_ok >> strip_tac >>
  `EVERY (expr_writes_ok
     (\w. FST (place_access w []) <> TopLevelNameTarget (src,name)))
     (custom_error_exprs err)` by
    (first_x_assum irule >> gvs[well_typed_custom_error_def]) >>
  drule_then assume_tac vyperASTTheory.order_custom_error_args_perm >>
  `EVERY (expr_writes_ok
     (\w. FST (place_access w []) <> TopLevelNameTarget (src,name))) es`
    by metis_tac[sortingTheory.PERM_EVERY] >>
  `~supported_exprs_exists expr_internal_call_root es` by
    (gvs[supported_exprs_exists_every, NOT_EXISTS, combinTheory.o_DEF] >>
     metis_tac[sortingTheory.PERM_EVERY]) >>
  drule_all (cj 2 eval_immutable_frame) >> simp[]
QED

Theorem typed_target_immutable[local]:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) =
     SOME (Type (ArrayT elem bound))) /\
  type_place_target env t = SOME vt /\
  target_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) t /\
  ~supported_target_exists expr_internal_call_root t /\
  eval_target_place cx t st = (res,st') ==>
  lookup_immutable cx st' src name = lookup_immutable cx st src name
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule immutable_root_writes_ok >> strip_tac >>
  `target_writes_ok (\w. FST (place_access w []) <> TopLevelNameTarget (src,name)) t`
    by (first_x_assum irule >> simp[]) >>
  drule_all (cj 3 eval_immutable_frame) >> simp[]
QED

Theorem typed_iterator_immutable[local]:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) =
     SOME (Type (ArrayT elem bound))) /\
  well_typed_iterator env typ it /\
  (case it of
   | Array e => expr_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) e
   | Range x y =>
       expr_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) x /\
       expr_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) y) /\
  ~supported_iterator_exists expr_internal_call_root it /\
  eval_iterator cx it st = (res,st') ==>
  lookup_immutable cx st' src name = lookup_immutable cx st src name
Proof
  Cases_on `it` >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  gvs[well_typed_iterator_def, supported_iterator_exists_def] >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac lift_option_type_state >>
  imp_res_tac lift_sum_state >> gvs[return_def] >>
  imp_res_tac typed_expr_immutable >> gvs[]
QED

Theorem typed_guarded_target_write_immutable:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound))) /\
  type_place_target env target = SOME vt /\
  ~place_contains target (TopLevelNameTarget (src,name)) /\
  ~supported_target_exists expr_internal_call_root target /\
  target_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) target /\
  (do p <- eval_target_place cx target; write_place cx p v od) es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  gvs[bind_def, AllCaseEqs(), raise_def] >>
  imp_res_tac typed_target_immutable >>
  imp_res_tac typed_guarded_immutable_target_write >> gvs[]
QED

Theorem typed_guarded_assignment_immutable_mutual[local]:
  (!(cx:evaluation_context) (s:stmt). T) /\
  (!(cx:evaluation_context) (ss:stmt list). T) /\
  (!(cx:evaluation_context) (it:iterator). T) /\
  (!(cx:evaluation_context) (tyv:type_value) (nm:string) (body:stmt list) (vs:value list). T) /\
  (!(cx:evaluation_context) (e:expr). T) /\
  (!(cx:evaluation_context) (es:expr list). T) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!cx target v. !env src name elem bound ty es res es'.
    (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
     type_place_target env (TopLevelNameTarget (src,name)) =
       SOME (Type (ArrayT elem bound))) /\
    well_typed_atarget env target ty /\
    atarget_writes_ok (\t. ~place_contains t (TopLevelNameTarget (src,name))) target /\
    ~supported_assignment_exists expr_internal_call_root target /\
    assign_tuple_targets cx target v es = (res,es') ==>
    lookup_immutable cx es' src name = lookup_immutable cx es src name) /\
  (!cx targets vs. !env src name elem bound tys es res es'.
    (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
     type_place_target env (TopLevelNameTarget (src,name)) =
       SOME (Type (ArrayT elem bound))) /\
    LIST_REL (\tgt ty. well_typed_atarget env tgt ty) targets tys /\
    EVERY (atarget_writes_ok (\t. ~place_contains t (TopLevelNameTarget (src,name))))
      targets /\
    ~supported_assignments_exists expr_internal_call_root targets /\
    assign_tuple_target_list cx targets vs es = (res,es') ==>
    lookup_immutable cx es' src name = lookup_immutable cx es src name) /\
  (!(cx:evaluation_context) (es:expr list). T)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> simp[] >>
  rpt (gen_tac ORELSE disch_then (MAP_EVERY assume_tac o CONJUNCTS))
  >>~- ([`assign_tuple_targets _ (BaseTarget _) _ _ = _`],
      gvs[well_typed_atarget_def, well_typed_target_def, atarget_writes_ok_def,
          supported_assignment_exists_def] >>
      qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
      simp[Once evaluate_def] >> strip_tac >>
      metis_tac[typed_guarded_target_write_immutable])
  >>~- ([`assign_tuple_targets _ (TupleTarget _) _ _ = _`],
      gvs[well_typed_atarget_def, atarget_writes_ok_def,
          supported_assignment_exists_def, SF ETA_ss] >>
      qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, raise_def, vyperValueTheory.value_CASE_rator,
           vyperValueTheory.array_value_CASE_rator, AllCaseEqs()] >>
      strip_tac >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `assign_tuple_target_list _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, ignore_bind_def, bind_def, return_def, raise_def,
       AllCaseEqs()] >>
  strip_tac >>
  gvs[LIST_REL_CONS1, SF ETA_ss, supported_assignment_exists_def] >>
  metis_tac[]
QED

Theorem typed_guarded_assignment_immutable:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound))) /\
  well_typed_atarget env target ty /\
  atarget_writes_ok (\t. ~place_contains t (TopLevelNameTarget (src,name))) target /\
  ~supported_assignment_exists expr_internal_call_root target /\
  assign_tuple_targets cx target v es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  metis_tac[typed_guarded_assignment_immutable_mutual]
QED

Theorem assign_immutable_frame:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound))) /\
  well_typed_atarget env target ty /\
  atarget_writes_ok (\t. ~place_contains t (TopLevelNameTarget (src,name))) target /\
  ~supported_assignment_exists expr_internal_call_root target /\
  (!s r t. eval_expr cx rhs s = (r,t) ==>
    lookup_immutable cx t src name = lookup_immutable cx s src name) /\
  eval_stmt cx (Assign target rhs) es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  Cases_on `target` >> disch_then (MAP_EVERY assume_tac o CONJUNCTS)
  >~ [`eval_stmt _ (Assign (BaseTarget _) _) _ = _`]
  >- (rename1 `eval_stmt cx (Assign (BaseTarget bt) rhs) es = _` >>
      gvs[well_typed_atarget_def, well_typed_target_def, atarget_writes_ok_def,
          supported_assignment_exists_def] >>
      qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac read_result_state >> gvs[IgnAsm `!s r t. _`] >>
      first_x_assum drule >> strip_tac >>
      imp_res_tac typed_target_immutable >>
      imp_res_tac typed_guarded_immutable_target_write >> gvs[]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[IgnAsm `!s r t. _`] >>
  first_x_assum drule >> strip_tac >>
  imp_res_tac typed_guarded_assignment_immutable >> gvs[]
QED

Theorem augassign_immutable_frame:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound))) /\
  well_typed_target env bt ty /\ ~place_contains bt (TopLevelNameTarget (src,name)) /\
  ~supported_target_exists expr_internal_call_root bt /\
  target_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) bt /\
  (!s r t. eval_expr cx rhs s = (r,t) ==>
    lookup_immutable cx t src name = lookup_immutable cx s src name) /\
  eval_stmt cx (AugAssign ty bt bop rhs) es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> gvs[well_typed_target_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_place_state >> imp_res_tac place_type_value_state >>
  imp_res_tac read_result_state >> imp_res_tac lift_sum_state >>
  imp_res_tac typed_target_immutable >>
  gvs[IgnAsm `!s r t. _`] >> first_x_assum drule >> strip_tac >>
  all_tac
  >>~- ([`write_place _ _ _ _ = _`],
    qmatch_asmsub_rename_tac `write_place cx p result write_state` >>
    `lookup_immutable cx es' src name = lookup_immutable cx write_state src name`
      suffices_by metis_tac[] >>
    irule lookup_immutable_write_other >>
    goal_assum (drule_at Any) >> rpt strip_tac >> gvs[] >>
    drule eval_target_place_immutable_root >> strip_tac >>
    drule_at (Pat `type_place_target env bt`) typed_guarded_array_root >>
    simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem immutable_target_type_extend_local:
  type_place_target (extend_local env id ty assignable) (TopLevelNameTarget (src,name)) =
  type_place_target env (TopLevelNameTarget (src,name))
Proof
  simp[well_typed_expr_def, extend_local_def]
QED

Theorem immutable_target_type_stmt:
  type_stmt env ret_ty stmt = SOME env' ==>
  type_place_target env' (TopLevelNameTarget (src,name)) =
  type_place_target env (TopLevelNameTarget (src,name))
Proof
  strip_tac >> drule vyperTypeEnvExtensionTheory.type_stmt_preserve_nonlocal_fields >>
  strip_tac >> simp[well_typed_expr_def]
QED

Theorem immutable_target_type_stmts:
  type_stmts env ret_ty stmts = SOME env' ==>
  type_place_target env' (TopLevelNameTarget (src,name)) =
  type_place_target env (TopLevelNameTarget (src,name))
Proof
  strip_tac >> drule vyperTypeEnvExtensionTheory.type_stmts_preserve_nonlocal_fields >>
  strip_tac >> simp[well_typed_expr_def]
QED

Theorem finally_pop_immutable_frame:
  (!s r t. action s = (r,t) ==>
    lookup_immutable cx t src name = lookup_immutable cx s src name) /\
  finally action pop_scope es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  strip_tac >>
  gvs[finally_def, ignore_bind_def, bind_def, pop_scope_def,
      return_def, raise_def, AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >>
  gvs[lookup_immutable_def]
QED

Theorem loop_action_immutable_frame:
  !cx body src name es res es'.
  (!s r t. eval_stmts cx body s = (r,t) ==>
    lookup_immutable cx t src name = lookup_immutable cx s src name) /\
  try (do eval_stmts cx body; return F od) handle_loop_exception es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  rpt gen_tac >> strip_tac >>
  gvs[try_def, ignore_bind_def, bind_def, return_def, AllCaseEqs(),
      handle_loop_exception_def, raise_def] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  Cases_on `e = ContinueException` >> Cases_on `e = BreakException` >>
  gvs[return_def, raise_def]
QED

Theorem eval_for_immutable_frame:
  !vs cx tyv id stmts src name es res es'.
  (!s r t. eval_stmts cx stmts s = (r,t) ==>
    lookup_immutable cx t src name = lookup_immutable cx s src name) /\
  eval_for cx tyv id stmts vs es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  Induct_on `vs` >> simp[Once evaluate_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `finally action pop_scope` >>
  `!s r t. action s = (r,t) ==>
    lookup_immutable cx t src name = lookup_immutable cx s src name` by
    (rpt gen_tac >> simp[Abbr `action`] >> strip_tac >>
     irule loop_action_immutable_frame >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `ignore_bind _ _ es = _` mp_tac >>
  simp[push_scope_with_var_def, ignore_bind_def, bind_def, return_def,
       AllCaseEqs()] >> strip_tac >>
  imp_res_tac finally_pop_immutable_frame >>
  gvs[AllCaseEqs(), return_def] >>
  `!f. lookup_immutable cx (es with scopes updated_by f) src name =
     lookup_immutable cx es src name` by simp[lookup_immutable_def] >>
  gvs[] >>~- ([`(if broke then _ else _) _ = _`],
    Cases_on `broke` >> gvs[return_def] >>
    first_x_assum drule_all >> simp[]) >>
  gvs[raise_def]
QED

Theorem for_immutable_frame:
  !cx id typ it n stmts src name es res es'.
    (!s r t. eval_iterator cx it s = (r,t) ==>
      lookup_immutable cx t src name = lookup_immutable cx s src name) /\
    (!s r t. eval_stmts cx stmts s = (r,t) ==>
      lookup_immutable cx t src name = lookup_immutable cx s src name) /\
    eval_stmt cx (For id typ it n stmts) es = (res,es') ==>
    lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac lift_option_type_state >> imp_res_tac check_state >>
  gvs[IgnAsm `!s r t. _`] >>
  qpat_x_assum `!s r t. eval_iterator _ _ _ = _ ==> _` drule >> strip_tac
  >~ [`eval_for _ _ _ _ _ _ = _`]
  >- (drule_at (Pat `eval_for _ _ _ _ _ _ = _`) eval_for_immutable_frame >>
      disch_then (qspecl_then [`src`,`name`] mp_tac) >>
      (impl_tac >- simp[]) >> simp[]) >>
  gvs[IgnAsm `!s r t. _`]
QED

Theorem annassign_immutable_frame:
  !cx id typ e src name es res es'.
    (!s r t. eval_expr cx e s = (r,t) ==>
      lookup_immutable cx t src name = lookup_immutable cx s src name) /\
    eval_stmt cx (AnnAssign id typ e) es = (res,es') ==>
    lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac lift_option_type_state >> imp_res_tac read_result_state >>
  gvs[IgnAsm `!s r t. _`] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  qpat_x_assum `new_variable _ _ _ _ = _` mp_tac >>
  simp[new_variable_def, get_scopes_def, set_scopes_def, bind_def,
       ignore_bind_def, type_check_def, assert_def,
       lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> rename1 `lookup_scopes id mid.scopes = NONE` >>
  Cases_on `mid.scopes` >>
  gvs[set_scopes_def, return_def, raise_def, lookup_immutable_def]
QED

Theorem if_immutable_frame:
  !cx e ss1 ss2 src name es res es'.
    (!s r t. eval_expr cx e s = (r,t) ==>
      lookup_immutable cx t src name = lookup_immutable cx s src name) /\
    (!s r t. eval_stmts cx ss1 s = (r,t) ==>
      lookup_immutable cx t src name = lookup_immutable cx s src name) /\
    (!s r t. eval_stmts cx ss2 s = (r,t) ==>
      lookup_immutable cx t src name = lookup_immutable cx s src name) /\
    eval_stmt cx (If e ss1 ss2) es = (res,es') ==>
    lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, push_scope_def,
       get_scopes_def, set_scopes_def, return_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `!s r t. eval_expr _ _ _ = _ ==> _` drule >> strip_tac
  >~ [`v = INR exc`]
  >- gvs[IgnAsm `!s r t. _`] >>
  `!s r t. switch_BoolV cx tv (eval_stmts cx ss1) (eval_stmts cx ss2) s = (r,t) ==>
     lookup_immutable cx t src name = lookup_immutable cx s src name` by
    (rpt gen_tac >>
     simp[switch_BoolV_def, bind_def, AllCaseEqs()] >> strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     rename1 `(if value = BoolV T then _ else _) _ = _` >>
     Cases_on `value = BoolV T` >> Cases_on `value = BoolV F` >>
     gvs[raise_def] >> first_x_assum drule >> simp[]) >>
  drule_at (Pat `finally _ _ _ = _`) finally_pop_immutable_frame >>
  disch_then (qspecl_then [`src`,`name`,`cx`] mp_tac) >>
  (impl_tac >- simp[]) >>
  `!f. lookup_immutable cx (s'' with scopes updated_by f) src name =
       lookup_immutable cx s'' src name` by simp[NoAsms, lookup_immutable_def] >>
  simp[]
QED

(* gvs splits the type disjunction on the protected immutable; this puts it
   back for the lemmas that take it whole. *)
val imm_disj_tac : tactic =
  Q.SUBGOAL_THEN
    `type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
     type_place_target env (TopLevelNameTarget (src,name)) =
       SOME (Type (ArrayT elem bound))` assume_tac
  >- simp[];

Theorem typed_immutable_frames_mutual:
  (!env ret_ty stmt env' src name elem bound cx es res es'.
    (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
     type_place_target env (TopLevelNameTarget (src,name)) =
       SOME (Type (ArrayT elem bound))) /\
    type_stmt env ret_ty stmt = SOME env' /\
    stmt_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) stmt /\
    ~supported_stmt_expr_exists expr_internal_call_root stmt /\
    eval_stmt cx stmt es = (res,es') ==>
    lookup_immutable cx es' src name = lookup_immutable cx es src name) /\
  (!env ret_ty stmts env' src name elem bound cx es res es'.
    (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
     type_place_target env (TopLevelNameTarget (src,name)) =
       SOME (Type (ArrayT elem bound))) /\
    type_stmts env ret_ty stmts = SOME env' /\
    stmts_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) stmts /\
    ~supported_stmts_expr_exists expr_internal_call_root stmts /\
    eval_stmts cx stmts es = (res,es') ==>
    lookup_immutable cx es' src name = lookup_immutable cx es src name)
Proof
  ho_match_mp_tac type_stmt_ind >> rpt conj_tac >>
  rpt (gen_tac ORELSE disch_then (MAP_EVERY assume_tac o CONJUNCTS))
  >~ [`eval_stmt _ Pass _ = _`]
  >- (qpat_x_assum `eval_stmt _ Pass _ = _` mp_tac >>
      simp[Once evaluate_def, return_def, raise_def] >> rw[] >> simp[])
  >~ [`eval_stmt _ Break _ = _`]
  >- (qpat_x_assum `eval_stmt _ Break _ = _` mp_tac >>
      simp[Once evaluate_def, return_def, raise_def] >> rw[] >> simp[])
  >~ [`eval_stmt _ Continue _ = _`]
  >- (qpat_x_assum `eval_stmt _ Continue _ = _` mp_tac >>
      simp[Once evaluate_def, return_def, raise_def] >> rw[] >> simp[])
  >~ [`eval_stmt _ (Return NONE) _ = _`]
  >- (qpat_x_assum `eval_stmt _ (Return NONE) _ = _` mp_tac >>
      simp[Once evaluate_def, return_def, raise_def] >> rw[] >> simp[])
  >~ [`eval_stmt _ (Raise RaiseBare) _ = _`]
  >- (qpat_x_assum `eval_stmt _ (Raise RaiseBare) _ = _` mp_tac >>
      simp[Once evaluate_def, return_def, raise_def] >> rw[] >> simp[])
  >~ [`eval_stmt _ (Raise RaiseUnreachable) _ = _`]
  >- (qpat_x_assum `eval_stmt _ (Raise RaiseUnreachable) _ = _` mp_tac >>
      simp[Once evaluate_def, return_def, raise_def] >> rw[] >> simp[])
  >~ [`eval_stmts _ [] _ = _`]
  >- (qpat_x_assum `eval_stmts _ [] _ = _` mp_tac >>
      simp[Once evaluate_def, return_def, raise_def] >> rw[] >> simp[])
  >~ [`eval_stmt _ (Expr _) _ = _`] >- suspend "expr"
  >~ [`eval_stmt _ (Return (SOME _)) _ = _`] >- suspend "return"
  >~ [`eval_stmt _ (Raise (RaiseReason _)) _ = _`] >- suspend "raise_reason"
  >~ [`eval_stmt _ (Raise (RaiseCustomError _)) _ = _`] >- suspend "raise_custom"
  >~ [`eval_stmt _ (Assert _ AssertBare) _ = _`] >- suspend "assert_bare"
  >~ [`eval_stmt _ (Assert _ AssertUnreachable) _ = _`]
  >- suspend "assert_unreachable"
  >~ [`eval_stmt _ (Assert _ (AssertReason _)) _ = _`] >- suspend "assert_reason"
  >~ [`eval_stmt _ (Assert _ (AssertCustomError _)) _ = _`]
  >- suspend "assert_custom"
  >~ [`eval_stmt _ (Log _ _) _ = _`] >- suspend "log"
  >~ [`eval_stmt _ (AnnAssign _ _ _) _ = _`] >- suspend "annassign"
  >~ [`eval_stmt _ (Append _ _) _ = _`] >- suspend "append"
  >~ [`eval_stmt _ (Assign _ _) _ = _`] >- suspend "assign"
  >~ [`eval_stmt _ (AugAssign _ _ _ _) _ = _`] >- suspend "augassign"
  >~ [`eval_stmt _ (If _ _ _) _ = _`] >- suspend "if"
  >~ [`eval_stmt _ (For _ _ _ _ _) _ = _`] >- suspend "for"
  >~ [`eval_stmts _ (_::_) _ = _`] >- suspend "cons"
QED

Resume typed_immutable_frames_mutual[expr]:
  gvs[type_stmt_def, stmt_writes_ok_def, supported_stmt_expr_exists_def,
      AllCaseEqs()] >>
  imm_disj_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, type_check_def, assert_def,
       ignore_bind_def, return_def, raise_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac typed_expr_immutable >> gvs[]
QED

Resume typed_immutable_frames_mutual[return]:
  gvs[type_stmt_def, stmt_writes_ok_def, supported_stmt_expr_exists_def,
      supported_expr_exists_def, AllCaseEqs()] >>
  imm_disj_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, raise_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >>
  imp_res_tac typed_expr_immutable >> gvs[]
QED

Resume typed_immutable_frames_mutual[raise_reason]:
  gvs[type_stmt_def, stmt_writes_ok_def, supported_stmt_expr_exists_def,
      supported_raise_exists_def, AllCaseEqs()] >>
  imm_disj_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, raise_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac lift_option_type_state >>
  imp_res_tac typed_expr_immutable >> gvs[]
QED

Resume typed_immutable_frames_mutual[raise_custom]:
  rename1 `Raise (RaiseCustomError err)` >>
  gvs[type_stmt_def, stmt_writes_ok_def, supported_stmt_expr_exists_def,
      supported_raise_exists_def, AllCaseEqs()] >>
  imm_disj_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  Cases_on `err` >>
  simp[Once evaluate_def, bind_def, raise_def,
       vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >> strip_tac >>
  gvs[] >> imp_res_tac lift_option_state >>
  fs[combinTheory.o_DEF] >>
  imp_res_tac typed_custom_error_immutable >> gvs[]
QED

Resume typed_immutable_frames_mutual[assert_bare]:
  gvs[type_stmt_def, stmt_writes_ok_def, supported_stmt_expr_exists_def,
      supported_assert_exists_def, AllCaseEqs()] >>
  imm_disj_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >>
  strip_tac >>
  imp_res_tac typed_expr_immutable >>
  imp_res_tac read_result_state >>
  gvs[return_def, raise_def, COND_RATOR, AllCaseEqs()]
QED

Resume typed_immutable_frames_mutual[assert_unreachable]:
  gvs[type_stmt_def, stmt_writes_ok_def, supported_stmt_expr_exists_def,
      supported_assert_exists_def, AllCaseEqs()] >>
  imm_disj_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >>
  strip_tac >>
  imp_res_tac typed_expr_immutable >>
  imp_res_tac read_result_state >>
  gvs[return_def, raise_def, COND_RATOR, AllCaseEqs()]
QED

Resume typed_immutable_frames_mutual[assert_reason]:
  rename1 `Assert cond (AssertReason msg)` >>
  gvs[type_stmt_def, stmt_writes_ok_def, supported_stmt_expr_exists_def,
      supported_assert_exists_def, AllCaseEqs()] >>
  imm_disj_tac >>
  `!s r t. eval_expr cx msg s = (r,t) ==>
     lookup_immutable cx t src name = lookup_immutable cx s src name` by
    (rpt strip_tac >> drule_all typed_expr_immutable >> simp[]) >>
  `!s r t. eval_expr cx cond s = (r,t) ==>
     lookup_immutable cx t src name = lookup_immutable cx s src name` by
    (rpt strip_tac >> drule_all typed_expr_immutable >> simp[]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >>
  strip_tac >>
  imp_res_tac read_result_state >>
  gvs[IgnAsm `!s r t. _`, return_def, raise_def, COND_RATOR, bind_def,
      AllCaseEqs()] >>
  imp_res_tac read_result_state >> imp_res_tac lift_option_type_state >>
  gvs[IgnAsm `!s r t. _`] >> metis_tac[]
QED

Resume typed_immutable_frames_mutual[assert_custom]:
  rename1 `Assert cond (AssertCustomError err)` >>
  gvs[type_stmt_def, stmt_writes_ok_def, supported_stmt_expr_exists_def,
      supported_assert_exists_def, AllCaseEqs()] >>
  imm_disj_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  Cases_on `err` >>
  simp[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >>
  strip_tac >>
  imp_res_tac typed_expr_immutable >>
  imp_res_tac read_result_state >>
  gvs[return_def, raise_def, COND_RATOR, bind_def,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  imp_res_tac lift_option_state >> gvs[] >>
  fs[combinTheory.o_DEF] >>
  imp_res_tac typed_custom_error_immutable >> gvs[]
QED

Resume typed_immutable_frames_mutual[log]:
  gvs[type_stmt_def, stmt_writes_ok_def, supported_stmt_expr_exists_def,
      AllCaseEqs()] >>
  imm_disj_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  Cases_on `cx.txn.is_static` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >>
  imp_res_tac typed_exprs_immutable >>
  imp_res_tac lift_option_state >> imp_res_tac push_log_immutables >>
  gvs[] >> metis_tac[same_immutables_observation]
QED

Resume typed_immutable_frames_mutual[annassign]:
  rename1 `eval_stmt cx (AnnAssign id typ rhs) es = (res,es')` >>
  gvs[type_stmt_def, stmt_writes_ok_def, supported_stmt_expr_exists_def,
      AllCaseEqs()] >>
  imm_disj_tac >>
  `!s r t. eval_expr cx rhs s = (r,t) ==>
     lookup_immutable cx t src name = lookup_immutable cx s src name` by
    (rpt strip_tac >> drule_all typed_expr_immutable >> simp[]) >>
  drule_all annassign_immutable_frame >> simp[]
QED

Resume typed_immutable_frames_mutual[append]:
  rename1 `eval_stmt cx (Append bt rhs) es = (res,es')` >>
  gvs[type_stmt_def, stmt_writes_ok_def, supported_stmt_expr_exists_def,
      AllCaseEqs()] >>
  imm_disj_tac >>
  `FST (place_access bt []) <> TopLevelNameTarget (src,name)` by
    (irule typed_guarded_array_root >> simp[] >> metis_tac[]) >>
  `!s r t. eval_expr cx rhs s = (r,t) ==>
     lookup_immutable cx t src name = lookup_immutable cx s src name` by
    (rpt strip_tac >> drule_all typed_expr_immutable >> simp[]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac typed_target_immutable >>
  gvs[IgnAsm `!s r t. _`] >> res_tac
  >>~- ([`append_place _ _ _ _ = _`],
      rename1 `append_place cx dest value mid = (res,es')` >>
      `!other_src other_name path. dest = ImmutablePlace other_src other_name path ==>
         (other_src,other_name) <> (src,name)` by
        (rpt strip_tac >> gvs[] >> drule eval_target_place_immutable_root >>
         simp[]) >>
      drule_all append_guarded_immutable_frame >> strip_tac >> metis_tac[]) >>
  TRY (qpat_x_assum `!s r t. eval_expr _ _ _ = _ ==> _`
         (fn th => imp_res_tac th)) >>
  gvs[]
QED

Resume typed_immutable_frames_mutual[assign]:
  rename1 `eval_stmt cx (Assign target rhs) es = (res,es')` >>
  gvs[type_stmt_def, stmt_writes_ok_def, supported_stmt_expr_exists_def,
      AllCaseEqs()] >>
  imm_disj_tac >>
  drule_all vyperTypeArgFitsTheory.atarget_accepts_well_typed_atarget >>
  strip_tac >>
  `!s r t. eval_expr cx rhs s = (r,t) ==>
     lookup_immutable cx t src name = lookup_immutable cx s src name` by
    (rpt strip_tac >> drule_all typed_expr_immutable >> simp[]) >>
  drule_all assign_immutable_frame >> simp[]
QED

Resume typed_immutable_frames_mutual[augassign]:
  rename1 `eval_stmt cx (AugAssign ty bt bop rhs) es = (res,es')` >>
  gvs[type_stmt_def, stmt_writes_ok_def, supported_stmt_expr_exists_def,
      AllCaseEqs()] >>
  imm_disj_tac >>
  `!s r t. eval_expr cx rhs s = (r,t) ==>
     lookup_immutable cx t src name = lookup_immutable cx s src name` by
    (rpt strip_tac >> drule_all typed_expr_immutable >> simp[]) >>
  drule_all augassign_immutable_frame >> simp[]
QED

Resume typed_immutable_frames_mutual[if]:
  rename1 `eval_stmt cx (If e ss1 ss2) es = (res,es')` >>
  gvs[type_stmt_def, stmt_writes_ok_def, supported_stmt_expr_exists_def,
      optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >>
  imm_disj_tac >>
  irule if_immutable_frame >> goal_assum (drule_at Any) >>
  rpt conj_tac >> rpt strip_tac >>
  FIRST [drule_all typed_expr_immutable >> simp[],
         first_x_assum drule_all >> simp[]]
QED

Resume typed_immutable_frames_mutual[for]:
  rename1 `eval_stmt cx (For id typ it n stmts) es = (res,es')` >>
  gvs[type_stmt_def, stmt_writes_ok_def, supported_stmt_expr_exists_def,
      optionTheory.IS_SOME_EXISTS, immutable_target_type_extend_local,
      AllCaseEqs()] >>
  imm_disj_tac >>
  irule for_immutable_frame >> goal_assum (drule_at Any) >>
  conj_tac >> rpt strip_tac >>
  FIRST [drule_all typed_iterator_immutable >> simp[],
         first_x_assum drule_all >> simp[]]
QED

Resume typed_immutable_frames_mutual[cons]:
  rename1 `eval_stmts cx (s::ss) es = (res,es')` >>
  qpat_x_assum `type_stmts _ _ (_::_) = _` mp_tac >>
  simp[Once type_stmt_def, AllCaseEqs()] >> strip_tac >>
  rename1 `type_stmt env ret_ty s = SOME env1` >>
  gvs[stmt_writes_ok_def, supported_stmt_expr_exists_def] >>
  imm_disj_tac >>
  (Q.SUBGOAL_THEN
     `type_place_target env1 (TopLevelNameTarget (src,name)) = NONE \/
      type_place_target env1 (TopLevelNameTarget (src,name)) =
        SOME (Type (ArrayT elem bound))` assume_tac
   >- metis_tac[immutable_target_type_stmt]) >>
  qpat_x_assum `eval_stmts _ (_::_) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, ignore_bind_def, bind_def, AllCaseEqs()] >>
  strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  TRY (first_x_assum drule_all >> strip_tac) >>
  gvs[]
QED

Finalise typed_immutable_frames_mutual

Theorem typed_stmt_immutable_frame:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound))) /\
  type_stmt env ret_ty stmt = SOME env' /\
  stmt_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) stmt /\
  ~supported_stmt_expr_exists expr_internal_call_root stmt /\
  eval_stmt cx stmt es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  metis_tac[typed_immutable_frames_mutual]
QED

Theorem typed_stmts_immutable_frame:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound))) /\
  type_stmts env ret_ty stmts = SOME env' /\
  stmts_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  eval_stmts cx stmts es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  metis_tac[typed_immutable_frames_mutual]
QED

Theorem coherent_immutable_array_target_type[local]:
  env_context_consistent env cx /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT elem bound) ==>
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound)))
Proof
  strip_tac >>
  Cases_on `FLOOKUP env.bare_global_assignable (src,name)`
  >- simp[well_typed_expr_def] >>
  fs[env_context_consistent_def] >>
  `x = ArrayT elem bound` by metis_tac[optionTheory.SOME_11] >>
  gvs[well_typed_expr_def]
QED

Theorem immutable_array_body_observation:
  env_context_consistent env cx /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT elem bound) /\
  type_stmts env ret_ty stmts = SOME env' /\
  iterator_unmodified (Array (TopLevelName (ArrayT elem bound) (src,name))) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  eval_stmts cx stmts es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  rpt strip_tac >>
  drule_all coherent_immutable_array_target_type >> strip_tac >>
  fs[iterator_unmodified_def, expr_place_def] >>
  metis_tac[typed_stmts_immutable_frame]
QED

Theorem immutable_array_body_pop_observation:
  env_context_consistent env cx /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT elem bound) /\
  type_stmts env ret_ty stmts = SOME env' /\
  iterator_unmodified (Array (TopLevelName (ArrayT elem bound) (src,name))) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  finally (eval_stmts cx stmts) pop_scope es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  rpt strip_tac >>
  drule_at (Pat `finally _ _ _ = _`) finally_pop_immutable_frame >>
  disch_then irule >> metis_tac[immutable_array_body_observation]
QED
