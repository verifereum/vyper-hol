(* Current-read provenance at effect-free source expression origins. *)
Theory exprStorageOrigin
Ancestors
  accountsRelProps vyperStoragePlaceProvenance vyperStorageBackend
  supportedExprTraverse vyperStatePreservation vyperState
  exprEffectStorage vyperTypeStoragePreservation vyperInterpreter

Definition storage_result_live_def:
  storage_result_live cx es (PlaceR (StoragePlace tr slot tv)) =
    (storage_read_live cx tr (get_storage cx es tr) slot tv /\
     slots_in_range (get_storage cx es tr) (w2n slot) tv) /\
  storage_result_live cx es (HashMapRef tr slot kt vt) =
    storage_mapping_region cx tr slot (HashMapT kt vt) /\
  storage_result_live cx es _ = T
End

Theorem declared_storage_region_live:
  contract_storage_well_formed cx es /\
  declared_storage_region cx mid id keys = SOME (tr,slot,tv) ==>
  storage_result_live cx es (PlaceR (StoragePlace tr slot tv))
Proof
  strip_tac >> simp[storage_result_live_def] >>
  conj_tac >- metis_tac[declared_storage_region_read_live] >>
  fs[vyperStorageLayoutSafetyTheory.contract_storage_well_formed_def] >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  simp[get_storage_backend_eq]
QED

Theorem lookup_global_result_live:
  contract_storage_well_formed cx es /\
  lookup_global cx mid id es = (INL r,es') ==>
  storage_result_live cx es' r
Proof
  strip_tac >> drule lookup_global_state >> strip_tac >> gvs[] >>
  Cases_on `r` >> simp[storage_result_live_def]
  >- (Cases_on `p` >> simp[storage_result_live_def] >>
      drule lookup_global_storage_region >> strip_tac >>
      drule_all declared_storage_region_live >> simp[storage_result_live_def])
  >> metis_tac[lookup_global_mapping_region]
QED

val _ = List.app (fn th =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail "Storage origin dependency" else ()
  end) [declared_storage_region_live, lookup_global_result_live];

Theorem storage_mapping_region_live_leaf:
  contract_storage_well_formed cx es /\
  storage_mapping_region cx tr slot (Type typ) /\
  evaluate_type (get_tenv cx) typ = SOME tv ==>
  storage_result_live cx es (PlaceR (StoragePlace tr slot tv))
Proof
  strip_tac >>
  qpat_x_assum `storage_mapping_region _ _ _ _` mp_tac >>
  rewrite_tac[storage_mapping_region_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >>
  simp[vyperStorageLayoutSafetyTheory.resolve_hashmap_leaf_def] >> strip_tac >>
  irule declared_storage_region_live >> metis_tac[]
QED

Theorem extend_mapping_place_live:
  contract_storage_well_formed cx es /\
  storage_mapping_region cx tr slot (HashMapT kt vt) /\
  extend_place cx (HashMapRef tr slot kt vt) sb es = (INL r,es') ==>
  storage_result_live cx es' r
Proof
  Cases_on `sb` >>
  simp[extend_place_def, vyperStateTheory.raise_def] >>
  strip_tac >>
  drule storage_mapping_region_step >>
  disch_then (qspec_then `v` assume_tac) >>
  Cases_on `vt` >>
  gvs[extend_place_def, vyperStateTheory.bind_def,
      lift_option_type_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def, AllCaseEqs(), storage_result_live_def] >>
  Cases_on `evaluate_type (get_tenv cx) t` >>
  gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  drule_all storage_mapping_region_live_leaf >> simp[storage_result_live_def]
QED

Theorem extend_place_result_live:
  contract_storage_well_formed cx es /\ storage_result_live cx es r /\
  extend_place cx r sb es = (INL r',es') ==>
  storage_result_live cx es' r'
Proof
  Cases_on `r` >> simp[storage_result_live_def, extend_place_def,
                       vyperStateTheory.raise_def]
  >- (Cases_on `p` >>
      simp[storage_result_live_def, extend_place_def,
           vyperStateTheory.bind_def, vyperStateTheory.return_def,
           AllCaseEqs()] >> strip_tac >>
      gvs[extend_memory_place_def, storage_result_live_def,
          vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
          vyperStateTheory.return_def, AllCaseEqs()] >>
      rename1 `extend_storage_place _ _ _ _ _ _ = (INL selected,_)` >>
      Cases_on `selected` >> simp[storage_result_live_def] >>
      drule_all extend_storage_place_read_live >>
      simp[storage_result_live_def]) >>
  metis_tac[extend_mapping_place_live]
QED

Theorem select_result_live:
  contract_storage_well_formed cx es /\ storage_result_live cx es r /\
  select_result cx ty r sb es = (INL r',es') ==>
  storage_result_live cx es' r'
Proof
  Cases_on `r` >>
  simp[select_result_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       AllCaseEqs()] >> strip_tac >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.return_def, AllCaseEqs(),
      storage_result_live_def] >>
  metis_tac[extend_place_result_live, storage_result_live_def]
QED

val _ = List.app (fn th =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail "Storage selection origin dependency" else ()
  end) [storage_mapping_region_live_leaf, extend_mapping_place_live,
         extend_place_result_live, select_result_live];

Theorem evaluate_storage_result_live[local]:
  (!cx s. eval_stmt cx s = eval_stmt cx s) /\
  (!cx ss. eval_stmts cx ss = eval_stmts cx ss) /\
  (!cx it. eval_iterator cx it = eval_iterator cx it) /\
  (!cx ty id body vs. eval_for cx ty id body vs = eval_for cx ty id body vs) /\
  (!cx e. !st r st'.
    contract_storage_well_formed cx st /\
    ~supported_expr_exists expr_effect_root e /\
    eval_expr cx e st = (INL r,st') ==>
    storage_result_live cx st' r) /\
  (!cx es. eval_exprs cx es = eval_exprs cx es) /\
  (!cx bt. eval_base_place cx bt = eval_base_place cx bt) /\
  (!cx tgt. eval_target_place cx tgt = eval_target_place cx tgt) /\
  (!cx tgt v. assign_tuple_targets cx tgt v = assign_tuple_targets cx tgt v) /\
  (!cx tgts vs. assign_tuple_target_list cx tgts vs = assign_tuple_target_list cx tgts vs) /\
  (!cx es. eval_expr_results cx es = eval_expr_results cx es)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[supported_expr_exists_def, expr_effect_root_def] >>
  rpt gen_tac >> strip_tac
  >~ [`eval_expr _ (Name _ _) _ = _`] >- suspend "name"
  >~ [`eval_expr _ (Literal _ _) _ = _`]
  >- gvs[Once evaluate_def, vyperStateTheory.return_def, storage_result_live_def]
  >~ [`eval_expr _ (TopLevelName _ _) _ = _`]
  >- (gvs[Once evaluate_def] >> metis_tac[lookup_global_result_live])
  >~ [`eval_expr _ (FlagMember _ _ _) _ = _`] >- suspend "flag"
  >~ [`eval_expr _ (Attribute _ _ _) _ = _`] >- suspend "attribute"
  >~ [`eval_expr _ (Subscript _ _ _) _ = _`] >- suspend "subscript"
  >~ [`eval_expr _ (IfExp _ _ _ _) _ = _`] >- suspend "ifexp"
  >~ [`eval_expr _ (StructLit _ _ _) _ = _`] >- suspend "struct"
  >~ [`eval_expr _ (TypeBuiltin _ _ _ _) _ = _`] >- suspend "type_builtin"
  >~ [`eval_expr _ (Builtin _ _ _) _ = _`] >- suspend "builtin"
QED

Resume evaluate_storage_result_live[name]:
  gvs[Once evaluate_def, vyperStateTheory.bind_def, get_scopes_def,
      type_check_def, vyperStateTheory.assert_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def, vyperStateTheory.ignore_bind_def,
      AllCaseEqs(), storage_result_live_def]
QED

Resume evaluate_storage_result_live[flag]:
  PairCases_on `nsid` >>
  gvs[Once evaluate_def, lookup_flag_mem_def] >>
  Cases_on `get_module_code cx nsid0` >>
  gvs[vyperStateTheory.raise_def] >>
  Cases_on `lookup_flag nsid1 x` >>
  gvs[vyperStateTheory.raise_def] >>
  Cases_on `INDEX_OF mid x'` >>
  gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def,
      storage_result_live_def]
QED

Resume evaluate_storage_result_live[attribute]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ (Attribute _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, vyperStateTheory.bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  irule select_result_live >> goal_assum (drule_at Any) >>
  conj_tac >- (irule contract_storage_well_formed_backends_frame >>
    drule_all eval_expr_effect_free_storage >> metis_tac[]) >>
  first_x_assum irule >> metis_tac[]
QED

Resume evaluate_storage_result_live[subscript]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, vyperStateTheory.bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  imp_res_tac read_result_state >> gvs[] >>
  rename1 `eval_expr cx e' s'' = (INL idx,si)` >>
  `storage_result_live cx s'' res` by metis_tac[] >>
  `s''.accounts = st.accounts /\ s''.tStorage = st.tStorage` by
    metis_tac[eval_expr_effect_free_storage] >>
  `si.accounts = s''.accounts /\ si.tStorage = s''.tStorage` by
    metis_tac[eval_expr_effect_free_storage] >>
  `storage_result_live cx si res` by
    (qpat_x_assum `storage_result_live _ _ _` mp_tac >>
     Cases_on `res` >> simp[storage_result_live_def] >>
     Cases_on `p` >> simp[storage_result_live_def] >>
     metis_tac[get_storage_accounts_transient_frame]) >>
  `contract_storage_well_formed cx si` by
    metis_tac[contract_storage_well_formed_backends_frame] >>
  metis_tac[select_result_live]
QED

Resume evaluate_storage_result_live[struct]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ (StructLit _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  strip_tac >> gvs[storage_result_live_def]
QED

Resume evaluate_storage_result_live[type_builtin]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ (TypeBuiltin _ _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       AllCaseEqs()] >>
  strip_tac >> gvs[storage_result_live_def]
QED

Resume evaluate_storage_result_live[ifexp]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, vyperStateTheory.bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `conditional_result _ _ _ = _` mp_tac >>
  Cases_on `res` >>
  simp[conditional_result_def, vyperStateTheory.return_def,
       vyperStateTheory.bind_def, AllCaseEqs(), storage_result_live_def] >>
  rpt strip_tac >> gvs[storage_result_live_def, vyperStateTheory.raise_def] >>
  Cases_on `p` >>
  simp[conditional_result_def, vyperStateTheory.return_def,
       vyperStateTheory.bind_def, AllCaseEqs(), storage_result_live_def] >>
  rpt strip_tac >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.return_def,
      AllCaseEqs(), storage_result_live_def] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  IF_CASES_TAC >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[storage_result_live_def]
QED

Resume evaluate_storage_result_live[builtin]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       AllCaseEqs()] >>
  strip_tac >> gvs[storage_result_live_def]
QED

Finalise evaluate_storage_result_live

Theorem eval_expr_storage_result_live:
  contract_storage_well_formed cx st /\ ~expr_has_effect e /\
  eval_expr cx e st = (INL r,st') ==>
  storage_result_live cx st' r
Proof
  simp[expr_has_effect_def] >> metis_tac[evaluate_storage_result_live]
QED

val _ = List.app (fn th =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail "Expression origin dependency" else ()
  end) [eval_expr_storage_result_live];
