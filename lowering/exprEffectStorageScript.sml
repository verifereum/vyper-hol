(* Storage frames for effect-free operands, independent of typing and oracles. *)
Theory exprEffectStorage
Ancestors
  supportedExprTraverse vyperInterpreter vyperStatePreservation
  vyperPlaceFrames vyperState vyperAST vyperStorageBackend list
Libs monadsyntax

Theorem evaluate_effect_free_storage[local]:
  (!cx s. eval_stmt cx s = eval_stmt cx s) /\
  (!cx ss. eval_stmts cx ss = eval_stmts cx ss) /\
  (!cx it. eval_iterator cx it = eval_iterator cx it) /\
  (!cx ty id body vs. eval_for cx ty id body vs = eval_for cx ty id body vs) /\
  (!cx e. !st res st'.
    ~supported_expr_exists expr_effect_root e /\
    eval_expr cx e st = (res,st') ==>
    st'.accounts = st.accounts /\ st'.tStorage = st.tStorage) /\
  (!cx es. !st res st'.
    ~supported_exprs_exists expr_effect_root es /\
    eval_exprs cx es st = (res,st') ==>
    st'.accounts = st.accounts /\ st'.tStorage = st.tStorage) /\
  (!cx bt. !st res st'.
    ~supported_target_exists expr_effect_root bt /\
    eval_base_place cx bt st = (res,st') ==>
    st'.accounts = st.accounts /\ st'.tStorage = st.tStorage) /\
  (!cx tgt. !st res st'.
    ~supported_target_exists expr_effect_root tgt /\
    eval_target_place cx tgt st = (res,st') ==>
    st'.accounts = st.accounts /\ st'.tStorage = st.tStorage) /\
  (!cx tgt v. assign_tuple_targets cx tgt v = assign_tuple_targets cx tgt v) /\
  (!cx tgts vs. assign_tuple_target_list cx tgts vs = assign_tuple_target_list cx tgts vs) /\
  (!cx es. !st res st'.
    ~supported_exprs_exists expr_effect_root es /\
    eval_expr_results cx es st = (res,st') ==>
    st'.accounts = st.accounts /\ st'.tStorage = st.tStorage)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[supported_expr_exists_def, expr_effect_root_def] >>
  rpt gen_tac >> strip_tac
  >~ [`eval_expr _ (Name _ _) _ = _`] >- suspend "name"
  >~ [`eval_expr _ (Literal _ _) _ = _`] >- gvs[Once evaluate_def, return_def]
  >~ [`eval_expr _ (TopLevelName _ _) _ = _`]
  >- (gvs[Once evaluate_def] >> drule lookup_global_state >> simp[])
  >~ [`eval_expr _ (FlagMember _ _ _) _ = _`]
  >- (gvs[Once evaluate_def] >> drule lookup_flag_mem_state >> simp[])
  >~ [`eval_expr _ (Attribute _ _ _) _ = _`] >- suspend "attribute"
  >~ [`eval_expr _ (Subscript _ _ _) _ = _`] >- suspend "subscript"
  >~ [`eval_expr _ (IfExp _ _ _ _) _ = _`] >- suspend "ifexp"
  >~ [`eval_expr _ (StructLit _ _ _) _ = _`] >- suspend "struct"
  >~ [`eval_expr _ (TypeBuiltin _ _ _ _) _ = _`] >- suspend "type_builtin"
  >~ [`eval_expr _ (Builtin _ _ _) _ = _`] >- suspend "builtin"
  >~ [`eval_exprs _ [] _ = _`] >- gvs[Once evaluate_def, return_def]
  >~ [`eval_expr_results _ [] _ = _`] >- gvs[Once evaluate_def, return_def]
  >~ [`eval_base_place _ (NameTarget _) _ = _`] >- suspend "name_target"
  >~ [`eval_base_place _ (TopLevelNameTarget _) _ = _`]
  >- (gvs[Once evaluate_def] >> drule lookup_global_state >> simp[])
  >~ [`eval_exprs _ (_::_) _ = _`] >- suspend "exprs"
  >~ [`eval_expr_results _ (_::_) _ = _`] >- suspend "results"
  >~ [`eval_base_place _ (AttributeTarget _ _) _ = _`] >- suspend "attr_target"
  >~ [`eval_base_place _ (SubscriptTarget _ _) _ = _`] >- suspend "sub_target" >>
  rpt strip_tac >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac get_place_state >> gvs[] >> metis_tac[]
QED

Resume evaluate_effect_free_storage[name]:
  gvs[Once evaluate_def, bind_def, get_scopes_def,
      type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  gvs[ignore_bind_def, bind_def, assert_def, return_def, raise_def, AllCaseEqs()]
QED

Resume evaluate_effect_free_storage[attribute]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ (Attribute _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED

Resume evaluate_effect_free_storage[subscript]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED

Resume evaluate_effect_free_storage[ifexp]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac read_result_state >>
  imp_res_tac conditional_result_state >> gvs[raise_def, AllCaseEqs()] >>
  rpt (qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
       IF_CASES_TAC >> simp[] >> strip_tac) >>
  gvs[raise_def] >> metis_tac[]
QED

Resume evaluate_effect_free_storage[struct]:
  rpt strip_tac >>
  gvs[supported_fields_exists_every, supported_exprs_exists_every,
      listTheory.EXISTS_MAP, combinTheory.o_DEF] >>
  qpat_x_assum `eval_expr _ (StructLit _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Resume evaluate_effect_free_storage[type_builtin]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ (TypeBuiltin _ _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac type_check_state >>
  imp_res_tac lift_sum_state >> gvs[return_def] >> metis_tac[]
QED

Resume evaluate_effect_free_storage[builtin]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac type_check_state >>
  imp_res_tac result_array_length_state >> imp_res_tac lift_sum_state >>
  imp_res_tac get_accounts_state >> imp_res_tac next_gas_reading_state >>
  gvs[return_def, AllCaseEqs()] >>
  rpt (qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
       IF_CASES_TAC >> simp[] >> strip_tac) >>
  gvs[bind_def, return_def, AllCaseEqs()] >>
  imp_res_tac result_array_length_state >> imp_res_tac lift_sum_state >>
  imp_res_tac get_accounts_state >> imp_res_tac next_gas_reading_state >>
  Cases_on `es` >> gvs[supported_expr_exists_def] >>
  gvs[type_check_def, assert_def, vyperContextTheory.builtin_args_length_ok_def,
      return_def, raise_def] >> metis_tac[]
QED

Resume evaluate_effect_free_storage[name_target]:
  gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
      type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
QED

Resume evaluate_effect_free_storage[exprs]:
  rpt strip_tac >>
  qpat_x_assum `eval_exprs _ (_::_) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED

Resume evaluate_effect_free_storage[results]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr_results _ (_::_) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Resume evaluate_effect_free_storage[attr_target]:
  rpt strip_tac >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac extend_place_state >> gvs[] >> metis_tac[]
QED

Resume evaluate_effect_free_storage[sub_target]:
  rpt strip_tac >>
  qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac extend_place_state >>
  gvs[] >> metis_tac[]
QED

Finalise evaluate_effect_free_storage

Theorem eval_expr_effect_free_storage:
  ~supported_expr_exists expr_effect_root e /\
  eval_expr cx e st = (res,st') ==>
  st'.accounts = st.accounts /\ st'.tStorage = st.tStorage
Proof
  metis_tac[evaluate_effect_free_storage]
QED

Theorem eval_exprs_effect_free_storage:
  ~supported_exprs_exists expr_effect_root es /\
  eval_exprs cx es st = (res,st') ==>
  st'.accounts = st.accounts /\ st'.tStorage = st.tStorage
Proof
  metis_tac[evaluate_effect_free_storage]
QED

Theorem eval_expr_results_effect_free_storage:
  ~supported_exprs_exists expr_effect_root es /\
  eval_expr_results cx es st = (res,st') ==>
  st'.accounts = st.accounts /\ st'.tStorage = st.tStorage
Proof
  metis_tac[evaluate_effect_free_storage]
QED

Theorem get_storage_accounts_transient_frame:
  st'.accounts = st.accounts /\ st'.tStorage = st.tStorage ==>
  get_storage cx st' tr = get_storage cx st tr
Proof
  Cases_on `tr` >> simp[get_storage_def]
QED

(* The other source fields used by delayed reads; storage is separate above. *)
Theorem evaluate_effect_free_source_fields[local]:
  (!cx s. eval_stmt cx s = eval_stmt cx s) /\
  (!cx ss. eval_stmts cx ss = eval_stmts cx ss) /\
  (!cx it. eval_iterator cx it = eval_iterator cx it) /\
  (!cx ty id body vs. eval_for cx ty id body vs = eval_for cx ty id body vs) /\
  (!cx e. !st res st'.
    ~supported_expr_exists expr_effect_root e /\
    eval_expr cx e st = (res,st') ==>
    st'.scopes = st.scopes /\ st'.immutables = st.immutables) /\
  (!cx es. !st res st'.
    ~supported_exprs_exists expr_effect_root es /\
    eval_exprs cx es st = (res,st') ==>
    st'.scopes = st.scopes /\ st'.immutables = st.immutables) /\
  (!cx bt. !st res st'.
    ~supported_target_exists expr_effect_root bt /\
    eval_base_place cx bt st = (res,st') ==>
    st'.scopes = st.scopes /\ st'.immutables = st.immutables) /\
  (!cx tgt. !st res st'.
    ~supported_target_exists expr_effect_root tgt /\
    eval_target_place cx tgt st = (res,st') ==>
    st'.scopes = st.scopes /\ st'.immutables = st.immutables) /\
  (!cx tgt v. assign_tuple_targets cx tgt v = assign_tuple_targets cx tgt v) /\
  (!cx tgts vs. assign_tuple_target_list cx tgts vs = assign_tuple_target_list cx tgts vs) /\
  (!cx es. !st res st'.
    ~supported_exprs_exists expr_effect_root es /\
    eval_expr_results cx es st = (res,st') ==>
    st'.scopes = st.scopes /\ st'.immutables = st.immutables)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[supported_expr_exists_def, expr_effect_root_def] >>
  rpt gen_tac >> strip_tac
  >~ [`eval_expr _ (Name _ _) _ = _`] >- suspend "name"
  >~ [`eval_expr _ (Literal _ _) _ = _`] >- gvs[Once evaluate_def, return_def]
  >~ [`eval_expr _ (TopLevelName _ _) _ = _`]
  >- (gvs[Once evaluate_def] >> drule lookup_global_state >> simp[])
  >~ [`eval_expr _ (FlagMember _ _ _) _ = _`]
  >- (gvs[Once evaluate_def] >> drule lookup_flag_mem_state >> simp[])
  >~ [`eval_expr _ (Attribute _ _ _) _ = _`] >- suspend "attribute"
  >~ [`eval_expr _ (Subscript _ _ _) _ = _`] >- suspend "subscript"
  >~ [`eval_expr _ (IfExp _ _ _ _) _ = _`] >- suspend "ifexp"
  >~ [`eval_expr _ (StructLit _ _ _) _ = _`] >- suspend "struct"
  >~ [`eval_expr _ (TypeBuiltin _ _ _ _) _ = _`] >- suspend "type_builtin"
  >~ [`eval_expr _ (Builtin _ _ _) _ = _`] >- suspend "builtin"
  >~ [`eval_exprs _ [] _ = _`] >- gvs[Once evaluate_def, return_def]
  >~ [`eval_expr_results _ [] _ = _`] >- gvs[Once evaluate_def, return_def]
  >~ [`eval_base_place _ (NameTarget _) _ = _`] >- suspend "name_target"
  >~ [`eval_base_place _ (TopLevelNameTarget _) _ = _`]
  >- (gvs[Once evaluate_def] >> drule lookup_global_state >> simp[])
  >~ [`eval_exprs _ (_::_) _ = _`] >- suspend "exprs"
  >~ [`eval_expr_results _ (_::_) _ = _`] >- suspend "results"
  >~ [`eval_base_place _ (AttributeTarget _ _) _ = _`] >- suspend "attr_target"
  >~ [`eval_base_place _ (SubscriptTarget _ _) _ = _`] >- suspend "sub_target" >>
  rpt strip_tac >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac get_place_state >> gvs[] >> metis_tac[]
QED

Resume evaluate_effect_free_source_fields[name]:
  gvs[Once evaluate_def, bind_def, get_scopes_def,
      type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  gvs[ignore_bind_def, bind_def, assert_def, return_def, raise_def, AllCaseEqs()]
QED

Resume evaluate_effect_free_source_fields[attribute]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ (Attribute _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED

Resume evaluate_effect_free_source_fields[subscript]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED

Resume evaluate_effect_free_source_fields[ifexp]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac read_result_state >>
  imp_res_tac conditional_result_state >> gvs[raise_def, AllCaseEqs()] >>
  rpt (qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
       IF_CASES_TAC >> simp[] >> strip_tac) >>
  gvs[raise_def] >> metis_tac[]
QED

Resume evaluate_effect_free_source_fields[struct]:
  rpt strip_tac >>
  gvs[supported_fields_exists_every, supported_exprs_exists_every,
      listTheory.EXISTS_MAP, combinTheory.o_DEF] >>
  qpat_x_assum `eval_expr _ (StructLit _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Resume evaluate_effect_free_source_fields[type_builtin]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ (TypeBuiltin _ _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac type_check_state >>
  imp_res_tac lift_sum_state >> gvs[return_def] >> metis_tac[]
QED

Resume evaluate_effect_free_source_fields[builtin]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac type_check_state >>
  imp_res_tac result_array_length_state >> imp_res_tac lift_sum_state >>
  imp_res_tac get_accounts_state >> imp_res_tac next_gas_reading_state >>
  gvs[return_def, AllCaseEqs()] >>
  rpt (qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
       IF_CASES_TAC >> simp[] >> strip_tac) >>
  gvs[bind_def, return_def, AllCaseEqs()] >>
  imp_res_tac result_array_length_state >> imp_res_tac lift_sum_state >>
  imp_res_tac get_accounts_state >> imp_res_tac next_gas_reading_state >>
  Cases_on `es` >> gvs[supported_expr_exists_def] >>
  gvs[type_check_def, assert_def, vyperContextTheory.builtin_args_length_ok_def,
      return_def, raise_def] >> metis_tac[]
QED

Resume evaluate_effect_free_source_fields[name_target]:
  gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
      type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
QED

Resume evaluate_effect_free_source_fields[exprs]:
  rpt strip_tac >>
  qpat_x_assum `eval_exprs _ (_::_) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED

Resume evaluate_effect_free_source_fields[results]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr_results _ (_::_) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Resume evaluate_effect_free_source_fields[attr_target]:
  rpt strip_tac >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac extend_place_state >> gvs[] >> metis_tac[]
QED

Resume evaluate_effect_free_source_fields[sub_target]:
  rpt strip_tac >>
  qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac extend_place_state >>
  gvs[] >> metis_tac[]
QED

Finalise evaluate_effect_free_source_fields

Theorem eval_expr_effect_free_source_fields:
  ~expr_has_effect e /\ eval_expr cx e st = (res,st') ==>
  st'.scopes = st.scopes /\ st'.immutables = st.immutables
Proof
  simp[expr_has_effect_def] >> metis_tac[evaluate_effect_free_source_fields]
QED

Theorem eval_exprs_effect_free_source_fields:
  ~EXISTS expr_has_effect es /\ eval_exprs cx es st = (res,st') ==>
  st'.scopes = st.scopes /\ st'.immutables = st.immutables
Proof
  strip_tac >>
  `~supported_exprs_exists expr_effect_root es` by
    (gvs[supported_exprs_exists_every, EXISTS_MEM, EVERY_MEM,
         expr_has_effect_def] >> metis_tac[]) >>
  metis_tac[evaluate_effect_free_source_fields]
QED

Theorem eval_expr_results_effect_free_source_fields:
  ~EXISTS expr_has_effect es /\ eval_expr_results cx es st = (res,st') ==>
  st'.scopes = st.scopes /\ st'.immutables = st.immutables
Proof
  strip_tac >>
  `~supported_exprs_exists expr_effect_root es` by
    (gvs[supported_exprs_exists_every, EXISTS_MEM, EVERY_MEM,
         expr_has_effect_def] >> metis_tac[]) >>
  metis_tac[evaluate_effect_free_source_fields]
QED

val _ = List.app (fn (name,th) =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail ("Effect-free source fields dependency: " ^ name) else ()
  end)
  [("evaluate_effect_free_source_fields", evaluate_effect_free_source_fields),
   ("eval_expr_effect_free_source_fields", eval_expr_effect_free_source_fields),
   ("eval_exprs_effect_free_source_fields", eval_exprs_effect_free_source_fields),
   ("eval_expr_results_effect_free_source_fields", eval_expr_results_effect_free_source_fields)];
