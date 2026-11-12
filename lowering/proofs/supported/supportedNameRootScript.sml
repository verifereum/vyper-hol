(* Supported code names no top-level root that is neither storage, an
   immutable nor a place root; in particular no constant declaration. *)
Theory supportedNameRoot
Ancestors
  supportedStmts supportedTargets supportedStmtTraverse supportedExprTraverse
  supportedExprs supportedExprForms supportedDecls vyperTypeContract
  vyperTypeConstantCells constSubst vyperAST list alist

(* p marks top-level names that are neither storage, immutable nor a place
   root; supported_pure_expr and supported_place_expr admit no such name. *)
Theorem supported_pure_no_name_root:
  (!tops e. supported_pure_expr tops e ==>
    (!x. p x ==> ?ty id. x = TopLevelName ty id /\
       ~supported_place_root tops id /\ ~supported_storage_value tops id ty /\
       supported_immutable_type tops id = NONE) ==>
    ~supported_expr_exists p e) /\
  (!tops es. supported_pure_exprs tops es ==>
    (!x. p x ==> ?ty id. x = TopLevelName ty id /\
       ~supported_place_root tops id /\ ~supported_storage_value tops id ty /\
       supported_immutable_type tops id = NONE) ==>
    ~supported_exprs_exists p es) /\
  (!tops fs. supported_pure_fields tops fs ==>
    (!x. p x ==> ?ty id. x = TopLevelName ty id /\
       ~supported_place_root tops id /\ ~supported_storage_value tops id ty /\
       supported_immutable_type tops id = NONE) ==>
    ~supported_fields_exists p fs) /\
  (!tops e. supported_place_expr tops e ==>
    (!x. p x ==> ?ty id. x = TopLevelName ty id /\
       ~supported_place_root tops id /\ ~supported_storage_value tops id ty /\
       supported_immutable_type tops id = NONE) ==>
    ~supported_expr_exists p e)
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  rw[supported_pure_expr_def, supported_expr_exists_def] >>
  rpt strip_tac >> res_tac >> gvs[]
QED

Theorem supported_effect_no_name_root:
  (!tops e. supported_effect_expr tops e ==>
    (!x. p x ==> ?ty id. x = TopLevelName ty id /\
       ~supported_place_root tops id /\ ~supported_storage_value tops id ty /\
       supported_immutable_type tops id = NONE) ==>
    ~supported_expr_exists p e) /\
  (!tops e. supported_effect_place_expr tops e ==>
    (!x. p x ==> ?ty id. x = TopLevelName ty id /\
       ~supported_place_root tops id /\ ~supported_storage_value tops id ty /\
       supported_immutable_type tops id = NONE) ==>
    ~supported_expr_exists p e)
Proof
  ho_match_mp_tac supported_effect_expr_ind >>
  rw[supported_effect_expr_def, supported_expr_exists_def] >>
  imp_res_tac supported_pure_no_name_root >>
  rpt strip_tac >> res_tac >> gvs[]
QED

Theorem supported_expr_no_name_root:
  supported_expr tops e /\
  (!x. p x ==> ?ty id. x = TopLevelName ty id /\
     ~supported_place_root tops id /\ ~supported_storage_value tops id ty /\
     supported_immutable_type tops id = NONE) ==>
  ~supported_expr_exists p e
Proof
  rw[supported_expr_def] >>
  metis_tac[supported_pure_no_name_root, supported_effect_no_name_root]
QED

Theorem supported_target_info_no_name_root:
  (!e:expr. T) /\
  (!target tops bindings.
    supported_target_info tops bindings target <> NONE /\
    (!x. p x ==> ?ty id. x = TopLevelName ty id /\
       ~supported_place_root tops id /\ ~supported_storage_value tops id ty /\
       supported_immutable_type tops id = NONE) ==>
    ~supported_target_exists p target)
Proof
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[supported_target_info_def, supported_expr_exists_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[supported_expr_no_name_root]
QED

Theorem supported_target_no_name_root[local]:
  supported_target tops bindings target /\
  (!x. p x ==> ?ty id. x = TopLevelName ty id /\
     ~supported_place_root tops id /\ ~supported_storage_value tops id ty /\
     supported_immutable_type tops id = NONE) ==>
  ~supported_target_exists p target
Proof
  Cases_on `target` >>
  simp[supported_target_def, supported_expr_exists_def] >>
  qmatch_goalsub_rename_tac `supported_target_exists p parent` >>
  Cases_on `parent` >> simp[supported_expr_exists_def] >>
  metis_tac[supported_expr_no_name_root]
QED

Theorem supported_assignment_no_name_root[local]:
  supported_assignment tops bindings target e /\
  (!x. p x ==> ?ty id. x = TopLevelName ty id /\
     ~supported_place_root tops id /\ ~supported_storage_value tops id ty /\
     supported_immutable_type tops id = NONE) ==>
  ~supported_assignment_exists p target /\ ~supported_expr_exists p e
Proof
  strip_tac >> fs[supported_assignment_def] >>
  `~supported_expr_exists p e` by metis_tac[supported_expr_no_name_root] >>
  simp[] >> Cases_on `target` >> gvs[supported_assignment_exists_def]
  >~ [`supported_assignments_exists p targets`]
  >- (qpat_x_assum `EVERY _ targets` mp_tac >>
  Induct_on `targets` >> simp[supported_assignment_exists_def] >>
  qx_gen_tac `head` >> Cases_on `head` >>
      simp[supported_assignment_exists_def] >>
      metis_tac[supported_target_no_name_root]) >>
  Cases_on `supported_target_info tops bindings b` >> gvs[] >>
  metis_tac[supported_target_no_name_root,
            cj 2 supported_target_info_no_name_root,
            optionTheory.NOT_SOME_NONE]
QED

Theorem supported_string_reason_no_name_root:
  supported_string_reason tops e /\
  (!x. p x ==> ?ty id. x = TopLevelName ty id /\
     ~supported_place_root tops id /\ ~supported_storage_value tops id ty /\
     supported_immutable_type tops id = NONE) ==>
  ~supported_expr_exists p e
Proof
  strip_tac >> Cases_on `?ty text. e = Literal ty (StringL text)`
  >- (gvs[supported_expr_exists_def] >> strip_tac >> res_tac >> gvs[]) >>
  `supported_pure_expr tops e` suffices_by
    metis_tac[supported_pure_no_name_root] >>
  Cases_on `e` >> gvs[supported_string_reason_def] >>
  rename1 `Literal _ lit` >> Cases_on `lit` >>
  gvs[supported_string_reason_def, supported_pure_expr_def]
QED

Theorem supported_range_bounds[local]:
  supported_iterator tops ty (Range a b) n ==>
  (supported_pure_expr tops a \/ ?t l. a = Literal t l) /\
  (supported_pure_expr tops b \/ ?t l. b = Literal t l)
Proof
  simp[supported_iterator_def] >>
  Cases_on `a` >> simp[] >>
  rename1 `Literal ta la` >> Cases_on `la` >> simp[] >>
  Cases_on `b` >> simp[] >>
  rename1 `Literal tb lb` >> Cases_on `lb` >> simp[]
QED

Theorem supported_iterator_no_name_root[local]:
  supported_iterator tops ty it n /\
  (!x. p x ==> ?ty id. x = TopLevelName ty id /\
     ~supported_place_root tops id /\ ~supported_storage_value tops id ty /\
     supported_immutable_type tops id = NONE) ==>
  ~supported_iterator_exists p it
Proof
  Cases_on `it` >> simp[supported_iterator_exists_def]
  >- (rename1 `Array e` >> simp[supported_iterator_def] >> strip_tac >>
      Cases_on `(?t v. e = Name t v) \/ (?t nid. e = TopLevelName t nid)`
      >- (pop_assum strip_assume_tac >>
          gvs[supported_expr_exists_def] >> strip_tac >> res_tac >> gvs[] >>
          Cases_on `t` >> gvs[]) >>
      `supported_expr tops e` by (Cases_on `e` >> gvs[]) >>
      metis_tac[supported_expr_no_name_root]) >>
  strip_tac >> drule supported_range_bounds >> strip_tac >>
  imp_res_tac supported_pure_no_name_root >>
  gvs[supported_expr_exists_def] >> rpt strip_tac >> res_tac >> gvs[]
QED

Theorem supported_stmts_no_name_root:
  (!tops bindings s. supported_stmt tops bindings s ==>
    (!x. p x ==> ?ty id. x = TopLevelName ty id /\
       ~supported_place_root tops id /\ ~supported_storage_value tops id ty /\
       supported_immutable_type tops id = NONE) ==>
    ~supported_stmt_expr_exists p s) /\
  (!tops bindings ss. supported_stmts tops bindings ss ==>
    (!x. p x ==> ?ty id. x = TopLevelName ty id /\
       ~supported_place_root tops id /\ ~supported_storage_value tops id ty /\
       supported_immutable_type tops id = NONE) ==>
    ~supported_stmts_expr_exists p ss)
Proof
  ho_match_mp_tac supported_stmt_ind >>
  rw[supported_stmt_def, supported_stmt_expr_exists_def,
     supported_expr_exists_def]
  >~ [`supported_aug_target tops bindings target`,
      `~supported_target_exists p target`]
  >- (gvs[supported_aug_target_def] >>
      Cases_on `supported_target_info tops bindings target` >- gvs[] >>
      irule (cj 2 supported_target_info_no_name_root) >>
      qexistsl [`bindings`, `tops`] >> simp[])
  >~ [`supported_append_target tops target`]
  >- (Cases_on `target` >> gvs[supported_append_target_def,
                                supported_expr_exists_def] >>
      metis_tac[supported_pure_no_name_root])
  >~ [`supported_assert_exists p reason`]
  >- (Cases_on `reason` >>
      gvs[supported_assert_reason_def, supported_assert_exists_def] >>
      metis_tac[supported_string_reason_no_name_root,
                supported_pure_no_name_root])
  >~ [`supported_raise_exists p reason`]
  >- (Cases_on `reason` >>
      gvs[supported_raise_reason_def, supported_raise_exists_def] >>
      metis_tac[supported_string_reason_no_name_root])
  >~ [`supported_log tops id es`]
  >- (gvs[supported_log_def] >> metis_tac[supported_pure_no_name_root])
  >> rpt strip_tac >>
  imp_res_tac supported_expr_no_name_root >>
  imp_res_tac supported_assignment_no_name_root >>
  imp_res_tac supported_target_no_name_root >>
  imp_res_tac supported_iterator_no_name_root >>
  imp_res_tac (cj 1 supported_pure_no_name_root) >>
  gvs[]
QED

(* ===== Constant declarations ===== *)

(* A constant is neither a place root, storage nor an immutable. *)
Theorem supported_constant_decl_not_root:
  supported_variable_decl tops id = SOME (vis,Constant c,ty,slot) ==>
  ~supported_place_root tops id /\ ~supported_storage_value tops id ty' /\
  supported_immutable_type tops id = NONE
Proof
  Cases_on `vis` >> Cases_on `slot` >>
  simp[supported_place_root_def, supported_storage_value_def,
       supported_immutable_type_def]
QED

Theorem supported_variable_decl_distinct_mem:
  !tops.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) tops)) /\
    MEM (VariableDecl vis mut id ty slot) tops ==>
    supported_variable_decl tops (NONE,id) = SOME (vis,mut,ty,slot)
Proof
  Induct >> simp[supported_variable_decl_def] >> Cases >>
  simp[toplevel_vtype_keys_toplevel_def, supported_variable_decl_def,
       ALL_DISTINCT_APPEND] >>
  rw[] >> gvs[] >>
  metis_tac[vyperTypeConstantCellsTheory.module_toplevel_vtype_key_MEM_Variable_any]
QED

Theorem module_consts_env_names_MEM[local]:
  !tops acc id.
    MEM id (MAP FST (module_consts_env tops acc)) ==>
    MEM id (MAP FST acc) \/
    ?vis c ty slot. MEM (VariableDecl vis (Constant c) id ty slot) tops
Proof
  recInduct module_consts_env_ind >> rw[module_consts_env_def] >>
  res_tac >> gvs[] >> metis_tac[]
QED

(* With distinct top-level keys, every name module_consts_env binds is the
   constant supported_variable_decl finds. *)
Theorem distinct_module_consts_env_names_constant:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) ==>
  !id. MEM id (MAP FST (module_consts_env tops [])) ==>
    ?vis c ty slot.
      supported_variable_decl tops (NONE,id) = SOME (vis,Constant c,ty,slot)
Proof
  rpt strip_tac >> drule module_consts_env_names_MEM >> rw[] >>
  drule_all supported_variable_decl_distinct_mem >> simp[]
QED

