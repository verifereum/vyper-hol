(* Typing reads the function signatures only at the keys it calls.

   TOP-LEVEL: well_typed_fn_sigs_restrict, type_stmt_fn_sigs_restrict:
   restricting env.fn_sigs to a set holding every internal callee leaves
   expression and statement typing unchanged. The deployment bridge uses it
   to drop the constructor's own signature, which a constructor body never
   calls (the call graph is acyclic). *)
Theory whitelistCheckerFnSigs
Ancestors
  list pred_set finite_map vyperAST vyperTypeSystem vyperTypeCallGraph

Theorem subscript_base_type_exact_fn_sigs_restrict[local]:
  set (int_calls_expr e) SUBSET ks ==>
  (subscript_base_type_exact (env with fn_sigs := DRESTRICT env.fn_sigs ks) e <=>
   subscript_base_type_exact env e)
Proof
  Cases_on `e` >> simp[subscript_base_type_exact_def] >>
  rename1 `Call _ c` >> Cases_on `c` >>
  simp[subscript_base_type_exact_def, int_calls_expr_def, INSERT_SUBSET,
       FLOOKUP_DRESTRICT]
QED

Theorem well_typed_fn_sigs_restrict:
  (!env e. set (int_calls_expr e) SUBSET ks ==>
     (well_typed_expr (env with fn_sigs := DRESTRICT env.fn_sigs ks) e <=>
      well_typed_expr env e)) /\
  (!env e. set (int_calls_expr e) SUBSET ks ==>
     type_place_expr (env with fn_sigs := DRESTRICT env.fn_sigs ks) e =
     type_place_expr env e) /\
  (!env tgt. set (int_calls_target tgt) SUBSET ks ==>
     type_place_target (env with fn_sigs := DRESTRICT env.fn_sigs ks) tgt =
     type_place_target env tgt) /\
  (!env es. set (int_calls_exprs es) SUBSET ks ==>
     (well_typed_exprs (env with fn_sigs := DRESTRICT env.fn_sigs ks) es <=>
      well_typed_exprs env es)) /\
  (!env opt. set (int_calls_opt opt) SUBSET ks ==>
     (well_typed_opt (env with fn_sigs := DRESTRICT env.fn_sigs ks) opt <=>
      well_typed_opt env opt)) /\
  (!env kes. set (int_calls_named_exprs kes) SUBSET ks ==>
     (well_typed_named_exprs (env with fn_sigs := DRESTRICT env.fn_sigs ks) kes <=>
      well_typed_named_exprs env kes))
Proof
  ho_match_mp_tac well_typed_expr_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >> fs[int_calls_expr_def, UNION_SUBSET, INSERT_SUBSET] >>
  TRY (rename1 `Call _ (IntCall _) _ drv` >> Cases_on `drv`) >>
  ONCE_REWRITE_TAC[well_typed_expr_def] >>
  fs[FLOOKUP_DRESTRICT, subscript_base_type_exact_fn_sigs_restrict,
     int_calls_expr_def]
QED

Theorem int_calls_atargets_MEM[local]:
  !ts t. MEM t ts ==>
    set (int_calls_atarget t) SUBSET set (int_calls_atargets ts)
Proof
  Induct >> rw[int_calls_atarget_def] >> res_tac >> fs[SUBSET_DEF]
QED

Theorem well_typed_atarget_fn_sigs_restrict[local]:
  !env tgt ty. set (int_calls_atarget tgt) SUBSET ks ==>
    (well_typed_atarget (env with fn_sigs := DRESTRICT env.fn_sigs ks) tgt ty <=>
     well_typed_atarget env tgt ty)
Proof
  recInduct well_typed_atarget_ind >>
  rw[well_typed_atarget_def, well_typed_target_def, int_calls_atarget_def]
  >- (drule (cj 3 well_typed_fn_sigs_restrict) >> simp[]) >>
  `!tys. LIST_REL (\tgt ty. well_typed_atarget
            (env with fn_sigs := DRESTRICT env.fn_sigs ks) tgt ty) tgts tys <=>
         LIST_REL (\tgt ty. well_typed_atarget env tgt ty) tgts tys`
    suffices_by simp[] >>
  gen_tac >> irule EVERY2_cong >> rw[] >>
  metis_tac[int_calls_atargets_MEM, SUBSET_TRANS]
QED

Theorem atarget_accepts_fn_sigs_restrict[local]:
  set (int_calls_atarget tgt) SUBSET ks ==>
  (atarget_accepts (env with fn_sigs := DRESTRICT env.fn_sigs ks) tgt ty <=>
   atarget_accepts env tgt ty)
Proof
  Cases_on `tgt` >> rw[atarget_accepts_def, int_calls_atarget_def]
  >- (drule (cj 3 well_typed_fn_sigs_restrict) >> simp[]) >>
  irule well_typed_atarget_fn_sigs_restrict >> simp[int_calls_atarget_def]
QED

Theorem well_typed_iterator_fn_sigs_restrict[local]:
  set (int_calls_iterator it) SUBSET ks ==>
  (well_typed_iterator (env with fn_sigs := DRESTRICT env.fn_sigs ks) ty it <=>
   well_typed_iterator env ty it)
Proof
  Cases_on `it` >>
  rw[well_typed_iterator_def, int_calls_iterator_def, UNION_SUBSET] >>
  imp_res_tac (cj 1 well_typed_fn_sigs_restrict) >> simp[]
QED

Theorem target_mutable_fn_sigs_update[local]:
  target_mutable (env with fn_sigs := X) bt <=> target_mutable env bt
Proof
  Cases_on `bt` >> simp[target_mutable_def]
QED

Theorem extend_local_fn_sigs_restrict[local]:
  extend_local (env with fn_sigs := DRESTRICT env.fn_sigs ks) id ty b =
  extend_local env id ty b with
    fn_sigs := DRESTRICT (extend_local env id ty b).fn_sigs ks
Proof
  simp[extend_local_def]
QED

Theorem type_stmt_fn_sigs_restrict:
  (!env ret s. set (int_calls_stmt s) SUBSET ks ==>
     type_stmt (env with fn_sigs := DRESTRICT env.fn_sigs ks) ret s =
     OPTION_MAP (\e. e with fn_sigs := DRESTRICT e.fn_sigs ks)
       (type_stmt env ret s)) /\
  (!env ret ss. set (int_calls_stmts ss) SUBSET ks ==>
     type_stmts (env with fn_sigs := DRESTRICT env.fn_sigs ks) ret ss =
     OPTION_MAP (\e. e with fn_sigs := DRESTRICT e.fn_sigs ks)
       (type_stmts env ret ss))
Proof
  ho_match_mp_tac type_stmt_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >>
  fs[int_calls_stmt_def, int_calls_assert_reason_def, int_calls_expr_def,
     int_calls_raise_reason_def, UNION_SUBSET]
  >~ [`type_stmts _ _ (s::ss)`]
  >- (simp[Once type_stmt_def] >> simp[SimpRHS, Once type_stmt_def] >>
      Cases_on `type_stmt env ret s` >> gvs[]) >>
  ONCE_REWRITE_TAC[type_stmt_def] >>
  fs[well_typed_fn_sigs_restrict, atarget_accepts_fn_sigs_restrict,
     well_typed_iterator_fn_sigs_restrict, target_mutable_fn_sigs_update,
     extend_local_fn_sigs_restrict, well_typed_target_def,
     well_typed_custom_error_def, int_calls_iterator_def, optionTheory.IS_SOME_MAP] >>
  BasicProvers.every_case_tac >> rw[] >> fs[extend_local_def]
QED
