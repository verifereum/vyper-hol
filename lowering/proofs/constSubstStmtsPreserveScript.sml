(* What a body keeps under subst_consts_stmts: its abi_decode targets and its
   internal calls when every inlined constant is free of them, and the whole
   body when it is supported and every substituted name is a constant. *)
Theory constSubstStmtsPreserve
Ancestors
  constSubstCorrect constSubst supportedProgram supportedStmts supportedTargets
  supportedStmtTraverse supportedExprTraverse supportedExprs supportedExprForms
  supportedDecls vyperTypeContract vyperTypeCallGraph vyperAST list alist

(* ===== abi_decode targets ===== *)

Theorem subst_consts_expr_abi_decode_target:
  (!env e.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists (expr_abi_decode_target_root tgt) r) ==>
    ~supported_expr_exists (expr_abi_decode_target_root tgt) e ==>
    ~supported_expr_exists (expr_abi_decode_target_root tgt)
      (subst_consts_expr env e)) /\
  (!env t.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists (expr_abi_decode_target_root tgt) r) ==>
    ~supported_target_exists (expr_abi_decode_target_root tgt) t ==>
    ~supported_target_exists (expr_abi_decode_target_root tgt)
      (subst_consts_btarget env t)) /\
  (!env es.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists (expr_abi_decode_target_root tgt) r) ==>
    ~supported_exprs_exists (expr_abi_decode_target_root tgt) es ==>
    ~supported_exprs_exists (expr_abi_decode_target_root tgt)
      (subst_consts_exprs env es)) /\
  (!env opt.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists (expr_abi_decode_target_root tgt) r) ==>
    ~supported_opt_exists (expr_abi_decode_target_root tgt) opt ==>
    ~supported_opt_exists (expr_abi_decode_target_root tgt)
      (subst_consts_opt env opt)) /\
  (!env fs.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists (expr_abi_decode_target_root tgt) r) ==>
    ~supported_fields_exists (expr_abi_decode_target_root tgt) fs ==>
    ~supported_fields_exists (expr_abi_decode_target_root tgt)
      (subst_consts_fields env fs))
Proof
  ho_match_mp_tac subst_consts_expr_ind >>
  simp[subst_consts_expr_def, supported_expr_exists_def,
       expr_abi_decode_target_root_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `ns` >>
      simp[subst_consts_expr_def, supported_expr_exists_def,
           expr_abi_decode_target_root_def] >>
      Cases_on `ALOOKUP env id` >>
      gvs[supported_expr_exists_def, expr_abi_decode_target_root_def] >>
      metis_tac[])
  >~ [`TypeBuiltin`]
  >- (Cases_on `bi` >> gvs[expr_abi_decode_target_root_def])
  >> metis_tac[]
QED

Theorem subst_consts_target_abi_decode_target:
  (!env t.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists (expr_abi_decode_target_root tgt) r) ==>
    ~supported_assignment_exists (expr_abi_decode_target_root tgt) t ==>
    ~supported_assignment_exists (expr_abi_decode_target_root tgt)
      (subst_consts_target env t)) /\
  (!env ts.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists (expr_abi_decode_target_root tgt) r) ==>
    ~supported_assignments_exists (expr_abi_decode_target_root tgt) ts ==>
    ~supported_assignments_exists (expr_abi_decode_target_root tgt)
      (subst_consts_targets env ts))
Proof
  ho_match_mp_tac subst_consts_target_ind >>
  simp[subst_consts_target_def, supported_assignment_exists_def] >>
  metis_tac[subst_consts_expr_abi_decode_target]
QED

Theorem subst_consts_error_exprs[local]:
  custom_error_exprs (subst_consts_error env err) =
  MAP (subst_consts_expr env) (custom_error_exprs err)
Proof
  Cases_on `err` >>
  simp[subst_consts_error_def, custom_error_exprs_def, subst_consts_fields_maps,
       subst_consts_exprs_map]
QED

Theorem subst_consts_stmt_abi_decode_target:
  (!env s.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists (expr_abi_decode_target_root tgt) r) ==>
    ~supported_stmt_expr_exists (expr_abi_decode_target_root tgt) s ==>
    ~supported_stmt_expr_exists (expr_abi_decode_target_root tgt)
      (subst_consts_stmt env s)) /\
  (!env ss.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists (expr_abi_decode_target_root tgt) r) ==>
    ~supported_stmts_expr_exists (expr_abi_decode_target_root tgt) ss ==>
    ~supported_stmts_expr_exists (expr_abi_decode_target_root tgt)
      (subst_consts_stmts env ss))
Proof
  ho_match_mp_tac subst_consts_stmt_ind >>
  simp[subst_consts_stmt_def, supported_stmt_expr_exists_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> strip_tac
  >~ [`subst_consts_iter`]
  >- (Cases_on `it` >>
      gvs[subst_consts_iter_def, supported_iterator_exists_def] >>
      metis_tac[subst_consts_expr_abi_decode_target])
  >~ [`subst_consts_areason`]
  >- (Cases_on `r` >>
      gvs[subst_consts_areason_def, supported_assert_exists_def,
          subst_consts_error_exprs, EXISTS_MAP, EXISTS_MEM, MEM_MAP, PULL_EXISTS] >>
      metis_tac[subst_consts_expr_abi_decode_target])
  >~ [`subst_consts_rreason`]
  >- (Cases_on `r` >>
      gvs[subst_consts_rreason_def, supported_raise_exists_def,
          subst_consts_error_exprs, EXISTS_MAP, EXISTS_MEM, MEM_MAP, PULL_EXISTS] >>
      metis_tac[subst_consts_expr_abi_decode_target])
  >> metis_tac[subst_consts_expr_abi_decode_target,
               subst_consts_target_abi_decode_target]
QED

(* ===== Internal calls ===== *)

Theorem subst_consts_expr_int_calls:
  (!env e.
    (!id r. ALOOKUP env id = SOME r ==> int_calls_expr r = []) ==>
    int_calls_expr (subst_consts_expr env e) = int_calls_expr e) /\
  (!env t.
    (!id r. ALOOKUP env id = SOME r ==> int_calls_expr r = []) ==>
    int_calls_target (subst_consts_btarget env t) = int_calls_target t) /\
  (!env es.
    (!id r. ALOOKUP env id = SOME r ==> int_calls_expr r = []) ==>
    int_calls_exprs (subst_consts_exprs env es) = int_calls_exprs es) /\
  (!env opt.
    (!id r. ALOOKUP env id = SOME r ==> int_calls_expr r = []) ==>
    int_calls_opt (subst_consts_opt env opt) = int_calls_opt opt) /\
  (!env fs.
    (!id r. ALOOKUP env id = SOME r ==> int_calls_expr r = []) ==>
    int_calls_named_exprs (subst_consts_fields env fs) =
    int_calls_named_exprs fs)
Proof
  ho_match_mp_tac subst_consts_expr_ind >>
  rpt strip_tac >> res_tac >>
  gvs[subst_consts_expr_def, int_calls_expr_def]
  >~ [`Call`] >- (Cases_on `ct` >> gvs[int_calls_expr_def])
  >> rpt CASE_TAC >> gvs[int_calls_expr_def] >> res_tac
QED

Theorem subst_consts_int_calls_all[local]:
  (!id r. ALOOKUP env id = SOME r ==> int_calls_expr r = []) ==>
  (!e. int_calls_expr (subst_consts_expr env e) = int_calls_expr e) /\
  (!t. int_calls_target (subst_consts_btarget env t) = int_calls_target t) /\
  (!es. int_calls_exprs (subst_consts_exprs env es) = int_calls_exprs es) /\
  (!opt. int_calls_opt (subst_consts_opt env opt) = int_calls_opt opt)
Proof
  metis_tac[subst_consts_expr_int_calls]
QED

Theorem subst_consts_target_int_calls:
  (!env t.
    (!id r. ALOOKUP env id = SOME r ==> int_calls_expr r = []) ==>
    int_calls_atarget (subst_consts_target env t) = int_calls_atarget t) /\
  (!env ts.
    (!id r. ALOOKUP env id = SOME r ==> int_calls_expr r = []) ==>
    int_calls_atargets (subst_consts_targets env ts) = int_calls_atargets ts)
Proof
  ho_match_mp_tac subst_consts_target_ind >>
  rpt strip_tac >> res_tac >>
  drule_then strip_assume_tac subst_consts_int_calls_all >>
  gvs[subst_consts_target_def, int_calls_atarget_def]
QED

Theorem subst_consts_stmt_int_calls:
  (!env s.
    (!id r. ALOOKUP env id = SOME r ==> int_calls_expr r = []) ==>
    int_calls_stmt (subst_consts_stmt env s) = int_calls_stmt s) /\
  (!env ss.
    (!id r. ALOOKUP env id = SOME r ==> int_calls_expr r = []) ==>
    int_calls_stmts (subst_consts_stmts env ss) = int_calls_stmts ss)
Proof
  ho_match_mp_tac subst_consts_stmt_ind >>
  rpt strip_tac >> res_tac >>
  drule_then strip_assume_tac subst_consts_int_calls_all >>
  drule_then assume_tac (cj 1 subst_consts_target_int_calls) >>
  gvs[subst_consts_stmt_def, int_calls_stmt_def]
  >~ [`subst_consts_iter`]
  >- (Cases_on `it` >> gvs[subst_consts_iter_def, int_calls_iterator_def])
  >~ [`subst_consts_areason`]
  >- (Cases_on `r` >>
      gvs[subst_consts_areason_def, int_calls_assert_reason_def,
          subst_consts_error_exprs, GSYM subst_consts_exprs_map])
  >~ [`subst_consts_rreason`]
  >- (Cases_on `r` >>
      gvs[subst_consts_rreason_def, int_calls_raise_reason_def,
          subst_consts_error_exprs, GSYM subst_consts_exprs_map])
QED

(* ===== Substitution leaves a body with no substituted name unchanged ===== *)

Theorem subst_consts_expr_unchanged:
  (!env e.
    ~supported_expr_exists
       (\x. ?ty id. x = TopLevelName ty (NONE,id) /\ IS_SOME (ALOOKUP env id)) e ==>
    subst_consts_expr env e = e) /\
  (!env t.
    ~supported_target_exists
       (\x. ?ty id. x = TopLevelName ty (NONE,id) /\ IS_SOME (ALOOKUP env id)) t ==>
    subst_consts_btarget env t = t) /\
  (!env es.
    ~supported_exprs_exists
       (\x. ?ty id. x = TopLevelName ty (NONE,id) /\ IS_SOME (ALOOKUP env id)) es ==>
    subst_consts_exprs env es = es) /\
  (!env opt.
    ~supported_opt_exists
       (\x. ?ty id. x = TopLevelName ty (NONE,id) /\ IS_SOME (ALOOKUP env id)) opt ==>
    subst_consts_opt env opt = opt) /\
  (!env fs.
    ~supported_fields_exists
       (\x. ?ty id. x = TopLevelName ty (NONE,id) /\ IS_SOME (ALOOKUP env id)) fs ==>
    subst_consts_fields env fs = fs)
Proof
  ho_match_mp_tac subst_consts_expr_ind >>
  rw[subst_consts_expr_def, supported_expr_exists_def] >>
  rpt CASE_TAC >> gvs[]
QED

Theorem subst_consts_target_unchanged:
  (!env t.
    ~supported_assignment_exists
       (\x. ?ty id. x = TopLevelName ty (NONE,id) /\ IS_SOME (ALOOKUP env id)) t ==>
    subst_consts_target env t = t) /\
  (!env ts.
    ~supported_assignments_exists
       (\x. ?ty id. x = TopLevelName ty (NONE,id) /\ IS_SOME (ALOOKUP env id)) ts ==>
    subst_consts_targets env ts = ts)
Proof
  ho_match_mp_tac subst_consts_target_ind >>
  rw[subst_consts_target_def, supported_assignment_exists_def,
     subst_consts_expr_unchanged]
QED

Theorem subst_consts_fields_unchanged[local]:
  !fs. ~EXISTS (supported_expr_exists
         (\x. ?ty id. x = TopLevelName ty (NONE,id) /\ IS_SOME (ALOOKUP env id)))
         (MAP SND fs) ==>
       subst_consts_fields env fs = fs
Proof
  Induct >> simp[subst_consts_expr_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >> gvs[subst_consts_expr_unchanged]
QED

Theorem subst_consts_error_unchanged[local]:
  ~EXISTS (supported_expr_exists
     (\x. ?ty id. x = TopLevelName ty (NONE,id) /\ IS_SOME (ALOOKUP env id)))
     (custom_error_exprs err) ==>
  subst_consts_error env err = err
Proof
  Cases_on `err` >>
  rw[subst_consts_error_def, custom_error_exprs_def, EXISTS_APPEND,
     subst_consts_fields_unchanged] >>
  irule (cj 3 subst_consts_expr_unchanged) >>
  gvs[supported_exprs_exists_every]
QED

Theorem subst_consts_stmt_unchanged:
  (!env s.
    ~supported_stmt_expr_exists
       (\x. ?ty id. x = TopLevelName ty (NONE,id) /\ IS_SOME (ALOOKUP env id)) s ==>
    subst_consts_stmt env s = s) /\
  (!env ss.
    ~supported_stmts_expr_exists
       (\x. ?ty id. x = TopLevelName ty (NONE,id) /\ IS_SOME (ALOOKUP env id)) ss ==>
    subst_consts_stmts env ss = ss)
Proof
  ho_match_mp_tac subst_consts_stmt_ind >>
  rw[subst_consts_stmt_def, supported_stmt_expr_exists_def,
     subst_consts_expr_unchanged, subst_consts_target_unchanged]
  >~ [`subst_consts_iter`]
  >- (Cases_on `it` >>
      gvs[subst_consts_iter_def, supported_iterator_exists_def,
          subst_consts_expr_unchanged])
  >~ [`subst_consts_areason`]
  >- (Cases_on `r` >>
      gvs[subst_consts_areason_def, supported_assert_exists_def,
          subst_consts_expr_unchanged, subst_consts_error_unchanged])
  >~ [`subst_consts_rreason`]
  >- (Cases_on `r` >>
      gvs[subst_consts_rreason_def, supported_raise_exists_def,
          subst_consts_expr_unchanged, subst_consts_error_unchanged])
QED

(* ===== A supported body names no top-level root it cannot read ===== *)

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

Theorem supported_target_info_no_name_root[local]:
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

Theorem supported_string_reason_no_name_root[local]:
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

(* ===== P1: a supported body is unchanged when every substituted name is a
   constant declaration ===== *)

Theorem subst_consts_supported_stmts_unchanged:
  (!id. IS_SOME (ALOOKUP E id) ==>
     ?vis c ty slot.
       supported_variable_decl tops (NONE,id) = SOME (vis,Constant c,ty,slot)) /\
  supported_stmts tops bindings ss ==>
  subst_consts_stmts E ss = ss
Proof
  strip_tac >> irule (cj 2 subst_consts_stmt_unchanged) >>
  drule_then irule (cj 2 supported_stmts_no_name_root) >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  Cases_on `vis` >> Cases_on `slot` >>
  simp[supported_place_root_def, supported_storage_value_def,
       supported_immutable_type_def]
QED

(* ===== P1's premise at entry: every substituted name is a constant ===== *)

Theorem module_consts_env_names[local]:
  !tops acc.
    MAP FST (module_consts_env tops acc) = MAP FST acc ++ const_decl_names tops
Proof
  recInduct module_consts_env_ind >>
  simp[module_consts_env_def, const_decl_names_def]
QED

Theorem supported_variable_decl_distinct_mem[local]:
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

Theorem checked_module_consts_env_names_constant:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods NONE = SOME tops ==>
  !id. IS_SOME (ALOOKUP (module_consts_env tops []) id) ==>
    ?vis c ty slot.
      supported_variable_decl tops (NONE,id) = SOME (vis,Constant c,ty,slot)
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[vyperTypeContractStaticMapsTheory.check_contract_runtime_namespaces,
      vyperTypeContractStaticMapsTheory.contract_namespaces_ok_module_toplevel_vtype_keys,
      ALOOKUP_MEM] >>
  `MEM id (const_decl_names tops)` by
    (gvs[optionTheory.IS_SOME_EXISTS] >> imp_res_tac ALOOKUP_MEM >>
     `MEM id (MAP FST (module_consts_env tops []))` by
       (simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
     gvs[module_consts_env_names]) >>
  gvs[const_decl_names_MEM] >>
  drule_all supported_variable_decl_distinct_mem >> simp[]
QED
