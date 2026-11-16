(* What a body keeps under subst_consts_stmts: its abi_decode targets and its
   internal calls when every inlined constant is free of them, and the whole
   body when it is supported and every substituted name is a constant. *)
Theory constSubstStmtsPreserve
Ancestors
  supportedNameRoot constSubstCorrect constSubst supportedProgram supportedStmts
  supportedTargets supportedStmtTraverse supportedExprTraverse supportedExprs
  supportedExprForms supportedDecls vyperTypeContract vyperTypeCallGraph vyperAST
  list alist

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
  drule supported_constant_decl_not_root >> simp[]
QED

(* ===== P1's premise at entry: every substituted name is a constant ===== *)

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
  drule distinct_module_consts_env_names_constant >> disch_then irule >>
  spose_not_then assume_tac >> gvs[GSYM ALOOKUP_NONE]
QED
