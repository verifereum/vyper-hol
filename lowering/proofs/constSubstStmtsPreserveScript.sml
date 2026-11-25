(* What a body keeps under subst_consts_stmts: its abi_decode targets and its
   internal calls when every inlined constant is free of them. *)
Theory constSubstStmtsPreserve
Ancestors
  supportedNameRoot supportedIteratorProps constSubstCorrect constSubstStmts constSubst supportedProgram supportedStmts
  supportedTargets supportedStmtTraverse supportedExprTraverse supportedExprs
  supportedExprForms supportedDecls vyperTypeContract vyperTypeCallGraph vyperAST
  exprSimHypsDefs exprLowering compileVyper vyperTypeSystem vyperTypeEnv
  vyperTypeContractContext vyperTypeContractStaticMaps vyperTypeEnvExtension
  vyperTypeContractFunction
  placeTypingBuildProps constSubstMods finite_map list alist

Theorem subst_consts_stmt_bindings:
  (!E s. supported_stmt_bindings locals (subst_consts_stmt E s) =
          supported_stmt_bindings locals s) /\
  (!E ss. supported_stmts_bindings locals (subst_consts_stmts E ss) =
           supported_stmts_bindings locals ss)
Proof
  ho_match_mp_tac subst_consts_stmt_ind >>
  simp[subst_consts_stmt_def, supported_stmt_bindings_def]
QED

(* ===== abi_decode targets ===== *)

Theorem constant_expr_no_abi_decode:
  (!e. constant_expr mods e ==>
     ~supported_expr_exists (expr_abi_decode_target_root tgt) e) /\
  (!es. EVERY (constant_expr mods) es ==>
     ~supported_exprs_exists (expr_abi_decode_target_root tgt) es) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) ==>
     ~supported_fields_exists (expr_abi_decode_target_root tgt) fs)
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[constant_expr_def, supported_expr_exists_def, expr_abi_decode_target_root_def] >>
  rpt strip_tac >>
  Cases_on `bi` >>
  gvs[constant_type_builtin_def, expr_abi_decode_target_root_def]
QED

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

Theorem closed_constant_no_const_name[local]:
  (!e. constant_expr [(NONE,tops)] e /\ const_local_refs e = [] ==>
    ~supported_expr_exists (const_name_root_mods [(NONE,tops)]) e) /\
  (!es. EVERY (constant_expr [(NONE,tops)]) es /\ const_local_exprs es = [] ==>
    ~supported_exprs_exists (const_name_root_mods [(NONE,tops)]) es) /\
  (!fs. EVERY (constant_expr [(NONE,tops)]) (MAP SND fs) /\ const_local_fields fs = [] ==>
    ~supported_fields_exists (const_name_root_mods [(NONE,tops)]) fs)
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[constant_expr_def, const_local_refs_def, supported_expr_exists_def,
       const_name_root_mods_def] >>
  rpt strip_tac >> gvs[]
  >- (PairCases_on `ns` >> Cases_on `ns0` >>
      gvs[const_local_refs_def, const_name_root_mods_def, cx_const_name_mods_def]) >>
  metis_tac[]
QED

Theorem subst_consts_expr_const_name_free[local]:
  (!env e.
    (!id. ALOOKUP env id = NONE ==>
      ALOOKUP (module_consts_env tops []) id = NONE) /\
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists (const_name_root_mods [(NONE,tops)]) r) ==>
    ~supported_expr_exists (const_name_root_mods [(NONE,tops)])
      (subst_consts_expr env e)) /\
  (!env t.
    (!id. ALOOKUP env id = NONE ==>
      ALOOKUP (module_consts_env tops []) id = NONE) /\
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists (const_name_root_mods [(NONE,tops)]) r) ==>
    ~supported_target_exists (const_name_root_mods [(NONE,tops)])
      (subst_consts_btarget env t)) /\
  (!env es.
    (!id. ALOOKUP env id = NONE ==>
      ALOOKUP (module_consts_env tops []) id = NONE) /\
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists (const_name_root_mods [(NONE,tops)]) r) ==>
    ~supported_exprs_exists (const_name_root_mods [(NONE,tops)])
      (subst_consts_exprs env es)) /\
  (!env opt.
    (!id. ALOOKUP env id = NONE ==>
      ALOOKUP (module_consts_env tops []) id = NONE) /\
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists (const_name_root_mods [(NONE,tops)]) r) ==>
    ~supported_opt_exists (const_name_root_mods [(NONE,tops)])
      (subst_consts_opt env opt)) /\
  (!env fs.
    (!id. ALOOKUP env id = NONE ==>
      ALOOKUP (module_consts_env tops []) id = NONE) /\
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists (const_name_root_mods [(NONE,tops)]) r) ==>
    ~supported_fields_exists (const_name_root_mods [(NONE,tops)])
      (subst_consts_fields env fs))
Proof
  ho_match_mp_tac subst_consts_expr_ind >>
  simp[subst_consts_expr_def, supported_expr_exists_def,
       const_name_root_mods_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `ns` >>
      gvs[subst_consts_expr_def, supported_expr_exists_def,
          const_name_root_mods_def] >>
      Cases_on `ALOOKUP env id` >>
      gvs[supported_expr_exists_def, const_name_root_mods_def,
          cx_const_name_mods_def]
      >- (qpat_x_assum `!id. ALOOKUP env id = NONE ==> _`
        (qspec_then `id` mp_tac) >> gvs[ALOOKUP_NONE]) >>
      metis_tac[])
  >> metis_tac[]
QED

Theorem subst_consts_target_const_name_free[local]:
  (!env t.
    (!id. ALOOKUP env id = NONE ==>
      ALOOKUP (module_consts_env tops []) id = NONE) /\
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists (const_name_root_mods [(NONE,tops)]) r) ==>
    ~supported_assignment_exists (const_name_root_mods [(NONE,tops)])
      (subst_consts_target env t)) /\
  (!env ts.
    (!id. ALOOKUP env id = NONE ==>
      ALOOKUP (module_consts_env tops []) id = NONE) /\
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists (const_name_root_mods [(NONE,tops)]) r) ==>
    ~supported_assignments_exists (const_name_root_mods [(NONE,tops)])
      (subst_consts_targets env ts))
Proof
  ho_match_mp_tac subst_consts_target_ind >>
  simp[subst_consts_target_def, supported_assignment_exists_def] >>
  metis_tac[subst_consts_expr_const_name_free]
QED

Theorem subst_consts_stmt_const_name_free[local]:
  (!env s.
    (!id. ALOOKUP env id = NONE ==>
      ALOOKUP (module_consts_env tops []) id = NONE) /\
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists (const_name_root_mods [(NONE,tops)]) r) ==>
    ~supported_stmt_expr_exists (const_name_root_mods [(NONE,tops)])
      (subst_consts_stmt env s)) /\
  (!env ss.
    (!id. ALOOKUP env id = NONE ==>
      ALOOKUP (module_consts_env tops []) id = NONE) /\
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists (const_name_root_mods [(NONE,tops)]) r) ==>
    ~supported_stmts_expr_exists (const_name_root_mods [(NONE,tops)])
      (subst_consts_stmts env ss))
Proof
  ho_match_mp_tac subst_consts_stmt_ind >>
  simp[subst_consts_stmt_def, supported_stmt_expr_exists_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >~ [`subst_consts_iter`]
  >- (Cases_on `it` >>
      gvs[subst_consts_iter_def, supported_iterator_exists_def] >>
      metis_tac[subst_consts_expr_const_name_free])
  >~ [`subst_consts_areason`]
  >- (Cases_on `r` >>
      gvs[subst_consts_areason_def, supported_assert_exists_def,
          subst_consts_error_exprs, EXISTS_MAP, EXISTS_MEM, MEM_MAP, PULL_EXISTS] >>
      metis_tac[subst_consts_expr_const_name_free])
  >~ [`subst_consts_rreason`]
  >- (Cases_on `r` >>
      gvs[subst_consts_rreason_def, supported_raise_exists_def,
          subst_consts_error_exprs, EXISTS_MAP, EXISTS_MEM, MEM_MAP, PULL_EXISTS] >>
      metis_tac[subst_consts_expr_const_name_free])
  >> metis_tac[subst_consts_expr_const_name_free,
               subst_consts_target_const_name_free]
QED

Theorem checked_const_substitution_const_name_free:
  check_contract mode layouts addr [(NONE,tops)] = SOME art /\
  constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME A ==>
  ~supported_stmts_expr_exists (const_name_root_mods [(NONE,tops)])
    (subst_consts_stmts (module_consts_env tops []) ss)
Proof
  strip_tac >> irule (cj 2 subst_consts_stmt_const_name_free) >>
  simp[GSYM ALOOKUP_NONE] >>
  rpt strip_tac >>
  `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
  drule_all checked_module_consts_env_replacement >> strip_tac >>
  metis_tac[closed_constant_no_const_name]
QED

Theorem checked_const_substitution_abi_decode_target:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  supported_stmts_expr_exists (expr_abi_decode_target_root tgt)
    (subst_consts_stmts (module_consts_env tops []) ss) ==>
  supported_stmts_expr_exists (expr_abi_decode_target_root tgt) ss
Proof
  strip_tac >> spose_not_then assume_tac >>
  drule_all checked_module_consts_env_agrees >> strip_tac >>
  `!id r. ALOOKUP (module_consts_env tops []) id = SOME r ==>
     ~supported_expr_exists (expr_abi_decode_target_root tgt) r` by
    (fs[const_acc_agrees_def] >> metis_tac[constant_expr_no_abi_decode]) >>
  metis_tac[CONJUNCT2 subst_consts_stmt_abi_decode_target]
QED

Theorem constant_expr_no_internal_calls:
  (!e. constant_expr mods e ==> int_calls_expr e = []) /\
  (!es. EVERY (constant_expr mods) es ==> int_calls_exprs es = []) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) ==> int_calls_named_exprs fs = [])
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[constant_expr_def, int_calls_expr_def, SF ETA_ss] >>
  rpt strip_tac >> gvs[SF ETA_ss]
QED

Theorem checked_const_substitution_int_calls:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A ==>
  int_calls_stmts (subst_consts_stmts (module_consts_env tops []) ss) =
  int_calls_stmts ss
Proof
  strip_tac >> drule_all checked_module_consts_env_agrees >> strip_tac >>
  irule (CONJUNCT2 subst_consts_stmt_int_calls) >>
  fs[const_acc_agrees_def] >> metis_tac[constant_expr_no_internal_calls]
QED

Theorem no_evm_run_stmts[local]:
  !ss. ~supported_stmts_expr_exists expr_evm_run_root ss
Proof
  `(!p e. p = expr_evm_run_root ==> ~supported_expr_exists p e) /\
   (!p t. p = expr_evm_run_root ==> ~supported_target_exists p t) /\
   (!p es. p = expr_evm_run_root ==> ~supported_exprs_exists p es) /\
   (!p opt. p = expr_evm_run_root ==> ~supported_opt_exists p opt) /\
   (!p fs. p = expr_evm_run_root ==> ~supported_fields_exists p fs)` by
    (ho_match_mp_tac supported_expr_exists_ind >>
     rw[supported_expr_exists_def, expr_evm_run_root_def]) >>
  `(!p t. p = expr_evm_run_root ==> ~supported_assignment_exists p t) /\
   (!p ts. p = expr_evm_run_root ==> ~supported_assignments_exists p ts)` by
    (ho_match_mp_tac supported_assignment_exists_ind >>
     rw[supported_assignment_exists_def]) >>
  `(!p s. p = expr_evm_run_root ==> ~supported_stmt_expr_exists p s) /\
   (!p ss. p = expr_evm_run_root ==> ~supported_stmts_expr_exists p ss)`
    suffices_by simp[] >>
  ho_match_mp_tac supported_stmt_expr_exists_ind >>
  rw[supported_stmt_expr_exists_def]
  >~ [`supported_iterator_exists`]
  >- (Cases_on `iter` >> simp[supported_iterator_exists_def])
  >~ [`supported_assert_exists`]
  >- (Cases_on `reason` >> simp[supported_assert_exists_def, EXISTS_MEM])
  >~ [`supported_raise_exists`]
  >- (Cases_on `reason` >> simp[supported_raise_exists_def, EXISTS_MEM])
QED

Theorem checked_const_substitution_body_safe:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  body_stmts_safe tops ss ==>
  body_stmts_safe tops (subst_consts_stmts (module_consts_env tops []) ss)
Proof
  strip_tac >> drule_all checked_const_substitution_int_calls >>
  simp[body_stmts_safe_iff, no_evm_run_stmts] >>
  gvs[body_stmts_safe_iff]
QED

(* The substituted initializer keeps the annotation of every well-typed
   reference to its declaration. The traversal lets that fact be reused
   by gate checks on nested expressions, targets, and reasons. *)
Definition const_subst_changes_type_def:
  const_subst_changes_type E e <=>
    expr_type (subst_consts_expr E e) <> expr_type e
End

Theorem const_subst_preserves_expr_type[local]:
  ~supported_expr_exists (const_subst_changes_type E) e ==>
  expr_type (subst_consts_expr E e) = expr_type e
Proof
  metis_tac[const_subst_changes_type_def, supported_expr_exists_root]
QED

Theorem const_subst_preserves_arg_types[local]:
  ~supported_exprs_exists (const_subst_changes_type E) es ==>
  MAP expr_type (subst_consts_exprs E es) = MAP expr_type es
Proof
  Induct_on `es` >>
  simp[subst_consts_expr_def, supported_expr_exists_def,
       const_subst_preserves_expr_type]
QED

Definition const_subst_typed_names_def:
  const_subst_typed_names E env <=>
    !id r. ALOOKUP E id = SOME r ==>
      FLOOKUP env.bare_globals (NONE,id) = SOME (expr_type r) /\
      FLOOKUP env.toplevel_vtypes (NONE,id) = SOME (Type (expr_type r))
End

Theorem const_subst_typed_names_extend_local[simp]:
  const_subst_typed_names E (extend_local env id ty writable) =
  const_subst_typed_names E env
Proof
  simp[const_subst_typed_names_def, extend_local_def]
QED

Theorem const_subst_well_typed_annotations[local]:
  (!env e. well_typed_expr env e ==>
    !E. const_subst_typed_names E env ==>
      ~supported_expr_exists (const_subst_changes_type E) e) /\
  (!env e. IS_SOME (type_place_expr env e) ==>
    !E. const_subst_typed_names E env ==>
      ~supported_expr_exists (const_subst_changes_type E) e) /\
  (!env t. IS_SOME (type_place_target env t) ==>
    !E. const_subst_typed_names E env ==>
      ~supported_target_exists (const_subst_changes_type E) t) /\
  (!env es. well_typed_exprs env es ==>
    !E. const_subst_typed_names E env ==>
      ~supported_exprs_exists (const_subst_changes_type E) es) /\
  (!env opt. well_typed_opt env opt ==>
    !E. const_subst_typed_names E env ==>
      ~supported_opt_exists (const_subst_changes_type E) opt) /\
  (!env fs. well_typed_named_exprs env fs ==>
    !E. const_subst_typed_names E env ==>
      ~supported_fields_exists (const_subst_changes_type E) fs)
Proof
  ho_match_mp_tac well_typed_expr_ind >>
  simp[Once well_typed_expr_def, supported_expr_exists_def,
       const_subst_changes_type_def, subst_consts_expr_def, expr_type_def] >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  gvs[AllCaseEqs(), well_typed_expr_def, expr_type_def, vtype_annotation_ok_def,
      const_subst_typed_names_def] >>
  gvs[optionTheory.IS_SOME_EXISTS, AllCaseEqs(), vtype_annotation_ok_def,
      supported_expr_exists_def] >>
  TRY (Cases_on `src_id_opt` >> Cases_on `ALOOKUP E id` >>
       gvs[expr_type_def] >> res_tac >>
       gvs[vtype_annotation_ok_def] >> NO_TAC) >>
  res_tac >> gvs[] >> metis_tac[]
QED

Theorem const_subst_typed_atarget_annotations[local]:
  (!p t. !env ty E.
    p = const_subst_changes_type E /\
    const_subst_typed_names E env /\ well_typed_atarget env t ty ==>
    ~supported_assignment_exists p t) /\
  (!p ts. !env tys E.
    p = const_subst_changes_type E /\ const_subst_typed_names E env /\
    LIST_REL (well_typed_atarget env) ts tys ==>
    ~supported_assignments_exists p ts)
Proof
  ho_match_mp_tac supported_assignment_exists_ind >>
  simp[supported_assignment_exists_def, well_typed_atarget_def,
       well_typed_target_def, LIST_REL_CONS1] >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >> gvs[]
  >- (mp_tac (Q.SPECL [`env`, `target`] (cj 3 const_subst_well_typed_annotations)) >>
      simp[] >> qexists_tac `E` >> simp[])
  >- (qpat_x_assum `!env' tys' E'. _` (qspecl_then [`env`, `tys`, `E`] mp_tac) >>
      fs[LIST_REL_EL_EQN])
  >- (qpat_x_assum `!env' ty E'. _` (qspecl_then [`env`, `h'`, `E`] mp_tac) >>
      simp[])
  >- (qpat_x_assum `!env' tys' E'. _` (qspecl_then [`env`, `t'`, `E`] mp_tac) >>
      simp[])
QED

Theorem const_subst_assign_annotations[local]:
  const_subst_typed_names E env /\ atarget_accepts env t ty ==>
  ~supported_assignment_exists (const_subst_changes_type E) t
Proof
  Cases_on `t`
  >- (simp[atarget_accepts_def, supported_assignment_exists_def] >>
      Cases_on `type_place_target env b` >> simp[] >>
      Cases_on `x` >> simp[] >> rpt strip_tac >>
      mp_tac (Q.SPECL [`env`, `b`] (cj 3 const_subst_well_typed_annotations)) >>
      simp[] >> qexists_tac `E` >> simp[]) >>
  simp[atarget_accepts_def] >> strip_tac >>
  mp_tac (Q.SPECL [`const_subst_changes_type E`, `TupleTarget l`, `env`, `ty`, `E`]
    (cj 1 const_subst_typed_atarget_annotations)) >>
  simp[supported_assignment_exists_def]
QED

Theorem const_subst_stmt_annotations[local]:
  (!env ret s. !env' E. type_stmt env ret s = SOME env' /\
    const_subst_typed_names E env ==>
    ~supported_stmt_expr_exists (const_subst_changes_type E) s) /\
  (!env ret ss. !env' E. type_stmts env ret ss = SOME env' /\
    const_subst_typed_names E env ==>
    ~supported_stmts_expr_exists (const_subst_changes_type E) ss)
Proof
  ho_match_mp_tac type_stmt_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[Once type_stmt_def, supported_stmt_expr_exists_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs(), supported_stmt_expr_exists_def, supported_expr_exists_def,
      supported_assert_exists_def, supported_raise_exists_def,
      well_typed_custom_error_def, GSYM supported_exprs_exists_every,
      optionTheory.IS_SOME_EXISTS]
  >~ [`supported_iterator_exists`]
  >- (Cases_on `it` >>
      gvs[well_typed_iterator_def, supported_iterator_exists_def] >>
      metis_tac[cj 1 const_subst_well_typed_annotations])
  >> TRY (drule type_stmt_env_preserved_static >> strip_tac >>
      fs[const_subst_typed_names_def] >> metis_tac[] >> NO_TAC) >>
  metis_tac[cj 1 const_subst_well_typed_annotations,
            cj 3 const_subst_well_typed_annotations,
            cj 4 const_subst_well_typed_annotations,
            const_subst_assign_annotations, well_typed_target_def,
            optionTheory.IS_SOME_EXISTS]
QED

Theorem const_subst_supported_builtin_form[local]:
  supported_builtin_form tops ty bi es ==>
  supported_builtin_form tops ty bi (subst_consts_exprs E es)
Proof
  Cases_on `bi` >>
  simp[supported_builtin_form_def, subst_consts_exprs_map, supported_binop_def] >>
  rpt (CASE_TAC >> gvs[])
QED

Theorem const_subst_supported_type_builtin_form[local]:
  ~supported_exprs_exists (const_subst_changes_type E) es /\
  supported_type_builtin_form tops ty bi target es ==>
  supported_type_builtin_form tops ty bi target (subst_consts_exprs E es)
Proof
  Cases_on `bi` >> Cases_on `es` >>
  simp[supported_type_builtin_form_def, subst_consts_expr_def,
       supported_expr_exists_def, const_subst_preserves_expr_type] >>
  TRY (Cases_on `t`) >>
  rw[supported_type_builtin_form_def, subst_consts_expr_def,
     supported_expr_exists_def] >>
  gvs[const_subst_preserves_expr_type] >>
  Cases_on `t'` >> gvs[subst_consts_expr_def]
QED

Theorem const_subst_supported_struct_elements[local]:
  supported_struct_elements tops ty fs ==>
  supported_struct_elements tops ty (subst_consts_fields E fs)
Proof
  Cases_on `ty` >> simp[supported_struct_elements_def] >>
  rpt CASE_TAC >> gvs[EVERY_MEM, pairTheory.FORALL_PROD] >>
  `MAP FST (subst_consts_fields E fs) = MAP FST fs` by
    simp[subst_consts_fields_maps] >>
  rpt strip_tac >>
  `MEM p_1 (MAP FST fs)` by
    (qpat_assum `MAP FST (subst_consts_fields _ _) = _`
       (fn th => REWRITE_TAC [GSYM th]) >>
     simp[MEM_MAP] >> qexists_tac `(p_1,p_2)` >> simp[]) >>
  pop_assum mp_tac >> simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]
QED

Theorem supported_pure_places[local]:
  supported_pure_expr tops e /\
  (!ty name. e <> Name ty name) /\ (!ty id. e <> TopLevelName ty id) ==>
  supported_place_expr tops e
Proof
  Cases_on `e` >> simp[supported_pure_expr_def]
QED

Theorem supported_effect_pure[local]:
  (!tops e. supported_effect_expr tops e ==> supported_pure_expr tops e) /\
  (!tops e. supported_effect_place_expr tops e ==> supported_place_expr tops e)
Proof
  ho_match_mp_tac supported_effect_expr_ind >>
  simp[supported_effect_expr_def, supported_pure_expr_def] >> metis_tac[]
QED

Definition const_subst_supported_replacements_def:
  const_subst_supported_replacements tops E <=>
    !id r. ALOOKUP E id = SOME r ==>
      supported_pure_expr tops r /\ supported_place_expr tops r /\
      supported_place_info tops r = ValPT (expr_type r) /\
      build_hashmap_info tops (NONE,id) = NONE /\
      (!ty name. r <> Name ty name) /\
      (!ty ns. r <> TopLevelName ty ns) /\
      (!ty ct es drv. r <> Call ty ct es drv)
End

Theorem closed_constant_not_name[local]:
  constant_expr [(NONE,tops)] r /\ const_local_refs r = [] ==>
  (!ty name. r <> Name ty name) /\
  (!ty ns. r <> TopLevelName ty ns) /\
  (!ty ct es drv. r <> Call ty ct es drv)
Proof
  Cases_on `r` >> simp[constant_expr_def, const_local_refs_def] >>
  PairCases_on `p` >> Cases_on `p0` >>
  simp[constant_expr_def, const_local_refs_def, declared_constant_def]
QED

Theorem closed_constant_place_info[local]:
  !r. constant_expr [(NONE,tops)] r /\ const_local_refs r = [] ==>
    supported_place_info tops r = ValPT (expr_type r)
Proof
  measureInduct_on `expr_size r` >>
  rename1 `constant_expr [(NONE,tops)] r /\ _ ==> _` >> Cases_on `r` >>
  simp[exprLoweringTheory.place_type_def, supported_place_info_def, expr_type_def] >>
  rpt strip_tac
  >- metis_tac[closed_constant_not_name] >>
  gvs[constant_expr_def, const_local_refs_def] >>
  first_x_assum (qspec_then `e` mp_tac) >>
  simp[expr_size_def, supported_place_info_def]
QED

Theorem checked_const_subst_supported_replacements[local]:
  check_contract mode layouts addr [(NONE,tops)] = SOME art /\
  constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME A /\
  supported_program tops ==>
  const_subst_supported_replacements tops (module_consts_env tops [])
Proof
  rw[const_subst_supported_replacements_def] >>
  `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
  drule_all checked_module_consts_env_replacement >> strip_tac >>
  drule_all supported_program_const_replacement >> strip_tac >>
  drule_all closed_constant_not_name >> strip_tac >>
  simp[closed_constant_place_info, supported_pure_places] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[check_contract_runtime_namespaces,
              contract_namespaces_ok_module_toplevel_vtype_keys, ALOOKUP_MEM] >>
  metis_tac[build_hashmap_info_variable]
QED

Theorem checked_const_subst_typed_names[local]:
  check_contract mode layouts addr [(NONE,tops)] = SOME art /\
  env.bare_globals = art.cta_bare_globals /\ env.toplevel_vtypes = art.cta_toplevel_vtypes ==>
  const_subst_typed_names (module_consts_env tops []) env
Proof
  rw[const_subst_typed_names_def] >>
  `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
  drule_all checked_module_consts_env_replacement_annotation >> strip_tac
  >- (drule check_contract_nonsig_maps >> strip_tac >> simp[] >>
      irule build_contract_type_artifact_bare_globals_complete >>
      metis_tac[check_contract_runtime_namespaces]) >>
  metis_tac[vyperTypeContractStaticMapsTheory.check_contract_bare_global_toplevel_vtype]
QED

Triviality const_subst_qualified_place_root:
  !e. qualified_place_root e ==> qualified_place_root (subst_consts_expr E e)
Proof
  measureInduct_on `expr_size e` >> Cases_on `e` >>
  simp[qualified_place_root_def, subst_consts_expr_def, expr_size_def] >>
  rpt strip_tac
  >~ [`TopLevelName _ _`] >- (PairCases_on `p` >> Cases_on `p0` >>
                              gvs[subst_consts_expr_def, qualified_place_root_def]) >>
  first_x_assum irule >> simp[expr_size_def]
QED

Theorem const_subst_supported_pure[local]:
  (!E e.
    const_subst_supported_replacements tops E /\
    ~supported_expr_exists (const_subst_changes_type E) e ==>
    (supported_pure_expr tops e ==>
     supported_pure_expr tops (subst_consts_expr E e)) /\
    (supported_place_expr tops e ==>
     supported_place_expr tops (subst_consts_expr E e)) /\
    supported_place_info tops (subst_consts_expr E e) = supported_place_info tops e) /\
  (!E t.
    const_subst_supported_replacements tops E /\
    ~supported_target_exists (const_subst_changes_type E) t ==>
    (EVERY (supported_pure_expr tops) (target_indices t) ==>
     EVERY (supported_pure_expr tops) (target_indices (subst_consts_btarget E t)))) /\
  (!E es.
    const_subst_supported_replacements tops E /\
    ~supported_exprs_exists (const_subst_changes_type E) es /\
    supported_pure_exprs tops es ==>
    supported_pure_exprs tops (subst_consts_exprs E es)) /\
  (!E opt.
    const_subst_supported_replacements tops E /\
    ~supported_opt_exists (const_subst_changes_type E) opt /\
    (case opt of NONE => T | SOME d => supported_pure_expr tops d) ==>
    (case subst_consts_opt E opt of NONE => T | SOME d => supported_pure_expr tops d)) /\
  (!E fs.
    const_subst_supported_replacements tops E /\
    ~supported_fields_exists (const_subst_changes_type E) fs /\
    supported_pure_fields tops fs ==>
    supported_pure_fields tops (subst_consts_fields E fs))
Proof
  ho_match_mp_tac subst_consts_expr_ind >>
  simp[subst_consts_expr_def, supported_expr_exists_def,
       supported_pure_expr_def, supported_subscript_place_def,
       exprLoweringTheory.place_type_def, expr_type_def, supported_place_info_def,
       target_indices_def] >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >> res_tac >>
  gvs[GSYM supported_place_info_def, supported_subscript_place_def] >>
  TRY (Cases_on `ns` >> Cases_on `ALOOKUP E id` >>
       gvs[subst_consts_expr_def, const_subst_changes_type_def, expr_type_def,
           supported_place_info_def, exprLoweringTheory.place_type_def,
           supported_pure_expr_def, const_subst_supported_replacements_def] >>
       res_tac >> gvs[] >> NO_TAC) >>
  metis_tac[const_subst_preserves_expr_type, const_subst_supported_builtin_form,
            const_subst_supported_type_builtin_form, const_subst_supported_struct_elements,
            const_subst_qualified_place_root]
QED

Theorem const_subst_supported_expr[local]:
  const_subst_supported_replacements tops E /\
  ~supported_expr_exists (const_subst_changes_type E) e /\
  supported_expr tops e ==>
  supported_expr tops (subst_consts_expr E e)
Proof
  rw[supported_expr_def] >>
  metis_tac[cj 1 const_subst_supported_pure, cj 1 supported_effect_pure]
QED

Theorem const_subst_supported_target[local]:
  !target.
    const_subst_supported_replacements tops E /\
    ~supported_target_exists (const_subst_changes_type E) target ==>
    (supported_target tops bindings target ==>
      supported_target tops bindings (subst_consts_btarget E target)) /\
    (IS_SOME (supported_target_info tops bindings target) ==>
      supported_target_info tops bindings (subst_consts_btarget E target) =
        supported_target_info tops bindings target)
Proof
  measureInduct_on `base_assignment_target_size target` >>
  Cases_on `target` >>
  simp[subst_consts_expr_def, supported_target_def, supported_target_info_def,
       supported_expr_exists_def] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[expr_size_def] >>
  TRY (Cases_on `supported_expr tops e` >> fs[] >>
       `supported_expr tops (subst_consts_expr E e)` by
         metis_tac[const_subst_supported_expr] >> simp[] >> NO_TAC) >>
  metis_tac[]
QED

Theorem const_subst_supported_assignment[local]:
  (!p t. p = const_subst_changes_type E ==>
    const_subst_supported_replacements tops E /\
    ~supported_assignment_exists p t /\
    (case t of BaseTarget bt => supported_target tops bindings bt | _ => F) ==>
    (case subst_consts_target E t of
       BaseTarget bt => supported_target tops bindings bt | _ => F)) /\
  (!p ts. p = const_subst_changes_type E ==>
    const_subst_supported_replacements tops E /\
    ~supported_assignments_exists p ts /\
    EVERY (\t. case t of BaseTarget bt => supported_target tops bindings bt | _ => F) ts ==>
    EVERY (\t. case t of BaseTarget bt => supported_target tops bindings bt | _ => F)
      (subst_consts_targets E ts))
Proof
  ho_match_mp_tac supported_assignment_exists_ind >>
  simp[supported_assignment_exists_def, subst_consts_target_def] >>
  metis_tac[const_subst_supported_target]
QED

Theorem const_subst_supported_log[local]:
  const_subst_supported_replacements tops E /\
  ~supported_exprs_exists (const_subst_changes_type E) es /\
  supported_log tops id es ==>
  supported_log tops id (subst_consts_exprs E es)
Proof
  simp[supported_log_def] >> strip_tac >>
  conj_tac >- metis_tac[cj 3 const_subst_supported_pure] >>
  drule const_subst_preserves_arg_types >> strip_tac >>
  Cases_on `supported_event_fields tops id` >>
  fs[LIST_REL_EL_EQN, subst_consts_exprs_map] >> rpt strip_tac >>
  `expr_type (subst_consts_expr E (EL n es)) = expr_type (EL n es)` by
    (qpat_assum `MAP expr_type (MAP _ _) = _` (mp_tac o Q.AP_TERM `EL n`) >>
     simp[EL_MAP]) >>
  simp[EL_MAP] >> metis_tac[]
QED

Theorem const_subst_supported_string_reason[local]:
  const_subst_supported_replacements tops E /\
  ~supported_expr_exists (const_subst_changes_type E) e /\
  supported_string_reason tops e ==>
  supported_string_reason tops (subst_consts_expr E e)
Proof
  `!e. supported_pure_expr tops e /\
    (case expr_type e of BaseT (StringT _) => T | _ => F) ==>
    supported_string_reason tops e` by
      (Cases >> simp[supported_string_reason_def, expr_type_def] >>
       Cases_on `l` >> simp[supported_string_reason_def, expr_type_def]) >>
  strip_tac >>
  Cases_on `?ty text. e = Literal ty (StringL text)` >> gvs[subst_consts_expr_def] >>
  `supported_pure_expr tops e /\
   (case expr_type e of BaseT (StringT _) => T | _ => F)` by
    (Cases_on `e` >> gvs[supported_string_reason_def, expr_type_def] >>
     Cases_on `l` >> gvs[supported_string_reason_def, expr_type_def]) >>
  drule const_subst_preserves_expr_type >>
  metis_tac[cj 1 const_subst_supported_pure]
QED

Theorem const_subst_supported_custom_error[local]:
  const_subst_supported_replacements tops E /\
  ~supported_exprs_exists (const_subst_changes_type E) (custom_error_exprs err) /\
  supported_custom_error tops err /\
  EVERY (supported_pure_expr tops) (custom_error_exprs err) ==>
  supported_custom_error tops (subst_consts_error E err) /\
  EVERY (supported_pure_expr tops) (custom_error_exprs (subst_consts_error E err))
Proof
  strip_tac >> conj_tac
  >- (Cases_on `err` >> PairCases_on `p` >> Cases_on `p0` >>
      fs[supported_custom_error_def, custom_error_resolved_def, subst_consts_error_def,
         order_custom_error_args_subst] >>
      Cases_on `lookup_custom_error_args_in p1 tops` >> fs[] >>
      Cases_on `order_custom_error_args x (CustomError (NONE,p1) l l0)` >> fs[] >>
      drule order_custom_error_args_perm >> strip_tac >>
      `!e. MEM e x' ==> MEM e (custom_error_exprs (CustomError (NONE,p1) l l0))` by
        metis_tac[sortingTheory.PERM_MEM_EQ] >>
      `~supported_exprs_exists (const_subst_changes_type E) x'` by
        (fs[supported_exprs_exists_every, EXISTS_MEM] >> metis_tac[]) >>
      fs[const_subst_preserves_arg_types]) >>
  simp[subst_consts_error_exprs, GSYM subst_consts_exprs_map] >>
  metis_tac[cj 3 const_subst_supported_pure, supported_pure_exprs_every]
QED

Theorem const_subst_supported_reasons[local]:
  (const_subst_supported_replacements tops E /\
   ~supported_assert_exists (const_subst_changes_type E) a /\
   supported_assert_reason tops a ==>
   supported_assert_reason tops (subst_consts_areason E a)) /\
  (const_subst_supported_replacements tops E /\
   ~supported_raise_exists (const_subst_changes_type E) r /\
   supported_raise_reason tops r ==>
   supported_raise_reason tops (subst_consts_rreason E r))
Proof
  Cases_on `a` >> Cases_on `r` >>
  simp[subst_consts_areason_def, subst_consts_rreason_def,
       supported_assert_exists_def, supported_raise_exists_def,
       supported_assert_reason_def, supported_raise_reason_def,
       GSYM supported_exprs_exists_every] >>
  metis_tac[const_subst_supported_string_reason, const_subst_supported_custom_error]
QED

Theorem const_subst_supported_array[local]:
  const_subst_supported_replacements tops E /\
  ~supported_expr_exists (const_subst_changes_type E) e /\
  supported_iterator tops ty (Array e) n ==>
  supported_iterator tops ty (Array (subst_consts_expr E e)) n
Proof
  strip_tac >>
  Cases_on `?t name. e = Name t name` >> gvs[subst_consts_expr_def] >>
  Cases_on `?t id. e = TopLevelName t id`
  >- (gvs[] >> PairCases_on `id` >> Cases_on `id0` >>
      gvs[subst_consts_expr_def] >> Cases_on `ALOOKUP E id1` >> gvs[] >>
      fs[const_subst_supported_replacements_def] >>
      first_x_assum drule >> strip_tac >>
      simp[supported_non_name_array_iterator, supported_expr_def] >>
      drule const_subst_preserves_expr_type >>
      Cases_on `t` >> simp[supported_iterator_def, expr_type_def] >>
      rpt strip_tac >> gvs[supported_iterator_def, subst_consts_expr_def] >>
      metis_tac[]) >>
  `(!t name. subst_consts_expr E e <> Name t name) /\
   (!t id. subst_consts_expr E e <> TopLevelName t id) /\
   (!t fid args drv. subst_consts_expr E e = Call t (IntCall fid) args drv ==>
      ?args' drv'. e = Call t (IntCall fid) args' drv')` by
     (Cases_on `e` >> gvs[subst_consts_expr_def]) >>
  fs[supported_non_name_array_iterator] >>
  metis_tac[const_subst_preserves_expr_type, const_subst_supported_expr]
QED

Theorem checked_const_substitution_idempotent_expr[local]:
  check_contract mode layouts addr [(NONE,tops)] = SOME art /\
  constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME A ==>
  subst_consts_expr (module_consts_env tops [])
    (subst_consts_expr (module_consts_env tops []) e) =
  subst_consts_expr (module_consts_env tops []) e
Proof
  strip_tac >>
  `!id r. ALOOKUP (module_consts_env tops []) id = SOME r ==>
      ALOOKUP (module_consts_env tops []) id = SOME r /\
      subst_consts_expr (module_consts_env tops []) r = r` by
    (rpt strip_tac >> simp[] >>
     `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
     drule_all checked_module_consts_env_replacement >> strip_tac >>
     metis_tac[const_closed_subst]) >>
  drule subst_consts_absorb >> simp[]
QED

Theorem supported_range_case[local]:
  (case (a,b) of (Literal _ (IntL lo), Literal _ (IntL hi)) => P lo hi | _ => d) =
  if ?at bt lo hi. a = Literal at (IntL lo) /\ b = Literal bt (IntL hi)
  then ?at bt lo hi. a = Literal at (IntL lo) /\ b = Literal bt (IntL hi) /\ P lo hi
  else d
Proof
  Cases_on `a` >> simp[] >> Cases_on `b` >> simp[] >> rpt (CASE_TAC >> gvs[])
QED

Theorem const_subst_supported_range[local]:
  const_subst_supported_replacements tops (module_consts_env tops []) /\
  ~supported_expr_exists (const_subst_changes_type (module_consts_env tops [])) a /\
  ~supported_expr_exists (const_subst_changes_type (module_consts_env tops [])) b /\
  check_contract mode layouts addr [(NONE,tops)] = SOME art /\
  constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME A /\
  supported_iterator tops ty (Range a b) n ==>
  supported_iterator tops ty
    (Range (subst_consts_expr (module_consts_env tops []) a)
           (subst_consts_expr (module_consts_env tops []) b)) n
Proof
  strip_tac >>
  drule_all checked_const_substitution_idempotent_expr >>
  disch_then (fn th => qspec_then `a` assume_tac th >> qspec_then `b` assume_tac th) >>
  Cases_on `?at bt lo hi. a = Literal at (IntL lo) /\ b = Literal bt (IntL hi)`
  >- gvs[supported_iterator_def, subst_consts_expr_def] >>
  gvs[supported_iterator_def, supported_range_case, COND_EXPAND] >>
  `supported_pure_expr tops (subst_consts_expr (module_consts_env tops []) a) /\
   supported_pure_expr tops (subst_consts_expr (module_consts_env tops []) b)` by
    metis_tac[cj 1 const_subst_supported_pure] >>
  fs[] >> metis_tac[]
QED

Theorem checked_const_subst_supported_stmts[local]:
  (!E s. E = module_consts_env tops [] ==>
    check_contract mode layouts addr [(NONE,tops)] = SOME art /\
    constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME A /\
    const_subst_supported_replacements tops E /\
    ~supported_stmt_expr_exists (const_subst_changes_type E) s /\
    supported_stmt tops bindings s ==>
    supported_stmt tops bindings (subst_consts_stmt E s)) /\
  (!E ss. E = module_consts_env tops [] ==>
    check_contract mode layouts addr [(NONE,tops)] = SOME art /\
    constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME A /\
    const_subst_supported_replacements tops E /\
    ~supported_stmts_expr_exists (const_subst_changes_type E) ss /\
    supported_stmts tops bindings ss ==>
    supported_stmts tops bindings (subst_consts_stmts E ss))
Proof
  ho_match_mp_tac subst_consts_stmt_ind >>
  simp[subst_consts_stmt_def, supported_stmt_def, supported_stmt_expr_exists_def,
       supported_binop_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >~ [`subst_consts_iter _ it`]
  >- (Cases_on `it` >>
      fs[subst_consts_iter_def, supported_iterator_exists_def] >>
      metis_tac[const_subst_supported_array, const_subst_supported_range])
  >~ [`supported_assignment _ _ _ _`]
  >- (Cases_on `t` >>
      fs[supported_assignment_def, subst_consts_target_def, supported_assignment_exists_def] >>
      metis_tac[const_subst_supported_expr, const_subst_supported_target,
                cj 2 const_subst_supported_assignment])
  >~ [`supported_append_target`]
  >- (Cases_on `t` >>
      gvs[supported_append_target_def, subst_consts_expr_def, target_indices_def,
          supported_expr_exists_def, EVERY_APPEND] >>
      metis_tac[cj 1 const_subst_supported_pure, cj 2 const_subst_supported_pure])
  >~ [`subst_consts_opt`]
  >- (Cases_on `e` >> gvs[subst_consts_expr_def, supported_expr_exists_def, supported_stmt_def] >>
      metis_tac[const_subst_supported_expr]) >>
  metis_tac[cj 1 const_subst_supported_pure, const_subst_supported_expr,
            const_subst_supported_target, const_subst_supported_log,
            const_subst_supported_reasons, supported_aug_target_def]
QED

Theorem checked_const_substituted_function_support:
  check_contract mode layouts addr [(NONE,tops)] = SOME art /\
  constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME A /\
  supported_program tops /\
  env.bare_globals = art.cta_bare_globals /\ env.toplevel_vtypes = art.cta_toplevel_vtypes /\
  IS_SOME (type_stmts env ret ss) /\ well_typed_exprs (defaults_env env) dflts /\
  supported_function_body tops vis args ss /\ supported_pure_exprs tops dflts ==>
  supported_function_body tops vis args (subst_consts_stmts (module_consts_env tops []) ss) /\
  supported_pure_exprs tops (subst_consts_exprs (module_consts_env tops []) dflts)
Proof
  strip_tac >>
  `const_subst_typed_names (module_consts_env tops []) env` by
    metis_tac[checked_const_subst_typed_names] >>
  `~supported_stmts_expr_exists (const_subst_changes_type (module_consts_env tops [])) ss` by
    (fs[optionTheory.IS_SOME_EXISTS] >>
     drule_all (cj 2 const_subst_stmt_annotations) >> simp[]) >>
  `const_subst_typed_names (module_consts_env tops []) (defaults_env env)` by
    (qpat_assum `const_subst_typed_names _ env` mp_tac >>
     simp_tac (srw_ss()) [const_subst_typed_names_def, defaults_env_def]) >>
  `~supported_exprs_exists (const_subst_changes_type (module_consts_env tops [])) dflts` by
    (drule (cj 4 const_subst_well_typed_annotations) >> simp[]) >>
  drule_all checked_const_subst_supported_replacements >> strip_tac >>
  fs[supported_function_body_def, subst_consts_stmt_bindings] >>
  rpt conj_tac
  >- metis_tac[cj 2 checked_const_subst_supported_stmts]
  >- (match_mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `mode` |-> `mode`,
       `layouts` |-> `layouts`, `addr` |-> `addr`, `artifact` |-> `art`,
       `imms` |-> `imms`, `A` |-> `A`] checked_const_substitution_body_safe) >> simp[])
  >- metis_tac[cj 3 const_subst_supported_pure]
QED

Theorem checked_const_substituted_function:
  check_contract mode layouts addr [(NONE,tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
  (vis <> Deploy \/ mode) /\ supported_program tops /\
  supported_function_body tops vis args ss /\ supported_pure_exprs tops dflts /\
  constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME A /\
  env = function_entry_env art [(NONE,tops)] NONE vis args ==>
  supported_function_body tops vis args (subst_consts_stmts (module_consts_env tops []) ss) /\
  IS_SOME (type_stmts env ret (subst_consts_stmts (module_consts_env tops []) ss)) /\
  well_typed_exprs (defaults_env env) (subst_consts_exprs (module_consts_env tops []) dflts) /\
  ~supported_stmts_expr_exists (const_name_root_mods [(NONE,tops)])
    (subst_consts_stmts (module_consts_env tops []) ss) /\
  supported_pure_exprs tops (subst_consts_exprs (module_consts_env tops []) dflts)
Proof
  strip_tac >>
  `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
  `check_function_body layouts addr [(NONE,tops)] art NONE vis mut nr args dflts ret ss` by
    (Cases_on `mode` >>
     metis_tac[check_contract_main_module_allocated, check_contract_runtime_function_body_MEM,
       check_contract_deploy_function_body_MEM]) >>
  `env.bare_globals = art.cta_bare_globals /\
   env.toplevel_vtypes = art.cta_toplevel_vtypes` by
    simp[function_entry_env_def, FOLDL_extend_local_args_static, artifact_env_def] >>
  fs[check_function_body_def, constSubstModsTheory.consts_env_mods_singleton,
     constSubstModsTheory.subst_consts_mods_singleton] >>
  metis_tac[checked_const_substituted_function_support,
            checked_const_substitution_const_name_free]
QED

Theorem constant_expr_no_msg_gas[local]:
  (!e. constant_expr mods e ==>
     ~supported_expr_exists expr_msg_gas_root e) /\
  (!es. EVERY (constant_expr mods) es ==>
     ~supported_exprs_exists expr_msg_gas_root es) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) ==>
     ~supported_fields_exists expr_msg_gas_root fs)
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[constant_expr_def, supported_expr_exists_def, expr_msg_gas_root_def] >>
  rpt strip_tac >>
  rename1 `constant_builtin bt` >>
  Cases_on `bt` >> gvs[constant_builtin_def, expr_msg_gas_root_def]
QED

Theorem subst_consts_expr_no_msg_gas[local]:
  (!env e.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists expr_msg_gas_root r) /\
    ~supported_expr_exists expr_msg_gas_root e ==>
    ~supported_expr_exists expr_msg_gas_root (subst_consts_expr env e)) /\
  (!env t.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists expr_msg_gas_root r) /\
    ~supported_target_exists expr_msg_gas_root t ==>
    ~supported_target_exists expr_msg_gas_root (subst_consts_btarget env t)) /\
  (!env es.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists expr_msg_gas_root r) /\
    ~supported_exprs_exists expr_msg_gas_root es ==>
    ~supported_exprs_exists expr_msg_gas_root (subst_consts_exprs env es)) /\
  (!env opt.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists expr_msg_gas_root r) /\
    ~supported_opt_exists expr_msg_gas_root opt ==>
    ~supported_opt_exists expr_msg_gas_root (subst_consts_opt env opt)) /\
  (!env fs.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists expr_msg_gas_root r) /\
    ~supported_fields_exists expr_msg_gas_root fs ==>
    ~supported_fields_exists expr_msg_gas_root (subst_consts_fields env fs))
Proof
  ho_match_mp_tac subst_consts_expr_ind >>
  simp[subst_consts_expr_def, supported_expr_exists_def, expr_msg_gas_root_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `ns` >>
      simp[subst_consts_expr_def, supported_expr_exists_def, expr_msg_gas_root_def] >>
      Cases_on `ALOOKUP env id` >>
      gvs[supported_expr_exists_def, expr_msg_gas_root_def] >> metis_tac[]) >>
  TRY (rename1 `expr_msg_gas_root (Builtin _ bi _)` >>
       Cases_on `bi` >> gvs[expr_msg_gas_root_def] >>
       rename1 `expr_msg_gas_root (Builtin _ (Env eb) _)` >>
       Cases_on `eb` >> gvs[expr_msg_gas_root_def]) >>
  metis_tac[]
QED

Theorem module_consts_defaults_no_msg_gas:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  ~supported_exprs_exists expr_msg_gas_root ds ==>
  ~supported_exprs_exists expr_msg_gas_root (subst_consts_exprs (module_consts_env tops []) ds)
Proof
  strip_tac >> irule (cj 3 subst_consts_expr_no_msg_gas) >> simp[] >>
  rpt strip_tac >> metis_tac[cj 1 constant_expr_no_msg_gas, module_consts_env_constant_expr]
QED

Theorem checked_singleton_internal_function_body:
  check_contract mode layouts addr [(NONE,tops)] = SOME art /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops ==>
  check_function_body layouts addr [(NONE,tops)] art NONE Internal mut nr args dflts ret ss
Proof
  strip_tac >>
  Cases_on `mode` >> fs[]
  >- (irule check_contract_deploy_function_body_MEM >> simp[] >>
      qexistsl_tac [`name`, `rr`] >> simp[]) >>
  irule check_contract_runtime_function_body_MEM >> simp[] >>
  qexistsl_tac [`name`, `rr`] >> simp[] >>
  match_mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `in_deploy` |-> `F`,
    `art` |-> `art`] check_contract_main_module_allocated) >>
  simp[]
QED

Theorem checked_const_substituted_defaults:
  check_contract mode layouts addr [(NONE,tops)] = SOME art /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME A ==>
  MAP expr_type (subst_consts_exprs (module_consts_env tops []) dflts) =
    MAP expr_type dflts /\
  (!k. int_calls_exprs (DROP k (subst_consts_exprs (module_consts_env tops []) dflts)) =
    int_calls_exprs (DROP k dflts)) /\
  ~supported_exprs_exists (const_name_root_mods [(NONE,tops)])
    (subst_consts_exprs (module_consts_env tops []) dflts) /\
  (!target. supported_exprs_exists (expr_abi_decode_target_root target)
      (subst_consts_exprs (module_consts_env tops []) dflts) ==>
    supported_exprs_exists (expr_abi_decode_target_root target) dflts)
Proof
  strip_tac >>
  `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
  `check_function_body layouts addr [(NONE,tops)] art NONE Internal mut nr args dflts ret ss` by
    (drule_all_then ACCEPT_TAC checked_singleton_internal_function_body) >>
  `!id r. ALOOKUP (module_consts_env tops []) id = SOME r ==>
     constant_expr [(NONE,tops)] r /\ const_local_refs r = []` by
    (rpt strip_tac >> drule_all_then strip_assume_tac checked_module_consts_env_replacement >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (irule const_subst_preserves_arg_types >>
      irule (cj 4 const_subst_well_typed_annotations) >>
      qexists_tac `defaults_env (function_entry_env art [(NONE,tops)] NONE Internal args)` >>
      rpt conj_tac >> TRY (fs[check_function_body_def] >> NO_TAC) >>
      irule checked_const_subst_typed_names >>
      qexistsl_tac [`addr`, `art`, `layouts`, `mode`] >>
      simp[defaults_env_def, function_entry_env_def, artifact_env_def,
           FOLDL_extend_local_args_static]) >>
  conj_tac
  >- (simp[constSubstCorrectTheory.subst_consts_exprs_map, GSYM listTheory.MAP_DROP] >>
      rewrite_tac[GSYM constSubstCorrectTheory.subst_consts_exprs_map] >>
      irule (cj 3 subst_consts_expr_int_calls) >>
      metis_tac[constant_expr_no_internal_calls]) >>
  conj_tac
  >- (irule (cj 3 subst_consts_expr_const_name_free) >>
      simp[] >> metis_tac[closed_constant_no_const_name]) >>
  gen_tac >> spose_not_then strip_assume_tac >>
  `~supported_exprs_exists (expr_abi_decode_target_root target)
     (subst_consts_exprs (module_consts_env tops []) dflts)` by
    (irule (cj 3 subst_consts_expr_abi_decode_target) >>
     metis_tac[constant_expr_no_abi_decode]) >>
  fs[]
QED

Theorem checked_const_substituted_defaults_typed:
  check_contract cx.in_deploy cx.layouts cx.txn.target [(NONE,tops)] = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  env_context_consistent env cx /\
  frame_maps env art /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops ==>
  well_typed_exprs (defaults_env (env with current_src := NONE))
    (subst_consts_exprs (module_consts_env tops []) dflts)
Proof
  strip_tac >>
  `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
  `check_function_body cx.layouts cx.txn.target [(NONE,tops)] art NONE Internal mut nr
      args dflts ret ss` by
    (drule_all_then ACCEPT_TAC checked_singleton_internal_function_body) >>
  qabbrev_tac `entry = function_entry_env art [(NONE,tops)] NONE Internal args` >>
  `static_maps_transfer_env entry (entry with
    <|toplevel_vtypes := env.toplevel_vtypes; flag_members := env.flag_members|>)` by
    (simp[Abbr `entry`] >>
     irule vyperTypeContractFunctionTheory.function_entry_env_static_maps_transfer >>
     fs[frame_maps_def] >> qexists_tac `cx` >> simp[]) >>
  `well_typed_exprs (defaults_env entry)
    (subst_consts_exprs (module_consts_env tops []) dflts)` by
    fs[check_function_body_def, Abbr `entry`, constSubstModsTheory.consts_env_mods_singleton,
       constSubstModsTheory.subst_consts_mods_singleton] >>
  qpat_assum `well_typed_exprs (defaults_env entry) _`
    (mp_then Any mp_tac (cj 4 well_typed_static_maps_transfer)) >>
  disch_then (qspec_then `defaults_env (env with current_src := NONE)` mp_tac) >>
  simp[defaults_env_def] >>
  qpat_assum `static_maps_transfer_env _ _`
    (strip_assume_tac o REWRITE_RULE [vyperTypeContractFunctionTheory.static_maps_transfer_env_def]) >>
  fs[Abbr `entry`, function_entry_env_def, artifact_env_def,
     FOLDL_extend_local_args_static, vyperTypeInvariantsTheory.env_context_consistent_def,
     vyperContextTheory.get_tenv_def] >>
  disch_then irule >> fs[frame_maps_def]
QED
