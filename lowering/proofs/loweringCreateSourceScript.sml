(* Checker and substitution facts for the CREATE-free opcode branch. *)
Theory loweringCreateSource
Ancestors
  list alist option loweringShapeProps loweringShapeSource ctorCallFreeExpr
  vyperTypeSystem vyperTypeContract vyperTypeContractContext supportedExprTraverse
  supportedStmtTraverse compileVyper constSubst constSubstCorrect vyperAST
  vyperGetter

val _ = Parse.hide "body";
val _ = Parse.hide "tops";

Definition create_or_short_builtin_root_def:
  create_or_short_builtin_root e <=>
    expr_create_root e \/ expr_short_builtin_root e
End

Theorem well_typed_expr_no_short_builtin[local]:
  (!env e. well_typed_expr env e ==>
     ~supported_expr_exists expr_short_builtin_root e) /\
  (!env e vt. type_place_expr env e = SOME vt ==>
     ~supported_expr_exists expr_short_builtin_root e) /\
  (!env t vt. type_place_target env t = SOME vt ==>
     ~supported_target_exists expr_short_builtin_root t) /\
  (!env es. well_typed_exprs env es ==>
     ~supported_exprs_exists expr_short_builtin_root es) /\
  (!env opt. well_typed_opt env opt ==>
     ~supported_opt_exists expr_short_builtin_root opt) /\
  (!env kes. well_typed_named_exprs env kes ==>
     ~supported_fields_exists expr_short_builtin_root kes)
Proof
  ho_match_mp_tac well_typed_expr_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >>
  gvs[well_typed_expr_def, supported_expr_exists_def, expr_short_builtin_root_def, AllCaseEqs()] >>
  rpt (qpat_x_assum `_ \/ _` strip_assume_tac) >>
  res_tac >> imp_res_tac well_typed_builtin_app_arity >>
  imp_res_tac well_typed_type_builtin_args_arity >> gvs[]
QED

Theorem well_typed_atarget_no_short_builtin[local]:
  (!p t. p = expr_short_builtin_root ==>
     !ty. well_typed_atarget env t ty ==>
     ~supported_assignment_exists p t) /\
  (!p ts. p = expr_short_builtin_root ==>
     !tys. LIST_REL (\t ty. well_typed_atarget env t ty) ts tys ==>
     ~supported_assignments_exists p ts)
Proof
  ho_match_mp_tac supported_assignment_exists_ind >>
  rw[supported_assignment_exists_def] >>
  gvs[well_typed_atarget_def, well_typed_target_def, LIST_REL_CONS1] >>
  imp_res_tac well_typed_expr_no_short_builtin >> res_tac >> gvs[]
QED

Theorem atarget_accepts_no_short_builtin[local]:
  atarget_accepts env tgt t ==>
  ~supported_assignment_exists expr_short_builtin_root tgt
Proof
  Cases_on `tgt` >>
  simp[atarget_accepts_def, supported_assignment_exists_def] >>
  rpt strip_tac
  >- (rename1 `type_place_target env b` >>
      Cases_on `type_place_target env b` >> fs[] >>
      metis_tac[well_typed_expr_no_short_builtin]) >>
  metis_tac[well_typed_atarget_no_short_builtin, supported_assignment_exists_def]
QED

Theorem well_typed_iterator_no_short_builtin[local]:
  well_typed_iterator env typ it ==>
  ~supported_iterator_exists expr_short_builtin_root it
Proof
  Cases_on `it` >>
  rw[well_typed_iterator_def, supported_iterator_exists_def] >>
  metis_tac[well_typed_expr_no_short_builtin]
QED

Theorem type_stmt_no_short_builtin:
  (!env ret s env1. type_stmt env ret s = SOME env1 ==>
     ~supported_stmt_expr_exists expr_short_builtin_root s) /\
  (!env ret ss env1. type_stmts env ret ss = SOME env1 ==>
     ~supported_stmts_expr_exists expr_short_builtin_root ss)
Proof
  ho_match_mp_tac type_stmt_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >>
  gvs[type_stmt_def, supported_stmt_expr_exists_def, AllCaseEqs(),
      IS_SOME_EXISTS, supported_assert_exists_def, supported_raise_exists_def,
      supported_iterator_exists_def, well_typed_iterator_def,
      well_typed_custom_error_def, well_typed_target_def,
      GSYM supported_exprs_exists_every, supported_expr_exists_def] >>
  rpt (qpat_x_assum `_ \/ _` strip_assume_tac) >>
  res_tac >> imp_res_tac well_typed_expr_no_short_builtin >>
  imp_res_tac atarget_accepts_no_short_builtin >>
  imp_res_tac well_typed_iterator_no_short_builtin >> gvs[]
QED

Theorem constant_expr_no_create:
  (!e. constant_expr mods e ==> ~supported_expr_exists expr_create_root e) /\
  (!es. EVERY (constant_expr mods) es ==>
    ~supported_exprs_exists expr_create_root es) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) ==>
    ~supported_fields_exists expr_create_root fs)
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[constant_expr_def, supported_expr_exists_def, expr_create_root_def] >>
  rpt strip_tac >> gvs[constant_builtin_def, GSYM EVERY_NOT_EXISTS,
    combinTheory.o_DEF, SF ETA_ss] >>
  gvs[EXISTS_MEM, EVERY_MEM] >> res_tac
QED

Theorem subst_consts_expr_no_create:
  (!env e.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists create_or_short_builtin_root r) ==>
    ~supported_expr_exists create_or_short_builtin_root e ==>
    ~supported_expr_exists create_or_short_builtin_root (subst_consts_expr env e)) /\
  (!env t.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists create_or_short_builtin_root r) ==>
    ~supported_target_exists create_or_short_builtin_root t ==>
    ~supported_target_exists create_or_short_builtin_root (subst_consts_btarget env t)) /\
  (!env es.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists create_or_short_builtin_root r) ==>
    ~supported_exprs_exists create_or_short_builtin_root es ==>
    ~supported_exprs_exists create_or_short_builtin_root (subst_consts_exprs env es)) /\
  (!env opt.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists create_or_short_builtin_root r) ==>
    ~supported_opt_exists create_or_short_builtin_root opt ==>
    ~supported_opt_exists create_or_short_builtin_root (subst_consts_opt env opt)) /\
  (!env fs.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists create_or_short_builtin_root r) ==>
    ~supported_fields_exists create_or_short_builtin_root fs ==>
    ~supported_fields_exists create_or_short_builtin_root (subst_consts_fields env fs))
Proof
  ho_match_mp_tac subst_consts_expr_ind >>
  simp[subst_consts_expr_def, supported_expr_exists_def, create_or_short_builtin_root_def,
        expr_create_root_def, expr_short_builtin_root_def] >>
  rpt strip_tac >> gvs[] >> TRY (res_tac >> NO_TAC)
  >- (Cases_on `ns` >> simp[subst_consts_expr_def, supported_expr_exists_def,
        create_or_short_builtin_root_def,
        expr_create_root_def, expr_short_builtin_root_def] >> Cases_on `ALOOKUP env id` >>
        gvs[supported_expr_exists_def, create_or_short_builtin_root_def,
        expr_create_root_def, expr_short_builtin_root_def] >> metis_tac[])
  >~ [`expr_create_root (Call ty ct _ _)`]
  >- (Cases_on `ct` >> gvs[expr_create_root_def])
  >> res_tac >> gvs[] >> metis_tac[]
QED

Theorem subst_consts_target_no_create:
  (!env t.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists create_or_short_builtin_root r) ==>
    ~supported_assignment_exists create_or_short_builtin_root t ==>
    ~supported_assignment_exists create_or_short_builtin_root (subst_consts_target env t)) /\
  (!env ts.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists create_or_short_builtin_root r) ==>
    ~supported_assignments_exists create_or_short_builtin_root ts ==>
    ~supported_assignments_exists create_or_short_builtin_root (subst_consts_targets env ts))
Proof
  ho_match_mp_tac subst_consts_target_ind >>
  simp[subst_consts_target_def, supported_assignment_exists_def] >>
  metis_tac[subst_consts_expr_no_create]
QED



Theorem subst_consts_error_no_create:
  (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists create_or_short_builtin_root r) /\
  ~EXISTS (supported_expr_exists create_or_short_builtin_root) (custom_error_exprs err) ==>
  ~EXISTS (supported_expr_exists create_or_short_builtin_root)
    (custom_error_exprs (subst_consts_error env err))
Proof
  Cases_on `err` >>
  pure_rewrite_tac[subst_consts_error_def, custom_error_exprs_def, EXISTS_APPEND] >>
  pure_rewrite_tac[EXISTS_MAP, combinTheory.o_DEF] >>
  rpt strip_tac >>
  imp_res_tac (SIMP_RULE std_ss
    [supported_exprs_exists_every, supported_fields_exists_every,
     EXISTS_MAP, combinTheory.o_DEF] subst_consts_expr_no_create) >>
  metis_tac[]
QED

Theorem subst_consts_stmt_no_create:
  (!env s.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists create_or_short_builtin_root r) ==>
    ~supported_stmt_expr_exists create_or_short_builtin_root s ==>
    ~supported_stmt_expr_exists create_or_short_builtin_root (subst_consts_stmt env s)) /\
  (!env ss.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists create_or_short_builtin_root r) ==>
    ~supported_stmts_expr_exists create_or_short_builtin_root ss ==>
    ~supported_stmts_expr_exists create_or_short_builtin_root (subst_consts_stmts env ss))
Proof
  ho_match_mp_tac subst_consts_stmt_ind >>
  simp[subst_consts_stmt_def, supported_stmt_expr_exists_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> strip_tac
  >> gvs[subst_consts_iter_def, subst_consts_areason_def, subst_consts_rreason_def,
         supported_iterator_exists_def, supported_assert_exists_def,
         supported_raise_exists_def, AllCaseEqs()]
  >> imp_res_tac subst_consts_expr_no_create
  >> imp_res_tac subst_consts_target_no_create >> gvs[]
  >- (Cases_on `it` >> gvs[subst_consts_iter_def, supported_iterator_exists_def] >> metis_tac[])
  >~ [`supported_assert_exists create_or_short_builtin_root (subst_consts_areason env r)`]
  >- (Cases_on `r` >>
      rule_assum_tac (PURE_REWRITE_RULE [supported_assert_exists_def]) >>
      pure_rewrite_tac[subst_consts_areason_def, supported_assert_exists_def] >>
      rpt strip_tac >>
      imp_res_tac subst_consts_expr_no_create >> metis_tac[subst_consts_error_no_create])
  >~ [`supported_raise_exists create_or_short_builtin_root (subst_consts_rreason env r)`]
  >- (Cases_on `r` >>
      rule_assum_tac (PURE_REWRITE_RULE [supported_raise_exists_def]) >>
      pure_rewrite_tac[subst_consts_rreason_def, supported_raise_exists_def] >>
      rpt strip_tac >>
      imp_res_tac subst_consts_expr_no_create >> metis_tac[subst_consts_error_no_create])
  >> metis_tac[]
QED

Theorem build_getter_avoids_create:
  !e kt vt n.
    ~supported_expr_exists create_or_short_builtin_root e ==>
    ~supported_expr_exists create_or_short_builtin_root (SND (SND (build_getter e kt vt n)))
Proof
  recInduct build_getter_ind >> rpt conj_tac >> rpt gen_tac >>
  disch_tac >> disch_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >>
  gvs[supported_expr_exists_def, create_or_short_builtin_root_def,
        expr_create_root_def, expr_short_builtin_root_def] >>
  pairarg_tac >> gvs[] >>
  metis_tac[pairTheory.SND]
QED

Theorem getter_body_avoids_create:
  getter nr e kt vt = (mut,nr',args,dflts,ret,gbody) /\
  ~supported_expr_exists create_or_short_builtin_root e ==>
  ~supported_stmts_expr_exists create_or_short_builtin_root gbody
Proof
  simp[getter_def] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  simp[supported_stmt_expr_exists_def, supported_expr_exists_def] >>
  metis_tac[build_getter_avoids_create, pairTheory.SND]
QED

Theorem create_or_short_builtin_root_split:
  create_or_short_builtin_root =
    (\e. expr_create_root e \/ expr_short_builtin_root e)
Proof
  simp[FUN_EQ_THM, create_or_short_builtin_root_def]
QED

Theorem checked_const_replacements_avoid_create:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\
  ALOOKUP (module_consts_env tops []) id = SOME e ==>
  ~supported_expr_exists create_or_short_builtin_root e
Proof
  strip_tac >>
  drule_all checked_module_consts_env_replacement_constant >>
  drule_all checked_module_consts_env_replacement_shape >>
  simp[create_or_short_builtin_root_split, supported_expr_exists_disj] >>
  metis_tac[constant_expr_no_create, supported_expr_exists_mono,
            expr_short_builtin_root_def, expr_shape_root_def]
QED

Theorem checked_function_avoids_create:
  check_contract deploy layouts addr [(NONE,tops)] = SOME art /\
  (deploy \/ vis <> Deploy) /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
  ~supported_stmts_expr_exists expr_create_root body /\
  ~EXISTS (supported_expr_exists expr_create_root) dflts ==>
  ~supported_stmts_expr_exists create_or_short_builtin_root body /\
  EVERY (\e. ~supported_expr_exists create_or_short_builtin_root e) dflts /\
  LENGTH dflts <= LENGTH args
Proof
  strip_tac >>
  `check_function_body layouts addr [(NONE,tops)] art NONE vis mut nr args dflts ret body` by
    (Cases_on `deploy`
     >- (drule check_contract_deploy_function_body_MEM >>
         simp[] >> disch_then (drule_at (Pat `MEM (FunctionDecl _ _ _ _ _ _ _ _ _) _`)) >>
         simp[])
     >> fs[] >> drule check_contract_main_module_allocated >> simp[] >> strip_tac >>
     drule check_contract_runtime_function_body_MEM >> simp[] >>
     disch_then drule_all >> simp[]) >>
  fs[check_function_body_def, IS_SOME_EXISTS] >>
  `LENGTH dflts <= LENGTH args` by
    (qpat_assum `MAP expr_type dflts = _`
       (mp_tac o AP_TERM ``LENGTH : type list -> num``) >>
     simp[] >> decide_tac) >>
  imp_res_tac (cj 2 type_stmt_no_short_builtin) >>
  imp_res_tac (cj 4 well_typed_expr_no_short_builtin) >>
  fs[create_or_short_builtin_root_split, supported_stmt_expr_exists_disj,
     supported_expr_exists_disj, supported_exprs_exists_every, EVERY_MEM, EXISTS_MEM] >>
  rpt strip_tac >>
  qpat_assum `!e. ~MEM e dflts \/ ~supported_expr_exists _ e`
    (qspec_then `e` mp_tac) >> simp[]
QED

Theorem public_getter_body_avoids_create:
  !top mut nr rr name args dflts ret body.
  public_getter top = SOME (mut,nr,rr,name,args,dflts,ret,body) ==>
  ~supported_stmts_expr_exists create_or_short_builtin_root body
Proof
  Cases_on `top` >> simp[public_getter_def] >>
  rpt gen_tac >>
  Cases_on `v` >> simp[public_getter_def] >>
  rpt CASE_TAC >> gvs[] >> strip_tac >> gvs[] >>
  simp[supported_stmt_expr_exists_def, supported_expr_exists_def,
       create_or_short_builtin_root_def, expr_create_root_def, expr_short_builtin_root_def] >>
  pairarg_tac >> gvs[] >>
  drule getter_body_avoids_create >>
  simp[supported_expr_exists_def, create_or_short_builtin_root_def, expr_create_root_def,
       expr_short_builtin_root_def]
QED

Theorem public_getter_defaults_nil[local]:
  public_getter top = SOME (mut,nr,rr,name,args,dflts,ret,body) ==> dflts = []
Proof
  Cases_on `top` >> simp[public_getter_def] >>
  Cases_on `v` >> simp[public_getter_def, getter_def] >>
  rpt CASE_TAC >> gvs[] >> rpt (pairarg_tac >> gvs[])
QED


Definition runtime_bodies_avoid_create_def:
  runtime_bodies_avoid_create tops <=>
    (!mut nr rr name args dflts ret body.
      MEM (mut,nr,rr,name,args,dflts,ret,body) (FST (classify_functions tops)) ==>
      LENGTH dflts <= LENGTH args) /\
    !mut nr rr name args dflts ret body.
      (MEM (mut,nr,rr,name,args,dflts,ret,body) (FST (classify_functions tops)) \/
       MEM (mut,nr,rr,name,args,dflts,ret,body) (FST (SND (classify_functions tops))) \/
       FST (SND (SND (classify_functions tops))) =
         SOME (mut,nr,rr,name,args,dflts,ret,body)) ==>
      ~supported_stmts_expr_exists create_or_short_builtin_root body /\
      EVERY (\e. ~supported_expr_exists create_or_short_builtin_root e) dflts
End

Theorem subst_consts_body_avoids_create:
  (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists create_or_short_builtin_root r) /\
  ~supported_stmts_expr_exists create_or_short_builtin_root body /\
  EVERY (\e. ~supported_expr_exists create_or_short_builtin_root e) dflts ==>
  ~supported_stmts_expr_exists create_or_short_builtin_root (subst_consts_stmts env body) /\
  EVERY (\e. ~supported_expr_exists create_or_short_builtin_root e) (subst_consts_exprs env dflts)
Proof
  strip_tac >> conj_tac >- metis_tac[subst_consts_stmt_no_create] >>
  `~supported_exprs_exists create_or_short_builtin_root dflts` by
    (fs[supported_exprs_exists_every, EXISTS_MEM, EVERY_MEM] >> metis_tac[]) >>
  imp_res_tac (cj 3 subst_consts_expr_no_create) >>
  fs[supported_exprs_exists_every, EXISTS_MEM, EVERY_MEM] >> metis_tac[]
QED

Theorem check_contract_runtime_bodies_avoid_create:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  (!vis mut nr rr name args dflts ret body.
    MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops ==>
      ~supported_stmts_expr_exists expr_create_root body /\
      ~EXISTS (supported_expr_exists expr_create_root) dflts) ==>
  runtime_bodies_avoid_create tops
Proof
  strip_tac >>
  `!id r. ALOOKUP (module_consts_env tops []) id = SOME r ==>
     ~supported_expr_exists create_or_short_builtin_root r` by
    metis_tac[checked_const_replacements_avoid_create, ALOOKUP_def] >>
  `!vis mut nr rr name args dflts ret body.
    MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\ vis <> Deploy ==>
    ~supported_stmts_expr_exists create_or_short_builtin_root body /\
    EVERY (\e. ~supported_expr_exists create_or_short_builtin_root e) dflts /\
    LENGTH dflts <= LENGTH args` by
    metis_tac[checked_function_avoids_create] >>
  pure_rewrite_tac[runtime_bodies_avoid_create_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule classify_functions_external_source >>
      disch_then (qx_choosel_then [`rawdefaults`, `rawbody`] strip_assume_tac) >>
      fs[subst_consts_fn_def]
      >- metis_tac[function_visibility_distinct] >>
      imp_res_tac public_getter_defaults_nil >> fs[]) >>
  rpt gen_tac >> strip_tac
  >- (drule classify_functions_external_source >> strip_tac >>
      fs[subst_consts_fn_def] >>
      irule subst_consts_body_avoids_create >> simp[] >>
      metis_tac[function_visibility_distinct, public_getter_body_avoids_create,
                public_getter_defaults_nil, EVERY_DEF])
  >- (gvs[MEM_classify_internal, subst_consts_fn_def] >>
      irule subst_consts_body_avoids_create >> simp[] >>
      metis_tac[function_visibility_distinct]) >>
  drule classify_functions_fallback_mem >> strip_tac >>
  gvs[subst_consts_fn_def] >>
  irule subst_consts_body_avoids_create >> simp[] >>
  metis_tac[function_visibility_distinct]
QED

Theorem runtime_bodies_avoid_create_func_defaults:
  runtime_bodies_avoid_create tops ==>
  EVERY (\nd. ~supported_exprs_exists create_or_short_builtin_root (SND nd))
    (build_func_defaults tops)
Proof
  rw[build_func_defaults_def, EVERY_MEM] >>
  gvs[MEM_MAP] >> PairCases_on `y` >> gvs[] >>
  fs[runtime_bodies_avoid_create_def] >>
  simp[supported_exprs_exists_every, NOT_EXISTS, combinTheory.o_DEF] >>
  metis_tac[]
QED
