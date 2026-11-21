(* The runtime blueprint exclusion survives compiler constant substitution. *)
Theory runtimePeakMemorySourceGate
Ancestors
  e2eDefs compileVyper constSubst constSubstCorrect vyperAST vyperTypeContract
  supportedExprTraverse supportedStmtTraverse loweringShapeProps loweringShapeSource
  publicGetterProps compileEnv exprLowering list rich_list alist

Definition blueprint_create_root_def:
  blueprint_create_root e <=>
    ?ty raw salted rof order es d.
      e = Call ty (CreateTarget (CreateFromBlueprint raw) salted rof order) es d
End

Theorem subst_consts_expr_blueprint_free[local]:
  (!env e.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists blueprint_create_root r) ==>
    ~supported_expr_exists blueprint_create_root e ==>
    ~supported_expr_exists blueprint_create_root (subst_consts_expr env e)) /\
  (!env t.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists blueprint_create_root r) ==>
    ~supported_target_exists blueprint_create_root t ==>
    ~supported_target_exists blueprint_create_root (subst_consts_btarget env t)) /\
  (!env es.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists blueprint_create_root r) ==>
    ~supported_exprs_exists blueprint_create_root es ==>
    ~supported_exprs_exists blueprint_create_root (subst_consts_exprs env es)) /\
  (!env opt.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists blueprint_create_root r) ==>
    ~supported_opt_exists blueprint_create_root opt ==>
    ~supported_opt_exists blueprint_create_root (subst_consts_opt env opt)) /\
  (!env fs.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists blueprint_create_root r) ==>
    ~supported_fields_exists blueprint_create_root fs ==>
    ~supported_fields_exists blueprint_create_root (subst_consts_fields env fs))
Proof
  ho_match_mp_tac subst_consts_expr_ind >>
  simp[subst_consts_expr_def, supported_expr_exists_def, blueprint_create_root_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `ns` >> simp[subst_consts_expr_def, supported_expr_exists_def,
        blueprint_create_root_def] >> Cases_on `ALOOKUP env id` >>
        gvs[supported_expr_exists_def, blueprint_create_root_def] >> metis_tac[])
  >> metis_tac[]
QED

Theorem subst_consts_target_blueprint_free[local]:
  (!env t.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists blueprint_create_root r) ==>
    ~supported_assignment_exists blueprint_create_root t ==>
    ~supported_assignment_exists blueprint_create_root (subst_consts_target env t)) /\
  (!env ts.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists blueprint_create_root r) ==>
    ~supported_assignments_exists blueprint_create_root ts ==>
    ~supported_assignments_exists blueprint_create_root (subst_consts_targets env ts))
Proof
  ho_match_mp_tac subst_consts_target_ind >>
  simp[subst_consts_target_def, supported_assignment_exists_def] >>
  metis_tac[subst_consts_expr_blueprint_free]
QED

Theorem subst_consts_error_blueprint_free[local]:
  (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists blueprint_create_root r) /\
  ~EXISTS (supported_expr_exists blueprint_create_root) (custom_error_exprs err) ==>
  ~EXISTS (supported_expr_exists blueprint_create_root)
    (custom_error_exprs (subst_consts_error env err))
Proof
  Cases_on `err` >>
  pure_rewrite_tac[subst_consts_error_def, custom_error_exprs_def, EXISTS_APPEND] >>
  pure_rewrite_tac[EXISTS_MAP, combinTheory.o_DEF] >>
  rpt strip_tac >>
  imp_res_tac (SIMP_RULE std_ss
    [supported_exprs_exists_every, supported_fields_exists_every,
     EXISTS_MAP, combinTheory.o_DEF] subst_consts_expr_blueprint_free) >>
  metis_tac[]
QED

Theorem subst_consts_stmt_blueprint_free[local]:
  (!env s.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists blueprint_create_root r) ==>
    ~supported_stmt_expr_exists blueprint_create_root s ==>
    ~supported_stmt_expr_exists blueprint_create_root (subst_consts_stmt env s)) /\
  (!env ss.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists blueprint_create_root r) ==>
    ~supported_stmts_expr_exists blueprint_create_root ss ==>
    ~supported_stmts_expr_exists blueprint_create_root (subst_consts_stmts env ss))
Proof
  ho_match_mp_tac subst_consts_stmt_ind >>
  simp[subst_consts_stmt_def, supported_stmt_expr_exists_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> strip_tac
  >> gvs[subst_consts_iter_def, subst_consts_areason_def, subst_consts_rreason_def,
         supported_iterator_exists_def, supported_assert_exists_def,
         supported_raise_exists_def, AllCaseEqs()]
  >> imp_res_tac subst_consts_expr_blueprint_free
  >> imp_res_tac subst_consts_target_blueprint_free >> gvs[]
  >- (Cases_on `it` >> gvs[subst_consts_iter_def, supported_iterator_exists_def] >>
      metis_tac[])
  >~ [`supported_assert_exists blueprint_create_root (subst_consts_areason env r)`]
  >- (Cases_on `r` >>
      rule_assum_tac (PURE_REWRITE_RULE [supported_assert_exists_def]) >>
      pure_rewrite_tac[subst_consts_areason_def, supported_assert_exists_def] >>
      rpt strip_tac >>
      imp_res_tac subst_consts_expr_blueprint_free >>
      metis_tac[subst_consts_error_blueprint_free])
  >~ [`supported_raise_exists blueprint_create_root (subst_consts_rreason env r)`]
  >- (Cases_on `r` >>
      rule_assum_tac (PURE_REWRITE_RULE [supported_raise_exists_def]) >>
      pure_rewrite_tac[subst_consts_rreason_def, supported_raise_exists_def] >>
      rpt strip_tac >>
      imp_res_tac subst_consts_expr_blueprint_free >>
      metis_tac[subst_consts_error_blueprint_free])
  >> metis_tac[]
QED

Theorem module_consts_env_blueprint_free:
  check_contract F layouts addr [(NONE, source_tops)] = SOME art /\
  ALOOKUP (module_consts_env source_tops []) id = SOME r ==>
  ~supported_expr_exists blueprint_create_root r
Proof
  `!e. blueprint_create_root e ==> expr_shape_root e` by
    (simp[blueprint_create_root_def, expr_shape_root_def] >> metis_tac[]) >>
  strip_tac >>
  `ALOOKUP [(NONE:num option,source_tops)] NONE = SOME source_tops` by simp[] >>
  drule_all checked_module_consts_env_replacement_shape >>
  metis_tac[cj 1 supported_expr_exists_mono]
QED

Theorem subst_consts_fn_blueprint_free:
  check_contract F layouts addr [(NONE, source_tops)] = SOME art /\
  ~supported_stmts_expr_exists blueprint_create_root stmts /\
  EVERY (\d. ~supported_expr_exists blueprint_create_root d) dflts ==>
  ~supported_stmts_expr_exists blueprint_create_root
    (subst_consts_stmts (module_consts_env source_tops []) stmts) /\
  EVERY (\d. ~supported_expr_exists blueprint_create_root d)
    (subst_consts_exprs (module_consts_env source_tops []) dflts)
Proof
  strip_tac >>
  `!id r. ALOOKUP (module_consts_env source_tops []) id = SOME r ==>
     ~supported_expr_exists blueprint_create_root r` by
    metis_tac[module_consts_env_blueprint_free] >>
  conj_tac >- metis_tac[subst_consts_stmt_blueprint_free] >>
  fs[subst_consts_exprs_map, EVERY_MAP, EVERY_MEM, MEM_MAP, combinTheory.o_DEF] >>
  metis_tac[subst_consts_expr_blueprint_free]
QED

Definition runtime_blueprint_free_def:
  runtime_blueprint_free source_tops <=>
    !vis mut nr rr name args dflts ret stmts.
      MEM (FunctionDecl vis mut nr rr name args dflts ret stmts) source_tops /\
      vis <> Deploy ==>
      ~supported_stmts_expr_exists blueprint_create_root stmts /\
      EVERY (\d. ~supported_expr_exists blueprint_create_root d) dflts
End

Theorem public_getter_blueprint_free[local]:
  public_getter top = SOME (mut,nr,rr,name,args,dflts,ret,stmts) ==>
  ~supported_stmts_expr_exists blueprint_create_root stmts /\
  EVERY (\d. ~supported_expr_exists blueprint_create_root d) dflts
Proof
  strip_tac >> drule public_getter_defaults >> simp[] >> strip_tac >>
  drule public_getter_body_shape >> strip_tac >>
  `!e. blueprint_create_root e ==> expr_shape_root e` by
    (simp[blueprint_create_root_def, expr_shape_root_def] >> metis_tac[]) >>
  metis_tac[CONJUNCT2 supported_stmt_expr_exists_mono]
QED

Theorem classify_external_blueprint_free:
  check_contract F layouts addr [(NONE, source_tops)] = SOME art /\ runtime_blueprint_free source_tops /\
  MEM (mut,nr,rr,name,args,dflts,ret,stmts)
      (FST (classify_functions source_tops)) ==>
  ~supported_stmts_expr_exists blueprint_create_root stmts /\
  EVERY (\d. ~supported_expr_exists blueprint_create_root d) dflts
Proof
  strip_tac >> drule classify_functions_external_source >> strip_tac >>
  gvs[subst_consts_fn_def] >> irule (GEN_ALL subst_consts_fn_blueprint_free) >>
  fs[runtime_blueprint_free_def] >>
  metis_tac[public_getter_blueprint_free, function_visibility_distinct]
QED

Theorem classify_internal_blueprint_free:
  check_contract F layouts addr [(NONE, source_tops)] = SOME art /\ (!mut nr rr name args ds ret ss.
    MEM (FunctionDecl Internal mut nr rr name args ds ret ss) source_tops ==>
    ~supported_stmts_expr_exists blueprint_create_root ss /\
    EVERY (\d. ~supported_expr_exists blueprint_create_root d) ds) /\
  MEM (mut,nr,rr,name,args,dflts,ret,stmts)
      (FST (SND (classify_functions source_tops))) ==>
  ~supported_stmts_expr_exists blueprint_create_root stmts /\
  EVERY (\d. ~supported_expr_exists blueprint_create_root d) dflts
Proof
  strip_tac >> drule (iffLR (SPEC_ALL MEM_classify_internal)) >> strip_tac >>
  gvs[subst_consts_fn_def] >> irule (GEN_ALL subst_consts_fn_blueprint_free) >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem classify_fallback_blueprint_free:
  check_contract F layouts addr [(NONE, source_tops)] = SOME art /\ runtime_blueprint_free source_tops /\
  FST (SND (SND (classify_functions source_tops))) =
    SOME (mut,nr,rr,name,args,dflts,ret,stmts) ==>
  ~supported_stmts_expr_exists blueprint_create_root stmts /\
  EVERY (\d. ~supported_expr_exists blueprint_create_root d) dflts
Proof
  strip_tac >> drule classify_functions_fallback_mem >> strip_tac >>
  gvs[subst_consts_fn_def] >> irule (GEN_ALL subst_consts_fn_blueprint_free) >>
  fs[runtime_blueprint_free_def] >> metis_tac[function_visibility_distinct]
QED

Theorem build_func_defaults_blueprint_free:
  check_contract F layouts addr [(NONE, source_tops)] = SOME art /\ (!mut nr rr name args ds ret ss.
    MEM (FunctionDecl Internal mut nr rr name args ds ret ss) source_tops ==>
    ~supported_stmts_expr_exists blueprint_create_root ss /\
    EVERY (\d. ~supported_expr_exists blueprint_create_root d) ds) ==>
  EVERY (EVERY (\d. ~supported_expr_exists blueprint_create_root d) o SND)
    (build_func_defaults source_tops)
Proof
  simp[build_func_defaults_def, EVERY_MAP, combinTheory.o_DEF] >>
  simp[EVERY_MEM, pairTheory.FORALL_PROD] >>
  metis_tac[SIMP_RULE (srw_ss()) [EVERY_MEM] classify_internal_blueprint_free]
QED

Definition compile_env_blueprint_free_def:
  compile_env_blueprint_free env <=>
    EVERY (EVERY (\d. ~supported_expr_exists blueprint_create_root d) o SND)
      env.ce_func_defaults
End

Theorem build_compile_env_blueprint_free:
  check_contract F layouts addr [(NONE, source_tops)] = SOME art /\ (!mut nr rr name args ds ret ss.
    MEM (FunctionDecl Internal mut nr rr name args ds ret ss) source_tops ==>
    ~supported_stmts_expr_exists blueprint_create_root ss /\
    EVERY (\d. ~supported_expr_exists blueprint_create_root d) ds) ==>
  compile_env_blueprint_free
    (build_compile_env source_tops vis mut name args ret stmts ut)
Proof
  simp[compile_env_blueprint_free_def, build_compile_env_ce_func_defaults] >>
  metis_tac[build_func_defaults_blueprint_free]
QED

Theorem omitted_defaults_blueprint_free:
  compile_env_blueprint_free env ==>
  EVERY (\d. ~supported_expr_exists blueprint_create_root d)
    (omitted_defaults env name nargs) /\
  compile_env_blueprint_free (cenv_without_defaults env name)
Proof
  simp[compile_env_blueprint_free_def, omitted_defaults_def, cenv_without_defaults_def] >>
  strip_tac >> conj_tac
  >- (Cases_on `ALOOKUP env.ce_func_defaults name` >> simp[] >>
      irule EVERY_DROP >> fs[EVERY_MEM, combinTheory.o_DEF] >>
      drule ALOOKUP_MEM >> disch_tac >>
      first_x_assum (qspec_then `(name,x)` mp_tac) >> simp[]) >>
  fs[EVERY_MEM, MEM_FILTER] >> metis_tac[]
QED
