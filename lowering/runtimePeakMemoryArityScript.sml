(* Checked builtin operands prevent lowering from selecting an absent child. *)
Theory runtimePeakMemoryArity
Ancestors
  runtimePeakMemorySourceGate loweringShapeSource loweringShapeProps
  e2eDefs vyperAST vyperTypeSystem vyperTypeContract vyperTypeContractContext
  supportedExprTraverse
  supportedStmtTraverse constSubst constSubstCorrect compileVyper publicGetterProps compileEnv
  exprLowering list rich_list alist

Definition short_builtin_args_def:
  short_builtin_args e <=>
    (?ty bi es. e = Builtin ty bi es /\ LENGTH es < builtin_arity bi) \/
    (?ty tb target es. e = TypeBuiltin ty tb target es /\
                       LENGTH es < type_builtin_arity tb)
End

Theorem well_typed_expr_builtin_arity:
  (!env e. well_typed_expr env e ==> ~supported_expr_exists short_builtin_args e) /\
  (!env e vt. type_place_expr env e = SOME vt ==>
     ~supported_expr_exists short_builtin_args e) /\
  (!env t vt. type_place_target env t = SOME vt ==>
     ~supported_target_exists short_builtin_args t) /\
  (!env es. well_typed_exprs env es ==> ~supported_exprs_exists short_builtin_args es) /\
  (!env opt. well_typed_opt env opt ==> ~supported_opt_exists short_builtin_args opt) /\
  (!env kes. well_typed_named_exprs env kes ==>
     ~supported_fields_exists short_builtin_args kes)
Proof
  ho_match_mp_tac well_typed_expr_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >>
  gvs[well_typed_expr_def, supported_expr_exists_def, short_builtin_args_def, AllCaseEqs()] >>
  rpt (qpat_x_assum `_ \/ _` strip_assume_tac) >>
  res_tac >> gvs[] >>
  FIRST [qpat_assum `LENGTH es < builtin_arity blt` (K (Cases_on `blt`)),
         Cases_on `tb`] >>
  gvs[well_typed_builtin_app_def, builtin_arity_def,
      well_typed_type_builtin_args_def, type_builtin_arity_def] >>
  qpat_assum `MAP expr_type es = _`
    (mp_tac o AP_TERM ``LENGTH : type list -> num``) >> simp[]
QED

Theorem typed_assignment_builtin_arity[local]:
  (!p t. p = short_builtin_args ==>
     !ty. well_typed_atarget env t ty ==> ~supported_assignment_exists p t) /\
  (!p ts. p = short_builtin_args ==>
     !tys. LIST_REL (\t ty. well_typed_atarget env t ty) ts tys ==>
     ~supported_assignments_exists p ts)
Proof
  ho_match_mp_tac supported_assignment_exists_ind >>
  rw[supported_assignment_exists_def] >>
  gvs[well_typed_atarget_def, well_typed_target_def, LIST_REL_CONS1] >>
  imp_res_tac well_typed_expr_builtin_arity >> res_tac >> gvs[]
QED

Theorem assignment_builtin_arity[local]:
  atarget_accepts env tgt t ==> ~supported_assignment_exists short_builtin_args tgt
Proof
  Cases_on `tgt` >>
  simp[atarget_accepts_def, supported_assignment_exists_def] >>
  rpt strip_tac
  >- (rename1 `type_place_target env b` >>
      Cases_on `type_place_target env b` >> fs[] >>
      metis_tac[well_typed_expr_builtin_arity]) >>
  metis_tac[typed_assignment_builtin_arity, supported_assignment_exists_def]
QED

Theorem iterator_builtin_arity[local]:
  well_typed_iterator env typ it ==> ~supported_iterator_exists short_builtin_args it
Proof
  Cases_on `it` >>
  rw[well_typed_iterator_def, supported_iterator_exists_def] >>
  metis_tac[well_typed_expr_builtin_arity]
QED

Theorem type_stmt_builtin_arity:
  (!env ret s env1. type_stmt env ret s = SOME env1 ==>
    ~supported_stmt_expr_exists short_builtin_args s) /\
  (!env ret ss env1. type_stmts env ret ss = SOME env1 ==>
    ~supported_stmts_expr_exists short_builtin_args ss)
Proof
  ho_match_mp_tac type_stmt_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >>
  gvs[type_stmt_def, supported_stmt_expr_exists_def, AllCaseEqs(),
      optionTheory.IS_SOME_EXISTS, supported_assert_exists_def, supported_raise_exists_def,
      supported_iterator_exists_def, well_typed_iterator_def,
      well_typed_custom_error_def, well_typed_target_def,
      GSYM supported_exprs_exists_every, supported_expr_exists_def] >>
  rpt (qpat_x_assum `_ \/ _` strip_assume_tac) >>
  res_tac >> imp_res_tac well_typed_expr_builtin_arity >>
  imp_res_tac assignment_builtin_arity >>
  imp_res_tac iterator_builtin_arity >> gvs[]
QED

Theorem checked_source_builtin_arity:
  check_contract mode layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret stmts) tops /\
  (mode \/ vis <> Deploy) ==>
  ~supported_stmts_expr_exists short_builtin_args stmts /\
  EVERY (\e. ~supported_expr_exists short_builtin_args e) dflts
Proof
  strip_tac >>
  `check_function_body layouts addr [(NONE,tops)] art NONE
     vis mut nr args dflts ret stmts` by
    (Cases_on `mode` >> fs[]
     >- (drule check_contract_deploy_function_body_MEM >> simp[] >>
         disch_then drule_all >> simp[])
     >> drule check_contract_main_module_allocated >> simp[] >> strip_tac >>
     drule check_contract_runtime_function_body_MEM >> simp[] >>
     disch_then drule_all >> simp[]) >>
  pop_assum mp_tac >>
  simp[check_function_body_def, optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  (conj_tac >- metis_tac[type_stmt_builtin_arity] >>
   qpat_x_assum `well_typed_exprs _ dflts`
     (mp_tac o MATCH_MP (cj 4 well_typed_expr_builtin_arity)) >>
   simp[supported_exprs_exists_every, GSYM EVERY_NOT_EXISTS, combinTheory.o_DEF])
QED

Theorem subst_consts_expr_builtin_arity[local]:
  (!env e.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists short_builtin_args r) ==>
    ~supported_expr_exists short_builtin_args e ==>
    ~supported_expr_exists short_builtin_args (subst_consts_expr env e)) /\
  (!env t.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists short_builtin_args r) ==>
    ~supported_target_exists short_builtin_args t ==>
    ~supported_target_exists short_builtin_args (subst_consts_btarget env t)) /\
  (!env es.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists short_builtin_args r) ==>
    ~supported_exprs_exists short_builtin_args es ==>
    ~supported_exprs_exists short_builtin_args (subst_consts_exprs env es)) /\
  (!env opt.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists short_builtin_args r) ==>
    ~supported_opt_exists short_builtin_args opt ==>
    ~supported_opt_exists short_builtin_args (subst_consts_opt env opt)) /\
  (!env fs.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists short_builtin_args r) ==>
    ~supported_fields_exists short_builtin_args fs ==>
    ~supported_fields_exists short_builtin_args (subst_consts_fields env fs))
Proof
  ho_match_mp_tac subst_consts_expr_ind >>
  simp[subst_consts_expr_def, supported_expr_exists_def, short_builtin_args_def, subst_consts_exprs_length] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `ns` >> simp[subst_consts_expr_def, supported_expr_exists_def,
        short_builtin_args_def, subst_consts_exprs_length] >> Cases_on `ALOOKUP env id` >>
        gvs[supported_expr_exists_def, short_builtin_args_def, subst_consts_exprs_length] >> metis_tac[])
  >> metis_tac[]
QED

Theorem subst_consts_target_builtin_arity[local]:
  (!env t.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists short_builtin_args r) ==>
    ~supported_assignment_exists short_builtin_args t ==>
    ~supported_assignment_exists short_builtin_args (subst_consts_target env t)) /\
  (!env ts.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists short_builtin_args r) ==>
    ~supported_assignments_exists short_builtin_args ts ==>
    ~supported_assignments_exists short_builtin_args (subst_consts_targets env ts))
Proof
  ho_match_mp_tac subst_consts_target_ind >>
  simp[subst_consts_target_def, supported_assignment_exists_def] >>
  metis_tac[subst_consts_expr_builtin_arity]
QED

Theorem subst_consts_error_builtin_arity[local]:
  (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists short_builtin_args r) /\
  ~EXISTS (supported_expr_exists short_builtin_args) (custom_error_exprs err) ==>
  ~EXISTS (supported_expr_exists short_builtin_args)
    (custom_error_exprs (subst_consts_error env err))
Proof
  Cases_on `err` >>
  pure_rewrite_tac[subst_consts_error_def, custom_error_exprs_def, EXISTS_APPEND] >>
  pure_rewrite_tac[EXISTS_MAP, combinTheory.o_DEF] >>
  rpt strip_tac >>
  imp_res_tac (SIMP_RULE std_ss
    [supported_exprs_exists_every, supported_fields_exists_every,
     EXISTS_MAP, combinTheory.o_DEF] subst_consts_expr_builtin_arity) >>
  metis_tac[]
QED

Theorem subst_consts_stmt_builtin_arity[local]:
  (!env s.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists short_builtin_args r) ==>
    ~supported_stmt_expr_exists short_builtin_args s ==>
    ~supported_stmt_expr_exists short_builtin_args (subst_consts_stmt env s)) /\
  (!env ss.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists short_builtin_args r) ==>
    ~supported_stmts_expr_exists short_builtin_args ss ==>
    ~supported_stmts_expr_exists short_builtin_args (subst_consts_stmts env ss))
Proof
  ho_match_mp_tac subst_consts_stmt_ind >>
  simp[subst_consts_stmt_def, supported_stmt_expr_exists_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> strip_tac
  >> gvs[subst_consts_iter_def, subst_consts_areason_def, subst_consts_rreason_def,
         supported_iterator_exists_def, supported_assert_exists_def,
         supported_raise_exists_def, AllCaseEqs()]
  >> imp_res_tac subst_consts_expr_builtin_arity
  >> imp_res_tac subst_consts_target_builtin_arity >> gvs[]
  >- (Cases_on `it` >> gvs[subst_consts_iter_def, supported_iterator_exists_def] >>
      metis_tac[])
  >~ [`supported_assert_exists short_builtin_args (subst_consts_areason env r)`]
  >- (Cases_on `r` >>
      rule_assum_tac (PURE_REWRITE_RULE [supported_assert_exists_def]) >>
      pure_rewrite_tac[subst_consts_areason_def, supported_assert_exists_def] >>
      rpt strip_tac >>
      imp_res_tac subst_consts_expr_builtin_arity >>
      metis_tac[subst_consts_error_builtin_arity])
  >~ [`supported_raise_exists short_builtin_args (subst_consts_rreason env r)`]
  >- (Cases_on `r` >>
      rule_assum_tac (PURE_REWRITE_RULE [supported_raise_exists_def]) >>
      pure_rewrite_tac[subst_consts_rreason_def, supported_raise_exists_def] >>
      rpt strip_tac >>
      imp_res_tac subst_consts_expr_builtin_arity >>
      metis_tac[subst_consts_error_builtin_arity])
  >> metis_tac[]
QED

Theorem short_builtin_args_shape_root[local]:
  !e. short_builtin_args e ==> expr_shape_root e
Proof
  simp[short_builtin_args_def, expr_shape_root_def] >> metis_tac[]
QED

Theorem checked_module_consts_builtin_arity[local]:
  check_contract F layouts addr [(NONE, source_tops)] = SOME art /\
  ALOOKUP (module_consts_env source_tops []) id = SOME r ==>
  ~supported_expr_exists short_builtin_args r
Proof
  strip_tac >>
  `ALOOKUP [(NONE:num option,source_tops)] NONE = SOME source_tops` by simp[] >>
  drule_all checked_module_consts_env_replacement_shape >>
  metis_tac[short_builtin_args_shape_root, cj 1 supported_expr_exists_mono]
QED

Theorem subst_checked_fn_builtin_arity:
  check_contract F layouts addr [(NONE, source_tops)] = SOME art /\
  ~supported_stmts_expr_exists short_builtin_args stmts /\
  EVERY (\d. ~supported_expr_exists short_builtin_args d) dflts ==>
  ~supported_stmts_expr_exists short_builtin_args
    (subst_consts_stmts (module_consts_env source_tops []) stmts) /\
  EVERY (\d. ~supported_expr_exists short_builtin_args d)
    (subst_consts_exprs (module_consts_env source_tops []) dflts)
Proof
  strip_tac >>
  `!id r. ALOOKUP (module_consts_env source_tops []) id = SOME r ==>
     ~supported_expr_exists short_builtin_args r` by
    metis_tac[checked_module_consts_builtin_arity] >>
  conj_tac >- metis_tac[subst_consts_stmt_builtin_arity] >>
  fs[subst_consts_exprs_map, EVERY_MAP, EVERY_MEM, MEM_MAP, combinTheory.o_DEF] >>
  metis_tac[subst_consts_expr_builtin_arity]
QED

Theorem public_getter_builtin_arity[local]:
  public_getter top = SOME (mut,nr,rr,name,args,dflts,ret,stmts) ==>
  ~supported_stmts_expr_exists short_builtin_args stmts /\
  EVERY (\d. ~supported_expr_exists short_builtin_args d) dflts
Proof
  strip_tac >> drule public_getter_defaults >> simp[] >> strip_tac >>
  drule public_getter_body_shape >> strip_tac >>
  metis_tac[short_builtin_args_shape_root, cj 2 supported_stmt_expr_exists_mono]
QED

Theorem classify_external_builtin_arity:
  check_contract F layouts addr [(NONE, source_tops)] = SOME art /\
  MEM (mut,nr,rr,name,args,dflts,ret,stmts)
      (FST (classify_functions source_tops)) ==>
  ~supported_stmts_expr_exists short_builtin_args stmts /\
  EVERY (\d. ~supported_expr_exists short_builtin_args d) dflts
Proof
  strip_tac >> drule classify_functions_external_source >> strip_tac >>
  gvs[subst_consts_fn_def] >> irule (GEN_ALL subst_checked_fn_builtin_arity) >>
  metis_tac[checked_source_builtin_arity, public_getter_builtin_arity,
            function_visibility_distinct]
QED

Theorem classify_internal_builtin_arity:
  check_contract F layouts addr [(NONE, source_tops)] = SOME art /\
  MEM (mut,nr,rr,name,args,dflts,ret,stmts)
      (FST (SND (classify_functions source_tops))) ==>
  ~supported_stmts_expr_exists short_builtin_args stmts /\
  EVERY (\d. ~supported_expr_exists short_builtin_args d) dflts
Proof
  strip_tac >> drule (iffLR (SPEC_ALL MEM_classify_internal)) >> strip_tac >>
  gvs[subst_consts_fn_def] >> irule (GEN_ALL subst_checked_fn_builtin_arity) >>
  metis_tac[checked_source_builtin_arity, function_visibility_distinct]
QED

Theorem classify_fallback_builtin_arity:
  check_contract F layouts addr [(NONE, source_tops)] = SOME art /\
  FST (SND (SND (classify_functions source_tops))) =
    SOME (mut,nr,rr,name,args,dflts,ret,stmts) ==>
  ~supported_stmts_expr_exists short_builtin_args stmts /\
  EVERY (\d. ~supported_expr_exists short_builtin_args d) dflts
Proof
  strip_tac >> drule classify_functions_fallback_mem >> strip_tac >>
  gvs[subst_consts_fn_def] >> irule (GEN_ALL subst_checked_fn_builtin_arity) >>
  metis_tac[checked_source_builtin_arity, function_visibility_distinct]
QED

Definition compile_env_builtin_arity_def:
  compile_env_builtin_arity env <=>
    EVERY (EVERY (\d. ~supported_expr_exists short_builtin_args d) o SND)
      env.ce_func_defaults
End

Theorem build_compile_env_builtin_arity:
  check_contract F layouts addr [(NONE, source_tops)] = SOME art ==>
  compile_env_builtin_arity
    (build_compile_env source_tops vis mut name args ret stmts ut)
Proof
  simp[compile_env_builtin_arity_def, build_compile_env_ce_func_defaults,
       build_func_defaults_def, EVERY_MAP, combinTheory.o_DEF] >>
  simp[EVERY_MEM, pairTheory.FORALL_PROD] >>
  metis_tac[SIMP_RULE (srw_ss()) [EVERY_MEM] classify_internal_builtin_arity]
QED

Theorem omitted_defaults_builtin_arity:
  compile_env_builtin_arity env ==>
  EVERY (\d. ~supported_expr_exists short_builtin_args d)
    (omitted_defaults env name nargs) /\
  compile_env_builtin_arity (cenv_without_defaults env name)
Proof
  simp[compile_env_builtin_arity_def, omitted_defaults_def, cenv_without_defaults_def] >>
  strip_tac >> conj_tac
  >- (Cases_on `ALOOKUP env.ce_func_defaults name` >> simp[] >>
      irule EVERY_DROP >> fs[EVERY_MEM, combinTheory.o_DEF] >>
      drule ALOOKUP_MEM >> disch_tac >>
      first_x_assum (qspec_then `(name,x)` mp_tac) >> simp[]) >>
  fs[EVERY_MEM, MEM_FILTER] >> metis_tac[]
QED
