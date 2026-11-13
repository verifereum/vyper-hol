(* Source-side boundary for the constructor's call-free lowering proof.
 * TOP-LEVEL: classified_constructor_call_free_source.
 * Helpers: constant substitution keeps a constructor body free of calls
 * when the substituted constants are (constant_expr has no Call case).
 *)
Theory ctorCallFreeSource
Ancestors
  list option e2eDeployDefs ctorDeployDefs ctorCallFreeRules loweringShapeProps
  loweringShapeSource vyperTypeContractContext vyperTypeContract
  vyperTypeContractStaticMaps supportedExprTraverse supportedStmtTraverse
  compileVyper constSubst constSubstCorrect vyperAST

Theorem constant_expr_call_free[local]:
  (!e. constant_expr mods e ==> ~supported_expr_exists expr_call_root e) /\
  (!es. EVERY (constant_expr mods) es ==>
    ~supported_exprs_exists expr_call_root es) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) ==>
    ~supported_fields_exists expr_call_root fs)
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[constant_expr_def, supported_expr_exists_def, expr_call_root_def] >>
  rpt strip_tac >> gvs[GSYM EVERY_NOT_EXISTS, combinTheory.o_DEF, SF ETA_ss] >>
  gvs[EXISTS_MEM, EVERY_MEM] >> res_tac
QED

Theorem subst_consts_expr_call_free[local]:
  (!env e.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists expr_call_root r) ==>
    ~supported_expr_exists expr_call_root e ==>
    ~supported_expr_exists expr_call_root (subst_consts_expr env e)) /\
  (!env t.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists expr_call_root r) ==>
    ~supported_target_exists expr_call_root t ==>
    ~supported_target_exists expr_call_root (subst_consts_btarget env t)) /\
  (!env es.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists expr_call_root r) ==>
    ~supported_exprs_exists expr_call_root es ==>
    ~supported_exprs_exists expr_call_root (subst_consts_exprs env es)) /\
  (!env opt.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists expr_call_root r) ==>
    ~supported_opt_exists expr_call_root opt ==>
    ~supported_opt_exists expr_call_root (subst_consts_opt env opt)) /\
  (!env fs.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists expr_call_root r) ==>
    ~supported_fields_exists expr_call_root fs ==>
    ~supported_fields_exists expr_call_root (subst_consts_fields env fs))
Proof
  ho_match_mp_tac subst_consts_expr_ind >>
  simp[subst_consts_expr_def, supported_expr_exists_def, expr_call_root_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `ns` >> simp[subst_consts_expr_def, supported_expr_exists_def,
        expr_call_root_def] >> Cases_on `ALOOKUP env id` >>
        gvs[supported_expr_exists_def, expr_call_root_def] >> metis_tac[])
  >> metis_tac[]
QED

Theorem subst_consts_target_call_free[local]:
  (!env t.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists expr_call_root r) ==>
    ~supported_assignment_exists expr_call_root t ==>
    ~supported_assignment_exists expr_call_root (subst_consts_target env t)) /\
  (!env ts.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists expr_call_root r) ==>
    ~supported_assignments_exists expr_call_root ts ==>
    ~supported_assignments_exists expr_call_root (subst_consts_targets env ts))
Proof
  ho_match_mp_tac subst_consts_target_ind >>
  simp[subst_consts_target_def, supported_assignment_exists_def] >>
  metis_tac[subst_consts_expr_call_free]
QED

Theorem subst_consts_error_call_free[local]:
  (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists expr_call_root r) /\
  ~EXISTS (supported_expr_exists expr_call_root) (custom_error_exprs err) ==>
  ~EXISTS (supported_expr_exists expr_call_root)
    (custom_error_exprs (subst_consts_error env err))
Proof
  Cases_on `err` >>
  pure_rewrite_tac[subst_consts_error_def, custom_error_exprs_def, EXISTS_APPEND] >>
  pure_rewrite_tac[EXISTS_MAP, combinTheory.o_DEF] >>
  rpt strip_tac >>
  imp_res_tac (SIMP_RULE std_ss
    [supported_exprs_exists_every, supported_fields_exists_every,
     EXISTS_MAP, combinTheory.o_DEF] subst_consts_expr_call_free) >>
  metis_tac[]
QED

Theorem subst_consts_stmt_call_free[local]:
  (!env s.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists expr_call_root r) ==>
    ~supported_stmt_expr_exists expr_call_root s ==>
    ~supported_stmt_expr_exists expr_call_root (subst_consts_stmt env s)) /\
  (!env ss.
    (!id r. ALOOKUP env id = SOME r ==> ~supported_expr_exists expr_call_root r) ==>
    ~supported_stmts_expr_exists expr_call_root ss ==>
    ~supported_stmts_expr_exists expr_call_root (subst_consts_stmts env ss))
Proof
  ho_match_mp_tac subst_consts_stmt_ind >>
  simp[subst_consts_stmt_def, supported_stmt_expr_exists_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> strip_tac
  >> gvs[subst_consts_iter_def, subst_consts_areason_def, subst_consts_rreason_def,
         supported_iterator_exists_def, supported_assert_exists_def,
         supported_raise_exists_def, AllCaseEqs()]
  >> imp_res_tac subst_consts_expr_call_free
  >> imp_res_tac subst_consts_target_call_free >> gvs[]
  >- (Cases_on `it` >> gvs[subst_consts_iter_def, supported_iterator_exists_def] >>
      metis_tac[])
  >~ [`supported_assert_exists expr_call_root (subst_consts_areason env r)`]
  >- (Cases_on `r` >>
      rule_assum_tac (PURE_REWRITE_RULE [supported_assert_exists_def]) >>
      pure_rewrite_tac[subst_consts_areason_def, supported_assert_exists_def] >>
      rpt strip_tac >>
      imp_res_tac subst_consts_expr_call_free >>
      metis_tac[subst_consts_error_call_free])
  >~ [`supported_raise_exists expr_call_root (subst_consts_rreason env r)`]
  >- (Cases_on `r` >>
      rule_assum_tac (PURE_REWRITE_RULE [supported_raise_exists_def]) >>
      pure_rewrite_tac[subst_consts_rreason_def, supported_raise_exists_def] >>
      rpt strip_tac >>
      imp_res_tac subst_consts_expr_call_free >>
      metis_tac[subst_consts_error_call_free])
  >> metis_tac[]
QED

(* The raw __init__ body: call-free by constructor_call_free, and so free of
   the raw shape roots too, which typing turns into the lowering's shape. *)
Theorem raw_constructor_call_free[local]:
  constructor_call_free tops /\
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  lookup_function NONE "__init__" Deploy tops =
    SOME (mut,nr,args,dflts,ret,bd) ==>
  ~supported_stmts_expr_exists expr_call_root bd /\
  ~supported_stmts_expr_exists expr_shape_root bd
Proof
  strip_tac >>
  `~supported_stmts_expr_exists expr_call_root bd` by
    (`~supported_stmts_expr_exists constructor_call_root bd` by
       metis_tac[constructor_call_free_def] >>
     strip_tac >>
     qpat_x_assum `~supported_stmts_expr_exists constructor_call_root _` mp_tac >>
     simp[] >> irule (cj 2 supported_stmt_expr_exists_mono) >>
     first_assum (irule_at Any) >>
     rpt strip_tac >> gvs[expr_call_root_def, constructor_call_root_def]) >>
  simp[] >>
  drule lookup_function_Deploy_SOME_cases >> strip_tac >>
  gvs[supported_stmt_expr_exists_def] >>
  `~supported_stmts_expr_exists expr_raw_shape_root bd` by
    (strip_tac >>
     qpat_x_assum `~supported_stmts_expr_exists expr_call_root _` mp_tac >>
     simp[] >> irule (cj 2 supported_stmt_expr_exists_mono) >>
     first_assum (irule_at Any) >>
     rpt strip_tac >> gvs[expr_raw_shape_root_def, expr_call_root_def]) >>
  drule check_contract_deploy_function_body_MEM >> simp[] >>
  disch_then drule >>
  simp[check_function_body_def, IS_SOME_EXISTS] >> strip_tac >>
  metis_tac[type_stmt_raw_shape]
QED

Theorem classified_constructor_call_free_source:
  !tops rpolicy runtime_bc dunit am tx exts ints fb
   mut nr rr fname args defaults ret ctor_body.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
    constructor_call_free tops /\ deploy_typing_ok tops am tx /\
    classify_functions tops =
      (exts, ints, fb, SOME (mut,nr,rr,fname,args,defaults,ret,ctor_body)) ==>
    ~supported_stmts_expr_exists expr_call_root ctor_body /\
    ~supported_stmts_expr_exists expr_shape_root ctor_body
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lower_vyper_deploy_unit_ctor_named_init >>
  simp[ctor_named_init_def] >> strip_tac >>
  qspecl_then [`tops`, `NONE`, `"__init__"`] mp_tac
    classify_functions_ctor_lookup >>
  simp[subst_consts_fn_def] >> strip_tac >>
  gvs[deploy_typing_ok_def] >>
  rename1 `check_contract T _ _ [(NONE,tops)] = SOME art` >>
  drule_all raw_constructor_call_free >> strip_tac >>
  conj_tac
  >- (irule (cj 2 subst_consts_stmt_call_free) >> simp[] >>
      rpt strip_tac >>
      `constant_expr [(NONE,tops)] r` by
        (drule checked_module_consts_env_replacement_constant >> simp[] >>
         disch_then drule >> simp[]) >>
      metis_tac[constant_expr_call_free]) >>
  irule (cj 2 subst_consts_stmt_shape) >> simp[] >>
  rpt strip_tac >>
  drule checked_module_consts_env_replacement_shape >> simp[] >>
  qexistsl [`r`, `id`] >> simp[]
QED
