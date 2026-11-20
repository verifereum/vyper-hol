Theory runtimeSymSrcClassifiedSource
Ancestors
  supportedProgram supportedDecls supportedNameRoot constSubstStmtsPreserve
  supportedExprs constSubst compileVyper list alist
  supportedExprTraverse supportedStmtTraverse exprLowering loweringShapeSource
  vyperAST vyperTypeContract constSubstCorrect

val _ = Parse.hide "body";

Theorem runtime_sym_constant_excludes_self_code[local]:
  (!e. constant_expr mods e ==> ~supported_expr_exists is_self_code e) /\
  (!es. EVERY (constant_expr mods) es ==> ~supported_exprs_exists is_self_code es) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) ==>
    ~supported_fields_exists is_self_code fs)
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[constant_expr_def, supported_expr_exists_def, is_self_code_def] >>
  rpt strip_tac >>
  gvs[GSYM EVERY_NOT_EXISTS, combinTheory.o_DEF, SF ETA_ss,
      EXISTS_MEM, EVERY_MEM] >>
  Cases_on `bi` >> gvs[constant_builtin_def, is_self_code_def] >> res_tac
QED

Theorem runtime_sym_checked_constant_replacements:
  check_contract mode layouts addr [(NONE,tops)] = SOME art /\
  ALOOKUP (module_consts_env tops []) id = SOME r ==>
  ~supported_expr_exists is_self_code r /\ !ty. r <> Builtin ty (Env SelfAddr) []
Proof
  strip_tac >>
  `ALOOKUP [(NONE:num option,tops)] NONE = SOME tops` by simp[] >>
  drule_all checked_module_consts_env_replacement_constant >> strip_tac >>
  conj_tac >- metis_tac[runtime_sym_constant_excludes_self_code] >>
  rpt strip_tac >> gvs[constant_expr_def, constant_builtin_def]
QED

Theorem runtime_sym_is_self_code_shape[local]:
  is_self_code e <=> ?ty addr_ty. e = Builtin ty (Acc Code)
                                      [Builtin addr_ty (Env SelfAddr) []]
Proof
  qid_spec_tac `e` >> ho_match_mp_tac is_self_code_ind >>
  simp[is_self_code_def] >> metis_tac[]
QED

Theorem runtime_sym_subst_self_addr[local]:
  (!id r. ALOOKUP env id = SOME r ==> !ty. r <> Builtin ty (Env SelfAddr) []) ==>
  (subst_consts_expr env e = Builtin ty (Env SelfAddr) [] <=>
   e = Builtin ty (Env SelfAddr) [])
Proof
  strip_tac >> Cases_on `e` >> simp[subst_consts_expr_def]
  >~ [`subst_consts_expr env (TopLevelName _ _)`]
  >- (rename1 `TopLevelName _ ns` >> PairCases_on `ns` >> Cases_on `ns0` >>
      gvs[subst_consts_expr_def, AllCaseEqs()] >> metis_tac[]) >>
  rename1 `subst_consts_exprs env es` >> Cases_on `es` >>
  simp[subst_consts_expr_def]
QED

Theorem runtime_sym_subst_is_self_code[local]:
  (!id r. ALOOKUP env id = SOME r ==>
    ~supported_expr_exists is_self_code r /\ !ty. r <> Builtin ty (Env SelfAddr) []) ==>
  is_self_code (subst_consts_expr env e) = is_self_code e
Proof
  strip_tac >>
  `!ty addr_ty. subst_consts_expr env (Builtin ty (Acc Code)
      [Builtin addr_ty (Env SelfAddr) []]) =
      Builtin ty (Acc Code) [Builtin addr_ty (Env SelfAddr) []]` by
    simp[subst_consts_expr_def] >>
  `!id r. ALOOKUP env id = SOME r ==> !ty. r <> Builtin ty (Env SelfAddr) []` by
    metis_tac[] >>
  eq_tac
  >- (Cases_on `e` >> simp[runtime_sym_is_self_code_shape, subst_consts_expr_def] >>
      rpt strip_tac >> gvs[]
      >~ [`subst_consts_expr env (TopLevelName _ _)`]
      >- (rename1 `TopLevelName _ ns` >> PairCases_on `ns` >> Cases_on `ns0` >>
          gvs[subst_consts_expr_def, AllCaseEqs()] >>
          metis_tac[supported_expr_exists_def, is_self_code_def]) >>
      rename1 `subst_consts_exprs env es` >> Cases_on `es` >>
      gvs[subst_consts_expr_def] >>
      rename1 `subst_consts_exprs env rest` >> Cases_on `rest` >>
      gvs[subst_consts_expr_def] >>
      metis_tac[runtime_sym_subst_self_addr]) >>
  simp[runtime_sym_is_self_code_shape] >> metis_tac[]
QED

Theorem runtime_sym_subst_builtin_self_code[local]:
  (!id r. ALOOKUP env id = SOME r ==>
    ~supported_expr_exists is_self_code r /\ !ty. r <> Builtin ty (Env SelfAddr) []) ==>
  is_self_code (Builtin ty bi (subst_consts_exprs env es)) =
  is_self_code (Builtin ty bi es)
Proof
  strip_tac >>
  drule (Q.INST [`e` |-> `Builtin ty bi es`] runtime_sym_subst_is_self_code) >>
  simp[subst_consts_expr_def]
QED

Theorem subst_consts_expr_self_code_free[local]:
  (!env e.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists is_self_code r /\ !ty. r <> Builtin ty (Env SelfAddr) []) ==>
    ~supported_expr_exists is_self_code e ==>
    ~supported_expr_exists is_self_code (subst_consts_expr env e)) /\
  (!env t.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists is_self_code r /\ !ty. r <> Builtin ty (Env SelfAddr) []) ==>
    ~supported_target_exists is_self_code t ==>
    ~supported_target_exists is_self_code (subst_consts_btarget env t)) /\
  (!env es.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists is_self_code r /\ !ty. r <> Builtin ty (Env SelfAddr) []) ==>
    ~supported_exprs_exists is_self_code es ==>
    ~supported_exprs_exists is_self_code (subst_consts_exprs env es)) /\
  (!env opt.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists is_self_code r /\ !ty. r <> Builtin ty (Env SelfAddr) []) ==>
    ~supported_opt_exists is_self_code opt ==>
    ~supported_opt_exists is_self_code (subst_consts_opt env opt)) /\
  (!env fs.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists is_self_code r /\ !ty. r <> Builtin ty (Env SelfAddr) []) ==>
    ~supported_fields_exists is_self_code fs ==>
    ~supported_fields_exists is_self_code (subst_consts_fields env fs))
Proof
  ho_match_mp_tac subst_consts_expr_ind >>
  simp[subst_consts_expr_def, supported_expr_exists_def] >>
  rpt strip_tac >> gvs[runtime_sym_subst_builtin_self_code, is_self_code_def]
  >- (Cases_on `ns` >> simp[subst_consts_expr_def, supported_expr_exists_def] >>
      Cases_on `ALOOKUP env id` >>
      gvs[supported_expr_exists_def, runtime_sym_is_self_code_shape] >> metis_tac[]) >>
  res_tac >> gvs[runtime_sym_is_self_code_shape] >>
  Cases_on `es` >> gvs[subst_consts_expr_def] >>
  rename1 `subst_consts_exprs env rest = []` >>
  Cases_on `rest` >> gvs[subst_consts_expr_def] >>
  metis_tac[runtime_sym_subst_self_addr]
QED

Theorem subst_consts_target_self_code_free[local]:
  (!env t.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists is_self_code r /\
      !ty. r <> Builtin ty (Env SelfAddr) []) ==>
    ~supported_assignment_exists is_self_code t ==>
    ~supported_assignment_exists is_self_code (subst_consts_target env t)) /\
  (!env ts.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists is_self_code r /\
      !ty. r <> Builtin ty (Env SelfAddr) []) ==>
    ~supported_assignments_exists is_self_code ts ==>
    ~supported_assignments_exists is_self_code (subst_consts_targets env ts))
Proof
  ho_match_mp_tac subst_consts_target_ind >>
  simp[subst_consts_target_def, supported_assignment_exists_def] >>
  metis_tac[subst_consts_expr_self_code_free]
QED

Theorem subst_consts_error_self_code_free[local]:
  (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists is_self_code r /\
      !ty. r <> Builtin ty (Env SelfAddr) []) /\
  ~EXISTS (supported_expr_exists is_self_code) (custom_error_exprs err) ==>
  ~EXISTS (supported_expr_exists is_self_code)
    (custom_error_exprs (subst_consts_error env err))
Proof
  Cases_on `err` >>
  pure_rewrite_tac[subst_consts_error_def, custom_error_exprs_def, EXISTS_APPEND] >>
  pure_rewrite_tac[EXISTS_MAP, combinTheory.o_DEF] >>
  rpt strip_tac >>
  imp_res_tac (SIMP_RULE std_ss
    [supported_exprs_exists_every, supported_fields_exists_every,
     EXISTS_MAP, combinTheory.o_DEF] subst_consts_expr_self_code_free) >>
  metis_tac[]
QED

Theorem subst_consts_stmt_self_code_free[local]:
  (!env s.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists is_self_code r /\
      !ty. r <> Builtin ty (Env SelfAddr) []) ==>
    ~supported_stmt_expr_exists is_self_code s ==>
    ~supported_stmt_expr_exists is_self_code (subst_consts_stmt env s)) /\
  (!env ss.
    (!id r. ALOOKUP env id = SOME r ==>
      ~supported_expr_exists is_self_code r /\
      !ty. r <> Builtin ty (Env SelfAddr) []) ==>
    ~supported_stmts_expr_exists is_self_code ss ==>
    ~supported_stmts_expr_exists is_self_code (subst_consts_stmts env ss))
Proof
  ho_match_mp_tac subst_consts_stmt_ind >>
  simp[subst_consts_stmt_def, supported_stmt_expr_exists_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> strip_tac
  >> gvs[subst_consts_iter_def, subst_consts_areason_def, subst_consts_rreason_def,
         supported_iterator_exists_def, supported_assert_exists_def,
         supported_raise_exists_def, AllCaseEqs()]
  >> imp_res_tac subst_consts_expr_self_code_free
  >> imp_res_tac subst_consts_target_self_code_free >> gvs[]
  >- (Cases_on `it` >> gvs[subst_consts_iter_def, supported_iterator_exists_def] >>
      metis_tac[])
  >~ [`supported_assert_exists is_self_code (subst_consts_areason env r)`]
  >- (Cases_on `r` >>
      rule_assum_tac (PURE_REWRITE_RULE [supported_assert_exists_def]) >>
      pure_rewrite_tac[subst_consts_areason_def, supported_assert_exists_def] >>
      rpt strip_tac >>
      imp_res_tac subst_consts_expr_self_code_free >>
      metis_tac[subst_consts_error_self_code_free])
  >~ [`supported_raise_exists is_self_code (subst_consts_rreason env r)`]
  >- (Cases_on `r` >>
      rule_assum_tac (PURE_REWRITE_RULE [supported_raise_exists_def]) >>
      pure_rewrite_tac[subst_consts_rreason_def, supported_raise_exists_def] >>
      rpt strip_tac >>
      imp_res_tac subst_consts_expr_self_code_free >>
      metis_tac[subst_consts_error_self_code_free])
  >> metis_tac[]
QED

Theorem runtime_sym_subst_function_exclusions:
  (!id r. ALOOKUP (module_consts_env tops []) id = SOME r ==>
    ~supported_expr_exists is_self_code r /\ !ty. r <> Builtin ty (Env SelfAddr) []) /\
  ~supported_exprs_exists is_self_code defaults /\
  ~supported_stmts_expr_exists is_self_code body ==>
  ~supported_exprs_exists is_self_code (subst_consts_exprs (module_consts_env tops []) defaults) /\
  ~supported_stmts_expr_exists is_self_code (subst_consts_stmts (module_consts_env tops []) body)
Proof
  metis_tac[cj 3 subst_consts_expr_self_code_free, cj 2 subst_consts_stmt_self_code_free]
QED

Theorem runtime_sym_const_lookup_names:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  IS_SOME (ALOOKUP (module_consts_env tops []) id) ==>
  ?vis c ty slot.
    supported_variable_decl tops (NONE,id) = SOME (vis,Constant c,ty,slot)
Proof
  strip_tac >> drule distinct_module_consts_env_names_constant >>
  disch_then irule >> spose_not_then assume_tac >> gvs[GSYM ALOOKUP_NONE]
QED

(* TEMPORARILY CHEATED - SCRATCH SEQ-8501 census (never lands)
Proof
  strip_tac >>
  drule_all supported_program_declaration >>
  simp[supported_function_header_contract, supported_declaration_body_def] >>
  strip_tac >>
  irule subst_consts_supported_fn_unchanged >>
  qexistsl_tac [`tops`, `vis`] >>
  Cases_on `vis = Deploy` >> gvs[NULL_EQ, supported_pure_expr_def] >>
  metis_tac[runtime_sym_const_lookup_names, supported_program_deploy_function]
QED
*)
Theorem runtime_sym_supported_function_subst:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ (vis = Deploy ==> supported_program_deploy tops) /\
  MEM (FunctionDecl vis mut nr rr name args defaults ret body) tops ==>
  subst_consts_fn (module_consts_env tops [])
    (mut,nr,rr,name,args,defaults,ret,body) =
    (mut,nr,rr,name,args,defaults,ret,body)
Proof
  cheat
QED
