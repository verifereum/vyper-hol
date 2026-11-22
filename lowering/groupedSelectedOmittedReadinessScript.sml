Theory groupedSelectedOmittedReadiness
Ancestors
  groupedDefaultSyntax groupedDefaultPre runtimeDefaultCompile
  constSubstCorrect constSubstStmtsPreserve supportedStmtTraverse
  e2eDefs compileVyper externalBodyFrame allocLimitsProps externalBodyWidths
  exprSimSource vyperTypeCallStackSoundness vyperTypeEvalProofs
  vyperTypeInvariants vyperTypeContract words list rich_list pair finite_map
  alist vyperContext vyperInterpreter gasContext constSubst exprSimHypsDefs
  gasShadowCompileBase compileEnv

(* Recover the environment used by allocation checking from the grouped package. *)
Triviality selected_default_allocs:
  fn_allocs_ok tops (mut,nr,rr,name,args,ds,ret,ss) /\
  package_external_group tops target T (K global_nonreentrant_slot)
    (mut,nr,rr,name,args,ds,ret,ss) = ExternalDefaults common entries specs off ==>
  ds <> [] /\ alloc_limits_exprs (common.ec_env with ce_vars := FEMPTY) ds /\
  EVERY (\(_,ty). type_memory_bytes common.ec_env ty < 2 ** 64) args
Proof
  strip_tac >>
  `ds <> []` by (strip_tac >> gvs[package_external_group_no_defaults]) >>
  Cases_on `set_external_package_target target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,rr,name,args,ds,ret,ss))` >> PairCases_on `r` >>
  `common.ec_env = r0` by gvs[package_external_group_def, NULL_EQ, LET_THM] >>
  `r4 = nr /\ r8 = ss` by
    (qpat_assum `set_external_package_target _ _ = _` mp_tac >>
     Cases_on `ret = NoneT` >>
     gvs[package_external_fn_def, set_external_package_target_def, LET_THM]) >>
  qpat_x_assum `r8 = ss` SUBST_ALL_TAC >>
  qpat_x_assum `r4 = nr` SUBST_ALL_TAC >>
  qpat_x_assum `common.ec_env = r0` SUBST_ALL_TAC >>
  drule external_package_alloc_env_agree >>
  disch_then (fn th =>
    mp_tac (Q.SPEC `r0 with ce_vars := FEMPTY` th) >>
    mp_tac (Q.SPEC `r0` th)) >>
  simp[] >> rpt disch_tac >> conj_tac
  >- (qpat_x_assum `alloc_env_agree _ r0` kall_tac >>
      drule_all fn_allocs_ok_body >> simp[]) >>
  qpat_x_assum `alloc_env_agree _ (_ with ce_vars := FEMPTY)` kall_tac >>
  drule_all fn_allocs_ok_body >> simp[]
QED

(* Substitution preserves annotations in the checked context and removes
   constant names throughout each substituted expression. *)
Triviality selected_default_substitution:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
  well_typed_exprs (artifact_env art [(NONE,tops)] NONE) raw ==>
  MAP expr_type (subst_consts_exprs (module_consts_env tops []) raw) =
    MAP expr_type raw /\
  EVERY (\e. ~supported_expr_exists (const_name_root_mods [(NONE,tops)]) e)
    (subst_consts_exprs (module_consts_env tops []) raw)
Proof
  strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  drule_all lower_vyper_runtime_unit_consts_guard >> strip_tac >>
  drule source_typing_ok_consts_ready >>
  disch_then (qx_choosel_then [`artifact`,`constants`] strip_assume_tac) >>
  `artifact = art` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `artifact = art` SUBST_ALL_TAC >>
  `ALOOKUP am.sources tx.target = SOME [(NONE,tops)]` by fs[source_deployment_rel_def] >>
  conj_tac
  >- (qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
      mp_tac (Q.INST [`cx` |-> `cx`, `mods` |-> `[(NONE,tops)]`, `artifact` |-> `art`,
        `imms` |-> `account_immutables am tx.target`, `sc` |-> `[]`,
        `current_src` |-> `NONE:num option`, `A` |-> `constants`]
        checked_module_consts_subst_context) >>
      impl_tac >- simp[Abbr `cx`, initial_evaluation_context_def] >>
      metis_tac[const_subst_typed_annotations]) >>
  simp[subst_consts_exprs_map, EVERY_MAP] >>
  simp[EVERY_MEM] >> qx_gen_tac `e` >> strip_tac >>
  drule_all checked_const_substitution_const_name_free >>
  disch_then (qspec_then `[Expr e]` mp_tac) >>
  simp[subst_consts_stmt_def, supported_stmt_expr_exists_def]
QED

Triviality selected_default_expr_pre:
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  source_deployment_rel tops am tx /\
  check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
  runtime_constant_expr [(NONE,tops)] e /\
  well_typed_expr (artifact_env art [(NONE,tops)] NONE) e /\
  alloc_limits_expr c0 e /\
  ~supported_expr_exists (const_name_root_mods [(NONE,tops)]) e /\
  expr_sim_inv c0 cx (artifact_env art [(NONE,tops)] NONE) es ==>
  expr_body_pre c0 cx (artifact_env art [(NONE,tops)] NONE) e es
Proof
  strip_tac >>
  `ALOOKUP am.sources tx.target = SOME [(NONE,tops)]` by fs[source_deployment_rel_def] >>
  `cx_tops cx = tops /\ get_tenv cx = type_env tops` by
    simp[cx_tops_def, get_module_code_def, get_tenv_def,
         initial_evaluation_context_def, type_env_all_modules_def, type_env_def] >>
  `call_evaluation_safe cx []` by
    (`cx with stk := [(NONE,tx.function_name)] = cx` by
       simp[initial_evaluation_context_def] >>
     pop_assum (fn th => ONCE_REWRITE_TAC [GSYM th]) >>
     irule checked_contract_call_evaluation_safe_singleton >>
     simp[initial_evaluation_context_def, calls_follow_call_graph_def] >>
     metis_tac[]) >>
  `byte_widths_expr e` by
    (irule well_typed_expr_byte_widths >>
     qexists `artifact_env art [(NONE,tops)] NONE` >>
     simp[] >> conj_tac >- simp[artifact_env_def] >>
     fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def]) >>
  irule runtime_constant_expr_body_pre >> simp[] >>
  metis_tac[const_name_root_mods_singleton]
QED

(* Both projections are taken at the same index of the allocated rows. *)
Triviality selected_default_row_alignment:
  MAP (\(n,_,ty,_). (n,ty)) vars = kws /\
  MAP (\(_,_,_,e). e) vars = ds /\
  MAP expr_type ds = MAP SND kws /\ MEM (n:string,dst,ty,e) vars ==>
  MEM e ds /\ MEM (n,ty) kws /\ expr_type e = ty
Proof
  strip_tac >>
  qpat_x_assum `MEM _ vars` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 `i < LENGTH vars` >>
  qpat_x_assum `(n,dst,ty,e) = EL i vars` (assume_tac o SYM) >>
  `EL i ds = e` by
    (qpat_assum `MAP _ vars = ds` (mp_tac o AP_TERM ``EL i : expr list -> expr``) >>
     simp[EL_MAP]) >>
  `EL i kws = (n,ty)` by
    (qpat_assum `MAP _ vars = kws`
       (mp_tac o AP_TERM ``EL i : (string # type) list -> string # type``) >>
     simp[EL_MAP]) >>
  `i < LENGTH ds /\ i < LENGTH kws` by
    (conj_tac
     >- (qpat_assum `MAP _ vars = ds` (mp_tac o AP_TERM ``LENGTH : expr list -> num``) >>
         simp[]) >>
     qpat_assum `MAP _ vars = kws`
       (mp_tac o AP_TERM ``LENGTH : (string # type) list -> num``) >> simp[]) >>
  conj_tac >- (pure_rewrite_tac[MEM_EL] >> qexists `i` >> metis_tac[]) >>
  conj_tac >- (pure_rewrite_tac[MEM_EL] >> qexists `i` >> metis_tac[]) >>
  qpat_assum `MAP expr_type ds = _` (mp_tac o AP_TERM ``EL i : type list -> type``) >>
  simp[EL_MAP]
QED

Theorem grouped_selected_omitted_readiness:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
  MEM (FunctionDecl External mut nr rr name args raw ret fbody) tops /\
  ds = subst_consts_exprs (module_consts_env tops []) raw /\
  ss = subst_consts_stmts (module_consts_env tops []) fbody /\
  MEM (mut,nr,rr,name,args,ds,ret,ss) (FST (classify_functions tops)) /\
  package_external_group tops rp.rpol_target T (K global_nonreentrant_slot)
    (mut,nr,rr,name,args,ds,ret,ss) = ExternalDefaults common entries specs off /\
  MAP (\(n,_,ty,_). (n,ty)) vars = DROP (LENGTH args - LENGTH ds) args /\
  MAP (\(_,_,_,e). e) vars = ds /\
  env = artifact_env art [(NONE,tops)] NONE /\
  ce = common.ec_env /\ c0 = (ce with ce_vars := FEMPTY) /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE ==>
  well_typed_exprs env (DROP k raw) /\
  DROP k ds = subst_consts_exprs (module_consts_env tops []) (DROP k raw) /\
  EVERY (runtime_constant_expr [(NONE,tops)]) (DROP k ds) /\
  no_sha256_exprs (DROP k ds) /\
  EVERY (\(n,dst,ty,e). runtime_constant_expr [(NONE,tops)] e /\ expr_type e = ty /\
    (!es'. expr_sim_inv c0 cx env es' ==> expr_body_pre c0 cx env e es') /\
    lower_value compile_expr c0 ty e = lower_value compile_expr ce ty e /\
    lower_value compile_expr (gas_shadow_env T c0) ty (gas_shadow_expr e) =
      lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) /\
    type_memory_bytes ce ty + 64 < dimword (:256)) (DROP k vars)
Proof
  strip_tac >>
  drule_all grouped_checked_default_syntax >> strip_tac >>
  `LENGTH ds = LENGTH raw` by simp[subst_consts_exprs_map] >>
  `well_typed_exprs env ds /\ EVERY (runtime_constant_expr [(NONE,tops)]) ds` by simp[] >>
  `MAP expr_type ds = MAP expr_type raw /\
   EVERY (\e. ~supported_expr_exists (const_name_root_mods [(NONE,tops)]) e) ds` by
    (qpat_assum `ds = _` (fn th => PURE_REWRITE_TAC [th]) >>
     match_mp_tac selected_default_substitution >> metis_tac[]) >>
  `MAP expr_type ds = MAP SND (DROP (LENGTH args - LENGTH ds) args)` by metis_tac[] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  `fn_allocs_ok tops (mut,nr,rr,name,args,ds,ret,ss)` by
    (irule lower_vyper_runtime_unit_allocs_ok >> metis_tac[pairTheory.FST]) >>
  drule_all selected_default_allocs >> strip_tac >>
  `EVERY external_defaults_no_sha256 q` by
    (`EXISTS external_has_defaults q` by
       (simp[EXISTS_MEM] >> qexists `(mut,nr,rr,name,args,ds,ret,ss)` >>
        fs[external_has_defaults_def, NULL_EQ]) >>
     gvs[lower_vyper_runtime_unit_def, AllCaseEqs()]) >>
  `MEM (mut,nr,rr,name,args,ds,ret,ss) q` by fs[] >>
  `no_sha256_exprs ds` by
    (qpat_assum `EVERY external_defaults_no_sha256 q`
       (qspec_then `(mut,nr,rr,name,args,ds,ret,ss)` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     simp[external_defaults_no_sha256_def]) >>
  conj_tac >- metis_tac[well_typed_exprs_DROP] >>
  conj_tac >- simp[subst_consts_exprs_map, MAP_DROP] >>
  conj_tac >- metis_tac[EVERY_DROP] >>
  conj_tac >- (fs[no_sha256_collections] >> metis_tac[EVERY_DROP]) >>
  irule EVERY_DROP >> simp[EVERY_MEM, FORALL_PROD] >>
  map_every qx_gen_tac [`n`,`dst`,`ty`,`e`] >>
  strip_tac >> drule_all selected_default_row_alignment >> strip_tac >>
  `MEM (n,ty) args` by metis_tac[MEM_DROP_IMP] >>
  `well_typed_expr env e` by metis_tac[well_typed_exprs_member] >>
  `runtime_constant_expr [(NONE,tops)] e` by fs[EVERY_MEM] >>
  `alloc_limits_expr c0 e` by metis_tac[alloc_limits_exprs_mem] >>
  `~supported_expr_exists (const_name_root_mods [(NONE,tops)]) e` by fs[EVERY_MEM] >>
  `type_memory_bytes ce ty < 2 ** 64` by
    (qpat_assum `EVERY _ args`
       (qspec_then `(n,ty)` mp_tac o REWRITE_RULE [EVERY_MEM]) >> simp[]) >>
  `type_memory_bytes ce ty + 64 < dimword (:256)` by
    (qpat_assum `type_memory_bytes ce ty < _` mp_tac >>
     simp[NoAsms, dimword_def] >> decide_tac) >>
  `!es'. expr_sim_inv c0 cx env es' ==> expr_body_pre c0 cx env e es'` by
    (rpt strip_tac >> qpat_x_assum `env = _` SUBST_ALL_TAC >>
     irule selected_default_expr_pre >> metis_tac[]) >>
  `!c. lower_value compile_expr (c with ce_vars := FEMPTY) ty e =
         lower_value compile_expr c ty e /\
       lower_value compile_expr (c with ce_vars := FEMPTY) ty (gas_shadow_expr e) =
         lower_value compile_expr c ty (gas_shadow_expr e)` by
    (gen_tac >> match_mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`]
       (SPEC_ALL runtime_default_lower_value_vars_frame)) >>
     qpat_assum `well_typed_expr env e`
       (mp_tac o MATCH_MP (cj 1 well_typed_expr_builtin_args_length)) >> simp[]) >>
  `gas_shadow_env T c0 = (gas_shadow_env T ce with ce_vars := FEMPTY)` by
    rw[gas_shadow_env_def, compile_env_component_equality] >>
  qpat_assum `!c. lower_value compile_expr _ _ _ = _ /\ _`
    (fn th => assume_tac (cj 1 (Q.SPEC `ce` th)) >>
              assume_tac (cj 2 (Q.SPEC `gas_shadow_env T ce` th))) >>
  qpat_x_assum `c0 = _` SUBST_ALL_TAC >>
  qpat_x_assum `ce = _` SUBST_ALL_TAC >>
  qpat_x_assum `cx = _` SUBST_ALL_TAC >>
  qpat_x_assum `env = _` SUBST_ALL_TAC >>
  asm_rewrite_tac[]
QED
