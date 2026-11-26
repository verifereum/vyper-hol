(* Qualified reads at the selected default cut, without repinning the caller. *)
Theory bodyIntCallDefaultSelectedReadsMods
Ancestors
  bodyFullPredsMods bodyInvCodeProps bodyQualifiedLookupPlaceMods
  immutableRegionTypingProps exprBodyPreProps exprSimHypsDefs vyperContext
  bodyFullPostsMods bodyInvSplit loweringStateRelDefs finite_map vyperState
  exprSimProps valueEncodingProofs venomState words
  constSubst constSubstMods constSubstModsCorrect vyperTypeContractStaticMaps
  supportedExprTraverse whitelistCheckerConsts vyperInterpreter vyperTypeContract
  list alist rich_list pair

Theorem default_name_occurrence_declared[local]:
  (!e. runtime_constant_expr mods e /\
       supported_expr_exists ($= (TopLevelName ann (owner,id))) e ==>
       declared_constant mods owner id \/ declared_immutable mods owner id) /\
  (!t:base_assignment_target. T) /\
  (!es. EVERY (runtime_constant_expr mods) es /\
        supported_exprs_exists ($= (TopLevelName ann (owner,id))) es ==>
        declared_constant mods owner id \/ declared_immutable mods owner id) /\
  (!opt:expr option. T) /\
  (!fs. EVERY (runtime_constant_expr mods) (MAP SND fs) /\
        supported_fields_exists ($= (TopLevelName ann (owner,id))) fs ==>
        declared_constant mods owner id \/ declared_immutable mods owner id)
Proof
  ho_match_mp_tac fold_const_expr_ind >>
  simp[runtime_constant_expr_def, supported_expr_exists_def, SF ETA_ss] >>
  rpt strip_tac >> gvs[runtime_constant_expr_def] >>
  metis_tac[constant_expr_runtime_constant, EVERY_MONOTONIC]
QED

Theorem default_module_const_keys[local]:
  !tops src acc owner vis e id ty slot.
    (owner = src /\ MEM (VariableDecl vis (Constant e) id ty slot) tops) \/
    MEM (owner,id) (MAP FST acc) ==>
    MEM (owner,id) (MAP FST (module_consts_env_mods src tops acc))
Proof
  Induct >> simp[module_consts_env_mods_def] >>
  Cases_on `h` >> simp[module_consts_env_mods_def] >>
  TRY (first_assum ACCEPT_TAC) >>
  rename1 `VariableDecl _ mut _ _ _` >> Cases_on `mut` >>
  simp[module_consts_env_mods_def] >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> first_x_assum irule >>
  simp[MAP_APPEND] >> metis_tac[]
QED

Theorem default_const_key_in_env[local]:
  !mods acc src id.
    declared_constant mods src id \/ MEM (src,id) (MAP FST acc) ==>
    MEM (src,id) (MAP FST (consts_env_mods_acc mods acc))
Proof
  Induct >> simp[consts_env_mods_acc_def, declared_constant_def] >>
  gen_tac >> PairCases_on `h` >> simp[consts_env_mods_acc_def, declared_constant_def] >>
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[default_module_const_keys, declared_constant_def]
QED

Theorem default_declared_const_key[local]:
  declared_constant mods owner id ==>
  ?r. ALOOKUP (consts_env_mods mods) (owner,id) = SOME r
Proof
  strip_tac >>
  `declared_constant (constants_order mods) owner id` by
    (fs[declared_constant_def, MEM_constants_order] >> metis_tac[]) >>
  `MEM (owner,id) (MAP FST (consts_env_mods mods))` by
    (simp[consts_env_mods_def, consts_env_modules_order_eq] >>
     irule default_const_key_in_env >> simp[]) >>
  Cases_on `ALOOKUP (consts_env_mods mods) (owner,id)` >> fs[ALOOKUP_NONE]
QED

Theorem default_declared_const_root[local]:
  ALL_DISTINCT (MAP FST mods) /\ declared_constant mods owner id ==>
  const_name_root_mods mods (TopLevelName ann (owner,id))
Proof
  strip_tac >> fs[declared_constant_def] >>
  drule_all_then assume_tac ALOOKUP_ALL_DISTINCT_MEM >>
  `MEM (NONE,id) (MAP FST (module_consts_env_mods NONE tls []))` by
    (irule default_module_const_keys >> metis_tac[]) >>
  `module_consts_env_mods NONE tls [] =
   MAP (\(k,v). ((NONE,k),v)) (module_consts_env tls [])` by
    (qspecl_then [`tls`,`[]`] mp_tac module_consts_env_mods_singleton >> simp[]) >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, const_name_root_mods_def,
      cx_const_name_mods_def, MEM_MAP, FORALL_PROD, EXISTS_PROD] >>
  goal_assum (drule_at Any)
QED

Theorem default_raw_constant_cell[local]:
  body_const_cells_agree_mods mods cx env es /\ declared_constant mods owner id ==>
  ?r pv v roots.
    ALOOKUP (consts_env_mods mods) (owner,id) = SOME r /\
    const_cells_agree roots es /\
    const_result_at roots cx (expr_type r) (PlaceR (ImmutablePlace owner id [])) v /\
    const_result_at roots cx (expr_type r) pv v /\
    lookup_global cx owner id es = (INL (PlaceR (ImmutablePlace owner id [])),es) /\
    eval_expr cx r es = (INL pv,es)
Proof
  strip_tac >> drule_then strip_assume_tac default_declared_const_key >>
  qpat_x_assum `body_const_cells_agree_mods _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_mods_def]) >>
  qpat_assum `!src id r. ALOOKUP _ _ = SOME r ==> _`
    (drule_then strip_assume_tac) >>
  qexistsl [`r`,`pv`,`v`,`roots`] >> simp[]
QED

Theorem default_bare_decl_lookup[local]:
  contract_namespaces_ok F mods /\ ALOOKUP cx.sources cx.txn.target = SOME mods /\
  (declared_constant mods owner id \/ declared_immutable mods owner id) ==>
  ?ts. ALOOKUP mods owner = SOME ts /\ get_module_code cx owner = SOME ts /\
       find_var_decl_by_name id ts = NONE
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP FST mods)` by fs[contract_namespaces_ok_def] >>
  fs[declared_constant_def, declared_immutable_def] >>
  drule_all_then assume_tac ALOOKUP_ALL_DISTINCT_MEM >>
  drule_all_then assume_tac contract_namespaces_ok_module_toplevel_vtype_keys >>
  qexists_tac `tls` >> simp[get_module_code_def] >>
  metis_tac[find_var_decl_by_name_NONE_Immutable, find_var_decl_by_name_NONE_Constant]
QED

Theorem default_compiled_immutable[local]:
  contract_inv mods exps ctx ce cx /\ expr_sim_inv_mods mods ce cx env es /\
  ALOOKUP mods owner = SOME ts /\
  MEM (VariableDecl vis Immutable id ty slot) ts /\
  ~unallocated_bare_global_root ce env (TopLevelName ann (owner,id)) /\
  ~const_name_root_mods mods (TopLevelName ann (owner,id)) ==>
  ?off. FLOOKUP ce.ce_module_vars (owner,id) = SOME (ImmutableLoc off)
Proof
  strip_tac >> drule_all_then assume_tac immutable_decl_bare_global_mods >>
  `IS_SOME (FLOOKUP ce.ce_module_vars (owner,id))` by
    fs[unallocated_bare_global_root_def, optionTheory.IS_SOME_EQ_NOT_NONE] >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [expr_sim_inv_mods_def]) >>
  qpat_assum `!src id ty. _ /\ (~cx_const_name_mods _ _ \/ _) ==> _`
    (qspecl_then [`owner`,`id`,`ty`] mp_tac) >> simp[] >>
  fs[const_name_root_mods_def, optionTheory.IS_SOME_EQ_NOT_NONE] >> metis_tac[]
QED

Theorem default_name_occurrence_not[local]:
  supported_exprs_exists ($= e) ds /\ ~supported_exprs_exists p ds ==> ~p e
Proof
  strip_tac >> strip_tac >>
  `supported_exprs_exists p ds` by
    (irule (cj 3 supported_expr_exists_mono) >> qexists_tac `$= e` >> simp[]) >>
  fs[]
QED

(* Only the compiled slice needs a target location. Lookup success in an
   untaken arm is not required: the value/bytes projection takes the reached
   immutable lookup as input. Contract namespaces rule out both slot kinds. *)
Theorem selected_default_read_inputs_mods:
  contract_inv mods exps ctx (ce with ce_module := src) cx /\
  expr_sim_inv_mods mods (ce with ce_module := src) cx env es /\
  body_const_cells_agree_mods mods cx env es /\
  immutable_frame_mods func ce cx es s /\
  get_module_code cx src = SOME tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  raw = DROP (LENGTH dflts - (LENGTH args - nargs)) dflts /\
  ds = DROP (LENGTH dflts - (LENGTH args - nargs))
       (subst_consts_exprs_mods (consts_env_mods mods) dflts) /\
  EVERY (runtime_constant_expr mods) raw /\ EVERY (runtime_constant_expr mods) ds /\
  ~supported_exprs_exists (const_name_root_mods mods) ds /\
  ~supported_exprs_exists (unallocated_bare_global_root ce env) ds ==>
  (!ann owner id. supported_exprs_exists ($= (TopLevelName ann (owner,id))) raw ==>
    (?ts. get_module_code cx owner = SOME ts /\ find_var_decl_by_name id ts = NONE) /\
    (declared_constant mods owner id ==>
     ?r pv v roots.
       ALOOKUP (consts_env_mods mods) (owner,id) = SOME r /\
       const_cells_agree roots es /\
       const_result_at roots cx (expr_type r) (PlaceR (ImmutablePlace owner id [])) v /\
       const_result_at roots cx (expr_type r) pv v /\
       lookup_global cx owner id es = (INL (PlaceR (ImmutablePlace owner id [])),es) /\
       eval_expr cx r es = (INL pv,es))) /\
  (!ann owner id. supported_exprs_exists ($= (TopLevelName ann (owner,id))) ds ==>
    ?ts off.
      declared_immutable mods owner id /\
      get_module_code cx owner = SOME ts /\ find_var_decl_by_name id ts = NONE /\
      ALOOKUP ce.ce_modules owner = SOME ts /\
      FLOOKUP ce.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
      immutables_rel ce cx.txn.target owner ce.ce_is_ctor es s /\
      (!rt v. lookup_immutable cx es owner id = SOME (rt,v) /\
              evaluate_type (get_tenv cx) ann = SOME rt ==>
         off + type_memory_size rt < dimword (:256) /\
         read_result cx (PlaceR (ImmutablePlace owner id [])) es = (INL v,es) /\
         immutable_value_admissible rt v /\
         (~ce.ce_is_ctor ==> off + type_memory_size rt <= LENGTH s.vs_data_section) /\
         val_in_memory rt v off (if ce.ce_is_ctor then s.vs_memory else s.vs_data_section)))
Proof
  strip_tac >>
  `?art. check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art` by
    (qpat_assum `body_const_cells_agree_mods _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [body_const_cells_agree_mods_def]) >>
     goal_assum (drule_at Any)) >>
  drule_then assume_tac check_contract_runtime_namespaces >>
  `ALL_DISTINCT (MAP FST mods)` by fs[contract_namespaces_ok_def] >>
  drule_then assume_tac body_const_cells_agree_mods_sources >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all_then strip_assume_tac (cj 3 default_name_occurrence_declared) >>
      (conj_tac >- metis_tac[default_bare_decl_lookup]) >>
      strip_tac >> irule default_raw_constant_cell >> simp[] >>
      goal_assum (drule_at Any)) >>
  rpt gen_tac >> strip_tac >>
  `~const_name_root_mods mods (TopLevelName ann (owner,id))` by
    (irule default_name_occurrence_not >> qexists_tac `ds` >> simp[]) >>
  `~unallocated_bare_global_root ce env (TopLevelName ann (owner,id))` by
    (irule default_name_occurrence_not >> qexists_tac `ds` >> simp[]) >>
  `declared_immutable mods owner id` by
    (drule_all_then strip_assume_tac (cj 3 default_name_occurrence_declared) >>
     metis_tac[default_declared_const_root]) >>
  `?ts. ALOOKUP mods owner = SOME ts /\ get_module_code cx owner = SOME ts /\
        find_var_decl_by_name id ts = NONE` by
    (irule default_bare_decl_lookup >> simp[]) >>
  `?vis ty slot. MEM (VariableDecl vis Immutable id ty slot) ts` by
    (fs[declared_immutable_def] >> drule_all_then assume_tac ALOOKUP_ALL_DISTINCT_MEM >>
     gvs[] >> metis_tac[]) >>
  `?off. FLOOKUP ce.ce_module_vars (owner,id) = SOME (ImmutableLoc off)` by
    (`~unallocated_bare_global_root (ce with ce_module := src) env
        (TopLevelName ann (owner,id))` by fs[unallocated_bare_global_root_def] >>
     drule_all_then mp_tac default_compiled_immutable >> simp[]) >>
  drule_then assume_tac contract_inv_cenv_modules >>
  `ce.ce_modules = mods` by fs[] >>
  `ALOOKUP ce.ce_modules owner = SOME ts` by simp[] >>
  qexistsl [`ts`,`off`] >> asm_rewrite_tac[] >> conj_tac
  >- (fs[immutable_frame_mods_def, immutables_rel_mods_def] >>
      first_x_assum drule >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `immutable_frame_mods func (ce with ce_module := src) cx es s` by
    (qpat_assum `immutable_frame_mods func ce cx es s` mp_tac >>
     REWRITE_TAC[immutable_frame_mods_def, immutable_alloca_sep_mods_def,
                 immutables_rel_mods_def, immutables_rel_def] >>
     simp[] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `FLOOKUP (ce with ce_module := src).ce_module_vars (owner,id) =
     SOME (ImmutableLoc off)` by simp[] >>
  drule_all_then strip_assume_tac qualified_lookup_place_mods >> fs[]
QED
