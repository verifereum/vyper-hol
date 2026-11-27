Theory bodySelectedCheckedBodySupportMods
Ancestors
  bodySelectedCalleeEnvMods bodySelectedMaterializedFormalsMods
  bodySelectedBodyAllocBoundsMods bodyImportedCtorArgAllocMods intCallAllocationProps
  bodyCheckedLinkedSupportMods bodySelectedCheckedBodySupportEnvMods
  bodyIntCallDefaultSliceConstRootsMods bodyInvExecutionProps
  bodyLinkedSubstAbiTargetsMods bodyLinkedSubstConstRootsMods
  bodyLinkedConstRhsRangeMods bodySelectedLockedGuardsMods
  linkedStateOwnership linkedEntryImmutableGuards linkedConstAnnotations
  externalBodyWidths bodyExprPreFacts bodyFullPredsMods supportedProgram
  constSubstStmtsPreserve constSubstModsCorrect constSubstMods allocLimitsProps
  vyperTypeContract compileUnit compileVyper finite_map alist list option pair

Theorem checked_selected_body_no_const_roots[local]:
  check_contract mode layouts addr mods = SOME art ==>
  ~supported_stmts_expr_exists (const_name_root_mods mods)
    (subst_consts_stmts_mods (consts_env_mods mods) ss)
Proof
  strip_tac >>
  `!key. cx_const_name_mods mods key ==> IS_SOME (ALOOKUP (consts_env_mods mods) key)` by
    simp[checked_const_key] >>
  `!key rhs. ALOOKUP (consts_env_mods mods) key = SOME rhs ==>
     ~supported_expr_exists (const_name_root_mods mods) rhs` by
    (drule checked_consts_env_mods_closed >>
     metis_tac[cj 1 fixed_const_root_free]) >>
  drule_all_then strip_assume_tac subst_const_roots_eliminated >>
  irule linked_subst_stmts_no_const_roots_mods >> simp[]
QED

Theorem checked_selected_body_abi_targets[local]:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops ==>
  !target. supported_stmts_expr_exists (expr_abi_decode_target_root target)
              (subst_consts_stmts_mods (consts_env_mods mods) ss) ==>
           EXISTS (occurs_abi_decode_target target o SND) mods
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `!key rhs. ALOOKUP (consts_env_mods mods) key = SOME rhs ==>
     ~supported_expr_exists (expr_abi_decode_target_root target) rhs` by
    (rpt strip_tac >> drule_all checked_const_rhs_constant_expr_mods >>
     metis_tac[cj 1 constant_expr_no_abi_decode]) >>
  drule_all_then assume_tac linked_subst_stmts_abi_target_back_mods >>
  simp[EXISTS_MEM, occurs_abi_decode_target_def] >>
  qexists_tac `(src,tops)` >> simp[] >> conj_tac
  >- (drule ALOOKUP_MEM >> simp[]) >>
  qexists_tac `FunctionDecl vis mut nr raw name args dflts ret ss` >>
  simp[declaration_abi_decode_target_def]
QED

Theorem checked_selected_body_guards[local]:
  MEM (src,name) (linked_live_functions mods exps) /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops /\
  body_const_cells_agree_mods mods p env locked /\
  contract_inv mods exps ctx body_ce p /\
  check_contract p.in_deploy p.layouts p.txn.target mods = SOME art /\
  exports_ok p.layouts p.txn.target mods exps ==>
  ~supported_stmts_expr_exists (unallocated_bare_global_root body_ce env)
     (subst_consts_stmts_mods (consts_env_mods mods) ss) /\
  (!key. MEM (WriteAcc (StateRef key))
      (accesses_stmts (subst_consts_stmts_mods (consts_env_mods mods) ss)) /\
    IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
    IS_SOME (FLOOKUP body_ce.ce_module_vars key))
Proof
  strip_tac >>
  drule_all_then assume_tac check_contract_linked_state_ownership >>
  `!art'. check_contract p.in_deploy p.layouts p.txn.target mods = SOME art' /\
      ALOOKUP mods src = SOME tops /\
      MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops /\
      MEM (src,name) (linked_live_functions mods exps) /\
      check_linked_state_ownership p.layouts p.txn.target mods
        (linked_live_functions mods exps) /\
      env.bare_globals = art'.cta_bare_globals /\
      env.bare_global_assignable = art'.cta_bare_global_assignable /\
      (!sid id r. ALOOKUP (consts_env_mods mods) (sid,id) = SOME r ==>
         accesses_expr r = []) /\
      immutable_section_layout_mods mods body_ce ==>
      ~supported_stmts_expr_exists (unallocated_bare_global_root body_ce env)
        (subst_consts_stmts_mods (consts_env_mods mods) ss) /\
      (!key. MEM (WriteAcc (StateRef key))
          (accesses_stmts (subst_consts_stmts_mods (consts_env_mods mods) ss)) /\
        IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
        IS_SOME (FLOOKUP body_ce.ce_module_vars key))` by
    (gen_tac >> strip_tac >>
     `!key r. ALOOKUP (consts_env_mods mods) key = SOME r ==> accesses_expr r = []` by
       (PairCases >> rpt strip_tac >>
        qpat_assum `!sid id r. ALOOKUP _ (sid,id) = SOME r ==> _`
          (drule_then ACCEPT_TAC)) >>
     drule_all linked_checked_body_immutable_guards >> simp[]) >>
  qpat_x_assum `!art'. check_contract _ _ _ _ = SOME art' /\ _ ==> _`
    (assume_tac o SIMP_RULE bool_ss []) >>
  metis_tac[SIMP_RULE bool_ss [LET_THM] selected_locked_immutable_guards_mods]
QED

Theorem selected_package_body_eq[local]:
  set_internal_package_target target
    (package_internal_fn_unit mods T (K global_nonreentrant_slot) deploy ilen
      (src,subst_consts_fn_mods (consts_env_mods mods)
        (mut,nr,raw,name,args,dflts,ret,ss))) =
    (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen',ss_comp,rt) ==>
  ss_comp = subst_consts_stmts_mods (consts_env_mods mods) ss
Proof
  simp[subst_consts_fn_mods_def, package_internal_fn_unit_def,
       set_internal_package_target_def] >> simp[]
QED

Theorem selected_classified_allocs[local]:
  contract_inv mods exps ctx caller cx /\
  (if cx.in_deploy then ?rbc. lower_vyper_deploy_unit_mods mods exps policy rbc = SOME unit
   else lower_vyper_runtime_unit_mods mods exps policy = SOME unit) /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors) /\
  (MEM f ints \/ (cx.in_deploy /\ MEM f imp_ctors)) ==>
  fn_allocs_ok_unit mods f
Proof
  strip_tac
  >- (`MEM f (FST (SND (classify_functions_unit mods exps)))` by simp[] >>
      drule_all contract_inv_internal_allocs >> simp[]) >>
  fs[] >> drule_all selected_imported_ctor_alloc_mods >> simp[]
QED

(* Static assembly at the actual materialized frame; no execution or replay. *)
Theorem selected_checked_body_support_alloc_mods:
  let p = cx with stk updated_by CONS (src,name) in
  let b = subst_consts_stmts_mods (consts_env_mods mods) ss in
  contract_inv mods exps ctx caller cx /\ ALOOKUP mods src = SOME tops /\
  (if cx.in_deploy then ?rbc. lower_vyper_deploy_unit_mods mods exps policy rbc = SOME unit
   else lower_vyper_runtime_unit_mods mods exps policy = SOME unit) /\
  ctx = unit.cu_context /\
  set_internal_package_target policy.rpol_target
    (package_internal_fn_unit mods T (K global_nonreentrant_slot) cx.in_deploy ilen
      (src,subst_consts_fn_mods (consts_env_mods mods)
        (mut,nr,raw,name,args,dflts,ret,ss))) =
    (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen',ss_comp,rt) /\
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,rpc),capture) /\
  materialize_internal_params ce1 caps reserved = (ce2,materialized) /\
  body_ce = ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|> /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor_decl,imp_ctors) /\
  (MEM (src,subst_consts_fn_mods (consts_env_mods mods)
          (mut,nr,raw,name,args,dflts,ret,ss)) ints \/
   (cx.in_deploy /\ MEM (src,subst_consts_fn_mods (consts_env_mods mods)
          (mut,nr,raw,name,args,dflts,ret,ss)) imp_ctors)) /\
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  check_function_body cx.layouts cx.txn.target mods art src vis mut nr args dflts ret ss /\
  MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops /\
  env = function_entry_env art mods src vis args /\
  type_stmts env ret b = SOME env' /\
  body_const_cells_agree_mods mods p env locked /\
  MEM (src,name) (linked_live_functions mods exps) /\
  exports_ok cx.layouts cx.txn.target mods exps ==>
  ?bindings. supported_stmts tops bindings b /\
    (!target. supported_stmts_expr_exists
      (expr_abi_decode_target_root target) b ==>
      EXISTS (occurs_abi_decode_target target o SND) mods) /\
    ce_locals_declared body_ce env /\
    locals_alloc_ok body_ce env /\
    stmts_exprs_ok body_ce b /\
    ~supported_stmts_expr_exists (unallocated_bare_global_root body_ce env) b /\
    (!key. MEM (WriteAcc (StateRef key)) (accesses_stmts b) /\
      IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
      IS_SOME (FLOOKUP body_ce.ce_module_vars key))
Proof
  ntac 2 (CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `env = function_entry_env _ _ _ _ _` (fn th =>
    drule_then strip_assume_tac
      (SIMP_RULE bool_ss [LET_THM, GSYM th] selected_entry_formals_mods)) >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==> MEM (id,ty) args` by
    metis_tac[] >>
  drule_all_then strip_assume_tac selected_materialized_body_env_mods >>
  `ce_locals_declared body_ce env` by
    (pure_rewrite_tac[bodySimTheory.ce_locals_declared_def] >> rpt strip_tac >>
     drule_all selected_materialized_formal_domain_mods >> simp[]) >>
  qpat_x_assum `body_ce = _` kall_tac >>
  drule_all_then assume_tac selected_classified_allocs >>
  drule_then SUBST_ALL_TAC selected_package_body_eq >>
  qabbrev_tac `b = subst_consts_stmts_mods (consts_env_mods mods) ss` >>
  qabbrev_tac `p = cx with stk updated_by CONS (src,name)` >>
  `body_ce.ce_modules = mods` by
    (qpat_assum `contract_inv _ _ _ body_ce _`
       (mp_tac o MATCH_MP bodyInvCodePropsTheory.contract_inv_cenv_modules) >> simp[]) >>
  `qualified_stmts_decls_ok mods b` by
    (simp[Abbr `b`] >> drule_all checked_qualified_body_decl_resolution >> simp[]) >>
  `alloc_limits_stmts body_ce b /\ locals_alloc_ok body_ce env` by
    (qpat_x_assum `fn_allocs_ok_unit _ _` mp_tac >>
     simp[subst_consts_fn_mods_def, GSYM (Abbr `b`)] >> strip_tac >>
     drule_all selected_body_alloc_bounds_mods >> simp[]) >>
  `src = NONE ==> supported_program tops` by
    (strip_tac >> gvs[] >> drule_all contract_inv_supported_module >> simp[]) >>
  `(cx.in_deploy /\ src = NONE /\ vis <> Deploy ==>
    !callee. MEM (NONE,callee) (int_calls_stmts ss) ==>
      IS_SOME (supported_function_decl tops (NONE,callee) Internal))` by
    (strip_tac >> qpat_x_assum `src = NONE` SUBST_ALL_TAC >> rpt strip_tac >>
     drule_all selected_main_deploy_raw_edge_mods >> simp[]) >>
  qabbrev_tac `env_s = env with fn_sigs := DRESTRICT env.fn_sigs (set (int_calls_stmts b))` >>
  `linked_body_env tops src (type_env_all_modules mods) env_s /\
   IS_SOME (type_stmts env_s ret b)` by
    (simp[Abbr `env_s`, Abbr `b`] >>
     drule_all (SIMP_RULE bool_ss [LET_THM] selected_checked_body_support_env_mods) >> simp[]) >>
  `~supported_stmts_expr_exists (\e. ~byte_widths_expr e) b` by
    (`linked_body_env tops src (type_env_all_modules mods)
        (env with fn_sigs := DRESTRICT env.fn_sigs (set (int_calls_stmts b)))` by
       gvs[Abbr `env_s`] >>
     drule_all selected_checked_entry_widths_mods >> simp[]) >>
  `~supported_stmts_expr_exists (const_name_root_mods mods) b` by
    (simp[Abbr `b`] >> drule checked_selected_body_no_const_roots >> simp[]) >>
  `stmts_exprs_ok body_ce b` by
    (irule stmt_exprs_ok_from_traversal_bounds >> simp[]) >>
  `FDOM env_s.var_types = set (MAP FST args)` by
    simp[Abbr `env_s`, whitelistCheckerDeclsTheory.function_entry_env_var_types_fdom] >>
  `supported_stmts tops (args ++ supported_stmts_bindings T b ++
     supported_stmts_bindings F b) b` by
    (`b = subst_consts_stmts_mods (consts_env_mods mods) ss` by simp[Abbr `b`] >>
     drule_all checked_linked_substituted_body_supported_mode >> simp[]) >>
  `check_contract p.in_deploy p.layouts p.txn.target mods = SOME art /\
   exports_ok p.layouts p.txn.target mods exps` by simp[Abbr `p`] >>
  drule_all_then strip_assume_tac checked_selected_body_guards >>
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) b ==>
       EXISTS (occurs_abi_decode_target target o SND) mods` by
    (simp[Abbr `b`] >> rpt strip_tac >>
     drule_all checked_selected_body_abi_targets >> simp[]) >>
  qpat_x_assum `env = function_entry_env _ _ _ _ _` kall_tac >>
  qexists_tac `args ++ supported_stmts_bindings T b ++ supported_stmts_bindings F b` >>
  simp[Abbr `b`]
QED
