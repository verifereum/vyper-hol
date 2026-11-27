Theory bodyIntCallDefaultSlicePreMods
Ancestors
  bodyIntCallDefaultSliceDomainMods bodyIntCallDefaultSliceSupportMods
  bodyIntCallDefaultSliceTypingMods bodyIntCallDefaultSliceAllocationMods
  bodyIntCallDefaultSliceConstRootsMods bodyIntCallDefaultSliceGlobalRootsMods
  bodyExprPreFacts bodyInvMetadataProps bodyInvExecutionProps exprSimSource
  exprBodyPreProps exprSimHypsDefs bodyFullPredsMods supportedExprTraverse supportedProgram
  vyperTypeCallStackSoundness vyperTypeContractContext vyperTypeContractFunction
  vyperTypeEvalProofs vyperTypeInvariants vyperTypeSystem constSubstCorrect
  vyperTypeContract vyperTypeContractStaticMaps constSubstMods supportedExprs
  whitelistCheckerConsts gasShadow alist list finite_map

val bad_builtin_arity = ``\e. case e of
    Builtin _ bt args => ~builtin_args_length_ok bt (LENGTH args)
  | TypeBuiltin _ bt _ args => ~type_builtin_args_length_ok bt (LENGTH args)
  | _ => F``;

val default_call_root = ``\e. expr_internal_call_root e \/
  expr_abi_decode_target_root target e \/ expr_evm_run_root e``;

Theorem runtime_default_excludes_call_roots[local]:
  (!q e. q = ^default_call_root /\ runtime_constant_expr mods e ==>
         ~supported_expr_exists q e) /\
  (!q t. q = ^default_call_root /\ F ==> ~supported_target_exists q t) /\
  (!q es. q = ^default_call_root /\ EVERY (runtime_constant_expr mods) es ==>
          ~supported_exprs_exists q es) /\
  (!q opt. q = ^default_call_root /\ F ==> ~supported_opt_exists q opt) /\
  (!q fs. q = ^default_call_root /\ EVERY (runtime_constant_expr mods) (MAP SND fs) ==>
          ~supported_fields_exists q fs)
Proof
  ho_match_mp_tac supported_expr_exists_ind >>
  rw[runtime_constant_expr_def, supported_expr_exists_def,
     expr_internal_call_root_def, expr_abi_decode_target_root_def, expr_evm_run_root_def] >>
  fs[EVERY_MEM] >>
  TRY (rename1 `constant_type_builtin tb` >> Cases_on `tb` >>
       gvs[constant_type_builtin_def, expr_abi_decode_target_root_def]) >>
  metis_tac[constant_expr_runtime_constant]
QED

Theorem runtime_default_member_calls[local]:
  runtime_constant_expr mods e ==>
  int_calls_expr e = [] /\ ~expr_has_evm_run e /\
  (!target. ~supported_expr_exists (expr_abi_decode_target_root target) e)
Proof
  strip_tac >>
  `!target. ~supported_expr_exists expr_internal_call_root e /\
            ~supported_expr_exists (expr_abi_decode_target_root target) e /\
            ~expr_has_evm_run e` by
    (gen_tac >>
     qspecl_then [`^default_call_root`,`e`] mp_tac
       (cj 1 runtime_default_excludes_call_roots) >>
     simp[supported_expr_exists_disj, expr_has_evm_run_def, SF ETA_ss]) >>
  `int_calls_expr e = []` by
    (irule (cj 1 no_internal_call_int_calls) >> simp[]) >>
  simp[]
QED

Theorem selected_default_members_pre[local]:
  contract_inv mods exps ctx cd p /\ expr_sim_inv_mods mods cd p ed mid /\
  call_evaluation_safe p [] /\ EVERY (runtime_constant_expr mods) ds /\
  well_typed_exprs ed ds /\ (!e. MEM e ds ==> byte_widths_expr e) /\
  alloc_limits_exprs cd ds /\
  ~supported_exprs_exists (const_name_root_mods mods) ds /\
  ~supported_exprs_exists (unallocated_bare_global_root cd ed) ds ==>
  !e. MEM e ds ==> expr_body_pre_mods mods cd p ed e mid
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `runtime_constant_expr mods e` by fs[EVERY_MEM] >>
  drule_then strip_assume_tac runtime_default_member_calls >>
  drule_then assume_tac contract_inv_type_env >>
  drule_all_then assume_tac well_typed_exprs_member >>
  drule_all_then assume_tac alloc_limits_exprs_mem >>
  qpat_x_assum `~supported_exprs_exists (const_name_root_mods _) _` mp_tac >>
  qpat_x_assum `~supported_exprs_exists (unallocated_bare_global_root _ _) _` mp_tac >>
  simp[supported_exprs_exists_every, EXISTS_MEM, expr_body_pre_mods_def] >>
  metis_tac[]
QED

Theorem intcall_default_slice_pre_mods:
  p = cx with stk updated_by CONS (src,name) /\
  ed = env with current_src := src /\ cd = ce with ce_module := src /\
  contract_inv mods exps ctx cd p /\
  expr_sim_inv_mods mods cd p ed mid /\ body_const_cells_agree mods p ed mid /\
  exports_ok p.layouts p.txn.target mods exps /\
  MEM (src,name) (linked_live_functions mods exps) /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr rawfn name args dflts ret ss) tops /\
  (vis = Internal \/ (cx.in_deploy /\ src <> NONE /\ vis = Deploy)) /\
  supported_pure_exprs tops dflts /\
  get_module_code cx src = SOME tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  well_typed_expr env (Call ann (IntCall (src,name)) es dflt) /\
  call_evaluation_safe cx (int_calls_expr (Call ann (IntCall (src,name)) es dflt)) ==>
  let raw = DROP n dflts in
  let ds = DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts) in
  supported_pure_exprs tops raw /\ supported_pure_exprs tops ds /\
  well_typed_exprs (defaults_env ed) raw /\ well_typed_exprs (defaults_env ed) ds /\
  well_typed_exprs ed raw /\ well_typed_exprs ed ds /\
  EVERY (runtime_constant_expr mods) raw /\ EVERY (runtime_constant_expr mods) ds /\
  EVERY (runtime_constant_expr mods) (MAP gas_shadow_expr raw) /\
  EVERY (runtime_constant_expr mods) (MAP gas_shadow_expr ds) /\
  ~supported_exprs_exists ^bad_builtin_arity raw /\
  ~supported_exprs_exists ^bad_builtin_arity ds /\
  ~supported_exprs_exists ^bad_builtin_arity (MAP gas_shadow_expr raw) /\
  ~supported_exprs_exists ^bad_builtin_arity (MAP gas_shadow_expr ds) /\
  ~supported_exprs_exists (const_name_root_mods mods) ds /\
  ~supported_exprs_exists (unallocated_bare_global_root cd ed) ds /\
  (!e. MEM e ds ==> expr_body_pre_mods mods cd p ed e mid)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> simp[LET_THM] >>
  `?art. check_contract p.in_deploy p.layouts p.txn.target mods = SOME art /\
         ALOOKUP p.sources p.txn.target = SOME mods /\ frame_maps ed art` by
    (qpat_assum `body_const_cells_agree _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [body_const_cells_agree_def]) >>
     qexists_tac `art` >> simp[]) >>
  `check_function_body p.layouts p.txn.target mods art src vis mut nr args dflts ret ss` by
    (irule check_contract_function_body_MEM >> conj_tac
     >- (qexists_tac `p.in_deploy` >> fs[check_function_body_in_mode_def]) >>
     qexistsl_tac [`name`, `rawfn`, `tops`] >> simp[] >>
     qpat_assum `well_typed_expr env _`
       (strip_assume_tac o PURE_ONCE_REWRITE_RULE [well_typed_expr_def]) >>
     drule check_contract_artifact_fields >> strip_tac >>
     gvs[frame_maps_def, FLOOKUP_DRESTRICT_SOME]) >>
  drule_all intcall_default_slice_domain_mods >>
  disch_then (qspec_then `n` mp_tac) >> simp[LET_THM] >> strip_tac >>
  `(src = NONE ==> supported_program tops)` by
    (strip_tac >> gvs[] >> drule_all contract_inv_supported_module >> simp[]) >>
  drule_all intcall_default_slice_support_mods >> strip_tac >>
  `env_context_consistent ed p` by
    (drule expr_sim_inv_mods_env >> simp[env_consistent_def]) >>
  `ed.current_src = src` by simp[] >>
  `!src id vt. FLOOKUP ed.toplevel_vtypes (src,id) = SOME vt ==>
      well_formed_vtype ed.type_defs vt` by fs[env_context_consistent_def] >>
  qabbrev_tac `raw = DROP n dflts` >>
  qabbrev_tac `ds = DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts)` >>
  `well_typed_exprs (defaults_env ed) raw /\ well_typed_exprs (defaults_env ed) ds` by
    (conj_tac >> irule default_slice_static_maps >>
     qexistsl_tac [`art`,`p`,`mods`] >> simp[]) >>
  `well_typed_exprs ed raw` by
    (qpat_assum `well_typed_exprs (defaults_env ed) raw`
       (mp_then Any mp_tac intcall_default_slice_typing_mods) >>
     disch_then (qspec_then `mods` mp_tac) >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `well_typed_exprs ed ds /\ (!e. MEM e ds ==> byte_widths_expr e)` by
    (qpat_assum `well_typed_exprs (defaults_env ed) ds`
       (mp_then Any mp_tac intcall_default_slice_typing_mods) >>
     disch_then (qspec_then `mods` mp_tac) >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `alloc_limits_exprs cd ds` by
    (`(vis = Internal \/ vis = Deploy) ==> alloc_limits_exprs cd ds`
       suffices_by fs[] >>
     disch_tac >> qunabbrev_tac `ds` >> qpat_x_assum `cd = _` SUBST_ALL_TAC >>
     drule_all intcall_default_slice_alloc_mods >> simp[]) >>
  `ds = DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts)` by
    simp[Abbr `ds`] >>
  drule_all intcall_default_slice_no_const_roots_mods >> strip_tac >>
  drule_all intcall_default_slice_no_unallocated_mods >> strip_tac >>
  `call_evaluation_safe p []` by
    (drule_all intcall_call_evaluation_safe_needed_defaults >>
     disch_then (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
     irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_exprs (DROP n dflts)` >> simp[]) >>
  qpat_assum `p = _` (SUBST1_TAC o SYM) >>
  qpat_assum `cd = _` (SUBST1_TAC o SYM) >>
  qpat_assum `ed = _` (SUBST1_TAC o SYM) >>
  rpt (conj_tac THEN1 first_assum ACCEPT_TAC) >>
  gen_tac >> strip_tac >>
  drule_all selected_default_members_pre >> disch_then ACCEPT_TAC
QED
