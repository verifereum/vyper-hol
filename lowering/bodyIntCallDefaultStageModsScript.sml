Theory bodyIntCallDefaultStageMods
Ancestors
  bodyIntCallDefaultStageFrameMods bodyIntCallDefaultScopeMods bodyIntCallStagePacketMods
  bodyIntCallDefaultPushedInvMods bodyIntCallDefaultSlicePreMods
  bodyIntCallDefaultErasureMods bodyIntCallDefaultCompilePinMods
  bodyIntCallDefaultAccessMods bodyIntCallDefaultSelectedReadsMods
  bodyIntCallDefaultSliceOccurrenceAccessMods gasShadowCompileHelpers
  vyperTypeEvalProofs vyperFiniteStoragePreservation vyperStorageFootprint
  gasOutcomeFullMods exprSimHypsDefs exprLowering compileEnv pair list alist
  bodyIntCallArgMetadataMods bodyFullPreds bodyFullPredsMods bodyInvSplit compileUnit
  loweringShapeProps constSubstMods vyperTypeContract vyperTypeContractStaticMaps
  linkedNsidProps venomFnInstsProofs

val bad_builtin_arity = ``\e. case e of
    Builtin _ bt args => ~builtin_args_length_ok bt (LENGTH args)
  | TypeBuiltin _ bt _ args => ~type_builtin_args_length_ok bt (LENGTH args)
  | _ => F``;

(* All these equalities leave the caller module pin and saved scopes alone. *)
Theorem default_stage_same_pin[local]:
  p = cx with stk updated_by f ==>
  (intcall_stage_ops_mods (lo,func) ce p sa (si,es,s,G,tn) pin rows =
   intcall_stage_ops_mods (lo,func) ce cx sa (si,es,s,G,tn) pin rows) /\
  (intcall_stage_frame_mods (DF,lo,d,ctx,func) ce p st0 (sa,es0,s0,G0,tn0)
     (si,es,s,G,tn) pin =
   intcall_stage_frame_mods (DF,lo,d,ctx,func) ce cx st0 (sa,es0,s0,G0,tn0)
     (si,es,s,G,tn) pin) /\
  (!H. dead_lo_ok_mods H (DF H) lo ce p = dead_lo_ok_mods H (DF H) lo ce cx)
Proof
  strip_tac >> PairCases_on `rows` >>
  rename1 `intcall_stage_ops_mods _ ce p _ (si,esi,s,G,tn) pin (ops,ws,vals,ptys,pflags) = _` >>
  mp_tac (Q.INST [`tag` |-> `""`] intcall_default_stage_frame_mods) >>
  mp_tac (Q.INST [`cx` |-> `p`, `f` |-> `I`, `tag` |-> `""`] intcall_default_stage_frame_mods) >>
  simp[combinTheory.I_THM] >> rpt strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  let val transport = Q.INST [`tag` |-> `""`]
        (INST_TYPE [``:α`` |-> ``:256``] intcall_default_stage_dead_lo_mods)
  in
    mp_tac transport >>
    mp_tac (Q.INST [`cx` |-> `p`, `f` |-> `I`] transport)
  end >>
  simp[combinTheory.I_THM]
QED

Theorem default_stage_compile_cut[local]:
  EVERY (runtime_constant_expr mods) ds /\
  ~supported_exprs_exists ^bad_builtin_arity ds /\
  EVERY (runtime_constant_expr mods) (MAP gas_shadow_expr ds) /\
  ~supported_exprs_exists ^bad_builtin_arity (MAP gas_shadow_expr ds) ==>
  (compile_stage_intcall_args compile_expr (cenv_without_defaults ce tag) ds flags tys si =
   compile_stage_intcall_args compile_expr ce ds flags tys si) /\
  (compile_stage_intcall_args compile_expr ce ds flags tys si =
   compile_stage_intcall_args compile_expr (ce with ce_module := src) ds flags tys si) /\
  (compile_stage_intcall_args compile_expr (gas_shadow_env T (cenv_without_defaults ce tag))
     (MAP gas_shadow_expr ds) flags tys shi =
   compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
     (MAP gas_shadow_expr ds) flags tys shi) /\
  (compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
     (MAP gas_shadow_expr ds) flags tys shi =
   compile_stage_intcall_args compile_expr (gas_shadow_env T (ce with ce_module := src))
     (MAP gas_shadow_expr ds) flags tys shi)
Proof
  strip_tac >> rpt conj_tac
  >- (irule compile_stage_default_erasure_mods >> simp[] >> qexists_tac `mods` >> first_assum ACCEPT_TAC)
  >- (sym_tac >> irule compile_stage_intcall_args_module_pin >>
      simp[] >> qexists_tac `mods` >> first_assum ACCEPT_TAC)
  >- (irule compile_stage_default_erasure_shadow_mods >> simp[] >> qexists_tac `mods` >> first_assum ACCEPT_TAC) >>
  `gas_shadow_env T (ce with ce_module := src) = (gas_shadow_env T ce) with ce_module := src` by
    simp[gasShadowCompileBaseTheory.gas_shadow_env_def, compile_env_component_equality] >>
  asm_rewrite_tac[] >> sym_tac >> irule compile_stage_intcall_args_module_pin >>
  simp[] >> qexists_tac `mods` >> first_assum ACCEPT_TAC
QED

(* The selected-use result is keyed by actual syntax occurrences, rather
   than by all entries in a module's compiled layout. *)
val default_selected_immutable = ``
  !ann owner id. supported_exprs_exists ($= (TopLevelName ann (owner,id))) ds ==>
    ?ts off.
      declared_immutable mods owner id /\
      get_module_code p owner = SOME ts /\ find_var_decl_by_name id ts = NONE /\
      ALOOKUP ce.ce_modules owner = SOME ts /\
      FLOOKUP ce.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
      immutables_rel ce p.txn.target owner ce.ce_is_ctor mid s /\
      (!rt v. lookup_immutable p mid owner id = SOME (rt,v) /\
              evaluate_type (get_tenv p) ann = SOME rt ==>
         off + type_memory_size rt < dimword (:256) /\
         read_result p (PlaceR (ImmutablePlace owner id [])) mid = (INL v,mid) /\
         immutable_value_admissible rt v /\
         (~ce.ce_is_ctor ==> off + type_memory_size rt <= LENGTH s.vs_data_section) /\
         val_in_memory rt v off (if ce.ce_is_ctor then s.vs_memory else s.vs_data_section))``;

val default_access_at_cut = ``
  (!owner id replacement.
    supported_exprs_exists (\e. ?ty. e = TopLevelName ty (owner,id)) raw /\
    ALOOKUP (consts_env_mods mods) (owner,id) = SOME replacement ==>
    lookup_global p owner id mid = (INL (PlaceR (ImmutablePlace owner id [])),mid)) /\
  (!owner id off imms tv v.
    supported_exprs_exists (\e. ?ty. e = TopLevelName ty (owner,id)) ds /\
    FLOOKUP ce.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
    ALOOKUP mid.immutables p.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables owner imms) id = SOME (tv,v) ==>
    immutable_value_admissible tv v /\
    (~ce.ce_is_ctor ==> off + type_memory_size tv <= LENGTH s.vs_data_section) /\
    val_in_memory tv v off (if ce.ce_is_ctor then s.vs_memory else s.vs_data_section) /\
    immutable_value_bytes_rel tv v
      (mem_bytes_at off (type_memory_size tv)
        (if ce.ce_is_ctor then s.vs_memory else s.vs_data_section))) /\
  (!owner id tr slot tv mid'.
    supported_exprs_exists (\e. ?ty. e = TopLevelName ty (owner,id)) ds /\
    lookup_global p owner id mid = (INL (PlaceR (StoragePlace tr slot tv)),mid') ==>
    FLOOKUP ce.ce_module_vars (owner,id) =
      SOME (if tr then TransientLoc slot else StorageLoc slot))``;

Theorem default_stage_reads[local]:
  contract_inv mods exps ctx (ce with ce_module := src) p /\
  expr_sim_inv_mods mods (ce with ce_module := src) p ed mid /\
  body_const_cells_agree mods p ed mid /\
  get_module_code p src = SOME tops /\
  lookup_callable_function p.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  raw = DROP (LENGTH dflts - (LENGTH args - nargs)) dflts /\
  ds = DROP (LENGTH dflts - (LENGTH args - nargs))
    (subst_consts_exprs_mods (consts_env_mods mods) dflts) /\
  EVERY (runtime_constant_expr mods) raw /\ EVERY (runtime_constant_expr mods) ds /\
  ~supported_exprs_exists (const_name_root_mods mods) ds /\
  ~supported_exprs_exists (unallocated_bare_global_root (ce with ce_module := src) ed) ds /\
  immutable_frame_mods func ce p mid s /\ stmt_state_rel H ctx func ce p mid s ==>
  (^default_selected_immutable) /\ (^default_access_at_cut)
Proof
  strip_tac >>
  `unallocated_bare_global_root (ce with ce_module := src) ed =
   unallocated_bare_global_root ce ed` by
    (simp[FUN_EQ_THM] >> Cases >> simp[unallocated_bare_global_root_def]) >>
  `~supported_exprs_exists (unallocated_bare_global_root ce ed) ds` by fs[] >>
  drule_all_then strip_assume_tac selected_default_read_inputs_mods >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule (SIMP_RULE (srw_ss()) [cenv_without_defaults_def] default_slice_access_frame_mods) >>
  rpt conj_tac
  >- (rpt strip_tac >> drule_then strip_assume_tac default_slice_occurrence_witness >>
      gvs[] >> first_x_assum drule >> strip_tac >> goal_assum drule)
  >- (qexists_tac `ed` >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`H`,`ctx`,`func`] >> simp[]
QED

Theorem default_source_row[local]:
  !mods src mut nr rr name args dflts ret ss.
    MEM (src,mut,nr,rr,name,args,dflts,ret,ss) (unit_internal_fns mods) <=>
    ?tops. MEM (src,tops) mods /\ MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops
Proof
  Induct >- simp[unit_internal_fns_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >>
  simp[unit_internal_fns_def] >> pairarg_tac >> gvs[] >>
  simp[MEM_MAP, EXISTS_PROD] >>
  qspec_then `h1` mp_tac classify_fold_internal >> simp[] >> metis_tac[]
QED

Theorem default_selected_row_unique[local]:
  contract_namespaces_ok F mods /\ ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
  MEM (owner,decls) mods /\ MEM (FunctionDecl Internal m n raw f a ds r b) decls /\
  nsid_to_string (owner,f) = nsid_to_string (src,name) ==>
  FunctionDecl Internal m n raw f a ds r b = FunctionDecl vis mut nr rr name args dflts ret ss
Proof
  strip_tac >>
  `MEM (src,tops) mods` by (drule ALOOKUP_MEM >> simp[]) >>
  `!s ts v m n raw f a ds r b. MEM (s,ts) mods /\
    MEM (FunctionDecl v m n raw f a ds r b) ts ==> ~MEM #"." f` by
    (qpat_assum `contract_namespaces_ok _ _` (strip_assume_tac o REWRITE_RULE [contract_namespaces_ok_def]) >>
     rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `EVERY (\(_,tls). EVERY _ tls) mods`
       (mp_tac o REWRITE_RULE [EVERY_MEM, FORALL_PROD]) >>
     disch_then (qspec_then `(s,ts)` mp_tac) >>
     simp[] >> disch_then drule >> simp[]) >>
  `(owner,f) = (src,name)` by (irule nsid_to_string_dot_free_injective >> simp[] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP FST mods)` by fs[contract_namespaces_ok_def] >>
  `owner = src /\ f = name` by fs[] >>
  qpat_x_assum `owner = src` SUBST_ALL_TAC >> qpat_x_assum `f = name` SUBST_ALL_TAC >>
  `ALOOKUP mods src = SOME decls` by (irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]) >>
  `decls = tops` by fs[] >> qpat_x_assum `decls = tops` SUBST_ALL_TAC >>
  `ALL_DISTINCT (FLAT (MAP (self_member_keys_toplevel src) tops))` by
    (irule vyperTypeContractTheory.contract_keys_module_distinct >> qexists_tac `mods` >>
     fs[contract_namespaces_ok_def]) >>
  qpat_assum `ALL_DISTINCT (FLAT (MAP _ tops))`
    (mp_then Any mp_tac all_distinct_flat_map_unique) >>
  disch_then (qspecl_then [`FunctionDecl Internal m n raw name a ds r b`,
    `FunctionDecl vis mut nr rr name args dflts ret ss`,`(src,name)`] mp_tac) >>
  simp[self_member_keys_toplevel_def]
QED

Theorem default_selected_table[local]:
  contract_namespaces_ok F mods /\ ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops ==>
  ALOOKUP (build_func_defaults_mods mods) (nsid_to_string (src,name)) =
    if vis = Internal then SOME (subst_consts_exprs_mods (consts_env_mods mods) dflts) else NONE
Proof
  strip_tac >> qabbrev_tac `key = nsid_to_string (src,name)` >>
  `!ds. MEM (key,ds) (build_func_defaults_mods mods) ==>
    vis = Internal /\ ds = subst_consts_exprs_mods (consts_env_mods mods) dflts` by
    (simp[build_func_defaults_mods_def,MEM_MAP,EXISTS_PROD,fn_decl_name_def,
          subst_consts_fn_mods_def,default_source_row] >>
     rpt gen_tac >> strip_tac >> qunabbrev_tac `key` >>
     qpat_x_assum `nsid_to_string (src,name) = _` (assume_tac o SYM) >>
     drule_all_then mp_tac default_selected_row_unique >> simp[]) >>
  Cases_on `ALOOKUP (build_func_defaults_mods mods) key`
  >- (spose_not_then assume_tac >> fs[] >>
      `MEM (key,subst_consts_exprs_mods (consts_env_mods mods) dflts)
        (build_func_defaults_mods mods)` by
        (simp[build_func_defaults_mods_def,MEM_MAP] >>
         qexists_tac `(src,mut,nr,rr,name,args,dflts,ret,ss)` >>
         simp[Abbr `key`,fn_decl_name_def,subst_consts_fn_mods_def,default_source_row] >>
         qexists_tac `tops` >> simp[] >> drule ALOOKUP_MEM >> simp[]) >>
      fs[ALOOKUP_NONE,MEM_MAP] >> metis_tac[FST]) >>
  drule ALOOKUP_MEM >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem default_selected_omitted[local]:
  contract_inv mods exps ctx ce cx /\ body_const_cells_agree mods cx env mid /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
  (vis = Internal \/ (cx.in_deploy /\ src <> NONE /\ vis = Deploy)) /\
  call_evaluation_safe cx (int_calls_expr (Call ann (IntCall (src,name)) es dflt)) ==>
  omitted_defaults ce (nsid_to_string (src,name)) (LENGTH es) =
  DROP (LENGTH dflts - (LENGTH args - LENGTH es))
    (subst_consts_exprs_mods (consts_env_mods mods) dflts)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?art. check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art` by
    (qpat_assum `body_const_cells_agree _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [body_const_cells_agree_def]) >>
     goal_assum (drule_at Any)) >>
  drule_then assume_tac check_contract_runtime_namespaces >>
  drule_all_then assume_tac default_selected_table >>
  drule_all_then (strip_assume_tac o SIMP_RULE std_ss [LET_THM]) selected_arg_metadata_mods >>
  drule_then assume_tac intcall_call_evaluation_safe_target_not_mem >>
  `ALOOKUP ce.ce_func_defaults (nsid_to_string (src,name)) =
    ALOOKUP (build_func_defaults_mods mods) (nsid_to_string (src,name))` by
    (fs[contract_inv_def] >> first_x_assum irule >> simp[]) >>
  Cases_on `vis = Internal`
  >- (`!xs. LENGTH (subst_consts_exprs_mods (consts_env_mods mods) xs) = LENGTH xs` by
       (Induct >> simp[subst_consts_expr_mods_def]) >>
      simp[omitted_defaults_def]) >>
  `vis = Deploy` by fs[] >> gvs[] >>
  drule_all check_contract_toplevel_decl_MEM_checked >>
  Cases_on `dflts` >> simp[omitted_defaults_def,check_toplevel_decl_def,function_header_ok_def,
                         subst_consts_expr_mods_def]
QED

Theorem selected_default_stage_enter_mods:
  let key = nsid_to_string (src,name) in
  let n = LENGTH dflts - (LENGTH args - LENGTH es) in
  let p = cx with stk updated_by CONS (src,name) in
  let ed = env with current_src := src in
  let cd = ce with ce_module := src in
  let raw = DROP n dflts in
  let ds = DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts) in
  contract_inv mods exps ctx ce cx /\
  expr_sim_inv_mods mods ce cx env mid /\ body_const_cells_agree mods cx env mid /\
  (mods = [(NONE,tops)] \/ MEM (src,name) (linked_live_functions mods exps)) /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr rawfn name args dflts ret ss) tops /\
  (vis = Internal \/ (cx.in_deploy /\ src <> NONE /\ vis = Deploy)) /\
  supported_pure_exprs tops dflts /\
  get_module_code cx src = SOME tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  well_typed_expr env (Call ann (IntCall (src,name)) es dflt) /\
  call_evaluation_safe cx (int_calls_expr (Call ann (IntCall (src,name)) es dflt)) /\
  (!H. dead_lo_ok_mods H (DF H) lo ce cx) /\
  intcall_stage_ops_mods (lo,func) ce cx sa (si,mid,s,G,tn) pin rows /\
  intcall_stage_frame_mods (DF,lo,d,ctx,func) ce cx st0 (sa,es0,s0,G0,tn0)
    (si,mid,s,G,tn) pin /\
  compile_stage_intcall_args compile_expr (cenv_without_defaults ce key)
    (omitted_defaults ce key (LENGTH es)) flags tys si = (def_ops,sf) /\
  compile_stage_intcall_args compile_expr (gas_shadow_env T (cenv_without_defaults ce key))
    (MAP gas_shadow_expr (omitted_defaults ce key (LENGTH es))) flags tys shi = (def_ops,shf) ==>
  omitted_defaults ce key (LENGTH es) = ds /\
  contract_inv mods exps ctx cd p /\ module_body_inv mods src tops cd p /\
  expr_sim_inv_mods mods cd p ed mid /\ body_const_cells_agree mods p ed mid /\
  (!e. MEM e ds ==> expr_body_pre_mods mods cd p ed e mid) /\
  EVERY (runtime_constant_expr mods) ds /\ ~supported_exprs_exists ^bad_builtin_arity ds /\
  compile_stage_intcall_args compile_expr ce ds flags tys si = (def_ops,sf) /\
  compile_stage_intcall_args compile_expr cd ds flags tys si = (def_ops,sf) /\
  compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
    (MAP gas_shadow_expr ds) flags tys shi = (def_ops,shf) /\
  compile_stage_intcall_args compile_expr (gas_shadow_env T cd)
    (MAP gas_shadow_expr ds) flags tys shi = (def_ops,shf) /\
  (!H. dead_lo_ok_mods H (DF H) lo ce p) /\
  intcall_stage_ops_mods (lo,func) ce p sa (si,mid,s,G,tn) pin rows /\
  intcall_stage_frame_mods (DF,lo,d,ctx,func) ce p st0 (sa,es0,s0,G0,tn0)
    (si,mid,s,G,tn) pin /\
  (!H. valid_horizon p st0 H mid.storage_trace ==>
     (^default_selected_immutable) /\ (^default_access_at_cut)) /\
  supported_pure_exprs tops raw /\ supported_pure_exprs tops ds /\
  well_typed_exprs (defaults_env ed) raw /\ well_typed_exprs (defaults_env ed) ds
Proof
  SIMP_TAC std_ss [LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> SIMP_TAC bool_ss [NoAsms,th]) default_selected_omitted >>
  drule_all_then (qspec_then `name` strip_assume_tac)
    (SIMP_RULE std_ss [LET_THM] intcall_default_pushed_inv_retained_mods) >>
  qabbrev_tac `p = cx with stk updated_by CONS (src,name)` >>
  qabbrev_tac `ed = env with current_src := src` >>
  qabbrev_tac `cd = ce with ce_module := src` >>
  `p = cx with stk updated_by CONS (src,name)` by simp[Abbr `p`] >>
  `cd = ce with ce_module := src` by simp[Abbr `cd`] >>
  `ed = env with current_src := src` by simp[Abbr `ed`] >>
  drule_all intcall_default_slice_pre_mods >>
  disch_then (qspec_then `LENGTH dflts - (LENGTH args - LENGTH es)` mp_tac) >>
  SIMP_TAC std_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `n = LENGTH dflts - (LENGTH args - LENGTH es)` >>
  qabbrev_tac `raw = DROP n dflts` >>
  qabbrev_tac `ds = DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts)` >>
  mp_tac (Q.INST [`tag` |-> `nsid_to_string (src,name)`] default_stage_compile_cut) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `cd = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  strip_tac >>
  mp_tac (Q.INST [`es` |-> `mid`, `f` |-> `CONS (src,name)`] default_stage_same_pin) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `intcall_stage_frame_mods (DF,lo,d,ctx,func) ce p st0 (sa,es0,s0,G0,tn0)
    (si,mid,s,G,tn) pin` by
    (qpat_assum `intcall_stage_frame_mods _ ce p _ _ _ _ = _`
       (fn th => REWRITE_TAC [th]) >> first_assum ACCEPT_TAC) >>
  `compile_stage_intcall_args compile_expr ce ds flags tys si = (def_ops,sf)` by
    (qpat_assum `compile_stage_intcall_args _ (cenv_without_defaults ce _) _ _ _ _ =
                 compile_stage_intcall_args _ ce _ _ _ _`
       (fn th => PURE_REWRITE_TAC [GSYM th]) >> first_assum ACCEPT_TAC) >>
  `compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
     (MAP gas_shadow_expr ds) flags tys shi = (def_ops,shf)` by
    (qpat_assum `compile_stage_intcall_args _ (gas_shadow_env T (cenv_without_defaults ce _)) _ _ _ _ =
                 compile_stage_intcall_args _ (gas_shadow_env T ce) _ _ _ _`
       (fn th => PURE_REWRITE_TAC [GSYM th]) >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac THEN1 first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `compile_stage_intcall_args _ ce _ _ _ _ = compile_stage_intcall_args _ cd _ _ _ _`
        (fn th => PURE_REWRITE_TAC [GSYM th]) >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_assum `compile_stage_intcall_args _ (gas_shadow_env T ce) _ _ _ _ =
                  compile_stage_intcall_args _ (gas_shadow_env T cd) _ _ _ _`
        (fn th => PURE_REWRITE_TAC [GSYM th]) >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (gen_tac >> qpat_assum `!H. dead_lo_ok_mods H _ _ ce p = _`
        (qspec_then `H` (fn th => REWRITE_TAC [th])) >> first_assum MATCH_ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `intcall_stage_ops_mods _ ce p _ _ _ _ = _`
        (fn th => REWRITE_TAC [th]) >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `get_module_code p src = SOME tops` by simp[Abbr `p`,get_module_code_stk_irrelevant] >>
  `lookup_callable_function p.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss)` by simp[Abbr `p`] >>
  `raw = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts` by simp[Abbr `raw`,Abbr `n`] >>
  `ds = DROP (LENGTH dflts - (LENGTH args - LENGTH es))
    (subst_consts_exprs_mods (consts_env_mods mods) dflts)` by simp[Abbr `ds`,Abbr `n`] >>
  gen_tac >> strip_tac >>
  `stmt_state_rel H ctx func ce p mid s /\ immutable_frame_mods func ce p mid s` by
    (qpat_assum `intcall_stage_frame_mods _ ce p _ _ _ pin`
       (strip_assume_tac o REWRITE_RULE [intcall_stage_frame_mods_def]) >>
     first_x_assum drule >> strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `cd = _` (fn th =>
    mp_tac (PURE_REWRITE_RULE [GSYM th]
      (Q.INST [`nargs` |-> `LENGTH (es:expr list)`]
        (INST_TYPE [``:α`` |-> ``:256``] default_stage_reads)))) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

(* The run of ds uses saved scopes throughout its physical packet. Restore
   the interpreter's scope bracket pointwise on the very same observation
   suffix; the raw-to-substituted replay is a separate producer. *)
Theorem selected_default_stage_restore_mods:
  let p = cx with stk updated_by CONS (src,name) in
  supported_pure_exprs tops ds /\ well_typed_exprs (defaults_env ed) ds /\
  (!tail. eval_exprs p ds (mid with gas_obs := obs ++ tail) =
      (INL dvs,fin with gas_obs := tail)) /\
  intcall_stage_ops_mods (lo,func) ce p sa (sf,fin,t,G,tn) pin rows /\
  intcall_stage_frame_mods (DF,lo,d,ctx,func) ce p st0 (sa,es0,s0,G0,tn0)
    (sf,fin,t,G,tn) pin ==>
  fin.scopes = mid.scopes /\
  (!tail. finally (ignore_bind (set_scopes [FEMPTY]) (eval_exprs p ds))
     (set_scopes mid.scopes) (mid with gas_obs := obs ++ tail) =
       (INL dvs,fin with gas_obs := tail)) /\
  intcall_stage_ops_mods (lo,func) ce cx sa (sf,fin,t,G,tn) pin rows /\
  intcall_stage_frame_mods (DF,lo,d,ctx,func) ce cx st0 (sa,es0,s0,G0,tn0)
    (sf,fin,t,G,tn) pin /\
  (!source Q R. gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods
     p st0 source (fin,t,G,tn) Q R =
   gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods
     cx st0 source (fin,t,G,tn) Q R)
Proof
  SIMP_TAC std_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `p = cx with stk updated_by CONS (src,name)` >>
  `p = cx with stk updated_by CONS (src,name)` by simp[Abbr `p`] >>
  mp_tac (Q.INST [`es` |-> `fin`, `si` |-> `sf`, `s` |-> `t`,
                   `f` |-> `CONS (src,name)`] default_stage_same_pin) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `eval_exprs p ds (mid with gas_obs := obs) = (INL dvs,fin with gas_obs := [])` by
    (qpat_assum `!tail. eval_exprs _ _ (_ with gas_obs := _ ++ tail) = _`
       (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL]))) >>
  `fin.scopes = mid.scopes` by
    (qabbrev_tac `z = mid with gas_obs := obs` >>
     `z.scopes = mid.scopes` by simp[Abbr `z`] >>
     drule_all_then (qspecl_then [`p`,`z`,`z.scopes`] mp_tac)
       intcall_default_slice_scope_mods >>
     qpat_assum `eval_exprs p ds z = _` (fn th =>
       SIMP_TAC (srw_ss()) [NoAsms, th]) >>
     disch_then (mp_tac o AP_TERM ``\z:evaluation_state. z.scopes``) >> simp[]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (qx_gen_tac `tail` >>
      drule_all_then (qspecl_then [`p`,`mid with gas_obs := obs ++ tail`] assume_tac)
        intcall_default_slice_bracket_mods >>
      qpat_x_assum `finally _ _ _ = _` (PURE_REWRITE_TAC o single o SIMP_RULE (srw_ss()) []) >>
      qpat_assum `!g. eval_exprs p ds (_ with gas_obs := _ ++ g) = _`
        (qspec_then `tail` ACCEPT_TAC))
  >- (qpat_assum `intcall_stage_ops_mods _ ce p _ _ _ _` mp_tac >>
      qpat_assum `intcall_stage_ops_mods _ ce p _ _ _ _ = _` (fn th => REWRITE_TAC [th]))
  >- (qpat_assum `intcall_stage_frame_mods _ ce p _ _ _ _` mp_tac >>
      qpat_assum `intcall_stage_frame_mods _ ce p _ _ _ _ = _` (fn th => REWRITE_TAC [th])) >>
  rpt gen_tac >> qpat_assum `p = _` SUBST1_TAC >>
  irule intcall_default_stage_outcome_mods
QED
