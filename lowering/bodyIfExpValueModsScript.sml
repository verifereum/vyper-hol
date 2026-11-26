(* Forcing the final IfExp representation emits no code and keeps the
   linked VV execution, including its immutable frame and counted exits. *)
Theory bodyIfExpValueMods
Ancestors
  bodyFullPostsMods exprSimIfExp exprSimUnwrap exprSimUnwrapProps
  exprSimMemorySource gasShadowCompile gasShadowState
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  haltExitProj stmtSimProps vyperStorageTrace vyperStorageFootprint
  loweringPosts exprLowering exprLoweringProps exprSimMemDefs bodyPtrDefs
  fragGasOriginPtr exprSimDefs vyperAST vyperInterpreter vyperState
  compileEnv context
Libs monadsyntax

Theorem ifexp_compiled_result[local]:
  compile_expr ce ty (IfExp t c a b) sa = (vv,sb) ==>
  ?rv. vv = (if is_word_type t then StackValue t (Var rv)
             else LocatedValue t (mk_ptr (Var rv) LocMemory))
Proof
  strip_tac >> drule_then strip_assume_tac compile_expr_ifexp >>
  qexists_tac `rv` >> simp[]
QED

Theorem ifexp_lower_value_result[local]:
  lower_value compile_expr ce ty (IfExp t c a b) sa = (op,sb) ==>
  compile_expr ce ty (IfExp t c a b) sa =
    (if is_word_type t then StackValue t op
     else LocatedValue t (mk_ptr op LocMemory),sb)
Proof
  Cases_on `compile_expr ce ty (IfExp t c a b) sa` >>
  drule_then strip_assume_tac ifexp_compiled_result >>
  Cases_on `is_word_type t` >>
  gvs[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def, mk_ptr_def]
QED

Theorem ifexp_read_post_mods[local]:
  vv = (if is_word_type t then StackValue t op
        else LocatedValue t (mk_ptr op LocMemory)) /\
  vv_post_mods H ctx func ce cx (IfExp t c a b) es sa sb s0 ee tv vv u /\
  vv_store_bound cx t t ee tv vv u /\
  ptr_vv_ok cx t tv vv ee G tn u ==>
  ?v. read_result cx tv ee = (INL v,ee) /\
    expr_post_mods H ctx func ce cx (IfExp t c a b) es sa sb s0 ee v op u /\
    expr_store_bound cx t v op u /\ ptr_val_ok cx t v op G tn u
Proof
  strip_tac >>
  `vv_post H ctx func ce cx (IfExp t c a b) es sa sb s0 ee tv vv u /\
   immutable_frame_mods func ce cx ee u` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [vv_post_mods_def]) >>
     `vv_holds ce cx (post_value_type ce (IfExp t c a b)) tv vv ee u` by
       (Cases_on `is_word_type t` >> gvs[vv_holds_mods_def, mk_ptr_def]) >>
     `vv_place_ptr ce cx ee u tv vv` by
       (Cases_on `is_word_type t` >- gvs[vv_place_ptr_def] >>
        Cases_on `tv` >> gvs[vv_place_ptr_mods_def, vv_place_ptr_def, mk_ptr_def] >>
        CASE_TAC >> gvs[vv_place_ptr_def]) >>
     rewrite_tac[vv_post_def] >> asm_rewrite_tac[]) >>
  `?v. read_result cx tv ee = (INL v,ee) /\ ptr_val_ok cx t v op G tn u` by
    (Cases_on `is_word_type t` >>
     gvs[ptr_vv_ok_def, ptr_val_ok_def, mk_ptr_def]) >>
  qexists_tac `v` >> simp[expr_post_mods_def] >>
  drule_all_then assume_tac vv_post_read_result >>
  Cases_on `is_word_type t` >> fs[]
  >- (simp[expr_store_bound_word] >> metis_tac[expr_post_of_vv_post_stack]) >>
  conj_tac
  >- (irule (SIMP_RULE (srw_ss()) [mk_ptr_def]
               (Q.INST [`p` |-> `mk_ptr op LocMemory`] (SPEC_ALL expr_post_of_vv_post_memory))) >>
      qexists_tac `t` >> gvs[mk_ptr_def]) >>
  qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
  simp[vv_store_bound_def, expr_store_bound_def, mk_ptr_def] >> metis_tac[]
QED

Theorem ifexp_shadow_result[local]:
  compile_expr ce ty (IfExp t c a b) sa = (vv,sb) /\
  gas_shadow_state sa shadow_sa /\
  lower_value compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (IfExp t c a b)) shadow_sa = (op,shadow_sb) /\
  vv = (if is_word_type t then StackValue t op
        else LocatedValue t (mk_ptr op LocMemory)) ==>
  compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (IfExp t c a b)) shadow_sa = (vv,shadow_sb)
Proof
  strip_tac >>
  `gas_shadow_compiles (compile_expr ce ty (IfExp t c a b))
     (compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr (IfExp t c a b)))` by
    irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
           Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`sa`,`shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  Cases_on `compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr (IfExp t c a b)) shadow_sa` >>
  simp[] >> strip_tac >>
  Cases_on `is_word_type t` >>
  gvs[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def, mk_ptr_def]
QED

Theorem ifexp_value_from_vv_mods:
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (IfExp t c a b) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (IfExp t c a b) es
Proof
  strip_tac >> rewrite_tac[expr_sim_full_mods_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `vv = if is_word_type t then StackValue t op
                  else LocatedValue t (mk_ptr op LocMemory)` >>
  `compile_expr ce ty (IfExp t c a b) sa = (vv,sb)` by
    (drule ifexp_lower_value_result >> simp[Abbr `vv`]) >>
  `compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr (IfExp t c a b)) shadow_sa =
    (vv,shadow_sb)` by
    (irule ifexp_shadow_result >> conj_tac
     >- (qexists_tac `op` >> simp[Abbr `vv`]) >>
     qexistsl_tac [`sa`,`sb`] >> simp[]) >>
  drule_then assume_tac forced_expr_admissible_raw >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`vv`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      qexistsl_tac [`mid`,`t'`,`v`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result _ v)`]
  >- simp[storage_trace_frame_read_result] >>
  qexists_tac `\H res ee G tn u. childQ H res ee G tn u /\ ee.gas_obs = [] /\ ~u.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      conj_tac >- simp[] >>
      rpt gen_tac >> Cases_on `res` >> simp[Abbr `childR`, expr_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
        INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  suspend "read"
QED

Resume ifexp_value_from_vv_mods[read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qunabbrev_tac `childQ` >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (strip_assume_tac o BETA_RULE)) >>
  disj1_tac >> qexists_tac `tv` >> simp[] >>
  `?v. read_result cx tv ee = (INL v,ee)` by
    (qpat_x_assum `ptr_vv_ok _ _ _ _ _ _ _ _` mp_tac >>
     Cases_on `is_word_type t` >>
     simp[Abbr `vv`, ptr_vv_ok_def, mk_ptr_def] >> metis_tac[]) >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G`,`ee`,`INL v`,`u`,`tn`] >> simp[read_result_gas_obs] >>
  qx_gen_tac `H` >> strip_tac >>
  conj_tac >- simp[cj 1 gas_origin_ptr_path_rules] >>
  gvs[expr_type_def, lowered_value_type_def] >>
  qpat_x_assum `!h. valid_horizon _ _ h ee.storage_trace ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qpat_assum `ee with gas_obs := [] = ee` (fn th => rewrite_tac [th]) >>
  `expr_post_mods H ctx func ce cx (IfExp t c a b) es sa sb s0 ee v op u /\
   expr_store_bound cx t v op u /\ ptr_val_ok cx t v op G tn u` by
    (`vv = (if is_word_type t then StackValue t op
             else LocatedValue t (mk_ptr op LocMemory))` by simp[Abbr `vv`] >>
     drule_all_then (qx_choose_then `w` mp_tac) ifexp_read_post_mods >>
     simp[] >> disch_then (strip_assume_tac o GSYM) >> fs[]) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!t' p. vv = LocatedValue t' p /\ _ ==> ptr_buf_ok _ _ _ _ _`
    (qspecl_then [`t`,`mk_ptr op LocMemory`] mp_tac) >>
  simp[Abbr `vv`, mk_ptr_def]
QED

Finalise ifexp_value_from_vv_mods
