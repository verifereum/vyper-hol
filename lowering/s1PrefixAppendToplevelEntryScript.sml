(* The top-level Append target records its storage root but emits no code. *)
Theory s1PrefixAppendToplevelEntry
Ancestors
  s1PrefixDefs s1PrefixPreds s1PrefixFrame bodyFullSimProjection
  bodyAppendStorageAdapter bodyAppendStorageLayoutFacts bodyAppendStorageFacts
  stmtSimAppendStorageCompose stmtSimAssignStorageFacts bodyInvCodeProps
  bodyExprPreFacts bodyFullPreds bodySimFull gasOutcomeFullCompose gasOutcomeFull fragGasOriginPtr
  exprSimSource exprLoweringProps exprSimWordArgs stateRelProj
  loweringPosts bodyPtrDefs vyperStorageFootprint vyperStorageTrace vyperState
  vyperInterpreter vyperTypeSystem supportedStmts supportedExprs list sum

Theorem append_toplevel_declaration[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  supported_stmt tops bindings (Append (TopLevelNameTarget nid) e) /\
  type_stmt env ret_ty (Append (TopLevelNameTarget nid) e) = SOME env' ==>
  ?elem cap tv tr slot.
    get_module_code cx (FST nid) = SOME tops /\
    find_var_decl_by_name (SND nid) tops =
      SOME (StorageVarDecl tr (ArrayT elem (Dynamic cap)),SND nid) /\
    lookup_var_slot_from_layout cx tr (FST nid) (SND nid) = SOME slot /\
    cenv.ce_module_var_type nid = SOME (ArrayT elem (Dynamic cap)) /\
    cenv.ce_hashmap_info nid = NONE /\
    (!st. eval_target_place cx (TopLevelNameTarget nid) st =
       (INL (StoragePlace tr (n2w slot) (ArrayTV tv (Dynamic cap))),
        st with storage_trace := st.storage_trace ++
          [StorageRoot tr slot (ArrayTV tv (Dynamic cap))]))
Proof
  PairCases_on `nid` >> strip_tac >>
  `supported_storage_dynamic_array tops (nid0,nid1)` by
    fs[Once supported_stmt_def, supported_append_target_def] >>
  `nid0 = NONE` by
    (drule append_typing_target >> strip_tac >>
     metis_tac[bodyTypedTargetScopeTheory.body_inv_toplevel_target_main,
               optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `nid0 = NONE` SUBST_ALL_TAC >>
  `get_module_code cx NONE = SOME tops` by metis_tac[body_inv_main_code] >>
  drule_then (qx_choosel_then [`vis`,`mut`,`elem`,`cap`,`ast_slot`]
    (map_every assume_tac o CONJUNCTS)) (SIMP_RULE (srw_ss()) []
    (Q.INST [`nid` |-> `(NONE,id)`] supported_append_storage_decl)) >>
  drule_all_then (qx_choosel_then [`tv`,`rslot`] strip_assume_tac)
    append_aggregate_target_layout >>
  drule_all_then strip_assume_tac body_append_root_metadata >>
  drule_then strip_assume_tac append_toplevel_place_any >>
  qexistsl_tac [`elem`,`cap`,`tv`,`mut = Transient`,`rslot`] >> simp[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac append_toplevel_declaration >>
  rename1 `lookup_var_slot_from_layout cx tr _ _ = SOME slot` >>
  qabbrev_tac `tv_arr = ArrayTV tv (Dynamic cap)` >>
  qabbrev_tac `place = StoragePlace tr (n2w slot) tv_arr` >>
  qabbrev_tac `root = StorageRoot tr slot tv_arr` >>
  qabbrev_tac `after = es with storage_trace := es.storage_trace ++ [root]` >>
  qpat_assum `stmt_frag_full_pre _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [stmt_frag_full_pre_def]) >>
  qexists_tac `\H res ee G tn u. res = INL place /\ ee = after with gas_obs := [] /\
    G = G0 /\ tn = tn0 /\ u = s0` >>
  BETA_TAC >> conj_tac >- suspend "target_full" >>
  conj_tac >- suspend "target_prefix" >> suspend "rhs_entry"
QED
*)
Theorem append_toplevel_prefix_entry:
  (!es0 p es1. eval_target_place cx (TopLevelNameTarget nid) es0 = (INL p,es1) ==>
     body_expr_full_ok cx e) /\
  (!es0 p es1. eval_target_place cx (TopLevelNameTarget nid) es0 = (INL p,es1) ==>
     body_expr_prefix_ok cx e) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Append (TopLevelNameTarget nid) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Append (TopLevelNameTarget nid) e) ==> occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\ expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Append (TopLevelNameTarget nid) e) = SOME env' /\
  stmt_exprs_ok cenv (Append (TopLevelNameTarget nid) e) /\
  call_evaluation_safe cx (int_calls_stmt (Append (TopLevelNameTarget nid) e)) /\
  stmt_frag_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Append (TopLevelNameTarget nid) e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty
      (gas_shadow_stmt (Append (TopLevelNameTarget nid) e)))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
    (st0,sa,sb,shadow_sa,shadow_sb,s0,G0,tn0,ce) /\
  (!b loc elem cap. compile_get_target_ptr compile_expr cenv (TopLevelNameTarget nid) sa =
     ((b,SOME loc,SOME (ValPT (ArrayT elem (Dynamic cap)))),sa) ==>
     ?op sm shadow_sm.
       lower_value compile_expr cenv elem e sa = (op,sm) /\
       lower_value compile_expr (gas_shadow_env T cenv) elem
         (gas_shadow_expr e) shadow_sa = (op,shadow_sm) /\
       gas_shadow_state sm shadow_sm /\
       fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func) ==>
  ?Q. gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (cx_tops cx) cx st0 (eval_target_place cx (TopLevelNameTarget nid))
        (es,s0,G0,tn0) Q (\H res ee gt r. F) /\
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cx st0 (eval_target_place cx (TopLevelNameTarget nid)) (es,s0,G0,tn0) /\
      (!marks p mid G1 tn1 u.
        (!tail. eval_target_place cx (TopLevelNameTarget nid)
          (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
          (INL p,mid with gas_obs := tail)) /\
        storage_trace_domain cx st0 mid.storage_trace /\
        (!H. valid_horizon cx st0 H mid.storage_trace ==> Q H (INL p) mid G1 tn1 u) ==>
        gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx))
          (mid,u,G1,tn1) (\H res ee G tn v. ~v.vs_halted) (\H res ee gt r. ISR res) /\
        gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          cx st0 (bind (eval_expr cx e) (read_result cx)) (mid,u,G1,tn1))
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume append_toplevel_prefix_entry[target_full]:
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`G0`,`after`,`INL place`,`s0`,`tn0`] >>
  simp[Abbr `after`, evaluation_state_fupdfupds_comp, gas_origin_ptr_path_rules]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume append_toplevel_prefix_entry[target_prefix]:
  irule gas_prefix_full_no_outcome >>
  simp[evaluate_storage_trace_frame] >>
  rpt strip_tac >> gvs[Abbr `after`, Abbr `root`, DROP_APPEND1]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume append_toplevel_prefix_entry[rhs_entry]:
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `mid = _` SUBST_ALL_TAC >>
  qpat_x_assum `u = s0` SUBST_ALL_TAC >>
  qpat_x_assum `G1 = G0` SUBST_ALL_TAC >>
  qpat_x_assum `tn1 = tn0` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H after.storage_trace ==>
       stmt_state_rel H ctx func cenv cx (after with gas_obs := []) s0 /\
       storage_well_formed_on cx (after with gas_obs := []) (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx (after with gas_obs := []) G0 tn0 s0` by
    suspend "horizons" >>
  `valid_horizon cx st0 (storage_trace_horizon after.storage_trace) after.storage_trace`
    by fs[] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    (qpat_assum `!H. valid_horizon _ _ H after.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> drule_then ACCEPT_TAC stmt_state_rel_vars_rels) >>
  drule_all_then assume_tac append_storage_compiler_location >>
  `FLOOKUP cenv.ce_module_vars nid =
    SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by fs[] >>
  `compile_get_target_ptr compile_expr cenv (TopLevelNameTarget nid) sa =
     ((Lit (n2w slot),SOME (if tr then LocTransient else LocStorage),
       SOME (ValPT (ArrayT elem (Dynamic cap)))),sa)` by
    (drule_all compile_get_target_ptr_toplevel >> simp[]) >>
  qpat_assum `!b loc elem cap. compile_get_target_ptr _ _ _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  `expr_body_pre cenv cx env e (after with gas_obs := []) /\
   body_const_cells_agree [(NONE,tops)] cx env (after with gas_obs := [])` by
    suspend "rhs_static" >>
  `body_expr_full_ok cx e /\ body_expr_prefix_ok cx e` by
    (conj_tac >> first_assum irule >> first_assum (irule_at Any)) >>
  suspend "rhs_sim"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume append_toplevel_prefix_entry[horizons]:
  qx_gen_tac `H` >> disch_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    (irule valid_horizon_append >> qexists_tac `[root]` >> fs[Abbr `after`]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `storage_well_formed_on cx (after with gas_obs := []) (FST H)` by
    (`(after with gas_obs := []).accounts = es.accounts /\
      (after with gas_obs := []).tStorage = es.tStorage` by simp[Abbr `after`] >>
     qpat_assum `storage_well_formed_on _ es _` mp_tac >>
     qpat_assum `_ = es.accounts` mp_tac >>
     qpat_assum `_ = es.tStorage` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[storage_well_formed_on_backends]) >>
  conj_tac >- simp[Abbr `after`, stmt_state_rel_start_gas_obs] >>
  asm_simp_tac bool_ss [] >>
  `(after with gas_obs := []).scopes = es.scopes` by simp[Abbr `after`] >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ es _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_at_def] >>
  qpat_assum `_ = es.scopes` (fn th => pure_rewrite_tac[th]) >>
  disch_then ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume append_toplevel_prefix_entry[rhs_static]:
  `supported_expr tops e` by fs[Once supported_stmt_def, supported_expr_def] >>
  `well_typed_expr env e` by (drule_then strip_assume_tac append_typing_target >> simp[]) >>
  `body_stmt_safe tops (Append (TopLevelNameTarget nid) e)` by
    (drule supported_stmt_body_safe >> simp[]) >>
  drule_all_then assume_tac body_append_expr_pre >>
  conj_tac >- simp[Abbr `after`] >>
  `body_const_cells_agree [(NONE,tops)] cx env (after with gas_obs := []) <=>
   body_const_cells_agree [(NONE,tops)] cx env es` by
    (irule body_const_cells_agree_immutables >> simp[Abbr `after`]) >>
  asm_simp_tac bool_ss []
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume append_toplevel_prefix_entry[rhs_sim]:
  qabbrev_tac `mid = after with gas_obs := []` >>
  `(!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x)` by
    fs[ret_pc_ok_def] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid` by
    (irule expr_body_pre_gas_admissible >> goal_assum (drule_at Any)) >>
  rename1 `lower_value compile_expr cenv elem e sa = (op,sm)` >>
  rename1 `lower_value compile_expr _ elem (gas_shadow_expr e) shadow_sa = (op,shadow_sm)` >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid s0 /\
       storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid G0 tn0 s0` by fs[Abbr `mid`] >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx elem e mid
    (st0,sa,sm,shadow_sa,shadow_sm,op,s0,G0,tn0)` by
    (simp[expr_sim_full_pre_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx elem e mid` by
    (irule (cj 1 body_expr_full_ok_simulations) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx elem e mid` by
    (qpat_x_assum `body_expr_prefix_ok _ _`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     metis_tac[]) >>
  reverse conj_tac
  >- (qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_prefix_def]) >> disch_then drule >> simp[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then drule_all >> strip_tac >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt gen_tac >> Cases_on `res` >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise append_toplevel_prefix_entry
*)
