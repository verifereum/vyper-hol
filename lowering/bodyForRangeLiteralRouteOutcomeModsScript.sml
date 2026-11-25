(* The literal Range setup installs a single header and passes it to the
   shared linked round driver. *)
Theory bodyForRangeLiteralRouteOutcomeMods
Ancestors
  bodyForRangeLiteralAllocReadyMods bodyForRangeLiteralStartMods bodyForRangeDriverMods
  bodyFullForRange bodyFullForFacts bodyForEntryInputsMods bodySimDeclCases
  bodyInvExecutionProps bodyFullIfExpReach gasOutcomeFullZeroPrefixMods
  gasOutcomeFullPostMods gasStorage vyperStorageTrace vyperStorageFootprint
  vyperTypeSystem vyperInterpreter vyperValue vyperState supportedStmts venomInst finite_map list

val _ = Parse.hide "body";

Theorem range_literal_route_outcome_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body) ==>
    EXISTS (occurs_abi_decode_target target o SND) mods) /\
  body_const_cells_agree_mods mods cx env es /\ expr_sim_inv_mods mods cenv cx env es /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  type_stmt env ret_ty (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body) = SOME env' /\
  stmt_exprs_ok cenv (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
    (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body) /\
  (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
      (vyperSubscriptOverlap$accesses_stmt
        (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body)) /\
    IS_SOME (FLOOKUP env.bare_global_assignable key) ==> IS_SOME (FLOOKUP cenv.ce_module_vars key)) /\
  call_evaluation_safe cx (int_calls_stmt
    (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body)) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv ret_ty /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  type_memory_bytes cenv typ = 32 /\ type_memory_size tyv = 32 /\ word_memory_type tyv /\
  lookup_scopes id es.scopes = NONE /\
  eval_stmt cx (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body) =
    eval_for cx tyv id body (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))) /\
  (!tenv s tv t s1 vs t1 s2 u t2.
    tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tv,t) /\
    eval_iterator cx (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) s1 = (INL vs,t1) /\
    check (compatible_bound (Dynamic bound) (LENGTH vs)) "For too long" s2 = (INL u,t2) ==>
    body_for_full_ok_mods mods exps cx tv id body vs) /\
  stmt_env cenv lctx ret_ty
    (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body) sa = (cenv',sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ret_ty
    (gas_shadow_stmt (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body)) ssa =
    (gas_shadow_env T cenv',ssb) /\
  gas_shadow_state sa ssa /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code ssa ssb shadow_func /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  gas_admissible (eval_stmt cx
    (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body)) (stmt_res_ok lctx) es /\
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\ alloca_history func s0 /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) mods cx st0
    (eval_stmt cx (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body))
    (es,s0,G0,tn0)
    (\H res ee G tn t. res = INL () /\
      range_done_mods DF lo d ctx func cenv cx lctx sa sb es s0 G0 tn0 H ee G tn t)
    (\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\ (ctx_has_dalloca ctx ==>
        !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >> reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- suspend "bad_domain" >>
  `cenv' = cenv` by
    (qpat_assum `stmt_env cenv _ _ (For _ _ _ _ _) sa = _`
      (mp_tac o REWRITE_RULE [range_full_outer_env]) >> simp[]) >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  drule_then assume_tac contract_inv_alloca_locals >>
  drule_then assume_tac supported_stmt_for_projection >>
  drule_then (strip_assume_tac o REWRITE_RULE [well_typed_iterator_def]) type_stmt_for_projection >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >>
     qpat_assum `type_stmt env _ (For _ _ _ _ _) = _` (irule_at Any) >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC body_inv_no_phi_mods) >>
  suspend "setup"
QED

Resume range_literal_route_outcome_mods[bad_domain]:
  irule gas_outcome_full_mods_bad_nil >> simp[] >> gen_tac >>
  qmatch_goalsub_abbrev_tac `SND (source (es with gas_obs := tail))` >>
  Cases_on `source (es with gas_obs := tail)` >> simp[] >>
  irule (INST_TYPE [alpha |-> ``:unit``] storage_trace_frame_preserves_bad_domain) >>
  qexistsl_tac [`source`,`q`,`es with gas_obs := tail`] >>
  simp[Abbr `source`, evaluate_storage_trace_frame]
QED

Resume range_literal_route_outcome_mods[setup]:
  drule_all_then (Q.ISPECL_THEN [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`p`,`sz`,`ainst`,`cv`,`ev`,`dv`,`nv`,`en`,`cn`,`bl`,`inc`,`ex`,`bc`,
      `body_cenv`,`sb0`,`sb1`,`sj`,`ss0`,`ss1`,`bbb`,`bb`,`w`,`sA`,`GA`,`tnA`] strip_assume_tac))
    range_literal_alloc_ready_mods >>
  suspend "scalar"
QED

Resume range_literal_route_outcome_mods[scalar]:
  qabbrev_tac `rs = GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))` >>
  `eval_iterator cx (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) es = (INL rs,es) /\
   eval_stmt cx (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body) es =
     eval_for cx tyv id body rs es /\
   ?t Gt tnt. ~t.vs_halted /\
     (!H. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (sA,GA,tnA) [] (OK t,Gt,tnt)) /\
     (!H. valid_horizon cx st0 H es.storage_trace ==>
       range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
         sa sb0 es s0 G0 tn0 n1 n2 bound cn cv ev p ainst.inst_id sz w H rs es Gt tnt t)` by
    (qunabbrev_tac `rs` >> irule (SIMP_RULE std_ss [LET_THM] range_literal_start_uniform_mods) >>
     (rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
      >- (qexistsl_tac [`bb`,`en`] >> simp[] >>
          qexistsl_tac [`sa.cs_next_id + 1`,`sa.cs_next_id + 2`,`sa.cs_next_id + 3`,`sa.cs_next_id + 4`] >>
          simp[])) >>
     qexists_tac `tops` >> first_assum ACCEPT_TAC) >>
  qmatch_asmsub_rename_tac `gas_origin_ptr_path _ (sA,GA,tnA) [] (OK t,GH,tnH)` >>
  qpat_x_assum `eval_stmt cx (For _ _ _ _ _) = _` SUBST_ALL_TAC >>
  irule gas_outcome_full_mods_zero_prefix >>
  qexistsl_tac [`GA`,`sA`,`tnA`] >> conj_tac
  >- (gen_tac >> first_assum irule) >>
  irule gas_outcome_full_mods_zero_prefix >>
  qexistsl_tac [`GH`,`t`,`tnH`] >> conj_tac >- first_assum ACCEPT_TAC >>
  suspend "rounds"
QED

Resume range_literal_route_outcome_mods[rounds]:
  `compatible_bound (Dynamic bound) (LENGTH rs)` by
    (qpat_x_assum `supported_iterator tops typ _ bound` mp_tac >>
     simp[supported_iterator_def, Abbr `rs`, compatible_bound_def]) >>
  `body_for_full_ok_mods mods exps cx tyv id body rs` by
    (qpat_assum `!tenv s tv t s1 vs t1 s2 u t2. _` irule >>
     simp[lift_option_type_def, return_def] >> conj_tac
     >- (qexistsl_tac [`es`,`es`] >> first_assum ACCEPT_TAC) >>
     simp[check_def, assert_def, return_def]) >>
  qunabbrev_tac `rs` >>
  irule range_rounds_from_header_mods >>
  (rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
   >- (qexists_tac `exps` >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  goal_assum (drule_at (Pat `for_code _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `type_stmt _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `declare_local _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `stmts_env _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `fn_has_code _ _ _`)) >>
  goal_assum (drule_at (Pat `module_body_inv _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `supported_stmt _ _ _`)) >>
  qexists_tac `w` >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >> simp[mk_inst_def]
QED

Finalise range_literal_route_outcome_mods
