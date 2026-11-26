(* Checked Range: run both operands, then the counter setup and rounds at
   the landing of those same operands in the paired compilation. *)
Theory bodyForRangeCheckedRouteOutcomeMods
Ancestors
  bodyForRangeCheckedCodeMods bodyForRangeEndpointPresMods bodyForRangeEndpointRunMods
  bodyForRangeCheckedSuffixJoinMods bodyForRangeDriverMods bodyForEntryInputsMods
  bodyFullIfExpReach bodyInvExecutionProps bodyInvCodeProps bodyFullForFacts
  bodySimDeclCases exprBodyPreProps vyperEvalPreservesScopes finite_map
  bodyForRangeRouteMods vyperTypeInvariants vyperTypeSystem
Libs
  monadsyntax

val _ = Parse.hide "body";

Theorem range_checked_route_outcome_mods:
  ~(?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ (Range e1 e2) bound body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Range e1 e2) bound body) ==>
    EXISTS (occurs_abi_decode_target target o SND) mods) /\
  body_const_cells_agree_mods mods cx env es /\ expr_sim_inv_mods mods cenv cx env es /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  type_stmt env ret_ty (For id typ (Range e1 e2) bound body) = SOME env' /\
  stmt_exprs_ok cenv (For id typ (Range e1 e2) bound body) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
    (For id typ (Range e1 e2) bound body) /\
  (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
                (vyperSubscriptOverlap$accesses_stmt (For id typ (Range e1 e2) bound body)) /\
         IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
         IS_SOME (FLOOKUP cenv.ce_module_vars key)) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Range e1 e2) bound body)) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ cenv ret_ty /\
  (!tenv s tv t. tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tv,t) ==>
    body_iterator_full_ok_mods mods exps cx (Range e1 e2)) /\
  (!tenv s tv t s1 vs t1 s2 u t2. tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tv,t) /\
    eval_iterator cx (Range e1 e2) s1 = (INL vs,t1) /\
    check (compatible_bound (Dynamic bound) (LENGTH vs)) "For too long" s2 = (INL u,t2) ==>
    body_for_full_ok_mods mods exps cx tv id body vs) /\
  bound < dimword (:256) /\
  (!tv. is_int_type typ /\ evaluate_type (get_tenv cx) typ = SOME tv ==>
    type_memory_bytes cenv typ = 32 /\ type_memory_size tv = 32 /\ word_memory_type tv) /\
  (!ee. expr_sim_inv_mods mods cenv cx env ee ==> lookup_scopes id ee.scopes = NONE) /\
  (!tv n1 n2. n1 <= n2 /\ Num (n2 - n1) <= bound ==>
    (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
        check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
        eval_for cx tv id body (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)) od) =
    eval_for cx tv id body (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1)))) /\
  stmt_env cenv lctx ret_ty (For id typ (Range e1 e2) bound body) sa = (cenv',sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ret_ty
    (gas_shadow_stmt (For id typ (Range e1 e2) bound body)) sha = (gas_shadow_env T cenv',shb) /\
  gas_shadow_state sa sha /\ gas_shadow_state sb shb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_has_code sa sb func /\
  fn_has_code sha shb shadow_func /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (eval_stmt cx (For id typ (Range e1 e2) bound body)) (stmt_res_ok lctx) es /\
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) mods cx st0
    (eval_stmt cx (For id typ (Range e1 e2) bound body)) (es,s0,G0,tn0)
    (\H res ee G tn t. res = INL () /\
      range_done_mods DF lo d ctx func cenv cx lctx sa sb es s0 G0 tn0 H ee G tn t)
    (\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\ (ctx_has_dalloca ctx ==>
        !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >>
  drule_then assume_tac contract_inv_alloca_locals >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then strip_assume_tac type_stmt_for_projection >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    (drule_then assume_tac expr_sim_inv_mods_env >>
     `env.type_defs = get_tenv cx` by fs[env_consistent_def, env_context_consistent_def] >>
     drule assignable_type_well_formed >>
     simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  `is_int_type typ /\ expr_type e1 = typ /\ expr_type e2 = typ` by
    fs[well_typed_iterator_def] >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> qexistsl_tac [`env`,`env'`,`ret_ty`,
       `For id typ (Range e1 e2) bound body`] >> simp[] >> metis_tac[]) >>
  `(!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z)` by simp[] >>
  `type_memory_bytes cenv typ = 32 /\ type_memory_size tyv = 32 /\ word_memory_type tyv` by
    (qpat_assum `!tv. is_int_type typ /\ _ ==> _` (drule_all_then ACCEPT_TAC)) >>
  drule_all_then assume_tac for_iterator_callback_mods >>
  drule_all_then strip_assume_tac range_endpoint_pres_mods >>
  drule_all range_checked_endpoint_intervals_mods >>
  disch_then (CONJUNCTS_THEN2 strip_assume_tac
    (CONJUNCTS_THEN2 strip_assume_tac
      (qx_choosel_then [`op1`,`op2`,`m`,`z`,`shm`,`shz`] strip_assume_tac))) >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  drule_all (Q.INST [`tenv` |-> `get_tenv cx`] (SPEC_ALL range_checked_code_mods)) >>
  disch_then (strip_assume_tac o
    CONV_RULE (TOP_DEPTH_CONV (REWR_CONV LET_THM ORELSEC BETA_CONV))) >>
  irule range_checked_endpoints_ready_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qhdtm_assum `module_body_inv` (irule_at Any) >>
  qhdtm_assum `contract_inv` (irule_at Any) >>
  qhdtm_assum `body_const_cells_agree_mods` (irule_at Any) >>
  qhdtm_assum `return_buf_frame` (irule_at Any) >>
  qhdtm_assum `gas_shadow_function` (irule_at Any) >>
  qpat_assum `lower_value compile_expr cenv typ e1 sa = _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr cenv typ e2 m = _` (irule_at Any) >>
  qpat_assum `gas_shadow_state m _` (irule_at Any) >>
  qpat_assum `gas_shadow_state z _` (irule_at Any) >>
  qpat_assum `gas_shadow_state sa _` (irule_at Any) >>
  qpat_assum `gas_admissible (eval_stmt cx _) _ es` (irule_at Any) >>
  qpat_assum `evaluate_type (get_tenv cx) typ = SOME _` (irule_at Any) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "suffix"
QED

Resume range_checked_route_outcome_mods[suffix]:
  qx_genl_tac [`gs1`,`gs2`,`n1`,`n2`,`mid1`,`mid2`,`G2`,`tn2`,`t2`] >> strip_tac >>
  `lookup_scopes id mid2.scopes = NONE` by
    (qpat_assum `!ee. expr_sim_inv_mods _ _ _ _ ee ==> lookup_scopes _ _ = NONE`
      (drule_then ACCEPT_TAC)) >>
  `lookup_scopes id es.scopes = NONE` by
    (irule lookup_scopes_none_map_fdom >> qexists_tac `mid2.scopes` >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (match_mp_tac (GEN_ALL body_inv_no_phi_mods) >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >> simp[]) >>
  qpat_assum `!tv n1 n2. _ ==> _ = eval_for _ tv _ _ _`
    (qspecl_then [`tyv`,`n1`,`n2`] assume_tac) >>
  irule range_checked_suffix_join_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qhdtm_assum `alloca_frame` (irule_at Any) >>
  qpat_assum `return_buf_frame _ _ _ t2` (irule_at Any) >>
  qpat_assum `body_const_cells_agree_mods _ _ _ mid2` (irule_at Any) >>
  qpat_assum `eval_operand _ t2 = SOME (i2w n1)` (irule_at Any) >>
  qpat_assum `eval_operand _ t2 = SOME (i2w n2)` (irule_at Any) >>
  qpat_assum `gas_admissible _ (stmt_res_ok _) mid2` (irule_at Any) >>
  qpat_assum `lookup_block z.cs_current_bb func.fn_blocks = SOME _` (irule_at Any) >>
  qpat_assum `lookup_block (fresh_label_output "for_entry" z.cs_next_label) _ = SOME _`
    (irule_at Any) >>
  qexistsl_tac [`tn0`,`b0`,`mid1`,`gs2`,`gs1`,`exps`,`e2`,`e1`,`G0`] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
  >- suspend "rounds" >>
  simp[ASCIInumbersTheory.toString_inj, wordsTheory.dimword_def,
       venomMemPropsTheory.dimindex_256, loweringStateRelDefsTheory.not_fresh_at_def] >>
  rpt strip_tac >> simp[ASCIInumbersTheory.toString_inj]
QED

Resume range_checked_route_outcome_mods[rounds]:
  qx_genl_tac [`w`,`mid`,`t`,`G`,`tn`,`rs`] >> strip_tac >>
  qpat_x_assum `rs = GENLIST _ _` SUBST_ALL_TAC >>
  `~not_fresh_at sa (STRING #"%" (toString (z.cs_next_var + 1)))` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
     decide_tac) >>
  irule range_rounds_from_header_mods >>
  (rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
   >- (qexists_tac `exps` >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  qhdtm_assum `for_code` (irule_at Any) >>
  qpat_assum `type_stmt env ret_ty (For id typ _ _ body) = SOME _` (irule_at Any) >>
  qpat_assum `declare_local cenv id typ z = _` (irule_at Any) >>
  qpat_assum `stmts_env bc _ ret_ty body b0 = _` (irule_at Any) >>
  qpat_assum `fn_has_code shb0 shb1 shadow_func` (irule_at Any) >>
  qpat_assum `module_body_inv mods src tops cenv cx` (irule_at Any) >>
  qpat_assum `supported_stmt tops bindings (For _ _ _ _ _)` (irule_at Any) >>
  qexists_tac `w` >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >> simp[venomInstTheory.mk_inst_def] >>
  qpat_assum `type_memory_bytes cenv typ = 32` (SUBST1_TAC o SYM) >>
  first_assum ACCEPT_TAC
QED

Finalise range_checked_route_outcome_mods
