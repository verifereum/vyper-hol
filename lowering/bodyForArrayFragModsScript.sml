(* Compose the Array expression, capture, and rounds at their actual cuts. *)
Theory bodyForArrayFragMods
Ancestors
  bodyForArrayCodeCutsMods bodyForArrayExprRunMods bodyForArrayCaptureInstallMods
  bodyForArrayOriginRoundsMods bodyForArrayRouteMods bodyForArraySelectedPacketMods
  bodyForArrayHeaderMods
  bodyForRangeHeaderMods bodyFullForFacts bodyFullForArrayRound bodyFullPostsMods
  gasOutcomeFullPostMods bodyInvCodeProps bodyInvExecutionProps exprBodyPreProps option
  loweringPosts stmtLowering compileEnv gasShadow vyperTypeSystem vyperTypeEvalCaseProofs
  vyperTypeInvariants vyperInterpreter vyperValue finite_map
Libs monadsyntax

val _ = Parse.hide "body";

Theorem array_stmt_env[local]:
  stmt_env cenv lctx ret_ty (For id typ (Array e) n body) sa = (cenv',sb) <=>
  cenv' = cenv /\
  compile_stmt cenv lctx ret_ty (For id typ (Array e) n body) sa = ((),sb)
Proof
  simp[stmt_env_def,declare_stmt_local_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  pairarg_tac >> simp[EQ_SYM_EQ]
QED

Theorem array_shadow_stmt_env[local]:
  stmt_env (gas_shadow_env T cenv) lctx ret_ty
    (gas_shadow_stmt (For id typ (Array e) n body)) sa =
    (gas_shadow_env T cenv,sb) <=>
  compile_stmt (gas_shadow_env T cenv) lctx ret_ty
    (gas_shadow_stmt (For id typ (Array e) n body)) sa = ((),sb)
Proof
  simp[gas_shadow_stmt_def,gas_shadow_iterator_def,array_stmt_env]
QED

Theorem compile_for_array_frag_full_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ (Array e) n body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Array e) n body) ==>
    EXISTS (occurs_abi_decode_target target o SND) mods) /\
  body_const_cells_agree_mods mods cx env es /\ expr_sim_inv_mods mods cenv cx env es /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  type_stmt env ret_ty (For id typ (Array e) n body) = SOME env' /\
  stmt_exprs_ok cenv (For id typ (Array e) n body) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
    (For id typ (Array e) n body) /\
  (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
       (vyperSubscriptOverlap$accesses_stmt (For id typ (Array e) n body)) /\
     IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
     IS_SOME (FLOOKUP cenv.ce_module_vars key)) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n body)) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ cenv ret_ty /\
  stmt_loop_calls_ok mods (For id typ (Array e) n body) /\
  (!tenv s tv t. tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tv,t) ==>
    body_iterator_full_ok_mods mods exps cx (Array e)) /\
  (!tenv s tv t s1 vs t1 s2 u t2. tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tv,t) /\
    eval_iterator cx (Array e) s1 = (INL vs,t1) /\
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s2 = (INL u,t2) ==>
    body_for_full_ok_mods mods exps cx tv id body vs) ==>
  stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (For id typ (Array e) n body))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty
      (gas_shadow_stmt (For id typ (Array e) n body)))
    (eval_stmt cx (For id typ (Array e) n body)) es
Proof
  strip_tac >> rewrite_tac[stmt_frag_full_mods_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env cenv _ _ (For _ _ _ _ _) sa = _`
    (strip_assume_tac o REWRITE_RULE [array_stmt_env]) >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
    (assume_tac o REWRITE_RULE [array_shadow_stmt_env]) >>
  drule_then (fn eq => rewrite_tac[eq]) contract_inv_cenv_modules >>
  drule_then assume_tac contract_inv_alloca_locals >>
  drule_then strip_assume_tac type_stmt_for_projection >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    (drule assignable_type_well_formed >> simp[well_formed_type_def,IS_SOME_EXISTS]) >>
  `?bd. expr_type e = ArrayT typ bd` by
    (drule type_stmt_for_array_bound >> metis_tac[]) >>
  drule_all_then strip_assume_tac for_array_paired_cuts_mods >>
  drule_all_then assume_tac for_array_source_pre_mods >>
  qabbrev_tac `Done = for_array_done_mods DF lo d ctx func cenv cx lctx sa sb es s0 G0 tn0` >>
  qabbrev_tac `Term = \H ex ee gt r.
    (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex : unit + exception) gt r) /\
    halt_exit H cx ee (INR ex : unit + exception) r /\ (ctx_has_dalloca ctx ==>
      !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)` >>
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`\H res ee G tn t. res = INL () /\ Done H ee G tn t`,
                `\H res ee gt r. ?ex. res = INR ex /\ Term H ex ee gt r`] >>
  conj_tac >-
    (simp[Abbr `Done`,for_array_done_mods_def,for_array_outer_frame_mods_def,
          range_outer_frame_mods_def] >> rpt strip_tac >> qexists_tac `cenv` >> simp[]) >>
  conj_tac >- (simp[Abbr `Term`] >> rpt strip_tac >> gvs[]) >>
  suspend "route"
QED

Resume compile_for_array_frag_full_mods[route]:
  qabbrev_tac `P = \H (res:eval_result + exception) ee G tn t.
    for_array_expr_landed_mods (DF,lo,d,ctx,func) mods cx cenv env e vv sbExpr
      (es,sa,s0,G0,tn0) H (OUTL res) ee G tn t` >>
  qabbrev_tac `Entry = for_array_selected_entry_mods mods exps cx env st0 tyv id body
    (DF,lo,d,ctx,func,shadow_func) (es,sa,s0,G0,tn0)
    ((cenv,id,typ,e,typ,bd,ret_ty,body),
     (vv,sbExpr,shadow_sa,shadow_sbExpr,loc,len_op,saL),
     (bc,saD,saA,xd,capacity,aidItem),
     (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var),
     (sa',stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy),
     (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody))` >>
  irule (Q.INST [`ok` |-> `stmt_res_ok lctx`] for_array_outcome_from_capture_mods) >>
  qexistsl_tac [`Entry`,`P`,`lctx`,`tyv`] >>
  conj_tac >- suspend "install" >>
  conj_tac >- suspend "rounds" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  suspend "raw"
QED

Resume compile_for_array_frag_full_mods[raw]:
  simp[Abbr `P`,Abbr `Term`] >> irule for_array_raw_run_mods >>
  qhdtm_assum `for_nonslot_layout`
    (strip_assume_tac o REWRITE_RULE [for_nonslot_layout_def]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexistsl_tac [`shadow_sa`,`shadow_func`,`shadow_sbExpr`] >>
              rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`bindings`,`body`,`env'`,`exps`,`id`,`n`,`ret_ty`,`src`,`tops`,`typ`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume compile_for_array_frag_full_mods[install]:
  simp[NoAsms,Abbr `P`,Abbr `Entry`] >> rpt gen_tac >> strip_tac >>
  irule for_array_origin_capture_install_mods >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexists_tac `gas_explicit marks s0.vs_gas_readings` >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists_tac `env'` >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume compile_for_array_frag_full_mods[rounds]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `Abbrev (Entry = _)`
    (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  simp[NoAsms,Abbr `Done`,Abbr `Term`] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    (qhdtm_assum `ret_pc_ok` (mp_tac o REWRITE_RULE [ret_pc_ok_def]) >> simp[]) >>
  irule for_array_origin_rounds_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  first_assum (part_match_exists_tac (fst o dest_conj) o concl) >>
  qexistsl_tac [`bindings`,`env'`,`n`,`src`,`tops`] >>
  pure_asm_rewrite_tac [AND_CLAUSES] >> FAIL_TAC "rounds cuts"
QED

Finalise compile_for_array_frag_full_mods
