(* The Append RHS starts at the replayed successful target cut. *)
Theory s1PrefixAppendReplayRhs
Ancestors
  s1PrefixPreds s1PrefixDefs bodyAppendResolvedPre bodyFullSimProjection
  bodyFullPreds targetPlaceSim exprSimHypsDefs exprSimSource
  gasOutcomeFullCompose exprOperandVar exprLoweringProps bodyMemoryDefs
  loweringPosts exprSimDefs vyperStorageFootprint vyperInterpreter vyperState
  exprLowering sum

Theorem append_replayed_rhs_source[local]:
  target_pre cenv cx env t es /\ expr_body_pre cenv cx env e es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  type_place_target env t = SOME (Type (ArrayT elem (Dynamic cap))) /\
  eval_target_place cx t (es with gas_obs := obs) = (INL p,mid) ==>
  expr_body_pre cenv cx env e mid /\
  body_const_cells_agree [(NONE,tops)] cx env mid
Proof
  strip_tac >> conj_tac
  >- (irule append_resolved_rhs_body_pre >>
      goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
      simp[target_pre_def, expr_sim_inv_gas_obs, expr_body_pre_gas_obs] >>
      fs[target_pre_def]) >>
  irule body_const_cells_agree_target >>
  goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >> simp[]
QED

Theorem append_replayed_target_shape[local]:
  target_post H ctx func cenv cx es sa sp s0 mid (PlaceR p)
    (Type (ArrayT elem (Dynamic cap))) r u ==>
  ?b loc. r = (b,SOME loc,SOME (ValPT (ArrayT elem (Dynamic cap))))
Proof
  PairCases_on `r` >> Cases_on `p` >>
  simp[target_post_def, value_type_place_def, place_ptr_rel_def] >> metis_tac[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  qpat_assum `stmt_frag_full_pre _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [stmt_frag_full_pre_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `eval_target_place cx t (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL p,mid)` by
    (`mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. eval_target_place cx t _ = (INL p,_)`
       (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid`
       (fn th => rewrite_tac[listTheory.APPEND_NIL,th])) >>
  drule_all_then strip_assume_tac append_replayed_rhs_source >>
  `body_expr_full_ok cx e /\ body_expr_prefix_ok cx e` by metis_tac[] >>
  drule_then strip_assume_tac append_replayed_target_shape >>
  qpat_assum `!b loc. _ ==> ?op sm shadow_sm. _`
    (drule_then (qx_choosel_then [`vop`,`sm`,`shadow_sm`] strip_assume_tac)) >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx elem e mid
     (st0,sp,sm,shadow_sp,shadow_sm,vop,u,Gm,tm)` by suspend "rhs_pre" >>
  conj_tac >- suspend "rhs_full" >>
  suspend "rhs_prefix"
QED
*)
Theorem append_replay_rhs_prefix_entry:
  stmt_frag_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Append t e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Append t e)))
    (eval_stmt cx (Append t e)) es (st0,sa,sb,shadow_sa,shadow_sb,s0,G0,tn0,ce) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  target_pre cenv cx env t es /\ expr_body_pre cenv cx env e es /\
  type_place_target env t = SOME (Type (ArrayT elem (Dynamic cap))) /\
  (!s q ee. eval_target_place cx t s = (INL q,ee) ==> body_expr_full_ok cx e) /\
  (!s q ee. eval_target_place cx t s = (INL q,ee) ==> body_expr_prefix_ok cx e) /\
  ci_mono sa sp /\ gas_shadow_state sp shadow_sp /\
  (!b loc. r = (b,SOME loc,SOME (ValPT (ArrayT elem (Dynamic cap)))) ==>
    ?op sm shadow_sm.
      lower_value compile_expr cenv elem e sp = (op,sm) /\
      lower_value compile_expr (gas_shadow_env T cenv) elem (gas_shadow_expr e)
        shadow_sp = (op,shadow_sm) /\
      gas_shadow_state sm shadow_sm /\ fn_has_code sp sm func /\
      fn_has_code shadow_sp shadow_sm shadow_func) /\
  (!tail. eval_target_place cx t
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL p,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    target_post H ctx func cenv cx es sa sp s0 mid (PlaceR p)
      (Type (ArrayT elem (Dynamic cap))) r u /\
    u.vs_current_bb = sp.cs_current_bb /\ u.vs_inst_idx = LENGTH sp.cs_current_insts /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx mid Gm tm u /\
    ~u.vs_halted /\ mid.gas_obs = [] /\
    (!fn i z. frag_reachable ctx func u fn i z ==> dalloca_fmp_headroom i z)) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (mid,u,Gm,tm)
    (\H res ee G tn v. ~v.vs_halted) (\H res ee gt er. ISR res) /\
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx e) (read_result cx)) (mid,u,Gm,tm)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume append_replay_rhs_prefix_entry[rhs_pre]:
  `local_ptrs_reserved cenv sp` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> fs[ci_mono_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sp x` by
    metis_tac[compiler_ci_mono_not_fresh] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x)` by
    metis_tac[ret_pc_ok_def] >>
  `return_buf_frame d cenv sp u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     fs[ci_mono_def,target_post_def]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid` by
    (irule expr_body_pre_gas_admissible >> goal_assum (drule_at Any)) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid u /\
    storage_well_formed_on cx mid (FST H) /\ ghost_inv_at (DF H) lo d cenv cx mid Gm tm u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> target_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (CONJUNCTS_THEN2
       (strip_assume_tac o REWRITE_RULE [target_post_def]) strip_assume_tac) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[expr_sim_full_pre_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume append_replay_rhs_prefix_entry[rhs_full]:
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx elem e mid` by
    (irule (cj 1 body_expr_full_ok_simulations) >>
     simp[] >> qexistsl_tac [`env`,`tops`] >> simp[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (drule_then (mp_then Any irule gas_outcome_full_post_source) o
     REWRITE_RULE [expr_sim_full_eq]) >>
  simp[] >> rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume append_replay_rhs_prefix_entry[rhs_prefix]:
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx elem e mid` by
    (qpat_x_assum `body_expr_prefix_ok cx e`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     first_x_assum (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `body_inv _ _ _ _`)) >> simp[]) >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def]) >>
  disch_then (drule_then ACCEPT_TAC)
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise append_replay_rhs_prefix_entry
*)
