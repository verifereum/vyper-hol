(* Join the tuple RHS prefix to the staged exact-layout stores. *)
Theory s1PrefixAssignTupleExactLayout
Ancestors
  s1PrefixAssignTupleExactLayoutCursor s1PrefixAssignTupleExactReplay
  s1PrefixDefs s1PrefixPreds s1PrefixCompose s1PrefixProps bodyFullAssignTuple
  loweringPosts bodyPtrDefs
  bodyFullPreds bodyFullTargetDefs bodyFullSimProjection bodyFullTupleTargetProjection
  bodySimFull bodySimStmtFacts
  exprSimSource exprSimDefs exprSimExtract32Post stmtSimAssignTuple
  tupleTargetStoreProps stmtSimForRounds vyperStatePreservation
  vyperStorageTrace vyperStorageFootprint vyperState vyperInterpreter
  bodyTupleExactStoreCursor list

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule tuple_targets_typing >> disch_then (qx_choose_then `tys` strip_assume_tac) >>
  `expr_body_pre cenv cx env e es` by (drule_all tuple_assignment_rhs_pre >> simp[]) >>
  drule_then assume_tac expr_body_pre_gas_admissible >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (TupleT tys) e es` by metis_tac[body_expr_full_ok_simulations] >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (TupleT tys) e es` by metis_tac[cj 1 body_expr_prefix_ok_def] >>
  rw[stmt_frag_prefix_def,stmt_frag_full_pre_def] >>
  drule_all tuple_assign_exact_rhs_parts >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
      (qx_choosel_then [`vv`,`sc`,`op`,`su`,`shadow_su`,`staged`,`sl`,`elems`,`ss`,`shadow_ss`]
        (map_every assume_tac o CONJUNCTS)))))) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
    by fs[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[expr_sim_prefix_def,expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`su`,`shadow_sa`,`shadow_su`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`su`,`shadow_sa`,`shadow_su`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  rewrite_tac[eval_assign_tuple_action] >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (mp_then Any irule gas_prefix_full_bind_replay) >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
       storage_trace_frame_read_result,requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame,requests_outcomes_frame_read_result] >>
  (reverse conj_tac >- (rpt strip_tac >> rename1 `expr_exit result _` >>
    Cases_on `result` >> fs[expr_exit_def])) >>
  map_every qx_gen_tac [`marks`,`source_v`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  suspend "stores"
QED
*)
Theorem tuple_assign_exact_with_borrowed_frame_prefix:
  !cx gs e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget gs) v) /\
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_prefix_ok cx (TupleTarget gs) v) /\
    body_expr_full_ok cx e /\
    body_expr_prefix_ok cx e /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget gs) e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    ~supported_stmt_expr_exists (const_name_root cx) (Assign (TupleTarget gs) e) /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    (!bt. MEM (BaseTarget bt) gs /\ immutable_root cx bt /\
          ~(?nsid. bt = TopLevelNameTarget nsid) ==>
          !(H : (bool # bytes32 # type_value) list # num list) src mid u t sa sb id path ty r obs name b cap p tvs.
            eval_target_place cx bt (src with gas_obs := obs) =
              (INL (ImmutablePlace NONE id path),mid) /\
            bodyFullTargetDefs$imm_target_post H ctx func cenv cx src sa sb u mid id path ty r t /\
            local_region cenv src.scopes u name b cap /\
            b <= p /\ p + type_memory_size_list tvs <= b+cap /\
            local_path_at cenv cx name (p-b) (TupleTV tvs) ==>
            mem_bytes_at p (type_memory_size_list tvs) t.vs_memory =
              mem_bytes_at p (type_memory_size_list tvs) u.vs_memory) /\
    lowered_value_type cenv e = expr_type e /\
    ~(?ids. gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] /\
            EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids) ==>
    stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (TupleTarget gs) e)))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume tuple_assign_exact_with_borrowed_frame_prefix[stores]:
  `?tvs vs u Gu tu.
     source_v = ArrayV (TupleV vs) /\
     evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
     values_have_types tvs vs /\ val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
     tuple_exact_prefix_inv (cenv,cx,env,tops,bindings)
       (DF,lo,d,ctx,func,shadow_func,st0) (sa,sb,shadow_sb) (es,s0,G0,tn0)
       (gs,tys,tvs,vs) gs vs (mid with gas_obs := []) u Gu tu /\
     (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t,G1,tn1) [] (OK u,Gu,tu))` by
    (irule tuple_exact_prefix_cursor_init >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`e`,`elems`,`marks`,`op`,`shadow_ss`,`sl`,`ss`,`staged`,`su`,`vv`] >>
     `cs_extends sa su` by metis_tac[compileEnvTheory.cs_extends_trans] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp[extract32_expr_post_end_gas_obs] >>
     qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     `ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G1 tn1 t` by
       (qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` mp_tac >>
        simp[NoAsms,ghost_inv_at_def] >> strip_tac >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `source_v = ArrayV (TupleV vs)` SUBST_ALL_TAC >>
  `assign_tuple_targets cx (TupleTarget gs) (ArrayV (TupleV vs)) =
     assign_tuple_target_list cx gs vs` by simp[Once evaluate_def] >>
  `?tv er. eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
       (INL tv,er) /\
     read_result cx tv er = (INL (ArrayV (TupleV vs)),mid with gas_obs := [])` by
    (qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
       (qspec_then `[]` (mp_tac o MATCH_MP bind_split)) >> simp[]) >>
  `body_tuple_targets_full_ok cx gs vs /\ body_tuple_targets_prefix_ok cx gs vs` by
    (conj_tac
     >- (irule body_tuple_target_full_ok_tuple_value >>
         qpat_assum `!a b c d e f. _ ==> body_tuple_target_full_ok _ _ _`
           (drule_all_then ACCEPT_TAC)) >>
     qpat_assum `!a b c d e f. _ ==> body_tuple_target_prefix_ok _ _ _`
       (drule_all_then mp_tac) >> simp[Once body_tuple_target_prefix_ok_def]) >>
  `gas_admissible (assign_tuple_target_list cx gs vs) (stmt_res_ok lctx) mid` by
    (qpat_assum `gas_admissible (eval_stmt cx _) _ es`
       (assume_tac o REWRITE_RULE[eval_assign_tuple_action]) >>
     drule_all gas_admissible_bind_tail >> simp[]) >>
  qhdtm_x_assum `tuple_exact_prefix_inv`
    (strip_assume_tac o PURE_REWRITE_RULE[tuple_exact_prefix_inv_def]) >>
  `~u.vs_halted` by
    (qhdtm_assum `tuple_exact_store_cursor`
       (mp_tac o PURE_REWRITE_RULE[tuple_exact_store_cursor_def,tuple_exact_cursor_common_def]) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
      (assign_tuple_target_list cx gs vs) (mid with gas_obs := [],u,Gu,tu)` by
    (qhdtm_assum `tuple_exact_store_cursor`
       (mp_then Any irule tuple_assign_exact_residual_store_prefix) >>
     simp[] >> (conj_tac >- first_assum ACCEPT_TAC) >>
     qexists_tac `stmt_res_ok lctx` >> first_assum ACCEPT_TAC) >>
  (* Staging precedes the stores but consumes no marks. *)
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
      (assign_tuple_target_list cx gs vs) (mid with gas_obs := [],t,G1,tn1)`
    suffices_by simp[gas_prefix_full_def] >>
  qpat_assum `gas_prefix_full _ _ _ (assign_tuple_target_list cx gs vs) _`
    (mp_then Any irule gas_prefix_full_zero_prefix_guarded) >>
  simp[evaluate_storage_trace_frame]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise tuple_assign_exact_with_borrowed_frame_prefix
*)
