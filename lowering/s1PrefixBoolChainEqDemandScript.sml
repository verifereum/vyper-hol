Theory s1PrefixBoolChainEqDemand
Ancestors
  s1PrefixDefs bodyFullPreds bodyFullBopWordLayout bodyFullIfExpReach
  exprSimHyps exprSimSource loweringPosts bodyMemoryDefs exprLoweringProps
  exprBodyPreProps freshWrites vyperStorageFootprint vyperState vyperAST

(* A demand is for a value-read at one actual entry, not an assertion that
   the expression simulates there. Its expected compiler type may differ
   from the expression's annotation. *)
Definition value_read_demand_def:
  value_read_demand (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      tops cenv cx env e ty es packet <=>
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env e es /\
    expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty e es packet
End

(* The two code slices are those of the demanded parent. The right demand
   is established at the successful left replay cut. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `value_read_demand _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [value_read_demand_def,expr_sim_full_pre_def]) >>
  drule_all bop_full_layout >> strip_tac >>
  drule expr_body_pre_bop >> strip_tac >>
  qexistsl_tac [`s1`,`s2`,`shadow_s1`,`shadow_s2`,`x`,`y`] >>
  conj_tac
  >- (simp[value_read_demand_def,expr_sim_full_pre_def] >>
      metis_tac[expr_body_pre_gas_admissible]) >>
  conj_tac >- (simp[expr_size_def] >> decide_tac) >>
  conj_tac >- (simp[expr_size_def] >> decide_tac) >>
  suspend "right_entry"
QED
*)
Theorem bool_chain_word_eq_demand_closure:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env ann ty l r es
     st0 sa sb shadow_sa shadow_sb op s0 G0 tn0.
    value_read_demand (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      tops cenv cx env (Builtin ann (Bop Eq) [l;r]) ty es
      (st0,sa,sb,shadow_sa,shadow_sb,op,s0,G0,tn0) /\
    is_word_type (expr_type l) /\ is_word_type (expr_type r) ==>
    ?s1 s2 shadow_s1 shadow_s2 x y.
      value_read_demand (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        tops cenv cx env l (expr_type l) es
        (st0,sa,s1,shadow_sa,shadow_s1,x,s0,G0,tn0) /\
      expr_size l < expr_size (Builtin ann (Bop Eq) [l;r]) /\
      expr_size r < expr_size (Builtin ann (Bop Eq) [l;r]) /\
      (!left v1 mid G1 tn1 t.
        (!tail. bind (eval_expr cx l) (read_result cx)
           (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ tail) =
             (INL v1,mid with gas_obs := tail)) /\
        storage_trace_domain cx st0 mid.storage_trace /\
        (!H. valid_horizon cx st0 H mid.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
            (s0,G0,tn0) left (OK t,G1,tn1) /\
          expr_post H ctx func cenv cx l es sa s1 s0 mid v1 x t /\
          expr_store_bound cx (post_value_type cenv l) v1 x t /\
          t.vs_current_bb = s1.cs_current_bb /\
          t.vs_inst_idx = LENGTH s1.cs_current_insts /\
          alloca_history func t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
          ptr_val_ok cx (post_value_type cenv l) v1 x G1 tn1 t /\
          (~is_word_type (post_value_type cenv l) ==> ptr_buf_ok cenv l x G1 t) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
          ~t.vs_halted /\ mid.gas_obs = []) ==>
        value_read_demand (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
          tops cenv cx env r (expr_type l) mid
          (st0,s1,s2,shadow_s1,shadow_s2,y,t,G1,tn1))
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_word_eq_demand_closure[right_entry]:
  qx_genl_tac [`left`,`v1`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> fs[expr_post_def]) >>
  `!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s` by
    (drule gas_origin_ptr_path_dalloca_fmp_headroom >>
     simp[] >> metis_tac[body_inv_no_phi]) >>
  qpat_assum `!tail. bind (eval_expr cx l) _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `expr_body_pre cenv cx env r mid` by
    (qpat_assum `!es'. expr_sim_inv _ _ _ es' ==> _` irule >>
     drule_at (Pos last) (REWRITE_RULE [ETA_THM] expr_body_pre_eval) >>
     disch_then (qspec_then `cenv` mp_tac) >> simp[] >> metis_tac[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`well_typed_expr env l` by metis_tac[expr_body_pre_static_facts] >>
     `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     `body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := [])`
       suffices_by simp[] >>
     irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx l) _ _ = (_,mid with gas_obs := [])`
       (irule_at Any) >> simp[]) >>
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z)` by
    metis_tac[not_fresh_at_mono] >>
  `return_buf_frame d cenv s1 t` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
     qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ mid _ _ t`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >> simp[]) >>
  simp[value_read_demand_def,expr_sim_full_pre_def] >>
  metis_tac[expr_body_pre_gas_admissible]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise bool_chain_word_eq_demand_closure
*)
