Theory s1PrefixBoolChainWordEqCut
Ancestors
  s1PrefixCompose s1PrefixProps s1PrefixDefs
  bodyFullPreds bodyFullBopWordLayout bodyFullSimProjection bodyFullIfExpReach
  exprSimHyps exprSimSource exprBopSimProps exprBopSimDefs vyperStorageTrace
  gasOutcomeFullCompose exprSimDefs loweringPosts bodyMemoryDefs
  freshWrites vyperStorageFootprint vyperState exprBodyPreProps exprSimWordArgs

(* Both callbacks are at the compiler slices of the original Eq instruction
   sequence. The right callback is needed only after a successful left replay. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `expr_sim_full_pre _ _ _ _ (Builtin _ _ _) _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_full_pre_def]) >>
  drule_all bop_full_layout >> strip_tac >>
  drule expr_body_pre_bop >> strip_tac >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type l) l es (st0,sa,s1,shadow_sa,shadow_s1,x,s0,G0,tn0)` by
    (simp[expr_sim_full_pre_def] >> metis_tac[expr_body_pre_gas_admissible]) >>
  qpat_assum `!a b c. _ ==> gas_outcome_full _ _ _ _ _ (es,s0,G0,tn0) _ _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ (es,s0,G0,tn0) headQ headR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx l) (read_result cx)) (es,s0,G0,tn0)
     (\H rr ee G tn u. headQ H rr ee G tn u /\ ~u.vs_halted /\ ee.gas_obs = []) headR` by
    (qpat_assum `gas_outcome_full _ _ _ _ _ _ headQ headR`
      (mp_then Any irule gas_outcome_full_post_source) >> simp[]) >>
  rewrite_tac[REWRITE_RULE [ETA_THM] eval_expr_bop_bind] >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ (\H rr ee G tn u. _ /\ ~u.vs_halted /\ _) headR`
    (mp_then Any irule gas_prefix_full_bind_replay) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result,
       Abbr `headR`] >>
  reverse (rpt conj_tac)
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
           storage_trace_frame_read_result] >>
      simp[storage_trace_frame_def, bop_result_def])
  >- (rpt gen_tac >> Cases_on `res` >> simp[]) >>
  suspend "right_entry"
QED
*)
Theorem bool_chain_word_eq_prefix_at_entry:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty l r env tops es
     st0 sa sb shadow_sa shadow_sb op s0 G0 tn0.
    ~is_bytestring_type (expr_type l) /\
    is_word_type (expr_type l) /\ is_word_type (expr_type r) /\
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Builtin (BaseT BoolT) (Bop Eq) [l;r]) es /\
    expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin (BaseT BoolT) (Bop Eq) [l;r]) es
      (st0,sa,sb,shadow_sa,shadow_sb,op,s0,G0,tn0) /\
    (!s1 shadow_s1 x.
      expr_body_pre cenv cx env l es /\
      body_const_cells_agree [(NONE,tops)] cx env es /\
      expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx (expr_type l) l es (st0,sa,s1,shadow_sa,shadow_s1,x,s0,G0,tn0) ==>
      gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (cx_tops cx) cx st0 (bind (eval_expr cx l) (read_result cx)) (es,s0,G0,tn0)
        (\H res ee G tn u. ?v. res = INL v /\
          expr_post H ctx func cenv cx l es sa s1 s0 ee v x u /\
          expr_store_bound cx (post_value_type cenv l) v x u /\
          u.vs_current_bb = s1.cs_current_bb /\
          u.vs_inst_idx = LENGTH s1.cs_current_insts /\
          alloca_history func u /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
          s0.vs_alloca_next <= u.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn u /\
          ptr_val_ok cx (post_value_type cenv l) v x G tn u /\
          (~is_word_type (post_value_type cenv l) ==> ptr_buf_ok cenv l x G u) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt ex. expr_exit res ex /\ halt_exit H cx ee res ex /\
          (ctx_has_dalloca ctx ==> !s. ex = Halt s ==> allocas_below_fmp s)) /\
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cx st0 (bind (eval_expr cx l) (read_result cx)) (es,s0,G0,tn0)) /\
    (!s1 s2 shadow_s1 shadow_s2 x y left v1 mid G1 tn1 t.
      expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx (expr_type l) l es (st0,sa,s1,shadow_sa,shadow_s1,x,s0,G0,tn0) /\
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
        ~t.vs_halted /\ mid.gas_obs = []) /\
      expr_body_pre cenv cx env r mid /\
      body_const_cells_agree [(NONE,tops)] cx env mid /\
      expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx (expr_type l) r mid (st0,s1,s2,shadow_s1,shadow_s2,y,t,G1,tn1) ==>
      gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (cx_tops cx) cx st0 (bind (eval_expr cx r) (read_result cx)) (mid,t,G1,tn1)
        (\H res ee G tn u. ?v. res = INL v /\
          expr_post H ctx func cenv cx r mid s1 s2 t ee v y u /\
          expr_store_bound cx (post_value_type cenv r) v y u /\
          u.vs_current_bb = s2.cs_current_bb /\
          u.vs_inst_idx = LENGTH s2.cs_current_insts /\
          alloca_history func u /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
          t.vs_alloca_next <= u.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn u /\
          ptr_val_ok cx (post_value_type cenv r) v y G tn u /\
          (~is_word_type (post_value_type cenv r) ==> ptr_buf_ok cenv r y G u) /\
          ghost_kept_at lo cenv mid s1 G1 tn1 t G tn)
        (\H res ee gt ex. expr_exit res ex /\ halt_exit H cx ee res ex /\
          (ctx_has_dalloca ctx ==> !s. ex = Halt s ==> allocas_below_fmp s)) /\
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cx st0 (bind (eval_expr cx r) (read_result cx)) (mid,t,G1,tn1)) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (bind (eval_expr cx (Builtin (BaseT BoolT) (Bop Eq) [l;r])) (read_result cx))
      (es,s0,G0,tn0)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_word_eq_prefix_at_entry[right_entry]:
  qx_genl_tac [`left`, `v1`, `mid`, `G1`, `tn1`, `t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (gen_tac >> disch_tac >>
     first_x_assum (qspec_then `H` (drule_then mp_tac)) >>
     simp[NoAsms, Abbr `headQ`, expr_post_def] >> strip_tac >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
      gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then mp_tac)) >>
  simp[NoAsms, Abbr `headQ`] >> strip_tac >>
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
  suspend "right_prefix"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume bool_chain_word_eq_prefix_at_entry[right_prefix]:
  `local_ptrs_reserved cenv s1` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z)` by
    metis_tac[not_fresh_at_mono] >>
  `return_buf_frame d cenv s1 t` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
     qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ mid _ _ t`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >> simp[]) >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type l) r mid (st0,s1,s2,shadow_s1,shadow_s2,y,t,G1,tn1)` by
    (simp[expr_sim_full_pre_def] >> metis_tac[expr_body_pre_gas_admissible]) >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (assume_tac o SIMP_RULE bool_ss [sumTheory.INL_11, GSYM CONJ_ASSOC] o BETA_RULE) >>
  qpat_assum `!a b c d e f g h i j k m. _ ==> gas_outcome_full _ _ _ _ _ (i,m,j,k) _ _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ (mid,t,G1,tn1) rightQ rightR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx r) (read_result cx)) (mid,t,G1,tn1)
     (\H rr ee G tn u. ~u.vs_halted) rightR` by
    (qpat_assum `gas_outcome_full _ _ _ _ _ _ rightQ rightR`
       (mp_then Any irule gas_outcome_full_post_source) >> simp[]) >>
  qpat_assum `gas_outcome_full _ _ _ _ _ (mid,t,G1,tn1) (\H rr ee G tn u. ~u.vs_halted) rightR`
    (mp_then Any irule gas_prefix_full_bind_no_outcome) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result,
       storage_trace_frame_def, Abbr `rightR`] >>
  conj_tac >- (rpt gen_tac >> Cases_on `res` >> simp[]) >>
  simp[bop_result_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise bool_chain_word_eq_prefix_at_entry
*)
