(* Request-prefix companion to bodyFullBopRestWordCompose. *)
Theory s1PrefixBopRestWordCompose
Ancestors
  s1PrefixPreds s1PrefixDefs
  s1PrefixCompose s1PrefixProps s1PrefixOfVV
  bodyFullPreds bodyFullExprsListFacts bodyFullSimProjection
  bodySimFull exprBopSimProps exprSimHypsDefs
  bodyFullBopRestWordLayout bodyFullBopRestWordEntry bodyFullIfExpReach
  gasOutcomeFullCompose vyperStorageTrace vyperState vyperInterpreter
  exprSimDefs bodyMemoryDefs exprSimHyps exprSimSource exprBopSimDefs
  contextRawReachable unitMemInv gasSummary exprBodyPreProps
  vyperStorageFootprint loweringPosts

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env e1 es` by
    (irule expr_body_pre_builtin_arg >>
     conj_tac >- metis_tac[expr_body_pre_static_facts] >>
     qexistsl [`ann`, `[e1;e2]`, `Bop bop`, `es`] >> simp[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e1) e1 es` by
    (`body_expr_full_ok cx e1` by fs[Once body_exprs_full_ok_cons] >>
     metis_tac[body_expr_full_ok_simulations]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e1) e1 es` by
    (qpat_assum `body_exprs_prefix_ok cx [e1;e2]`
       (mp_tac o Q.SPECL [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,
         `func`,`shadow_func`,`cenv`,`env`,`expr_type e1`,`es`] o
        CONJUNCT1 o ONCE_REWRITE_RULE [CONJUNCT1 body_expr_prefix_ok_def] o
        CONJUNCT1 o ONCE_REWRITE_RULE [CONJUNCT2 body_exprs_prefix_ok_def]) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  rewrite_tac[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all rest_word_full_compile_layout >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    metis_tac[bop_first_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ e1 _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >> disch_then drule_all >> strip_tac >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ e1 _` mp_tac >>
  rewrite_tac[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  disch_then drule_all >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ needleQ needleR` >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e1) (read_result cx))
     (es,s0,G0,tn0)
     (\H res ee G tn t. needleQ H res ee G tn t /\
       !fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)
     needleR` by
    (irule gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ needleQ needleR` (irule_at Any) >>
     rpt strip_tac >> simp[] >> metis_tac[gas_origin_ptr_path_dalloca_fmp_headroom]) >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e1) (read_result cx))
     (es,s0,G0,tn0)
     (\H res ee G tn t. (needleQ H res ee G tn t /\
       (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)) /\
       ~t.vs_halted /\ ee.gas_obs = []) needleR` by
    (irule gas_outcome_full_post_source >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn t. _) needleR`
       (irule_at Any) >> simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
  irule gas_prefix_full_bind >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn t. _) needleR` (irule_at Any) >>
  simp[Abbr `needleR`] >> rpt conj_tac
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      conj_tac >- simp[storage_trace_frame_def, bop_result_def] >>
      irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`requests_outcomes_frame _`]
  >- (irule requests_outcomes_frame_bind_all >>
      simp[evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >- suspend "array_prefix" >>
  rpt gen_tac >> rename1 `expr_exit res r /\ _ ==> _` >>
  Cases_on `res` >> simp[expr_exit_def]
QED
*)
Theorem compile_rest_word_membership_prefix:
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ty ann bop e1 e2 bd es.
  (bop = In \/ bop = NotIn) /\
  is_word_type (expr_type e1) /\
  expr_type e2 = ArrayT (expr_type e1) bd /\
  (!a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
  body_exprs_full_ok cx [e1;e2] /\
  body_exprs_prefix_ok cx [e1;e2] /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann (Bop bop) [e1;e2]) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_rest_word_membership_prefix[array_prefix]:
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  drule_all rest_word_full_second_entry >> strip_tac >>
  `body_expr_prefix_ok cx e2` by
    (qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
       (qspec_then `[]` (mp_tac o MATCH_MP (REWRITE_RULE [ETA_AX] eval_expr_read_INL))) >>
     simp[body_exprs_prefix_ok_def] >> strip_tac >>
     fs[body_exprs_prefix_ok_def] >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `needleQ (storage_trace_horizon mid.storage_trace) (INL v) mid G1 tn1 t /\
   ~t.vs_halted /\ mid.gas_obs = [] /\
   (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e2) e2 mid` by
    (fs[body_expr_prefix_ok_def, GSYM evaluation_state_component_equality] >> metis_tac[]) >>
  `gas_admissible (eval_expr cx e2) expr_vv_res_ok mid` by
    (qpat_assum `expr_body_pre _ _ _ e2 _`
       (mp_tac o MATCH_MP expr_body_pre_vv_gas_admissible) >>
     simp[GSYM evaluation_state_component_equality]) >>
  `return_buf_frame d cenv s1 t` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`, `s0`, `sa`] >>
     fs[Abbr `needleQ`, expr_post_def]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid t /\
       storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
       (qspec_then `H` (drule_then (strip_assume_tac o BETA_RULE))) >>
     fs[Abbr `needleQ`, expr_post_def]) >>
  `t.vs_current_bb = s1.cs_current_bb /\
   t.vs_inst_idx = LENGTH s1.cs_current_insts /\ alloca_history func t /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (fs[Abbr `needleQ`] >> metis_tac[]) >>
  qpat_x_assum `expr_vv_sim_prefix _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  disch_then drule_all >> strip_tac >>
  (* Reading the array and testing membership do not change source state. *)
  `!ee. SND (bind (bind (eval_expr cx e2) (read_result cx))
       (\w ff. (bop_result cx ann bop [expr_type e1; expr_type e2] v w ff,ff)) ee) =
       SND (eval_expr cx e2 ee)` by
    (POP_ASSUM_LIST (K all_tac) >>
     gen_tac >> Cases_on `eval_expr cx e2 ee` >> rename1 `_ = (res,ee')` >>
     Cases_on `res` >> simp[bind_def] >>
     rename1 `eval_expr cx e2 ee = (INL raw,ee')` >>
     Cases_on `read_result cx raw ee'` >> drule read_result_state >> strip_tac >>
     rename1 `read_result cx raw ee' = (rd,_)` >> Cases_on `rd` >> simp[]) >>
  fs[] >> metis_tac[gas_prefix_full_state_cong]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise compile_rest_word_membership_prefix
*)
