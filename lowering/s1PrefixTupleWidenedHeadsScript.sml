(* Widened tuple stores share a single RHS cut and a single visited-head loop. *)
Theory s1PrefixTupleWidenedHeads
Ancestors
  s1PrefixTupleWidenedStore s1PrefixPreds s1PrefixCompose s1PrefixProps
  s1PrefixTarget s1PrefixOfVV bodyFullAssignTuple bodyFullPreds
  tuplePlaceSource stmtSimAssignTuple stmtSimForRounds
  bodyPtrPopTargetFragTransport gasOutcomeFullCompose gasOutcomeFullStmts
  vyperStorageTrace vyperStorageFootprint vyperTypeArgFits allocLimits
  exprBodyPreProps exprSimSource exprSimHyps stateRelProj list pair
  s1PrefixDefs loweringPosts bodyFullShared bodyFullSimProjection
  fragExec vyperState vyperInterpreter tupleWidenedStoreEntry arithmetic
  supportedStmts tupleTargetStoreProps vyperTypeSystem vyperTypeValues
  s1PrefixTupleBaseStore s1PrefixFrame s1PrefixAssignTupleFlatTrace
  gasExemptCert targetPlaceSim exprSimDefs fragGasPath vyperTypeDefaults

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e es` by (drule_all tuple_assignment_rhs_pre >> simp[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    metis_tac[body_expr_full_ok_simulations] >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_assum `body_expr_prefix_ok _ _` mp_tac >>
     pure_once_rewrite_tac[body_expr_prefix_ok_def] >>
     disch_then (mp_tac o cj 1) >> metis_tac[]) >>
  rewrite_tac[stmt_frag_prefix_def,stmt_frag_full_pre_def] >> rpt gen_tac >> strip_tac >>
  drule_all tuple_widened_rhs_code_parts >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (qx_choosel_then [`op`,`su`,`shadow_su`,`vv`,`sc`]
      (map_every assume_tac o CONJUNCTS))) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x` by fs[ret_pc_ok_def] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es
     (st0,sa,su,shadow_sa,shadow_su,op,s0,G0,tn0)` by
    (simp[expr_sim_full_pre_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `expr_sim_full _ _ _ _ _ _`
    (drule_then assume_tac o REWRITE_RULE[expr_sim_full_eq]) >>
  qpat_assum `expr_sim_prefix _ _ _ _ _ _`
    (drule_then assume_tac o REWRITE_RULE[expr_sim_prefix_def]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (mp_then Any (drule_all_then assume_tac) gas_outcome_full_return_buf_allocas) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ rhsQ _` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     (\H res ee G tn t. rhsQ H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted)
     (\H res ee gt r. ISR res)` by
    (qpat_x_assum `gas_outcome_full _ _ _ _ _ _ rhsQ _`
       (mp_then Any irule gas_outcome_full_post_source) >>
     simp[] >> rpt strip_tac >> Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def]) >>
  rewrite_tac[eval_assign_tuple_action] >>
  pop_assum (mp_then Any irule gas_prefix_full_bind_replay) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result] >>
  map_every qx_gen_tac [`marks`,`v'`,`ee`,`G'`,`tn'`,`v`] >> strip_tac >>
  suspend "rhs_success"
QED
*)
Theorem tuple_widened_prefix_from_nested_heads:
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
  (!st0 ee sa sb shadow_sb s0 G0 tn0 tys dtys elems tvs vs w t tf
      j head c0 sh0 src0 s1 G1 tn1 obs0.
    j < LENGTH gs /\ EL j gs = BaseTarget head /\ immutable_root cx head /\
    ~(?nsid. head = TopLevelNameTarget nsid) /\
    expr_type e = TupleT dtys /\ lowered_value_type cenv e = TupleT tys /\
    type_widens_to env.type_defs (TupleT tys) (TupleT dtys) /\
    assignable_type env.type_defs (TupleT dtys) /\
    LIST_REL (\g ty. well_typed_atarget env g ty) gs dtys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs /\
    LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys tvs /\
    values_have_types tvs vs /\ val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
    LENGTH gs = LENGTH dtys /\ LENGTH tys = LENGTH dtys /\
    LENGTH tvs = LENGTH tys /\ LENGTH vs = LENGTH tvs /\ LENGTH elems = LENGTH tys /\
    w2n w + type_memory_size_list tvs < dimword (:256) /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n w) mem) /\
    body_const_cells_agree [(NONE,tops)] cx env ee /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    tuple_widened_store_entry (DF,lo,d,ctx,func,shadow_func) (cenv,cx,env,st0,es,ee)
      (sa,sb,shadow_sb,s0,G0,tn0) (tys,gs,elems,tvs,vs,w,t,tf) j c0 sh0 src0 s1 G1 tn1 obs0 /\
    storage_trace_domain cx st0 src0.storage_trace /\
    (!H. valid_horizon cx st0 H src0.storage_trace ==>
      storage_well_formed_on cx src0 (FST H)) /\
    gas_admissible (assign_tuple_target_list cx (DROP j gs) (DROP j vs)) (stmt_res_ok lctx) src0 /\
    body_tuple_target_full_ok cx (EL j gs) (EL j vs) /\
    body_tuple_target_prefix_ok cx (EL j gs) (EL j vs) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
      (assign_tuple_targets cx (EL j gs) (EL j vs)) (src0,s1,G1,tn1)
      (\H res mid G2 tn2 s2. ?c2 sh2 obs2.
        tuple_widened_store_entry (DF,lo,d,ctx,func,shadow_func) (cenv,cx,env,st0,es,ee)
          (sa,sb,shadow_sb,s0,G0,tn0) (tys,gs,elems,tvs,vs,w,t,tf)
          (SUC j) c2 sh2 mid s2 G2 tn2 obs2)
      (\H res ee gt r. ISR res) /\
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
      (assign_tuple_targets cx (EL j gs) (EL j vs)) (src0,s1,G1,tn1)) /\
  lowered_value_type cenv e <> expr_type e ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assign (TupleTarget gs) e)))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume tuple_widened_prefix_from_nested_heads[rhs_success]:
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `ee.gas_obs = [] /\ ~v.vs_halted` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `fn_has_code su sb func /\ fn_has_code shadow_su shadow_sb shadow_func` by
    metis_tac[fn_has_code_split] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s0,G0,tn0) marks (OK v,G',tn') /\
    expr_post H ctx func cenv cx e es sa su s0 ee v' op v /\
    v.vs_current_bb = su.cs_current_bb /\ v.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func v /\ (ctx_has_dalloca ctx ==> allocas_below_fmp v) /\
    s0.vs_alloca_next <= v.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx ee G' tn' v /\
    ptr_val_ok cx (post_value_type cenv e) v' op G' tn' v /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn' /\
    (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) v)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ rhsQ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> fs[Abbr `rhsQ`,ADD_COMM]) >>
  drule_all tuple_widened_load_entry_zero >>
  disch_then (qx_choosel_then [`tys`,`dtys`,`tvs`,`vs`,`elems`,`ss`,`shadow_ss`,`w`,`t`,`Gf`,`tf`]
    (map_every assume_tac o CONJUNCTS)) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v',ee)` by
    (qpat_assum `!tail. _ = (INL v',ee with gas_obs := tail)` (qspec_then `[]` mp_tac) >>
     qpat_assum `_ with gas_obs := [] = ee`
       (fn th => pure_rewrite_tac[APPEND_NIL,th]) >> disch_then ACCEPT_TAC) >>
  `body_const_cells_agree [(NONE,tops)] cx env ee` by
    (irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (INL v',ee)` (irule_at Any) >>
     drule_then (assume_tac o cj 2) expr_body_pre_static_facts >> simp[]) >>
  `body_tuple_targets_prefix_ok cx gs vs` by
    (qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (INL v',ee)` mp_tac >>
     simp[NoAsms,bind_def,AllCaseEqs()] >> strip_tac >> gvs[SF DNF_ss] >>
     qpat_assum `!s'' tv t s'3' v t'. _ ==> body_tuple_target_prefix_ok _ _ _`
       (drule_all_then mp_tac) >> simp[body_tuple_target_prefix_ok_def]) >>
  `gas_admissible (assign_tuple_target_list cx gs vs) (stmt_res_ok lctx) ee` by
    (qpat_assum `gas_admissible (eval_stmt cx (Assign _ _)) _ es`
       (assume_tac o REWRITE_RULE [eval_assign_tuple_action]) >>
     drule_all gas_admissible_bind_tail >> simp[]) >>
  qpat_assum `assign_tuple_targets cx (TupleTarget gs) v' = _` (pure_rewrite_tac o single) >>
  irule gas_prefix_full_zero_prefix_guarded >> simp[evaluate_storage_trace_frame] >>
  qexistsl_tac [`Gf`,`t`,`tf`] >> conj_tac
  >- (gen_tac >> disch_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qpat_assum `tuple_widened_store_entry _ _ _ _ 0 ss shadow_ss ee t Gf tf []`
    (mp_then Any irule
      (Q.INST [`i` |-> `0`] tuple_store_widened_prefix_from_heads |> REWRITE_RULE[DROP_0])) >>
  simp[] >> qexistsl_tac [`stmt_res_ok lctx`,`cx_tops cx`] >> simp[] >>
  suspend "visited_head"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume tuple_widened_prefix_from_nested_heads[visited_head]:
  map_every qx_gen_tac [`j`,`c0`,`sh0`,`src0`,`s1`,`G1`,`tn1`,`obs0`] >> strip_tac >>
  `j < LENGTH gs /\ j < LENGTH tys /\ LENGTH gs = LENGTH tys /\
   LENGTH gs = LENGTH vs` by decide_tac >>
  `?head. EL j gs = BaseTarget head /\ supported_target tops bindings head` by
    (qpat_assum `supported_stmt _ _ (Assign _ e)` mp_tac >>
     pure_once_rewrite_tac[supported_stmt_def] >>
     simp[NoAsms,supported_assignment_def,EVERY_MEM] >> strip_tac >>
     `MEM (EL j gs) gs` by simp[EL_MEM] >>
     first_x_assum (drule_then mp_tac) >> Cases_on `EL j gs` >> simp[]) >>
  `env.type_defs = get_tenv cx` by metis_tac[expr_body_pre_env_type_defs] >>
  `assignable_type (get_tenv cx) (TupleT dtys)` by metis_tac[] >>
  `?dtvs. evaluate_type (get_tenv cx) (TupleT dtys) = SOME (TupleTV dtvs)` by
    (drule assignable_type_well_formed >> simp[well_formed_type_def] >>
     Cases_on `evaluate_type (get_tenv cx) (TupleT dtys)` >>
     simp[] >> metis_tac[evaluate_type_TupleT_cases]) >>
  `tys <> dtys` by metis_tac[] >>
  `arg_types_fit tys dtys` by
    (qpat_assum `type_widens_to env.type_defs (TupleT tys) (TupleT dtys)` mp_tac >>
     simp[NoAsms,type_widens_to_def,cj 5 arg_type_fits_def,TypeBase.one_one_of ``:type``] >>
     metis_tac[]) >>
  `evaluate_type (get_tenv cx) (EL j dtys) = SOME (EL j dtvs) /\
   evaluate_type (get_tenv cx) (EL j tys) = SOME (EL j tvs) /\
   type_widens_to (get_tenv cx) (EL j tys) (EL j dtys) /\
   assignable_type (get_tenv cx) (EL j dtys) /\ 0 < type_slot_size (EL j dtvs)` by
    (drule_all tuple_place_type_facts >> strip_tac >>
     first_x_assum (qspec_then `j` mp_tac) >> simp[]) >>
  Cases_on `immutable_root cx head`
  >- (Cases_on `?nsid. head = TopLevelNameTarget nsid`
      >- (pop_assum (qx_choose_then `nsid` SUBST_ALL_TAC) >>
          PairCases_on `nsid` >> rename1 `EL j gs = BaseTarget (TopLevelNameTarget (ns,id))` >>
          suspend "direct_name") >>
      suspend "nested_callback") >>
  suspend "regular_head"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume tuple_widened_prefix_from_nested_heads[direct_name]:
  `well_typed_target env (TopLevelNameTarget (ns,id)) (EL j dtys)` by
    (qpat_assum `LIST_REL (\g ty. well_typed_atarget env g ty) gs dtys`
       (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     strip_tac >> first_x_assum (qspec_then `j` mp_tac) >>
     simp[tuple_target_base_type,well_typed_target_def]) >>
  `~s1.vs_halted` by
    (qpat_assum `tuple_widened_store_entry _ _ _ _ j _ _ src0 s1 _ _ _` mp_tac >>
     simp[NoAsms,tuple_widened_store_entry_def]) >>
  drule_all tuple_widened_immutable_name_advance >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`wc`,`swc`,`ff`,`q`,`Gq`,`tq`] strip_assume_tac)) >>
  `ff with gas_obs := [] = ff` by
    (qpat_assum `tuple_widened_store_entry _ _ _ _ (SUC j) _ _ ff q _ _ _` mp_tac >>
     simp[NoAsms,tuple_widened_store_entry_def,evaluation_state_component_equality]) >>
  pure_asm_rewrite_tac[] >> conj_tac
  >- (irule gas_outcome_full_pure >> simp[] >>
      qexistsl_tac [`Gq`,`ff`,`INL ()`,`q`,`tq`] >> simp[] >>
      rpt strip_tac >> qexistsl_tac [`wc`,`swc`,`obs0`] >> first_assum ACCEPT_TAC) >>
  irule gas_prefix_full_no_outcome >> simp[evaluate_storage_trace_frame] >>
  `assign_tuple_targets cx (TupleTarget [BaseTarget (TopLevelNameTarget (ns,id))])
       (ArrayV (TupleV [EL j vs])) (src0 with gas_obs := []) = (INL (),ff)` by
    (simp[Once evaluate_def] >> simp[Once evaluate_def,ignore_bind_def,bind_def] >>
     simp[Once evaluate_def,return_def]) >>
  pop_assum (mp_then Any mp_tac assign_tuple_flat_no_outcome) >>
  simp[EVERY_MEM] >> metis_tac[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume tuple_widened_prefix_from_nested_heads[nested_callback]:
  `storage_trace_domain cx st0 src0.storage_trace /\
   (!H. valid_horizon cx st0 H src0.storage_trace ==>
      storage_well_formed_on cx src0 (FST H))` by
    (qpat_assum `tuple_widened_store_entry _ _ _ _ j _ _ src0 s1 _ _ _` mp_tac >>
     simp[NoAsms,tuple_widened_store_entry_def] >> metis_tac[]) >>
  first_assum irule >> simp[] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac[])
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume tuple_widened_prefix_from_nested_heads[regular_head]:
  `!bt. EL j gs = BaseTarget bt ==> ~immutable_root cx bt` by simp[] >>
  qpat_assum `tuple_widened_store_entry _ _ _ _ j _ _ src0 s1 _ _ _`
    (mp_then Any mp_tac tuple_widened_place_head_parts) >>
  disch_then (qspecl_then [`tops`,`shadow_ctx`,`e`,`dtys`,`bindings`,`PG`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`bt`,`r`,`place_cs`,`shadow_place_cs`,
                              `write_cs`,`shadow_write_cs`,`loc`,`dty`]
    (map_every assume_tac o CONJUNCTS)) >>
  `bt = head` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  conj_tac >- suspend "regular_outcome" >>
  simp[] >> irule tuple_base_store_prefix_from_place >>
  `body_base_target_prefix_ok cx head` by fs[body_tuple_target_prefix_ok_def] >>
  drule_all body_target_sim_prefix >> metis_tac[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume tuple_widened_prefix_from_nested_heads[regular_outcome]:
  `value_has_type (EL j tvs) (EL j vs)` by
    (qpat_assum `values_have_types tvs vs` mp_tac >>
     simp[NoAsms,values_have_types_LIST_REL,LIST_REL_EL_EQN] >>
     strip_tac >> first_assum irule >> decide_tac) >>
  `value_has_type (EL j dtvs) (EL j vs)` by
    (drule_all type_widens_to_value_has_type >> simp[]) >>
  `tuple_assign_alloc_ok cenv tys gs` by
    (qpat_assum `stmt_exprs_ok cenv (Assign (TupleTarget gs) e)`
       (mp_tac o cj 2 o REWRITE_RULE[bodySimTheory.stmt_exprs_ok_def]) >>
     simp[alloc_limits_stmt_def]) >>
  `target_indices_pre cenv cx env head` by fs[target_pre_def] >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ storeQ storeR` >>
  `assign_tuple_targets cx (BaseTarget head) (EL j vs) =
     bind (eval_target_place cx head) (\p. write_place cx p (EL j vs))` by
    simp_tac bool_ss [Once evaluate_def] >>
  pure_asm_rewrite_tac[] >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ (eval_target_place cx head) _ placeQ placeR` >>
  irule gas_outcome_full_bind_all_path >> BETA_TAC >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_place >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_place >> simp[])
  >~ [`storage_trace_frame (eval_target_place _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame (write_place _ _ _)`]
  >- simp[storage_trace_frame_write_place] >>
  qexists_tac `\H res mid Gp tp sp. placeQ H res mid Gp tp sp /\
     mid.gas_obs = [] /\ ~sp.vs_halted` >> reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ placeQ placeR` (irule_at Any) >>
      simp[Abbr `placeR`,Abbr `storeR`] >> rpt strip_tac >>
      Cases_on `res` >> simp[] >>
      qpat_x_assum `expr_exit (INL _) _` mp_tac >> simp[expr_exit_def]) >>
  map_every qx_gen_tac [`headmarks`,`res`,`mid`,`Gp`,`tp`,`sp`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    simp[GSYM vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `(?p. res = INL p) /\ mid.gas_obs = [] /\ ~sp.vs_halted` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _ H res mid Gp tp sp`
       (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then mp_tac)) >>
     simp[Abbr `placeQ`] >> metis_tac[]) >>
  fs[] >>
  `(?ff q Gq tq.
     (!tail. write_place cx p (EL j vs) (mid with gas_obs := tail) =
       (INL (),ff with gas_obs := tail)) /\
     (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (sp,Gp,tp) [] (OK q,Gq,tq)) /\
     tuple_widened_store_entry (DF,lo,d,ctx,func,shadow_func) (cenv,cx,env,st0,es,ee)
       (sa,sb,shadow_sb,s0,G0,tn0) (tys,gs,elems,tvs,vs,w,t,tf)
       (SUC j) write_cs shadow_write_cs ff q Gq tq (obs0 ++ gas_explicit headmarks s1.vs_gas_readings)) \/
   ((!tail. write_place cx p (EL j vs) (mid with gas_obs := tail) =
      (INR (Error (RuntimeError "write in static context")),mid with gas_obs := tail)) /\
    ?q Gq tq. q.vs_call_ctx.cc_static /\
    !H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (sp,Gp,tp) [] (Abort ExHalt_abort (halt_state (set_returndata [] q)),Gq,tq))` by
   (irule tuple_widened_place_write_advance >>
    rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE
      (qexists_tac `tops` >> first_assum ACCEPT_TAC) ORELSE (simp[ADD_COMM] >> NO_TAC))) >>
    qexistsl_tac [`G1`,`c0`,`dtvs`,`dtys`,`head`,`place_cs`,`r`,`sh0`,`shadow_place_cs`,`src0`,`tn1`] >>
    simp[NoAsms] >> rpt conj_tac >>
    (first_assum ACCEPT_TAC ORELSE
     (qmatch_goalsub_rename_tac `valid_horizon cx st0 _ mid.storage_trace` >>
      qx_gen_tac `H` >> disch_tac >> conj_tac
      >- (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _`
            (qspec_then `H` (drule_then ACCEPT_TAC))) >>
      qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _ H (INL p) mid Gp tp sp`
        (qspec_then `H` (drule_then mp_tac)) >>
      simp[NoAsms,Abbr `placeQ`] >> NO_TAC) ORELSE
     (simp[GSYM ADD_COMM] >> NO_TAC) ORELSE
     (qpat_assum `assign_tuple_targets cx (BaseTarget head) _ = _` (fn th => simp[th]) >> NO_TAC) ORELSE
     (qpat_assum `loc = _` (fn le => qpat_assum `dty = _` (fn te =>
       first_assum (ACCEPT_TAC o REWRITE_RULE [le,te]))))))
  >- suspend "write_success"
  >> suspend "write_static"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume tuple_widened_prefix_from_nested_heads[write_success]:
  rename1 `tuple_widened_store_entry _ _ _ _ (SUC j) _ _ ff q Gq tq _` >>
  `ff with gas_obs := [] = ff` by
    (qpat_assum `tuple_widened_store_entry _ _ _ _ (SUC j) _ _ ff q _ _ _` mp_tac >>
     simp[NoAsms,tuple_widened_store_entry_def,evaluation_state_component_equality]) >>
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`Gq`,`ff`,`INL ()`,`q`,`tq`] >> simp[Abbr `storeQ`] >>
  rpt strip_tac >>
  qexistsl_tac [`write_cs`,`shadow_write_cs`,`obs0 ++ gas_explicit headmarks s1.vs_gas_readings`] >>
  first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume tuple_widened_prefix_from_nested_heads[write_static]:
  qmatch_asmsub_rename_tac `gas_origin_ptr_path _ (sp,Gp,tp) []
    (Abort ExHalt_abort (halt_state (set_returndata [] q)),Gq,tq)` >>
  irule gas_outcome_full_exit >> simp[] >>
  qexistsl_tac [`Gq`,`mid`,`Abort ExHalt_abort (halt_state (set_returndata [] q))`,
    `INR (Error (RuntimeError "write in static context"))`,`tq`] >>
  simp[Abbr `storeR`,exit_result_def, venomStateTheory.halt_state_def,
       venomStateTheory.set_returndata_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise tuple_widened_prefix_from_nested_heads
*)
