(* get_place changes the source result, not the compiled interval. *)
Theory entryCreateTargetGetPlace
Ancestors
  bodyFullTargetDefs bodyFullTargetSubscript bodyPtrPopTargetFragTransport
  targetLocalLive targetPlaceSim targetPlaceSimCases targetPlaceSimDefs
  entryCreateFocusSpec entryCreateBodyCut entryCreateCompletedCut
  gasContext gasStorage gasExemptCert gasSummaryCompose vyperStorageTrace
  vyperStorageFootprint vyperState exprSimDefs venomExecSemantics fragExec list

Theorem target_get_place_base_admissible[local]:
  gas_admissible (bind (eval_base_place cx bt) get_place) target_place_res_ok es ==>
  gas_admissible (eval_base_place cx bt) target_res_ok es
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then `gs` mp_tac) >> Cases_on `res` >>
  simp[bind_def, target_res_ok_def, target_place_res_ok_def]
QED

Theorem target_get_place_selected[local]:
  target_pre cenv cx env bt es /\ type_place_target env bt = SOME vt /\
  gas_admissible (bind (eval_base_place cx bt) get_place) target_place_res_ok es /\
  eval_base_place cx bt (es with gas_obs := gs) = (INL pv,ee) ==>
  ?p. pv = PlaceR p /\
      (!id path. p = MemoryPlace id path ==>
        ?entry v. lookup_scopes id ee.scopes = SOME entry /\
                  evaluate_subscripts entry.type entry.value path = INL v)
Proof
  strip_tac >>
  `?p. pv = PlaceR p` by
    (Cases_on `pv` >> simp[] >>
     qpat_x_assum `gas_admissible _ _ _`
       (qspec_then `gs` mp_tac o REWRITE_RULE[gas_admissible_def]) >>
     simp[bind_def,get_place_def,raise_def,target_place_res_ok_def]) >>
  gvs[] >> rpt strip_tac >> gvs[] >>
  `target_root bt = NameTarget id` by metis_tac[target_base_memory_root_ptr] >>
  `target_pre cenv cx env bt (es with gas_obs := gs)` by fs[target_pre_def] >>
  drule_all local_base_place_live >> simp[]
QED

(* Leave the completed base path, marks and ghosts unchanged: the source
   continuation is a return at that same exit. Left focus/abort need no
   continuation witness. *)
Theorem scoped_get_place[local]:
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sa sb
    (eval_base_place cx bt) (es,s,G,tn) Q (create_operand_exit_post ctx cx) /\
  target_pre cenv cx env bt es /\ type_place_target env bt = SOME vt /\
  gas_admissible (bind (eval_base_place cx bt) get_place) target_place_res_ok es /\
  (!H res ee G' tn' t. Q H res ee G' tn' t ==> ?pv. res = INL pv) /\
  (!H p ee G' tn' t. Q H (INL (PlaceR p)) ee G' tn' t /\
     (!id path. p = MemoryPlace id path ==>
       ?entry v. lookup_scopes id ee.scopes = SOME entry /\
                 evaluate_subscripts entry.type entry.value path = INL v) ==>
     P H (INL p) ee G' tn' t) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sa sb
    (bind (eval_base_place cx bt) get_place) (es,s,G,tn) P
    (create_operand_exit_post ctx cx)
Proof
  strip_tac >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE[scoped_operand_outcome_def]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks`
  >- (disj1_tac >> conj_tac
      >- (irule gas_bad_storage_at_bind_left >> simp[storage_trace_frame_get_place]) >>
      metis_tac[])
  >- (`valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
        by fs[storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` drule >> strip_tac
      >- (rename1 `Q _ res _ _ _ t` >>
          `?pv. res = INL pv` by metis_tac[] >> gvs[] >>
          `eval_base_place cx bt (es with gas_obs := gas_explicit marks s.vs_gas_readings) =
             (INL pv,ee with gas_obs := [])` by metis_tac[APPEND_NIL] >>
          drule_all target_get_place_selected >> strip_tac >> gvs[] >>
          disj2_tac >> disj1_tac >> qexistsl_tac [`INL p`,`ee`,`OK t`,`G'`,`tn'`] >>
          simp[] >> conj_tac >- simp[bind_def,get_place_def,return_def] >>
          rpt strip_tac >> res_tac >> gvs[exit_result_def] >> metis_tac[]) >>
      `?exc. res = INR exc` by (Cases_on `res` >> fs[create_operand_exit_post_def]) >> gvs[] >>
      disj2_tac >> disj1_tac >> qexistsl_tac [`INR exc`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> conj_tac >- simp[bind_def] >>
      rpt strip_tac >> res_tac >> gvs[create_operand_exit_post_def,halt_exit_def] >>
      metis_tac[expr_exit_INR_retype]) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  simp[] >> conj_tac
  >- (simp[ignore_bind_def,bind_assoc] >> irule gas_exempt_cert_error_result >>
      simp[ignore_bind_def]) >>
  metis_tac[]
QED

Theorem target_exit_post_eq[local]:
  create_operand_exit_post ctx cx =
    (\H res ee gt q. expr_exit res q /\ halt_exit H cx ee res q /\
      (ctx_has_dalloca ctx ==> !s. q = Halt s ==> allocas_below_fmp s))
Proof
  simp[FUN_EQ_THM,create_operand_exit_post_def]
QED

Theorem create_target_get_place_from_base:
  target_sim_judgment scoped_operand_outcome
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx env bt es /\
  target_pre cenv cx env bt es /\
  type_place_target env bt = SOME (Type ty) /\
  compile_get_target_ptr compile_expr cenv bt sa = (r,sb) /\
  compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
    (gas_shadow_target bt) shadow_sa = (r,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
  create_operand_at sa s0 /\
  create_operand_cut sa sb (gas_explicit_sites ctx shadow_ctx) ctx func (cx_tops cx)
    cx st0 (eval_base_place cx bt) (es,s0) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa sb (eval_target_place cx bt) (es,s0,G0,tn0)
    (\H res ee G tn t. ?p. res = INL p /\
      target_post H ctx func cenv cx es sa sb s0 ee (PlaceR p) (Type ty) r t /\
      (!id path. p = MemoryPlace id path ==>
        ?entry v. lookup_scopes id ee.scopes = SOME entry /\
                  evaluate_subscripts entry.type entry.value path = INL v) /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      target_ptr_ok cenv (PlaceR p) r G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sb (gas_explicit_sites ctx shadow_ctx) ctx func (cx_tops cx)
    cx st0 (eval_target_place cx bt) (es,s0)
Proof
  simp[eval_target_place_as_bind,create_operand_at_def] >> strip_tac >>
  reverse conj_tac
  >- (fs[create_operand_cut_def] >> rpt strip_tac >>
      irule create_cut_bind_left >> simp[storage_trace_frame_get_place] >>
      first_x_assum drule >> simp[]) >>
  drule_then assume_tac target_get_place_base_admissible >>
  qpat_x_assum `target_sim_judgment _ _ _ _ _ _ _`
    (assume_tac o REWRITE_RULE[target_sim_judgment_def]) >>
  first_x_assum drule_all >> strip_tac >>
  irule scoped_get_place >>
  qpat_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (irule_at Any o REWRITE_RULE[GSYM target_exit_post_eq]) >>
  simp[] >> metis_tac[]
QED
