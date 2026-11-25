(* A copying head consumes the chosen VV return, then executes a zero-mark
   materializer at that very cursor. Its stopped child branches do not copy. *)
Theory entryCreateCtorCopyAdapter
Ancestors
  bodyFullCreateHeld entryCreateScopedBind entryCreatePendingScope
  createSizeConcreteSnapshots allocaSiteResource bodyPtrBopHashFootprint
  vyperEvalExprPreservesScopesDom exprSimMemorySource
  stmtSimDefs stateRelProj fragGasOriginPtrExec entryCreateFocusSpec
  entryCreateCompletedCut entryCreatePathScope entryCreateOperandReplay
  createSizeCutCode createSizeCutRegion compileEnv exprLowering exprLoweringProps
  loweringPosts loweringStateRelDefs bodyPtrDefs exprSimMemDefs arithmetic
  vyperState vyperInterpreter vyperStorageTrace vyperStorageFootprint gasSummary
  gasExemptCert gasExplicitSites s1PrefixDefs fragExec context list
(* The fixed-child read supplies the pointer packet at its actual endpoint. *)
Definition copied_head_materialized_def:
  copied_head_materialized (DF,lo,d,ctx,func) cenv cx e
    (es,sa,sm,sb,op,s0,G0,tn0) H v ee G tn t <=>
    stmt_state_rel H ctx func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    ptr_val_ok cx (lowered_value_type cenv e) v op G tn t /\
    ptr_mem_ok cx (lowered_value_type cenv e) v op G tn t /\
    ptr_buf_ok cenv e op G t /\
    create_operand_at sb t /\ ~t.vs_halted /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    return_buf_frame d cenv sb t /\ wb_frame cenv es ee sa s0 t /\
    (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
    (~expr_has_effect e ==>
      (ee with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) =
      (es with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>)) /\
    (?x w tv. op = Var x /\ eval_operand op t = SOME w /\
      evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\ val_wf tv v /\
      FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
      sm.cs_next_id < sb.cs_next_id /\
      (!n b len. local_region cenv ee.scopes t n b len ==>
        regions_disjoint (w2n w) (type_memory_size tv) b len))
End

Definition copied_head_post_def:
  copied_head_post (DF,lo,d,ctx,func) cenv cx e
    (es,sa,sm,sb,sv,s0,G0,tn0) H res ee G tn t <=>
    ?v. res = INL v /\
      (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
           p.ptr_location = LocMemory /\ ~is_word_type (lowered_value_type cenv e)) /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
        vv_at cenv cx (lowered_value_type cenv e) sa sb ee raw sv t /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
        vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\ ptr_buf_ok cenv e (vv_operand sv) G t /\
      (?x w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var x /\
        eval_operand (vv_operand sv) t = SOME w /\
        evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\ val_wf tv v /\
        FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
        sm.cs_next_id < sb.cs_next_id /\
        (!n b len. local_region cenv ee.scopes t n b len ==>
          regions_disjoint (w2n w) (type_memory_size tv) b len)) /\
      stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      wb_frame cenv es ee sa s0 t /\ MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
      (~expr_has_effect e ==>
       (ee with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) =
       (es with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>))
End

Theorem copied_head_snapshot_post[local]:
  sa.cs_next_id <= sm.cs_next_id /\
  ~is_word_type (lowered_value_type cenv e) /\ MAP FDOM ee.scopes = MAP FDOM es.scopes /\
  sv = LocatedValue (lowered_value_type cenv e) (mk_ptr op LocMemory) /\
  copied_head_materialized (DF,lo,d,ctx,func) cenv cx e
    (es,sa,sm,sb,op,s0,G0,tn0) H v ee G tn t ==>
  copied_head_post (DF,lo,d,ctx,func) cenv cx e
    (es,sa,sm,sb,sv,s0,G0,tn0) H (INL v) ee G tn t
Proof
  simp[copied_head_materialized_def, copied_head_post_def, create_operand_at_def] >>
  strip_tac >> gvs[vv_location_def, vv_operand_def, mk_ptr_def, vv_storage_live_def] >>
  conj_tac
  >- (qexists `Value v` >>
      `w2n w + type_memory_size tv <= t.vs_alloca_next` by
        (irule alloca_site_registered_below >> conj_tac
         >- (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
         qexists `sm.cs_next_id` >> simp[]) >>
      `val_in_memory tv v (w2n w) t.vs_memory` by
        (drule_all ptr_mem_ok_representation >> simp[]) >>
      fs[ptr_val_ok_def] >>
      simp[read_result_def, return_def, vv_holds_def, vv_at_def,
        ptr_vv_ok_def, vv_store_bound_def] >>
      conj_tac
      >- (disj1_tac >> qexistsl [`sm.cs_next_id`,`w2n w`,`type_memory_size tv`] >>
          simp[exprSimPropsTheory.val_footprint_le] >>
          fs[regions_disjoint_def, ADD_COMM]) >>
      drule exprSimPropsTheory.val_store_size_le >> decide_tac) >>
  metis_tac[]
QED

(* This law is intentionally about the administrative part only: the state,
   VV, source trace and ghosts are supplied by the normal child branch. *)
Definition copied_head_read_law_def:
  copied_head_read_law (DF,lo,d,E,ctx,func,PG) cenv cx e st0
    (es,sa,sm,sb,vv,op,s0,G0,tn0) <=>
  !marks tv ee G1 tn1 s.
    (!tail. eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL tv,ee with gas_obs := tail)) /\
    storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
    create_operand_at sm s /\ ~s.vs_halted /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       create_operand_vv_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sm,s0,vv,G0,tn0)
         H (INL tv : eval_result + exception) ee G1 tn1 s) ==>
    ?v u Gf tm.
      read_result cx tv ee = (INL v,ee) /\ create_expr_prefix sm sb E ctx func s [] u /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (s,G1,tn1) [] (OK u,Gf,tm) /\
        copied_head_materialized (DF,lo,d,ctx,func) cenv cx e
                    (es,sa,sm,sb,op,s0,G0,tn0) H v ee Gf tm u)
End

Theorem copied_head_read_scope[local]:
  copied_head_read_law (DF,lo,d,E,ctx,func,PG) cenv cx e st0
    (es,sa,sm,sb,vv,op,s0,G0,tn0) /\
  sa.cs_next_id <= sm.cs_next_id /\
  ~is_word_type (lowered_value_type cenv e) /\
  sv = LocatedValue (lowered_value_type cenv e) (mk_ptr op LocMemory) /\
  (!tail. eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (res,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
  create_operand_at sm s /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     create_operand_vv_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sm,s0,vv,G0,tn0)
       H res ee G1 tn1 s /\
     gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (s0,G0,tn0) marks (OK s,G1,tn1)) ==>
  ?tv. res = INL tv /\ scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sm sb
    (read_result cx tv) (ee,s,G1,tn1)
    (copied_head_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sm,sb,sv,s0,G0,tn0)) R
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `?tv. res = INL tv` by (res_tac >> fs[create_operand_vv_post_def]) >> gvs[] >>
  `~s.vs_halted` by (res_tac >> drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  qpat_x_assum `copied_head_read_law _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [copied_head_read_law_def]) >>
  disch_then (qspecl_then [`marks`,`tv`,`ee`,`G1`,`tn1`,`s`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  `create_operand_at sb u` by (res_tac >> fs[copied_head_materialized_def]) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` (mp_tac o SIMP_RULE bool_ss [APPEND_NIL])) >>
     asm_rewrite_tac[] >> strip_tac >> drule eval_expr_preserves_scopes_dom >> simp[]) >>
  simp[scoped_operand_outcome_def] >> qexists `[]` >>
  disj2_tac >> disj1_tac >> qexistsl [`INL v`,`ee`,`OK u`,`Gf`,`tm`] >>
  simp[create_operand_full_scope_def, GSYM create_operand_at_def, read_result_gas_obs] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
  disj1_tac >> irule copied_head_snapshot_post >> simp[] >> qexists `op` >> simp[]
QED

Theorem copied_head_exit_post_transport[local]:
  (\H (res : eval_result + exception) ee gt r.
      (?exc. res = INR exc) /\ create_operand_exit_post ctx cx H res ee gt r) =
  (\H res ee gt r. ?exc. res = INR exc /\
      create_operand_exit_post ctx cx H (INR exc : value + exception) ee gt r)
Proof
  simp[FUN_EQ_THM] >> rpt gen_tac >> Cases_on `res` >>
  simp[create_operand_exit_post_def, exprSimDefsTheory.halt_exit_def] >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED

(* Keep the ordinary child scope and code parameters; only a successful VV
   return consults the materializer law. *)
Theorem create_ctor_copied_head_of_materialized_read:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  ~is_word_type (expr_type e) /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx (expr_type e) e es
    (st0,sa,sm,sha,shm,vv,s0,G0,tn0) /\
  compile_snapshot_vv cenv T (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,sb) /\
  fn_has_code sm sb func /\
  (!u. create_cut_region sa sm u /\ ~create_operand_at sm u ==> ~create_operand_at sb u) /\
  (!bb i. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sb.cs_current_insts) = SOME i ==> i.inst_id NOTIN frag_ids sa sm) /\
  (expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx (expr_type e) e es
    (st0,sa,sm,sha,shm,vv,s0,G0,tn0) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
      (cx_tops cx) cx st0 sa sm (eval_expr cx e) (es,s0,G0,tn0)
      (create_operand_vv_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sm,s0,vv,G0,tn0))
      (\H res ee gt r. (?exc. res = INR exc) /\ create_operand_exit_post ctx cx H res ee gt r)) /\
  (!op. compile_materialize_vv cenv (lowered_value_type cenv e) vv sm = (op,sb) ==>
    copied_head_read_law (DF,lo,d,gas_explicit_sites ctx shctx,ctx,func,PG) cenv cx e st0
      (es,sa,sm,sb,vv,op,s0,G0,tn0)) /\
  (!D lo E C f PG tops cx st0 a m b es s G tn Q1 Q R
    (source : evaluation_state -> (eval_result + exception) # evaluation_state)
    (next : eval_result -> evaluation_state -> (value + exception) # evaluation_state).
     scoped_operand_outcome (D,lo,E,C,f,PG) tops cx st0 a m source (es,s,G,tn)
       Q1 (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
     (!marks res mid G1 tn1 t.
        (!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
                 (res, mid with gas_obs := tail)) /\
        storage_trace_domain cx st0 mid.storage_trace /\ create_operand_at m t /\
        create_operand_full_scope a m E C f s marks (OK t) /\
        (!H. valid_horizon cx st0 H mid.storage_trace ==>
             Q1 H res mid G1 tn1 t /\ gas_origin_ptr_path (D H,lo,E,C,f,PG)
                (s,G,tn) marks (OK t,G1,tn1)) ==>
        ?v. res = INL v /\ scoped_operand_outcome (D,lo,E,C,f,PG) tops cx st0 m b
               (next v) (mid,t,G1,tn1) Q R) /\
     storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
     (!marks err ee leaf finish.
        gas_exempt_cert T tops (C,f) (ignore_bind source (return ()))
          (es,s) marks (err,ee) (leaf,finish) ==>
        gas_exempt_cert T tops (C,f) (ignore_bind (bind source next) (return ()))
          (es,s) marks (err,ee) (leaf,finish)) /\
     (!left v mid t right err ee leaf finish.
        gas_marked_exec T (C,f) source (es,s) left (INL v) mid (OK t) /\
        gas_exempt_cert T tops (C,f) (ignore_bind (next v) (return ()))
          (mid with gas_obs := [],t) right (err,ee) (leaf,finish) ==>
        gas_exempt_cert T tops (C,f) (ignore_bind (bind source next) (return ()))
          (es,s) (left ++ right) (err,ee) (leaf,finish)) /\
     (!marks. create_operand_focus_scope a m E C f s marks ==>
              create_operand_focus_scope a b E C f s marks) /\
     (!marks r. exit_result r /\ create_operand_full_scope a m E C f s marks r ==>
                create_operand_full_scope a b E C f s marks r) /\
     (!left t right. create_operand_full_scope a m E C f s left (OK t) /\
                     create_operand_focus_scope m b E C f t right ==>
                     create_operand_focus_scope a b E C f s (left ++ right)) /\
     (!left t right r. create_operand_full_scope a m E C f s left (OK t) /\
                       create_operand_full_scope m b E C f t right r ==>
                       create_operand_full_scope a b E C f s (left ++ right) r) ==>
     scoped_operand_outcome (D,lo,E,C,f,PG) tops cx st0 a b
       (bind source next) (es,s,G,tn) Q R) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa sb (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (copied_head_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sm,sb,sv,s0,G0,tn0))
    (create_operand_exit_post ctx cx)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (mp_then Any assume_tac operand_vv_cut_code) >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
  drule_all create_ctor_snapshot_retag >> strip_tac >>
  `~is_word_type (lowered_value_type cenv e)` by metis_tac[] >>
  `?op. compile_materialize_vv cenv (lowered_value_type cenv e) vv sm = (op,sb) /\
        sv = LocatedValue (lowered_value_type cenv e) (mk_ptr op LocMemory)` by
    (Cases_on `compile_materialize_vv cenv (lowered_value_type cenv e) vv sm` >>
     gvs[compile_snapshot_vv_def, comp_bind_def, comp_return_def, mk_ptr_def]) >>
  `create_cut_code {} sm sb` by
    (`sb = SND (compile_snapshot_vv cenv T (ext_call_arg_value (lowered_value_type cenv e) vv) sm)` by simp[] >>
     pop_assum SUBST1_TAC >> simp[create_vv_snapshot_cut_code]) >>
  `sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id` by
    fs[create_cut_code_def] >>
  `create_cut_region sa sm s0` by
    (irule (cj 1 create_cut_region_rules) >> simp[] >> metis_tac[]) >>
  qabbrev_tac `E = gas_explicit_sites ctx shctx` >>
  `!p chunk q. create_prefix_step sa sm E ctx func p chunk q ==>
      create_prefix_step sa sb E ctx func p chunk q` by
    (rpt strip_tac >> irule create_prefix_step_lift >> qexistsl [`sa`,`sm`] >> simp[]) >>
  `copied_head_read_law (DF,lo,d,E,ctx,func,PG) cenv cx e st0
       (es,sa,sm,sb,vv,op,s0,G0,tn0)` by metis_tac[] >>
  qpat_x_assum `!D lo E C f PG tops cx st0 a m b es s G tn Q1 Q R source next. _`
    (irule o SPEC_ALL) >>
  simp[evaluate_storage_trace_frame, storage_trace_frame_read_result,
       ignore_bind_def, bind_assoc] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`] >-
    (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
     qexistsl [`mid`,`t`,`v`] >> fs[ignore_bind_def])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`] >-
    (rpt strip_tac >> irule gas_exempt_cert_error_result >> simp[ignore_bind_def]) >>
  qexistsl [`\H res ee G1 tn1 t.
    create_operand_vv_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sm,s0,vv,G0,tn0)
      H res ee G1 tn1 t /\ ee.gas_obs = []`,`sm`] >> simp[] >>
  rpt conj_tac
  >- (rpt strip_tac >> irule create_operand_full_scope_lift_terminal >>
      qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
      qpat_assum `create_operand_full_scope _ _ _ _ _ _ _ _` (irule_at Any) >>
      fs[create_operand_at_def])
  >- (rpt strip_tac >> irule copied_head_read_scope >>
      qpat_assum `copied_head_read_law _ _ _ _ _ _` (irule_at Any) >> simp[] >>
      rename1 `storage_trace_domain cx st0 ee.storage_trace` >>
      `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
        fs[storage_trace_domain_def] >> metis_tac[])
  >- (rpt strip_tac >> irule create_operand_full_scope_prepend >>
      qpat_assum `create_operand_full_scope sm sb _ _ _ _ _ _` (irule_at Any) >> simp[])
  >- (rpt strip_tac >> irule create_operand_focus_scope_join >>
      qpat_assum `create_operand_focus_scope sm sb _ _ _ _ _` (irule_at Any) >>
      qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
      fs[create_operand_full_scope_def] >>
      drule_all create_cut_region_rules >> simp[])
  >- (rpt strip_tac >> irule create_operand_focus_scope_lift >>
      qpat_assum `create_operand_focus_scope sa sm _ _ _ _ _` (irule_at Any) >>
      qpat_assum `body_inv _ _ _ _` (irule_at Any) >> fs[create_operand_at_def]) >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _ ==> _` drule >>
  disch_then (mp_tac o ONCE_REWRITE_RULE [copied_head_exit_post_transport]) >>
  simp[scoped_operand_outcome_def]
QED
