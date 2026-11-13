(* Concrete range round, with schematic names for the explicit consumer
   invariant and done post.  The equations avoid a new invariant definition. *)
Theory forPtrRangeAssemble
Ancestors forPtrRangeFinish forPtrRangePrepare forPtrRangeCallback
  forPtrRangeSource forPtrRangeRound forPtrRoundCleanup forPtrRounds
  gasSummaryComposePtr gasExemptCert stmtSimProps stmtSimForLoop
  bodyPtrDefs loweringPosts compileEnv ptrDiscipline venomState vyperState
  exprSimWordArgs vyperInterpreter stmtFragPtr exprLoweringProps finite_map ghostPcTransportPtr
Libs monadsyntax

Theorem for_range_round_ptr:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  stmt_frag_ptr d ctx PG func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
    (es with <| scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tyv; value := IntV (n1 + &k); popped := []|>))
        :: es.scopes; gas_obs := [] |>) /\
  (!H j ei G tn s.
    Inv H j ei G tn s <=>
    P ei /\ lookup_scopes id ei.scopes = NONE /\ j <= Num (n2-n1) /\
    s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    stmt_state_rel H ctx func cenv cx ei s /\
    storage_well_formed_on cx ei (FST H) /\ ghost_inv H d cenv cx ei G tn s /\
    lookup_var cv s = SOME (i2w (n1 + &j)) /\
    lookup_var ev s = SOME (i2w n2) /\ lookup_var p s = SOME a /\
    FLOOKUP G cv = NONE /\ FLOOKUP G ev = NONE /\
    op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
    ptr_covers G tn p s sz /\
    FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n a,sz) /\
    (!name lo z. local_region cenv ei.scopes s name lo z ==>
      regions_disjoint (w2n a) sz lo z) /\
    (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
      lookup_var x s = SOME v) /\
    (!x. not_fresh_at st x ==> FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x))) /\
  (!H ei G tn t. Done H ei G tn t <=>
    t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    stmt_state_rel H ctx func cenv cx ei t /\
    storage_well_formed_on cx ei (FST H) /\ ghost_inv H d cenv cx ei G tn t /\
    (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
      lookup_var x t = SOME v) /\
    (!x. not_fresh_at st x ==> FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x))) /\
  (!ei j obs r ef sc rest.
    P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2-n1) /\
    eval_stmts cx stmts (ei with <| scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
        value := IntV (n1 + &j); popped := []|>)) :: ei.scopes;
      gas_obs := obs |>) = (r,ef) /\
    (r = INL () \/ r = INR ContinueException) /\ ef.scopes = sc :: rest ==>
    P (ef with scopes := rest)) /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\ ret_pc_ok cenv st s0 /\
  st.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at st x ==> not_fresh_at sb0 x /\ x <> dv /\ x <> cv /\ x <> nv) /\
  (!x q. cenv.ce_return_buf = SOME (PtrVar (Var x) q) ==> not_fresh_at st x) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  LENGTH vs = Num (n2-n1) /\
  (!j. j < LENGTH vs ==> EL j vs = IntV (n1 + &j) /\ (i2w (n1 + &j) : bytes32) <> i2w n2) /\
  k < LENGTH vs /\ (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H k es G tn s) /\
  gas_admissible (eval_for cx tyv id stmts (MAP Value (DROP k vs))) (stmt_res_ok lctx) es ==>
  gas_outcome_ptr (\H. cx_dead H cx) (cx_tops cx) (ctx,func) PG cx st0
    (do push_scope_with_var id tyv (EL k vs);
        finally (try (do eval_stmts cx stmts; return F od)
          handle_loop_exception) pop_scope od) (es,s,G,tn)
    (\H res ee gf tf t. ?broke. res = INL broke /\
      (broke ==> Done H ee gf tf t) /\ (~broke ==> Inv H (SUC k) ee gf tf t))
    (\H res ee gt r. ?ex. res = INR ex /\
      !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r)
Proof
  strip_tac >>
  reverse (Cases_on `?H. valid_horizon cx st0 H es.storage_trace`)
  >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_initial >>
      fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
      simp[ignore_bind_def, vyperStorageTraceTheory.storage_trace_frame_bind_all,
           vyperStorageTraceTheory.storage_trace_frame_state_updates,
           vyperStorageTraceTheory.storage_trace_frame_finally,
           vyperStorageTraceTheory.storage_trace_frame_try,
           vyperStorageTraceTheory.storage_trace_frame_loop_handler,
           vyperStorageTraceTheory.storage_trace_frame_return,
           vyperStorageTraceTheory.storage_trace_frame_pop_scope,
           vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  pop_assum (qx_choose_then `H0` assume_tac) >>
  `Inv H0 k es G tn s` by metis_tac[] >>
  qpat_assum `Inv H0 k es G tn s` mp_tac >> asm_rewrite_tac[] >> strip_tac >>
  `ret_pc_ok cenv st s` by
    (irule ret_pc_ok_frame >> goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `cenv` >> simp[]) >>
  `!r q. cenv.ce_return_buf = SOME (PtrVar (Var r) q) ==> r <> dv` by metis_tac[] >>
  `(i2w (n1 + &k) : bytes32) <> i2w n2` by metis_tac[] >>
  mp_tac (SRULE [op_prov_def] (Q.INST
    [`i` |-> `n1 + &k`, `z` |-> `i2w n2`, `D` |-> `cx_dead H0 cx`, `H` |-> `H0`]
    for_range_body_prepare_ptr)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_path_ptr (cx_dead H0 cx) 0 ctx func PG G tn s 0 G2 tf (OK s2)` >>
  `!HH:(bool # bytes32 # type_value) list # num list. gas_path_ptr (cx_dead HH cx) 0 ctx func PG G tn s 0 G2 tf (OK s2)` by
    (gen_tac >> mp_tac (SRULE [op_prov_def] (Q.INST
      [`i` |-> `n1 + &k`, `z` |-> `i2w n2`,
       `D` |-> `cx_dead HH cx`, `H` |-> `H0`] for_range_body_prepare_ptr)) >>
     impl_tac >- (simp[] >> metis_tac[]) >>
     disch_then (qx_choosel_then [`sH`,`GH`,`tfH`] strip_assume_tac) >>
     `tfH = tf` by simp[taint_component_equality] >>
     gvs[Abbr `s2`, Abbr `G2`]) >>
  `s2.vs_current_bb = body_lbl /\ s2.vs_inst_idx = 1 /\ ~s2.vs_halted` by
    gvs[Abbr `s2`] >>
  `!x. not_fresh_at st x ==> x <> dv` by metis_tac[] >>
  drule_all for_range_callback_entry_ptr >> strip_tac >>
  qmatch_asmsub_abbrev_tac `stmt_frag_ptr _ _ _ _ _ _ _ _ _ _ ei` >>
  `stmt_state_rel H0 ctx func bc cx ei s2 /\ ghost_inv H0 d bc cx ei G2 tf s2` by
    ( `ei = (es with scopes := (FEMPTY |+ (id,
         <|assignable := F; type := tyv; value := IntV (n1 + &k); popped := []|>))
           :: es.scopes) with gas_obs := []` by simp[Abbr `ei`] >>
      pop_assum SUBST1_TAC >>
      rewrite_tac[stmt_state_rel_gas_obs, ghost_inv_gas_obs] >> simp[]) >>
  `!HH. valid_horizon cx st0 HH ei.storage_trace ==>
    stmt_state_rel HH ctx func bc cx ei s2 /\
    storage_well_formed_on cx ei (FST HH) /\ ghost_inv HH d bc cx ei G2 tf s2` by
    (rpt strip_tac >>
     `Inv HH k es G tn s` by (fs[Abbr `ei`] >> metis_tac[]) >>
     qpat_assum `Inv HH k es G tn s` mp_tac >> asm_rewrite_tac[] >> strip_tac >>
     mp_tac (SRULE [op_prov_def] (Q.INST
       [`i` |-> `n1 + &k`, `z` |-> `i2w n2`,
        `D` |-> `cx_dead HH cx`, `H` |-> `HH`] for_range_body_prepare_ptr)) >>
     impl_tac >- (simp[] >> metis_tac[]) >>
     disch_then (qx_choosel_then [`sH`,`GH`,`tfH`] strip_assume_tac) >>
     `tfH = tf` by simp[taint_component_equality] >>
     gvs[Abbr `ei`, Abbr `s2`, Abbr `G2`, stmt_state_rel_gas_obs, ghost_inv_gas_obs,
         vyperStorageFootprintTheory.storage_well_formed_on_def,
         vyperStorageBackendTheory.get_storage_scopes]) >>
  `gas_admissible (eval_stmts cx stmts)
    (stmt_res_ok (InLoop exit_lbl incr_lbl)) ei` by
    (drule_all for_range_body_admissible >> simp[Abbr `ei`]) >>
  `ptr_covers G2 tf p s2 sz` by simp[Abbr `s2`] >>
  `lookup_var cv s2 = SOME (i2w (n1 + &k)) /\
   lookup_var ev s2 = SOME (i2w n2) /\
   FLOOKUP G2 cv = NONE /\ FLOOKUP G2 ev = NONE /\
   op_taint tf (Var cv) = {} /\ op_taint tf (Var ev) = {}` by
    (`dv <> cv /\ dv <> ev` by fs[for_code_def] >>
     simp[Abbr `G2`, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >>
     fs[op_taint_def] >> metis_tac[]) >>
  drule_all for_range_callback_contract >> strip_tac >>
  suspend "outcome"
QED

Resume for_range_round_ptr[outcome]:
  qmatch_goalsub_abbrev_tac `gas_outcome_ptr _ _ _ _ _ _ _ _ Qround Rround` >>
  dxrule for_outcome_source_evidence_ptr >>
  disch_then assume_tac >>
  drule (Q.INST [`Q'` |-> `\H res ee gf tf t.
    (res = INL ARB \/ res = INR ContinueException \/ res = INR BreakException) /\
    ee.scopes <> [] /\
    (res = INR BreakException ==> Done H (ee with scopes := TL ee.scopes) gf tf t) /\
    (res <> INR BreakException ==> Inv H (SUC k) (ee with scopes := TL ee.scopes) gf tf t)`]
    (INST_TYPE [alpha |-> ``:unit``] for_outcome_zero_suffix_ptr)) >>
  (impl_tac >- suspend "finish") >>
  disch_tac >>
  drule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _ _ _`)
    (Q.INST [`Q'` |-> `Qround`, `R'` |-> `Rround`] for_body_cleanup_outcome_ptr) >>
  (impl_tac >- (simp[Abbr `ei`] >> conj_tac
    >- (rpt gen_tac >> strip_tac >>
        fs[] >> qpat_x_assum `res = _` SUBST_ALL_TAC >>
        simp[Abbr `Qround`] >> fs[] >> metis_tac[]) >>
    rpt gen_tac >> strip_tac >>
    drule for_body_exit_cleanup_ptr >> disch_then (qspec_then `TL ee.scopes` strip_assume_tac) >>
    simp[Abbr `Rround`] >> gen_tac >>
    `ee with <|scopes := TL ee.scopes; gas_obs := tail|> =
     ee with <|gas_obs := tail; scopes := TL ee.scopes|>` by
      (Cases_on `ee` >> simp[]) >> asm_rewrite_tac[])) >>
  disch_tac >>
  `gas_marked_exec_ptr (cx_dead H0 cx) (ctx,func) PG
    (push_scope_with_var id tyv (EL k vs)) (es,s,G,tn) [] (INL ())
    (ei with gas_obs := es.gas_obs) G2 tf (OK s2)` by
    (simp[gas_marked_exec_ptr_def, Abbr `ei`,
      push_scope_with_var_def, bind_def, push_scope_def, new_variable_def,
      return_def] >> Cases_on `es` >> simp[evaluation_state_fn_updates]) >>
  drule gas_marked_exec_ptr_exec >> disch_tac >>
  rewrite_tac[ignore_bind_def] >>
  irule gas_outcome_ptr_bind_normal >>
  goal_assum (drule_at Any) >>
  simp[Abbr `ei`, vyperStorageTraceTheory.storage_trace_frame_finally,
       vyperStorageTraceTheory.storage_trace_frame_try,
       vyperStorageTraceTheory.storage_trace_frame_ignore_bind,
       vyperStorageTraceTheory.storage_trace_frame_loop_handler,
       vyperStorageTraceTheory.storage_trace_frame_return,
       vyperStorageTraceTheory.storage_trace_frame_pop_scope,
       vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  reverse conj_tac
  >- (qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ (finally _ _) _ _ _` mp_tac >>
      simp[ignore_bind_def]) >>
  rpt strip_tac >> drule gas_exempt_cert_bind_unit >> simp[] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

Resume for_range_round_ptr[finish]:
  rpt gen_tac >> strip_tac >>
  rename1 `valid_horizon cx st0 HF0 ee.storage_trace` >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `HF0` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> fs[] >>
  `(!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
     lookup_var x t = SOME v)` by metis_tac[] >>
  `(!x. not_fresh_at st x ==> FLOOKUP G' x = FLOOKUP G0 x /\
     op_taint tn' (Var x) = op_taint tn0 (Var x))` by
    (rpt strip_tac >> `x <> dv /\ not_fresh_at sb0 x` by metis_tac[] >>
     fs[Abbr `G2`, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `lookup_var p t = SOME a /\
   FLOOKUP t.vs_allocas ainst.inst_id = SOME (w2n a,sz)` by
    (fs[for_code_def, Abbr `s2`] >> metis_tac[]) >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >> simp[Abbr `ei`] >> disch_tac >>
  `k < Num (n2-n1) /\
   (!x. not_fresh_at st x ==> x <> cv /\ x <> nv) /\
   (res = INL () ==> ~block_is_terminated sb1)` by metis_tac[] >>
  drule_all (Q.INST [`H` |-> `HF0`] for_range_callback_finish_ptr) >>
  disch_then (qspecl_then [`PG`, `cx_dead HF0 cx`]
    (qx_choosel_then [`sc`, `rest`, `u`, `gf`, `tf`] strip_assume_tac)) >>
  `res = INL () \/ res = INR ContinueException \/ res = INR BreakException` by
    (qpat_x_assum `stmt_lands _ _ res t` mp_tac >>
     simp[stmt_lands_def] >> metis_tac[]) >>
  qexistsl_tac [`gf`, `tf`, `u`] >> qx_gen_tac `HF` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `HF` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> fs[] >>
  drule_all (Q.INST [`H` |-> `HF`] for_range_callback_finish_ptr) >>
  disch_then (qspecl_then [`PG`, `cx_dead HF cx`]
    (qx_choosel_then [`scH`, `restH`, `uH`, `gfH`, `tfH`] strip_assume_tac)) >>
  `uH = u /\ gfH = gf /\ tfH = tf` by simp[] >>
  `scH = sc /\ restH = rest` by metis_tac[] >>
  gvs[] >> Cases_on `res = INR BreakException` >> gvs[] >> metis_tac[]
QED
Finalise for_range_round_ptr
