(* Counted composition of the copied base, snapshot, forced key and selection. *)
Theory bodyCopiedArrayBindMods
Ancestors
  bodyCopiedArrayCutDefsMods bodyFullAttributeMods bodyFullIfExpReach
  bodyFullTargetSubscript exprSimSubscriptArray exprSimSubscriptArraySource
  exprSimMemorySource stmtSimForRounds haltExitProj freshWrites
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  vyperStorageTrace vyperStorageFootprint vyperState exprSimDefs
  gasOutcomeFullMods fragGasOriginPtr bodyFullPostsMods
  gasContext gasSummary gasShadowState gasShadow fragExec contextRawReachable
  vyperAST vyperInterpreter vyperTypeSystem words list
  exprLowering context compileEnv bodyMemoryDefs

(* The source replay and the machine path refer to the same marks. *)
Theorem copied_bind_keep_path[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,fn,PG) mods cx st0 source (es,s,G,tn) Q R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,fn,PG) mods cx st0 source (es,s,G,tn)
    (\H res ee G' tn' t. Q H res ee G' tn' t /\
      ?marks. (!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
                        (res,ee with gas_obs := tail)) /\
              gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) marks (OK t,G',tn')) R
Proof
  rewrite_tac[gas_outcome_full_mods_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> simp[] >> rpt (goal_assum (drule_at Any)) >> simp[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
      disj1_tac >> simp[] >> qexists_tac `marks` >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem copied_exit_eta[local]:
  (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)) =
  copied_vv_exit_mods cx ctx
Proof
  simp[FUN_EQ_THM,copied_vv_exit_mods_def]
QED

Theorem copied_bind_exit[local]:
  copied_vv_exit_mods cx ctx H (res : 'a + exception) ee gt r ==>
  ?exc. res = INR exc /\ copied_vv_exit_mods cx ctx H (INR exc : 'b + exception) ee gt r
Proof
  Cases_on `res` >> simp[copied_vv_exit_mods_def,expr_exit_def] >>
  metis_tac[expr_exit_INR_retype,halt_exit_INR_type]
QED

(* Normal continuations have both the actual source replay and the path
   needed to transfer caller headroom. Exceptional and exempt arms never
   need a successful continuation. *)
Theorem copied_bind_normal[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,fn,PG) mods cx st0 source (es,s,G,tn)
    Q1 (copied_vv_exit_mods cx ctx) /\
  (!H res ee G1 tn1 t. Q1 H res ee G1 tn1 t ==> ?v. res = INL v) /\
  (!marks v mid G1 tn1 t.
    (!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
             (INL v,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\ ~t.vs_halted /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> Q1 H (INL v) mid G1 tn1 t) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
         ?m. (!tail. source (es with gas_obs := gas_explicit m s.vs_gas_readings ++ tail) =
                       (INL v,mid with gas_obs := tail)) /\
             gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) m (OK t,G1,tn1)) ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,fn,PG) mods cx st0 (next v) (mid,t,G1,tn1)
      Q (copied_vv_exit_mods cx ctx)) /\
  storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
  (!marks err ee leaf stop_state.
     gas_exempt_cert_mods T mods (ctx,fn) (ignore_bind source (return ()))
       (es,s) marks (err,ee) (leaf,stop_state) ==>
     gas_exempt_cert_mods T mods (ctx,fn) (bind source (\v. ignore_bind (next v) (return ())))
       (es,s) marks (err,ee) (leaf,stop_state)) /\
  (!left v mid t right err ee leaf stop_state.
     gas_marked_exec T (ctx,fn) source (es,s) left (INL v) mid (OK t) /\
     gas_exempt_cert_mods T mods (ctx,fn) (ignore_bind (next v) (return ()))
       (mid with gas_obs := [],t) right (err,ee) (leaf,stop_state) ==>
     gas_exempt_cert_mods T mods (ctx,fn) (bind source (\v. ignore_bind (next v) (return ())))
       (es,s) (left ++ right) (err,ee) (leaf,stop_state)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,fn,PG) mods cx st0 (bind source next) (es,s,G,tn)
    Q (copied_vv_exit_mods cx ctx)
Proof
  strip_tac >> irule gas_outcome_full_mods_bind_all >> asm_rewrite_tac[] >>
  qexists_tac `\H res ee G' tn' t. Q1 H res ee G' tn' t /\ ee.gas_obs = [] /\ ~t.vs_halted /\
    ?m. (!tail. source (es with gas_obs := gas_explicit m s.vs_gas_readings ++ tail) =
                  (res,ee with gas_obs := tail)) /\
        gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) m (OK t,G',tn')` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      drule copied_bind_keep_path >> disch_then (irule_at Any) >>
      simp[copied_bind_exit]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> Q1 H _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H res ee G1 tn1 t. Q1 H res ee G1 tn1 t ==> _`
    (drule_then strip_assume_tac) >> gvs[] >>
  qpat_assum `!marks v mid G1 tn1 t. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _` irule >>
  conj_tac >- (qexists_tac `marks` >> simp[]) >> simp[]
QED

(* The certificate rules are chosen by the prefix result type. *)
fun copied_bind_tac certError certBind =
  irule copied_bind_normal >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
      irule certBind >> qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >>
      BETA_TAC >> first_assum ACCEPT_TAC)
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule certError >> simp[]) >>
  simp[storage_trace_frame_bind_all,storage_trace_frame_select,
       evaluate_storage_trace_frame,storage_trace_frame_read_result];

Theorem copied_outcome_read_snapshot[local]:
  ~s.vs_halted /\ mid.gas_obs = [] /\ read_result cx raw mid = (INL saved,mid) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,Gc,tc)) /\
  (!v. storage_trace_frame (next v)) /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,fn,PG) mods cx st0 (next saved) (mid,u,Gc,tc)
    Q (copied_vv_exit_mods cx ctx) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,fn,PG) mods cx st0
    (bind (read_result cx raw) next) (mid,s,G,tn) Q (copied_vv_exit_mods cx ctx)
Proof
  strip_tac >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  drule_then assume_tac read_result_gas_obs >>
  `gas_outcome_full_mods (DF,lo,explicit,ctx,fn,PG) mods cx st0 (read_result cx raw)
     (mid,s,G,tn) (\H res ee G' tn' t. res = INL saved /\ ee = mid /\
                                    G' = Gc /\ tn' = tc /\ t = u)
     (copied_vv_exit_mods cx ctx)` by
    (irule gas_outcome_full_mods_pure >> simp[] >>
     qexistsl_tac [`Gc`,`mid`,`INL saved`,`u`,`tc`] >> simp[]) >>
  copied_bind_tac gas_exempt_cert_mods_error_value gas_exempt_cert_mods_bind_value >>
  rpt (goal_assum (drule_at Any)) >> BETA_TAC >> rpt conj_tac
  >~ [`?v. _ = INL v`] >- simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `storage_trace_domain _ _ _` (strip_assume_tac o REWRITE_RULE [storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> INL _ = INL _ /\ _`
    (drule_then strip_assume_tac) >>
  `v = saved` by (qpat_assum `INL v = _` mp_tac >> simp[NoAsms]) >>
  map_every (fn pat => qpat_x_assum pat SUBST_ALL_TAC)
    [`v = saved`,`mid' = mid`,`G1 = Gc`,`tn1 = tc`,`t = u`] >> first_assum ACCEPT_TAC
QED

Theorem copied_tail_admissible[local]:
  gas_admissible (bind source next) A es /\
  (!tail. source (es with gas_obs := xs ++ tail) = (INL v,mid with gas_obs := tail)) ==>
  gas_admissible (next v) A mid
Proof
  strip_tac >> drule_all gas_admissible_bind_tail >> simp[]
QED

Theorem copied_key_admissible[local]:
  gas_admissible (bind key next) expr_vv_res_ok mid ==>
  gas_admissible key expr_res_ok mid
Proof
  simp[gas_admissible_def] >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >> simp[bind_def,expr_res_ok_def,expr_vv_res_ok_def]
QED

Theorem copied_replay_empty[local]:
  (!tail. source (es with gas_obs := xs ++ tail) = (res,ee with gas_obs := tail)) /\
  ee.gas_obs = [] ==> source (es with gas_obs := xs) = (res,ee)
Proof
  strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >> simp[]
QED

val copied_base_post = ``\(H : (bool # 256 word # type_value) list # num list)
  (res : eval_result + exception) ee G tn t.
  ?tv. res = INL tv /\
    vv_post_mods H ctx fn ce cx obj es sa sm s0 ee tv bvv t /\
    vv_store_bound cx (post_value_type ce obj) (lowered_value_type ce obj) ee tv bvv t /\
    t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history fn t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn t /\
    ptr_vv_ok cx (post_value_type ce obj) tv bvv ee G tn t /\
    (!v. tv = Value v /\ ~is_word_type (post_value_type ce obj) /\
         ~is_bytestring_type (post_value_type ce obj) ==>
         vv_own ce cx (post_value_type ce obj) sa sm ee tv bvv t /\
         (!t' p. bvv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
    (ce.ce_is_ctor /\ vv_location bvv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME rt /\
              eval_operand (vv_operand bvv) t = SOME w ==>
         w2n w + type_memory_size rt <= lo /\
         (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory rt val (w2n w) mem)) /\
    (!t' op. bvv = StackValue t' op /\ ~is_word_type (post_value_type ce obj) ==>
             ptr_buf_ok ce obj op G t) /\
    (!t' p. bvv = LocatedValue t' p /\ p.ptr_location = LocMemory ==> ptr_buf_ok ce obj p.ptr_operand G t) /\
    ghost_kept_at lo ce es sa G0 tn0 s0 G tn``;

val copied_key_post = ``\(H : (bool # 256 word # type_value) list # num list)
  (res : value + exception) ee G tn t.
  ?v. res = INL v /\
    expr_post_mods H ctx fn ce cx idx mid sc si u ee v iop t /\
    expr_store_bound cx (post_value_type ce idx) v iop t /\
    t.vs_current_bb = si.cs_current_bb /\ t.vs_inst_idx = LENGTH si.cs_current_insts /\
    alloca_history fn t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    u.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn t /\
    ptr_val_ok cx (post_value_type ce idx) v iop G tn t /\
    (~is_word_type (post_value_type ce idx) ==> ptr_buf_ok ce idx iop G t) /\
    ghost_kept_at lo ce mid sc Gc tc u G tn``;

Theorem copied_base_read[local]:
  vv_post_mods H ctx fn ce cx obj es sa sm s0 mid raw bvv s ==>
  ?saved. read_result cx raw mid = (INL saved,mid)
Proof
  strip_tac >> fs[vv_post_mods_def] >>
  drule attribute_vv_holds_read_operand_mods >> rpt strip_tac >> goal_assum (drule_at Any)
QED

(* The snapshot and selector are supplied at their reached cuts. This
   theorem fixes the counted sequencing, not how each cut is implemented. *)
Theorem copied_array_children_bind_mods:
  subscript_reads_base cx obj idx /\ expr_type obj = ArrayT et bd /\
  gas_admissible (eval_expr cx obj) expr_vv_res_ok es /\
  (MEM fn ctx.ctx_functions ==>
   !bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx ty obj es /\
  (!xs raw mid saved. eval_expr cx obj (es with gas_obs := xs) = (INL raw,mid) /\
    read_result cx raw mid = (INL saved,mid) ==>
    expr_sim_full_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx ty idx mid) /\
  (!st0 sa sb sha shb vv s0 G0 tn0.
    compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
    compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr (Subscript ann obj idx)) sha = (vv,shb) /\
    gas_shadow_state sa sha /\ gas_shadow_state sb shb /\
    gas_shadow_context ctx shctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function fn shfn /\ MEM fn ctx.ctx_functions /\ MEM shfn shctx.ctx_functions /\
    fn_has_code sa sb fn /\ fn_has_code sha shb shfn /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved ce sa /\ (!H. dead_lo_ok_mods H (DF H) lo ce cx) /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    gas_admissible (eval_expr cx (Subscript ann obj idx)) expr_vv_res_ok es /\
    return_buf_frame d ce sa s0 /\ alloca_history fn s0 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!f inst s. frag_reachable ctx fn s0 f inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx fn ce cx es s0 /\ immutable_frame_mods fn ce cx es s0 /\
      storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?bvv sm shm cvv sc shc iop si shi.
      compile_expr ce ty obj sa = (bvv,sm) /\
      compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr obj) sha = (bvv,shm) /\
      compile_snapshot_vv ce T bvv sm = (cvv,sc) /\
      lower_value compile_expr ce ty idx sc = (iop,si) /\
      lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr idx) shc = (iop,shi) /\
      gas_shadow_state sm shm /\ gas_shadow_state sc shc /\ gas_shadow_state si shi /\
      fn_has_code sa sm fn /\ fn_has_code sha shm shfn /\
      fn_has_code sc si fn /\ fn_has_code shc shi shfn /\
      sa.cs_next_var <= sc.cs_next_var /\
      (!xs raw mid saved s G tn.
        eval_expr cx obj (es with gas_obs := xs) = (INL raw,mid) /\
        read_result cx raw mid = (INL saved,mid) /\
        storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\ ~s.vs_halted /\
        (!H. valid_horizon cx st0 H mid.storage_trace ==> ^copied_base_post H (INL raw) mid G tn s) /\
        (!H. valid_horizon cx st0 H mid.storage_trace ==> valid_horizon cx st0 H es.storage_trace) ==>
        ?atv u Gc tc q w.
          copied_saved_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
            (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv) (sm,s,G,tn) (sc,u,Gc,tc) cvv (q,w)) /\
      (!xs raw mid saved atv s G tn u Gc tc q w ys key fin z Gi ti.
        eval_expr cx obj (es with gas_obs := xs) = (INL raw,mid) /\
        copied_saved_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
          (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv) (sm,s,G,tn) (sc,u,Gc,tc) cvv (q,w) /\
        bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := ys) = (INL key,fin) /\
        storage_trace_domain cx st0 fin.storage_trace /\ fin.gas_obs = [] /\ ~z.vs_halted /\
        (!H. valid_horizon cx st0 H fin.storage_trace ==> ^copied_key_post H (INL key) fin Gi ti z) /\
        (!H. valid_horizon cx st0 H fin.storage_trace ==> valid_horizon cx st0 H mid.storage_trace) /\
        gas_admissible (select_result cx (ArrayT et bd) (Value saved) (ValueSubscript key)) expr_vv_res_ok fin ==>
        gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shctx,ctx,fn,PG) ce.ce_modules cx st0
          (select_result cx (ArrayT et bd) (Value saved) (ValueSubscript key)) (fin,z,Gi,ti)
          (copied_located_post_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
            (ann,obj,idx) (es,sa,s0,G0,tn0) (sb,vv)) (copied_vv_exit_mods cx ctx))) ==>
  copied_located_vv_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx ty (ann,obj,idx) es
Proof
  BETA_TAC >> strip_tac >> rewrite_tac[copied_located_vv_mods_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `MEM fn ctx.ctx_functions ==> !bb. _`
    (drule_then assume_tac) >>
  qpat_x_assum `!st0 sa sb sha shb vv s0 G0 tn0. _ ==> ?bvv sm shm cvv sc shc iop si shi. _`
    (qspecl_then [`st0`,`sa`,`sb`,`sha`,`shb`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ obj _` (mp_tac o REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`sha`,`shm`,`bvv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  rewrite_tac[copied_exit_eta] >>
  disch_then (assume_tac o CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  drule eval_expr_subscript_copied_bind >>
  disch_then (fn th =>
    qpat_x_assum `gas_admissible (eval_expr _ (Subscript _ _ _)) _ _`
      (assume_tac o REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  qpat_assum `expr_type obj = ArrayT et bd` (fn th =>
    qpat_x_assum `gas_admissible (bind (eval_expr _ obj) _) _ _`
      (assume_tac o REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  copied_bind_tac gas_exempt_cert_mods_error_result gas_exempt_cert_mods_bind_result >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (eval_expr _ obj) _ _ _` (irule_at Any) >>
  BETA_TAC >> rpt conj_tac
  >~ [`?v. _ = INL v`] >- (rpt strip_tac >> goal_assum (drule_at Any)) >>
  suspend "reached_base"
QED

Resume copied_array_children_bind_mods[reached_base]:
  qx_genl_tac [`marks`,`raw`,`mid`,`G`,`tn`,`s`] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `xs = gas_explicit marks s0.vs_gas_readings` >>
  `eval_expr cx obj (es with gas_obs := xs) = (INL raw,mid)` by
    (irule copied_replay_empty >> simp[Abbr `xs`] >> rpt (goal_assum (drule_at Any))) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> valid_horizon cx st0 H es.storage_trace` by
    (gen_tac >> disch_tac >>
     qpat_assum `eval_expr _ _ _ = _` (mp_then (Pat `_ = _`) mp_tac valid_horizon_frame) >>
     simp[evaluate_storage_trace_frame]) >>
  `?saved. read_result cx raw mid = (INL saved,mid)` by
    (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
       fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ?tv. INL raw = INL tv /\ _`
       (drule_then strip_assume_tac) >>
     qpat_x_assum `INL raw = INL tv` (SUBST_ALL_TAC o REWRITE_RULE [sumTheory.INL_11]) >>
     drule copied_base_read >> simp[]) >>
  qpat_assum `!xs raw mid saved s G tn. _ ==> ?atv u Gc tc q w. _`
    (qspecl_then [`xs`,`raw`,`mid`,`saved`,`s`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `expr_sim_full_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx ty idx mid` by
    (qpat_assum `!xs raw mid saved. _ ==> expr_sim_full_mods _ _ _ _ _ _`
      (drule_all_then ACCEPT_TAC)) >>
  suspend "snapshot"
QED

Resume copied_array_children_bind_mods[snapshot]:
  qabbrev_tac `key_run = bind (eval_expr cx idx) (read_result cx)` >>
  qabbrev_tac `next = \base. bind key_run (\key. select_result cx (ArrayT et bd) (Value base) (ValueSubscript key))` >>
  `gas_admissible (bind (read_result cx raw) next) expr_vv_res_ok mid` by
    (qpat_assum `gas_admissible (bind (eval_expr _ obj) _) _ _`
       (mp_then (Pat `gas_admissible _ _ _`) mp_tac copied_tail_admissible) >>
     BETA_TAC >> disch_then (drule_then ACCEPT_TAC)) >>
  `gas_admissible (next saved) expr_vv_res_ok mid` by
    (qpat_assum `gas_admissible (bind (read_result _ raw) next) _ _`
       (mp_then (Pat `gas_admissible _ _ _`) mp_tac copied_tail_admissible) >>
     disch_then (qspecl_then [`[]`,`saved`,`mid`] mp_tac) >> simp[read_result_gas_obs]) >>
  `gas_admissible key_run expr_res_ok mid` by
    (qpat_assum `gas_admissible (next saved) _ _` mp_tac >>
     simp[NoAsms,Abbr `next`] >> disch_then (irule o MATCH_MP copied_key_admissible)) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,fn,PG) (s,G,tn) [] (OK u,Gc,tc)` by
    fs[copied_saved_cut_mods_def] >>
  irule copied_outcome_read_snapshot >>
  conj_tac >- simp[Abbr `next`,Abbr `key_run`,storage_trace_frame_bind_all,
                   storage_trace_frame_select,evaluate_storage_trace_frame,storage_trace_frame_read_result] >>
  asm_rewrite_tac[] >> qexistsl_tac [`Gc`,`saved`,`tc`,`u`] >> asm_rewrite_tac[] >>
  suspend "key_entry"
QED

Resume copied_array_children_bind_mods[key_entry]:
  drule_then strip_assume_tac copied_saved_cut_index_entry_mods >>
  `!f inst z. frag_reachable ctx fn u f inst z ==> dalloca_fmp_headroom inst z` by
    (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
       fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ?m. _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ (s,G,tn) [] _`
       (drule_then assume_tac) >>
     `!f inst z. frag_reachable ctx fn s f inst z ==> dalloca_fmp_headroom inst z` by
       (match_mp_tac (GEN_ALL gas_origin_ptr_path_dalloca_fmp_headroom) >>
        qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ (OK s,G,tn)` (irule_at Any) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     match_mp_tac (GEN_ALL gas_origin_ptr_path_dalloca_fmp_headroom) >>
     qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK u,Gc,tc)` (irule_at Any) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ idx _` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sc`,`si`,`shc`,`shi`,`iop`,`u`,`Gc`,`tc`] mp_tac) >>
  qunabbrev_tac `key_run` >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  rewrite_tac[copied_exit_eta] >> strip_tac >>
  qunabbrev_tac `next` >> BETA_TAC >> RULE_ASSUM_TAC BETA_RULE >>
  copied_bind_tac gas_exempt_cert_mods_error_value gas_exempt_cert_mods_bind_value >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (bind (eval_expr _ idx) _) _ _ _` (irule_at Any) >>
  BETA_TAC >> rpt conj_tac
  >~ [`?v. _ = INL v`] >- (rpt strip_tac >> goal_assum (drule_at Any)) >>
  suspend "select"
QED

Resume copied_array_children_bind_mods[select]:
  qx_genl_tac [`imarks`,`key`,`fin`,`Gi`,`ti`,`z`] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `ys = gas_explicit imarks u.vs_gas_readings` >>
  `bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := ys) = (INL key,fin)` by
    (irule copied_replay_empty >> simp[Abbr `ys`] >> rpt (goal_assum (drule_at Any))) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==> valid_horizon cx st0 H mid.storage_trace` by
    (gen_tac >> disch_tac >>
     qpat_assum `bind (eval_expr _ idx) _ _ = _` (mp_then (Pat `_ = _`) mp_tac valid_horizon_frame) >>
     simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
  `gas_admissible (select_result cx (ArrayT et bd) (Value saved) (ValueSubscript key)) expr_vv_res_ok fin` by
    (qpat_assum `gas_admissible (bind (bind (eval_expr _ idx) _) _) expr_vv_res_ok mid`
       (mp_then (Pat `gas_admissible _ _ _`) mp_tac copied_tail_admissible) >>
     BETA_TAC >> disch_then (drule_then ACCEPT_TAC)) >>
  qpat_assum `!xs raw mid saved atv s G tn u Gc tc q w ys key fin z Gi ti. _ ==> _` irule >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Finalise copied_array_children_bind_mods
