(* Scope the actual positional snapshot, after its guarded VV child. *)
Theory entryCreateExtPosHead
Ancestors
  entryCreateEffectFocus entryCreateNativeFirstExit entryCreateScopedBind
  createSizeConcreteSnapshots createCtorSegmentArrival createSizeRawReplay
  bodyFullExtCallPosList runtimeDefaultRejectCode fragObserverCodeProps
  entryCreateFocusSpec entryCreateCompletedCut createMarkedPath createSizePrefixReplay
  frameGasEvents fragGasOrigin venomExecSemantics venomExecProofs relation entryCreateExtPosVisit entryCreateExtPosWord entryCreateExtPosRetained entryCreateExtPosAllocRead entryCreatePosSnapshotBand entryCreatePosSnapshotCode createCtorSnapshotForward aggregateEvaluatedLayout exprSimHyps exprSimMemorySource gasSummary fragGasOriginPtr fragGasPath vyperStorageFootprint vyperStorageTrace vyperState exprSimDefs fragExec gasOutcomeFull gasExemptCert bodyFullIfExpReach bodySim entryCreateIntervalLayout entryCreateOperandReplay s1PrefixDefs exprLoweringProps bodyFullHashKeccakFixed exprSimAbiGasBridge bodyFullExtCallPosAggregate entryIntCallStageNeutral createSizeOperandCode gasExplicitSites compileEnv list

(* A fetched snapshot edge between live states is the actual caller edge.
   GAS is excluded explicitly: an empty gas-readings list is not a counter. *)
Theorem pos_snapshot_segment_edge[local]:
  ~s.vs_halted /\ ~t.vs_halted /\
  ctor_segment_fetch f s = SOME i /\ i.inst_opcode <> INVOKE /\
  i.inst_opcode <> GAS /\ ctor_segment_next f s i = SOME t ==>
  gas_origin_edge F E C f s [] (OK t)
Proof
  strip_tac >>
  gvs[ctor_segment_fetch_def, ctor_segment_next_def, ctor_segment_entry_def,
      AllCaseEqs()] >>
  simp[gas_origin_edge_def, step_inst_non_invoke, gas_events_step_plain] >>
  metis_tac[eval_phis_preserves_halted]
QED

Theorem pos_snapshot_prefix[local]:
  !s t. RTC (\u v. ~u.vs_halted /\ ~v.vs_halted /\ ~create_operand_at b u /\
       ?i. ctor_segment_fetch f u = SOME i /\ i.inst_id IN frag_ids a b /\
           i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
           ctor_segment_next f u i = SOME v) s t ==>
  create_expr_prefix a b E C f s [] t
Proof
  ho_match_mp_tac RTC_INDUCT >> simp[entryCreatePathScopeTheory.create_expr_prefix_nil] >>
  simp[PULL_EXISTS] >> rpt strip_tac >> drule_all pos_snapshot_segment_edge >> strip_tac >>
  irule (SIMP_RULE (srw_ss()) []
    (Q.INST [`left` |-> `[]`, `right` |-> `[]`] entryCreatePathScopeTheory.create_expr_prefix_append)) >>
  goal_assum (drule_at Any) >>
  simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
  fs[create_marked_edge_def, create_prefix_step_def, create_operand_at_def,
     ctor_segment_fetch_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem pos_snapshot_scope:
  RTC (\u v. ~u.vs_halted /\ ~v.vs_halted /\ ~create_operand_at b u /\
       ?i. ctor_segment_fetch f u = SOME i /\ i.inst_id IN frag_ids a b /\
           i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
           ctor_segment_next f u i = SOME v) s t /\
  create_operand_at b t ==>
  create_operand_full_scope a b E C f s [] (OK t)
Proof
  strip_tac >> drule_then assume_tac pos_snapshot_prefix >>
  fs[create_operand_full_scope_def, create_operand_at_def]
QED

Theorem pos_read_scoped_success[local]:
  read_result cx raw ee = (INL v,ee) /\ ee.gas_obs = [] /\
  storage_trace_domain cx st0 ee.storage_trace /\
  create_operand_full_scope m b E C f t [] (OK u) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,E,C,f,PG) (t,G,tn) [] (OK u,Gu,tu) /\
    Q H (INL v) ee Gu tu u) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
    (read_result cx raw) (ee,t,G,tn) Q R
Proof
  strip_tac >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  simp[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`INL v`,`ee`,`OK u`,`Gu`,`tu`] >>
  simp[gas_explicit_def] >> metis_tac[read_result_gas_obs]
QED

Theorem pos_snapshot_post_inl[local]:
  extcall_positional_post keep DF lo d C f ce cx env rest xs svs a b es s G tn
    H (INL vs : value list + 'a) ee Gu tu u =
  extcall_positional_post keep DF lo d C f ce cx env rest xs svs a b es s G tn
    H (INL vs : value list + vyperState$exception) ee Gu tu u
Proof
  simp[extcall_positional_post_def]
QED

Theorem pos_snapshot_read_continuation[local]:
  body_inv tops C ce cx /\ expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e a = (vv,m) /\
  compile_snapshot_vv ce (exprs_can_mutate ce rest)
    (ext_call_arg_value (lowered_value_type ce e) vv) m = (sv,b) /\
  fn_has_code m b f /\ fn_inst_ids_distinct f /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks b)) /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  local_ptrs_reserved ce a /\ return_buf_frame d ce a s0 /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> storage_well_formed_on cx es (FST H)) /\
  (!tail. eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (res,ee with gas_obs := tail)) /\
  ee.gas_obs = [] /\ storage_trace_domain cx st0 ee.storage_trace /\
  create_operand_at m t /\ ~t.vs_halted /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    create_operand_vv_post (DF,lo,d,C,f) ce cx e (es,a,m,s0,vv,G0,tn0) H res ee G tn t) ==>
  ?raw. res = INL raw /\
    scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
      (read_result cx raw) (ee,t,G,tn)
      (\H r out Gu tu u. ?v. r = INL v /\ extcall_positional_post T DF lo d C f ce cx env
         rest [e] [sv] a b es s0 G0 tn0 H (INL [v]) out Gu tu u) R
Proof
  strip_tac >> Cases_on `is_word_type (expr_type e)`
  >- suspend "word" >>
  `~is_word_type (lowered_value_type ce e)` by
    metis_tac[expr_body_pre_lowered_fits,arg_type_fits_word_type] >>
  Cases_on `exprs_can_mutate ce rest` >> gvs[]
  >- suspend "alloc" >> suspend "retain"
QED

Resume pos_snapshot_read_continuation[word]:
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `?raw. res = INL raw` by metis_tac[create_operand_vv_post_def] >> gvs[] >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.INST [`xs` |-> `[]`]
    extcall_pos_word_snapshot_site)) >>
  disch_then (qspecl_then [`T`,`E`,`PG`] strip_assume_tac) >>
  irule pos_read_scoped_success >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G'`,`tn'`,`z`,`v`] >> simp[] >> gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  pure_rewrite_tac[extcall_positional_post_def] >> simp[]
QED

Resume pos_snapshot_read_continuation[alloc]:
  drule_all_then strip_assume_tac extcall_pos_alloc_read_inputs >> gvs[] >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` (fn th => qpat_assum `ee with gas_obs := [] = ee`
    (fn eq => assume_tac (REWRITE_RULE [APPEND_NIL,eq] th)))) >>
  `ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx raw ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv) t = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)` by
    (strip_tac >> qexists_tac `v` >> simp[arithmeticTheory.ADD_COMM]) >>
  drule_all ctor_private_snapshot_forward >>
  disch_then (qspecl_then [`E`,`PG`] strip_assume_tac) >>
  `~is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) vv))` by
    metis_tac[extcall_operand_snapshot_type] >>
  drule_then assume_tac pos_snapshot_opcode_inventory >>
  drule_all_then assume_tac pos_materialized_snapshot_live_band >>
  `create_operand_at b u` by simp[create_operand_at_def] >>
  drule_all_then assume_tac pos_snapshot_scope >>
  irule pos_read_scoped_success >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >> metis_tac[]
QED

Resume pos_snapshot_read_continuation[retain]:
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `?raw. res = INL raw` by metis_tac[create_operand_vv_post_def] >> gvs[] >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` (fn th => qpat_assum `ee with gas_obs := [] = ee`
    (fn eq => assume_tac (REWRITE_RULE [APPEND_NIL,eq] th)))) >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.INST [`xs` |-> `[]`]
    extcall_pos_retained_snapshot_site)) >>
  disch_then (qspecl_then [`T`,`E`,`R`,`PG`] mp_tac) >>
  once_rewrite_tac[pos_snapshot_post_inl] >> metis_tac[]
QED

Finalise pos_snapshot_read_continuation[local]

(* Refine the child post without changing its selected marks or ghosts. *)

Theorem pos_snapshot_child[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m (eval_expr cx e) (es,s,G,tn)
    (\H res ee G1 tn1 t.
       create_operand_vv_post (DF,lo,d,C,f) ce cx e (es,a,m,s,vv,G,tn) H res ee G1 tn1 t /\
       create_operand_at m t)
    (create_operand_exit_post C cx) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m (eval_expr cx e) (es,s,G,tn)
    (\H res ee G1 tn1 t.
       create_operand_vv_post (DF,lo,d,C,f) ce cx e (es,a,m,s,vv,G,tn) H res ee G1 tn1 t /\
       ee.gas_obs = [] /\ ~t.vs_halted)
    (\H res ee gt r. ?exc. res = INR exc /\
      create_operand_exit_post C cx H (INR exc : value + vyperState$exception) ee gt r)
Proof
  simp[scoped_operand_outcome_def] >> strip_tac >> qexists_tac `marks` >> simp[]
  >- metis_tac[]
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G1`,`tn1`] >>
      simp[] >> rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >> simp[]
      >- metis_tac[gas_origin_ptr_path_erase,gas_path_normal] >>
      Cases_on `res` >>
      gvs[create_operand_exit_post_def,expr_exit_def,halt_exit_def,
          stmtSimPropsTheory.expr_exit_INR_type]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem pos_snapshot_bind[local]:
  body_inv tops C ce cx /\ expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e a = (vv,m) /\
  compile_snapshot_vv ce (exprs_can_mutate ce rest)
    (ext_call_arg_value (lowered_value_type ce e) vv) m = (sv,b) /\
  fn_has_code m b f /\ fn_inst_ids_distinct f /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks b)) /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  local_ptrs_reserved ce a /\ return_buf_frame d ce a s0 /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> storage_well_formed_on cx es (FST H)) /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m (eval_expr cx e) (es,s0,G0,tn0)
    (\H res ee G1 tn1 t.
       create_operand_vv_post (DF,lo,d,C,f) ce cx e (es,a,m,s0,vv,G0,tn0) H res ee G1 tn1 t /\
       create_operand_at m t)
    (create_operand_exit_post C cx) /\
  (!marks. create_operand_focus_scope a m E C f s0 marks ==>
           create_operand_focus_scope a b E C f s0 marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E C f s0 marks r ==>
             create_operand_full_scope a b E C f s0 marks r) /\
  (!left t right. create_operand_full_scope a m E C f s0 left (OK t) /\
         create_operand_focus_scope m b E C f t right ==>
         create_operand_focus_scope a b E C f s0 (left ++ right)) /\
  (!left t right r. create_operand_full_scope a m E C f s0 left (OK t) /\
           create_operand_full_scope m b E C f t right r ==>
           create_operand_full_scope a b E C f s0 (left ++ right) r) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
    (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H r out Gu tu u. ?v. r = INL v /\ extcall_positional_post T DF lo d C f ce cx env
       rest [e] [sv] a b es s0 G0 tn0 H (INL [v] : value list + vyperState$exception) out Gu tu u)
    (create_operand_exit_post C cx)
Proof
  strip_tac >> drule_then assume_tac pos_snapshot_child >>
  irule scoped_operand_bind_all_mixed >>
  simp[evaluate_storage_trace_frame,storage_trace_frame_read_result] >>
  conj_tac
  >- (rpt strip_tac >> simp[ignore_bind_def,bind_assoc] >>
      drule_then irule gas_exempt_cert_bind_result >> simp[GSYM ignore_bind_def]) >>
  conj_tac
  >- (rpt strip_tac >> simp[ignore_bind_def,bind_assoc] >>
      irule gas_exempt_cert_error_result >> simp[]) >>
  qexistsl_tac [`\H res ee G1 tn1 t.
    create_operand_vv_post (DF,lo,d,C,f) ce cx e (es,a,m,s0,vv,G0,tn0) H res ee G1 tn1 t /\
    ee.gas_obs = [] /\ ~t.vs_halted`, `m`] >>
  simp[] >> reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     create_operand_vv_post (DF,lo,d,C,f) ce cx e (es,a,m,s0,vv,G0,tn0) H res mid G1 tn1 t` by
    (rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> simp[]) >>
  drule_all pos_snapshot_read_continuation >>
  disch_then (qspecl_then [`create_operand_exit_post C cx`,`PG`,`E`] mp_tac) >>
  once_rewrite_tac[pos_snapshot_post_inl] >> metis_tac[]
QED

Theorem pos_snapshot_row_weaken[local]:
  extcall_positional_post T DF lo d C f ce cx env rest [e] [sv] a b es s G tn
    H (INL [v] : value list + vyperState$exception) ee Gu tu u ==>
  extcall_positional_post keep DF lo d C f ce cx env rest [e] [sv] a b es s G tn
    H (INL [v] : value list + vyperState$exception) ee Gu tu u
Proof
  Cases_on `keep` >> simp[extcall_positional_post_def]
QED

Theorem pos_snapshot_post_weaken[local]:
  scoped_operand_outcome D tops cx st0 a b source (es,s,G,tn)
    (\H r ee Gu tu u. ?v. r = INL v /\ extcall_positional_post T DF lo d C f ce cx env
       rest [e] [sv] a b es s G tn H (INL [v] : value list + vyperState$exception) ee Gu tu u) R ==>
  scoped_operand_outcome D tops cx st0 a b source (es,s,G,tn)
    (\H r ee Gu tu u. ?v. r = INL v /\ extcall_positional_post keep DF lo d C f ce cx env
       rest [e] [sv] a b es s G tn H (INL [v] : value list + vyperState$exception) ee Gu tu u) R
Proof
  Cases_on `keep` >> simp[] >> PairCases_on `D` >> simp[scoped_operand_outcome_def] >>
  strip_tac >> qexists_tac `marks` >> simp[]
  >- metis_tac[]
  >- (rename1 `create_operand_full_scope _ _ _ _ _ _ _ rr` >>
      disj2_tac >> disj1_tac >> qexistsl_tac [`r`,`ee`,`rr`,`Gu`,`tu`] >>
      simp[] >> rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
      metis_tac[pos_snapshot_row_weaken]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem extcall_pos_snapshot_scoped_cut:
  body_inv tops C ce cx /\ expr_body_pre ce cx env e es /\
  MEM f C.ctx_functions /\ MEM shf shC.ctx_functions /\
  gas_shadow_context C shC /\ ctx_inst_ids_distinct C /\ gas_shadow_function f shf /\
  fn_inst_ids_distinct f /\ create_layout a b /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks b)) /\
  gas_shadow_state a sha /\ gas_shadow_state m shm /\ gas_shadow_state b shb /\
  compile_expr ce (expr_type e) e a = (vv,m) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (vv,shm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce rest)
    (ext_call_arg_value (lowered_value_type ce e) vv) m = (sv,b) /\
  compile_snapshot_vv ce (exprs_can_mutate ce rest)
    (ext_call_arg_value (lowered_value_type ce e) vv) shm = (sv,shb) /\
  fn_has_code a b f /\ fn_has_code sha shb shf /\ local_ptrs_reserved ce a /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  return_buf_frame d ce a s /\ alloca_history f s /\ ~s.vs_halted /\ create_operand_at a s /\
  (!fn i u. frag_reachable C f s fn i u ==> dalloca_fmp_headroom i u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H C f ce cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G tn s) /\
  (let E = gas_explicit_sites C shC in
   (!marks. create_operand_focus_scope a m E C f s marks ==>
            create_operand_focus_scope a b E C f s marks) /\
   (!marks r. exit_result r /\ create_operand_full_scope a m E C f s marks r ==>
              create_operand_full_scope a b E C f s marks r) /\
   (!left t right. create_operand_full_scope a m E C f s left (OK t) /\
          create_operand_focus_scope m b E C f t right ==>
          create_operand_focus_scope a b E C f s (left ++ right)) /\
   (!left t right r. create_operand_full_scope a m E C f s left (OK t) /\
            create_operand_full_scope m b E C f t right r ==>
            create_operand_full_scope a b E C f s (left ++ right) r)) /\
  (expr_vv_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx (expr_type e) e es
      (st0,a,m,sha,shm,vv,s,G,tn) /\ create_layout a m ==>
   scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) tops cx st0 a m
     (eval_expr cx e) (es,s,G,tn)
     (\H r ee G1 tn1 t.
       create_operand_vv_post (DF,lo,d,C,f) ce cx e (es,a,m,s,vv,G,tn) H r ee G1 tn1 t /\
       create_operand_at m t) (create_operand_exit_post C cx) /\
   create_operand_cut a m (gas_explicit_sites C shC) C f tops cx st0 (eval_expr cx e) (es,s)) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) tops cx st0 a b
    (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (\H r ee G1 tn1 t. ?v. r = INL v /\ extcall_positional_post keep DF lo d C f ce cx env
       rest [e] [sv] a b es s G tn H (INL [v] : value list + vyperState$exception) ee G1 tn1 t)
    (create_operand_exit_post C cx) /\
  create_operand_cut a b (gas_explicit_sites C shC) C f tops cx st0
    (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s)
Proof
  simp[LET_THM] >> strip_tac >>
  `ci_mono a m /\ ci_mono m b /\ ci_mono sha shm /\ ci_mono shm shb` by
    metis_tac[cj 1 compile_expr_ci_mono,ci_mono_compile_snapshot_vv,pairTheory.SND] >>
  `fn_has_code a m f /\ fn_has_code m b f /\ fn_has_code sha shm shf /\ fn_has_code shm shb shf` by
    metis_tac[ci_mono_def,fn_has_code_split] >>
  `create_layout a m` by metis_tac[ci_mono_def,create_layout_subinterval,cs_extends_refl] >>
  `create_cut_code {} a m` by metis_tac[cj 1 create_operand_cut_code,pairTheory.SND] >>
  `!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `storage_trace_frame (vyperState$bind (eval_expr cx e) (read_result cx))` by
    simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result] >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- suspend "row" >>
  conj_tac >- (irule stage_scoped_initial_domain >> simp[]) >>
  simp[create_operand_cut_def,entryCreateBodyCutTheory.create_body_cut_def] >>
  rpt strip_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    (drule_all valid_horizon_frame >> simp[]) >>
  metis_tac[bodyFullExtCallPackingReadyTheory.extcall_packing_observed_domain]
QED

Resume extcall_pos_snapshot_scoped_cut[row]:
  `ctx_has_dalloca C ==> allocas_below_fmp s` by
    (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
       fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> metis_tac[stmt_state_rel_allocas_below_fmp]) >>
  `expr_vv_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx (expr_type e) e es
      (st0,a,m,sha,shm,vv,s,G,tn)` by
    (drule_then assume_tac expr_body_pre_vv_gas_admissible >>
     simp[expr_vv_sim_full_pre_def] >> fs[create_operand_at_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `_ /\ create_layout a m ==> _ /\ _` mp_tac >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  reverse conj_tac >- drule_all_then ACCEPT_TAC extcall_pos_snapshot_visit_cut >>
  irule pos_snapshot_post_weaken >> irule pos_snapshot_bind >> simp[] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Finalise extcall_pos_snapshot_scoped_cut
