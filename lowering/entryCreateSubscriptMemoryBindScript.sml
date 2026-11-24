(* The framed fixed-memory case, split at the two installed child exits. *)
Theory entryCreateSubscriptMemoryBind
Ancestors
  bodyFullFramedMemorySelectionSpec entryCreateSubscriptUncopied
  entryCreateImmSubscriptIntervals entryCreateStmtUpdateCode
  entryCreateIntervalLayout entryCreateFocusSpec entryCreateOperandReplay
  createSizeCutCode fragGasOriginPtrExec exprSimSubscriptArraySource
  exprSimTopLevelProps bodyFullEmptyLeafData exprSimFullBundleProps
  gasExemptCert vyperStorageTrace vyperStorageFootprint
  exprSimDefs exprLoweringProps compileEnv
  vyperState vyperInterpreter s1PrefixDefs entryCreateCompletedCut gasSummary fragExec

(* The polymorphic sequent of immutable_bind_at_interval.  Only the two
   success-type instances used below are needed by this case. *)
Definition framed_memory_interval_bind_def:
  framed_memory_interval_bind (:'a) (:'b) <=>
  !DF lo E C f PG tops cx st0 a m b source next es s G tn P Q R ce.
    immutable_scoped_bind_law (:'a) (:'b) /\ immutable_replay_bind_law (:'a) (:'b) /\
    body_inv tops C ce cx /\ MEM f C.ctx_functions /\ create_operand_at a s /\ ~s.vs_halted /\
    create_cut_code {} a m /\ create_cut_code {} m b /\
    fn_has_code a m f /\ fn_has_code m b f /\ create_layout a b /\
    storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
    immutable_subscript_bind_certs tops C f source next es s /\
    scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
      (source : evaluation_state -> 'a evaluation_result) (es,s,G,tn)
      (\H res ee G1 tn1 t. ?v. res = INL v /\ P H v ee G1 tn1 t)
      (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
    create_operand_cut a m E C f tops cx st0 source (es,s) /\
    (!left v mid t G1 tn1.
      immutable_subscript_return (DF,lo,E,C,f,PG) cx st0 a m source (es,s,G,tn)
        P left v (mid,t,G1,tn1) ==>
      scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
        ((next : 'a -> evaluation_state -> 'b evaluation_result) v) (mid,t,G1,tn1) Q R /\
      create_operand_cut m b E C f tops cx st0 (next v) (mid,t)) ==>
    scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
      (bind source next) (es,s,G,tn) Q R /\
    create_operand_cut a b E C f tops cx st0 (bind source next) (es,s)
End

Definition framed_memory_selector_scope_def:
  framed_memory_selector_scope Obs <=>
  !st2 sc sm sb idx n sgn sz off base out E ctx f t r D lo PG G tn Gf tnf.
    (* The fixed case has no length-load leg. *)
    array_bounds_check idx (Lit (n2w n)) sgn st2 = ((),sc) /\
    emit_op MUL [idx; Lit (n2w sz)] sc = (Var off,sm) /\
    emit_op ADD [base; Var off] sm = (Var out,sb) /\
    fn_has_code st2 sb f /\ create_layout st2 sb /\
    create_operand_at st2 t /\ ~t.vs_halted /\ Obs st2 sc sb t r /\
    gas_origin_ptr_path (D,lo,E,ctx,f,PG) (t,G,tn) [] (r,Gf,tnf) ==>
    create_operand_full_scope st2 sb E ctx f t [] r
End

Definition framed_memory_selector_inventory_def:
  framed_memory_selector_inventory <=>
  !base idx n sz sgn loader st2 dst sb E ctx f t tops cx st0 source es.
    compile_array_subscript base idx F n (word_scale LocMemory) sz sgn loader st2 = (dst,sb) /\
    fn_has_code st2 sb f /\ create_layout st2 sb /\ create_operand_at st2 t ==>
    create_operand_cut st2 sb E ctx f tops cx st0
      (source : evaluation_state -> eval_result evaluation_result) (es,t)
End

Theorem framed_memory_vv_post_elim[local]:
  expr_vv_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,b,s,vv,G0,tn0) H res ee G tn t ==>
  create_operand_vv_post (DF,lo,d,ctx,f) ce cx e (es,a,b,s,vv,G0,tn0) H res ee G tn t
Proof
  simp[expr_vv_sim_full_post_def,expr_sim_full_endpoint_def,create_operand_vv_post_def] >>
  strip_tac >> qexists_tac `tv` >> simp[]
QED

Theorem framed_memory_vv_success[local]:
  (\H res ee G tn t. ?v. res = INL v /\
      expr_vv_sim_full_post args ce cx e init H (INL v) ee G tn t) =
  expr_vv_sim_full_post args ce cx e init
Proof
  PairCases_on `args` >> PairCases_on `init` >>
  simp[FUN_EQ_THM,expr_vv_sim_full_post_def] >> metis_tac[]
QED

Theorem framed_memory_value_success[local]:
  (\H res ee G tn t. ?v. res = INL v /\
      expr_sim_full_post args ce cx e init H (INL v) ee G tn t) =
  expr_sim_full_post args ce cx e init
Proof
  PairCases_on `args` >> PairCases_on `init` >>
  simp[FUN_EQ_THM,expr_sim_full_post_def] >> metis_tac[]
QED

Theorem framed_memory_exit_retype[local]:
  create_operand_exit_post ctx cx H (INR ex : 'a + exception) ee gt r <=>
  create_operand_exit_post ctx cx H (INR ex : 'b + exception) ee gt r
Proof
  Cases_on `ex` >> Cases_on `r` >>
  simp[create_operand_exit_post_def,exprSimDefsTheory.expr_exit_def,
       exprSimDefsTheory.halt_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[exprSimDefsTheory.expr_exit_def]
QED

Theorem framed_memory_exit_mixed[local]:
  (\H res ee gt r. ?exc. res = INR exc /\
    create_operand_exit_post ctx cx H (INR exc : 'b + exception) ee gt r) =
  (\H res ee gt r. create_operand_exit_post ctx cx H (res : 'a + exception) ee gt r)
Proof
  simp[FUN_EQ_THM] >>
  qx_genl_tac [`H`,`res`,`ee`,`gt`,`r`] >> Cases_on `res`
  >- (Cases_on `r` >> simp[create_operand_exit_post_def,exprSimDefsTheory.expr_exit_def]) >>
  simp[] >> irule framed_memory_exit_retype
QED

Theorem framed_memory_base_certs[local,simp]:
  immutable_subscript_bind_certs tops ctx f (eval_expr cx e) next es s
Proof
  rw[immutable_subscript_bind_certs_def] >> rewrite_tac[ignore_bind_def,bind_assoc]
  >- (irule gas_exempt_cert_error_result >> simp[]) >>
  irule gas_exempt_cert_bind_result >> qexistsl_tac [`mid`,`t`,`v`] >>
  simp[GSYM ignore_bind_def]
QED

Theorem framed_memory_index_certs[local,simp]:
  immutable_subscript_bind_certs tops ctx f
    (bind (eval_expr cx e) (read_result cx)) next es s
Proof
  rw[immutable_subscript_bind_certs_def] >>
  rewrite_tac[ignore_bind_def,Once bind_assoc]
  >- (irule gas_exempt_cert_error_value >> simp[GSYM bind_assoc]) >>
  irule gas_exempt_cert_bind_value >> qexistsl_tac [`mid`,`t`,`v`] >>
  simp[GSYM ignore_bind_def,GSYM bind_assoc]
QED

Theorem framed_memory_pre_bundle[local]:
  expr_vv_sim_full_pre args ce cx ty e es init <=>
  expr_vv_sim_full_hypotheses args ce cx ty e es init
Proof
  PairCases_on `args` >> PairCases_on `init` >>
  simp[expr_vv_sim_full_pre_def,expr_vv_sim_full_hypotheses_def,expr_sim_full_code_def,
       CONJ_ASSOC]
QED

Theorem framed_memory_terminal[local]:
  framed_memory_selection_rule Obs /\ framed_memory_selector_scope Obs /\
  framed_memory_selector_inventory /\ create_layout st2 sb /\ create_operand_at st2 it /\
  framed_memory_selection_hypotheses
    (DF,lo,d,ctx,shctx,PG,f,shf) (tops,ce,cx,env,ty,ann,e1,e2,et,n)
    (st0,es,sa,sb,sha,shb,vv,s0,G0,tn0) (sm,bvv,marks,tv,mid,s,G1,tn1)
    (st2,iop,imarks,v,fin,it,Gi,tni) dst ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
    (cx_tops cx) cx st0 st2 sb (select_result cx (expr_type e1) tv (ValueSubscript v))
    (fin,it,Gi,tni)
    (expr_vv_sim_full_post (DF,lo,d,ctx,f) ce cx (Subscript ann e1 e2)
      (es,sa,sb,s0,vv,G0,tn0)) (create_operand_exit_post ctx cx) /\
  create_operand_cut st2 sb (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
    (select_result cx (expr_type e1) tv (ValueSubscript v)) (fin,it)
Proof
  strip_tac >>
  qpat_assum `framed_memory_selection_hypotheses _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [framed_memory_selection_hypotheses_def]) >>
  reverse conj_tac
  >- (qpat_x_assum `framed_memory_selector_inventory`
        (irule o REWRITE_RULE [framed_memory_selector_inventory_def]) >>
      qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >> simp[]) >>
  qpat_x_assum `framed_memory_selection_rule _`
    (drule_then strip_assume_tac o REWRITE_RULE [framed_memory_selection_rule_def])
  >>
  `create_operand_full_scope st2 sb (gas_explicit_sites ctx shctx) ctx f it [] r` by
    (qpat_x_assum `framed_memory_selector_scope _`
       (irule o REWRITE_RULE [framed_memory_selector_scope_def]) >> simp[] >>
     qpat_assum `emit_op ADD _ _ = _` (irule_at Any) >>
     qpat_assum `emit_op MUL _ _ = _` (irule_at Any) >>
     qpat_assum `array_bounds_check _ _ _ _ = _` (irule_at Any) >> simp[] >>
     qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> gas_origin_ptr_path _ _ [] _`
       (qspec_then `storage_trace_horizon fin.storage_trace` mp_tac) >>
     fs[storage_trace_domain_def] >> metis_tac[]) >>
  simp[scoped_operand_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`,`fin`,`r`,`Gf`,`tnf`] >> simp[gas_explicit_def] >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  rpt strip_tac >> gvs[create_operand_exit_post_def,exit_result_def] >> metis_tac[]
QED

Theorem framed_memory_clear_tail[local]:
  mid.gas_obs = [] /\
  (!tail. source (es with gas_obs := prefix ++ tail) = (INL v,mid with gas_obs := tail)) ==>
  source (es with gas_obs := prefix) = (INL v,mid)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac (qspec_then `[]` mp_tac)) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >> simp[]
QED

(* The two recursive callbacks are confined to the installed child intervals.
   The index callback carries the normal return of the selected base. *)
Theorem create_framed_memory_subscript_from_selection:
  framed_memory_selection_rule Obs /\ framed_memory_selector_scope Obs /\
  framed_memory_selector_inventory /\
  framed_memory_interval_bind (:eval_result) (:eval_result) /\
  framed_memory_interval_bind (:value) (:eval_result) /\
  immutable_scoped_bind_law (:eval_result) (:eval_result) /\
  immutable_replay_bind_law (:eval_result) (:eval_result) /\
  immutable_scoped_bind_law (:value) (:eval_result) /\
  immutable_replay_bind_law (:value) (:eval_result) /\
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  ~subscript_reads_base cx e1 e2 /\ ~copies_subscript_base ce e1 e2 /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env (Subscript ann e1 e2) es /\
  expr_type e1 = ArrayT et (Fixed n) /\
  place_type ce e1 = ValPT (ArrayT et (Fixed n)) /\
  post_value_type ce e1 = expr_type e1 /\
  (!t res t'. eval_expr cx e2 t = (INL res,t') ==>
     t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
  (!t tr slot vt t'. eval_expr cx e1 t <> (INL (PlaceR (StoragePlace tr slot vt)),t')) /\
  (!rt. evaluate_type (get_tenv cx) et = SOME rt ==> dynarray_free rt) /\
  (!ty' st. vv_location (FST (compile_expr ce ty' e1 st)) = SOME LocMemory) /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty (Subscript ann e1 e2)
    es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) /\ create_layout sa sb /\
  (!sm shm bvv.
    expr_body_pre ce cx env e1 es /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty e1
      es (st0,sa,sm,sha,shm,bvv,s0,G0,tn0) /\ create_layout sa sm ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 sa sm (eval_expr cx e1) (es,s0,G0,tn0)
      (expr_vv_sim_full_post (DF,lo,d,ctx,f) ce cx e1 (es,sa,sm,s0,bvv,G0,tn0))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut sa sm (gas_explicit_sites ctx shctx) ctx f tops cx st0
      (eval_expr cx e1) (es,s0)) /\
  (!gs tv mid s G1 tn1 sm shm st2 sh2 iop.
    eval_expr cx e1 (es with gas_obs := gs) = (INL tv,mid) /\
    body_const_cells_agree [(NONE,tops)] cx env mid /\ expr_body_pre ce cx env e2 mid /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty e2
      mid (st0,sm,st2,shm,sh2,iop,s,G1,tn1) /\ create_layout sm st2 ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 sm st2 (bind (eval_expr cx e2) (read_result cx)) (mid,s,G1,tn1)
      (expr_sim_full_post (DF,lo,d,ctx,f) ce cx e2 (mid,sm,st2,s,iop,G1,tn1))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut sm st2 (gas_explicit_sites ctx shctx) ctx f tops cx st0
      (bind (eval_expr cx e2) (read_result cx)) (mid,s)) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
    (cx_tops cx) cx st0 sa sb (eval_expr cx (Subscript ann e1 e2)) (es,s0,G0,tn0)
    (expr_vv_sim_full_post (DF,lo,d,ctx,f) ce cx (Subscript ann e1 e2) (es,sa,sb,s0,vv,G0,tn0))
    (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx f tops cx st0
    (eval_expr cx (Subscript ann e1 e2)) (es,s0)
Proof
  strip_tac >>
  `cx_tops cx = tops` by fs[bodySimTheory.body_inv_def,gasContextTheory.cx_tops_def] >>
  qpat_x_assum `cx_tops cx = tops` (SUBST_ALL_TAC o SYM) >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ (Subscript _ _ _) _ _`
    (strip_assume_tac o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
  drule_all_then (qx_choosel_then [`bvv`,`sm`,`shm`,`iop`,`st2`,`sh2`,`dst`,`loc`] strip_assume_tac)
    subscript_nocopy_selected_layout >>
  `vv_location bvv = SOME LocMemory` by metis_tac[pairTheory.FST] >> gvs[] >>
  `cs_extends sa st2 /\ cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  `create_layout sa sm /\ create_layout sm st2 /\ create_layout st2 sb /\ create_layout sm sb` by
    metis_tac[create_layout_subinterval,cs_extends_refl] >>
  `fn_has_code sm sb f` by metis_tac[fn_has_code_split] >>
  `create_operand_at sa s0` by simp[create_operand_at_def] >>
  `~array_slot_base ce e1` by metis_tac[array_slot_base_compile_location,pairTheory.FST] >>
  drule_all_then strip_assume_tac subscript_nocopy_base_ready >>
  qpat_assum `!sm shm bvv. _ ==> _ /\ _` (qspecl_then [`sm`,`shm`,`bvv`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ e1 _ _`
    (mp_then Any assume_tac operand_vv_cut_code) >>
  `create_cut_code {} st2 sb` by
    (qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     irule update_array_subscript_cut >> simp[]) >>
  `create_cut_code {} sm sb` by
    (irule create_cut_code_join >> qexists_tac `st2` >>
     simp[] >>
     qpat_assum `lower_value compile_expr ce ty e2 sm = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[createSizeOperandCodeTheory.create_operand_cut_code]) >>
  qpat_assum `~subscript_reads_base _ _ _` (SUBST1_TAC o MATCH_MP eval_expr_subscript_bind) >>
  qpat_x_assum `framed_memory_interval_bind (:eval_result) (:eval_result)`
    (irule o REWRITE_RULE [framed_memory_interval_bind_def]) >>
  simp[evaluate_storage_trace_frame,storage_trace_frame_bind_all,
       storage_trace_frame_select,storage_trace_frame_read_result] >>
  conj_tac >- (qexists_tac `ce` >> simp[]) >>
  qexistsl_tac [`\H raw ee G tn t. expr_vv_sim_full_post (DF,lo,d,ctx,f) ce cx e1
      (es,sa,sm,s0,bvv,G0,tn0) H (INL raw : eval_result + exception) ee G tn t`,`sm`] >>
  simp[framed_memory_vv_success,framed_memory_exit_mixed] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[] >>
  qx_genl_tac [`marks`,`tv`,`mid`,`s`,`G1`,`tn1`] >>
  simp[immutable_subscript_return_def] >> strip_tac >>
  suspend "after_base"
QED

Resume create_framed_memory_subscript_from_selection[after_base]:
  `eval_expr cx e1 (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,mid)` by
    (irule framed_memory_clear_tail >> simp[] >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    create_operand_vv_post (DF,lo,d,ctx,f) ce cx e1
      (es,sa,sm,s0,bvv,G0,tn0) H (INL tv : eval_result + exception) mid G1 tn1 s /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (s0,G0,tn0) marks (OK s,G1,tn1)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
       (drule_then strip_assume_tac) >>
     simp[] >> irule framed_memory_vv_post_elim >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac subscript_nocopy_index_ready >>
  qpat_assum `!gs tv mid s G1 tn1 sm shm st2 sh2 iop. _ ==> _ /\ _`
    (qspecl_then [`gas_explicit marks s0.vs_gas_readings`,`tv`,`mid`,`s`,`G1`,`tn1`,
                  `sm`,`shm`,`st2`,`sh2`,`iop`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `expr_sim_full_pre _ _ _ _ e2 _ _`
    (mp_then Any assume_tac operand_value_cut_code) >>
  qpat_x_assum `framed_memory_interval_bind (:value) (:eval_result)`
    (irule o REWRITE_RULE [framed_memory_interval_bind_def]) >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
       storage_trace_frame_read_result,storage_trace_frame_select] >>
  conj_tac >- (qexists_tac `ce` >> simp[]) >>
  qexistsl_tac [`\H v ee G tn t. expr_sim_full_post (DF,lo,d,ctx,f) ce cx e2
      (mid,sm,st2,s,iop,G1,tn1) H (INL v : value + exception) ee G tn t`,`st2`] >>
  simp[framed_memory_value_success,framed_memory_exit_mixed] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[] >>
  qx_genl_tac [`imarks`,`v`,`fin`,`it`,`Gi`,`tni`] >>
  simp[immutable_subscript_return_def] >> strip_tac >>
  `framed_memory_selection_hypotheses
     (DF,lo,d,ctx,shctx,PG,f,shf) (cx_tops cx,ce,cx,env,ty,ann,e1,e2,et,n)
     (st0,es,sa,sb,sha,shb,LocatedValue ann (mk_ptr dst LocMemory),s0,G0,tn0)
     (sm,bvv,marks,tv,mid,s,G1,tn1) (st2,iop,imarks,v,fin,it,Gi,tni) dst` by
    simp[framed_memory_selection_hypotheses_def,GSYM framed_memory_pre_bundle] >>
  qpat_assum `expr_type e1 = _` (SUBST1_TAC o SYM) >>
  irule framed_memory_terminal >>
  qpat_assum `framed_memory_selection_hypotheses _ _ _ _ _ _` (irule_at Any) >>
  qexists_tac `Obs` >> simp[]
QED

Finalise create_framed_memory_subscript_from_selection
