(* The selected ternary's source/physical continuation at its arm exit. *)
Theory entryCreateIfExpOutcome
Ancestors
  entryCreateFocusSpec entryCreateScopedBind bodyFullIfExpPrepare
  vyperStorageTrace vyperStorageFootprint fragGasOriginPtr
  entryCreateCompletedCut gasSummary gasSummaryCompose gasExemptCert stmtSimProps list
  exprSimFullBundleProps s1PrefixDefs exprSimIfExp freshWrites bodySimFull
  exprLoweringProps loweringPosts exprSimDefs allocaHistory venomState
  exprSimMemDefs bodyMemoryDefs bodyPtrDefs gasExplicitSites gasContext bodyFullPreds
  compileEnv vyperState entryCreateIfExpMidpoint entryIntCallStageNeutral haltExitProj fragGasOriginPtrExec
  createSizeCutRegion createSizeCutCode fragExec venomExecSemantics

(* The source step consumes nothing. Both physical suffixes are on the
   same execution that supplies the materialization and final VV posts. *)
Triviality ifexp_conditional_scoped_suffix:
  storage_trace_domain cx st0 ee.storage_trace /\
  (!tail. conditional_result cx raw (ee with gas_obs := tail) =
    (INL tv,ee with gas_obs := tail)) /\
  create_operand_full_scope sm sb E ctx fn z [] (OK t) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,E,ctx,fn,PG) (z,G,tn) [] (OK m,G1,tn1) /\
    gas_origin_ptr_path (DF H,lo,E,ctx,fn,PG) (m,G1,tn1) [] (OK t,G2,tn2) /\
    Q H (INL tv) (ee with gas_obs := []) G2 tn2 t) ==>
  scoped_operand_outcome (DF,lo,E,ctx,fn,PG) tops cx st0 sm sb
    (conditional_result cx raw) (ee,z,G,tn) Q R
Proof
  strip_tac >> simp[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`INL tv`,`ee`,`OK t`,`G2`,`tn2`] >>
  simp[gas_explicit_def] >> rpt strip_tac >> res_tac >>
  metis_tac[gas_origin_ptr_path_append,APPEND_NIL]
QED

(* A completed condition transfers the root pre to the actual arm entry.
   This uses the condition's path at its own marks, not parent success. *)
Theorem ifexp_selected_arm_after_test:
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfn) ce cx ty (IfExp t c a b) es
    (st0,sa,sb,sha,shb,vv,s0,G0,tn0) /\
  expr_type c = BaseT BoolT /\
  e = (if sel then a else b) /\ lbl = (if sel then tl else el) /\
  (!tail. vyperState$bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL (BoolV sel),mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
  ~z.vs_halted /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx c (es,sa,sc,s0,cop,G0,tn0)
      H (INL (BoolV sel)) mid G1 tn1 z /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
      (s0,G0,tn0) marks (OK z,G1,tn1)) /\
  emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\ fn_has_code sj sn fnc /\
  sj.cs_current_bb = sc.cs_current_bb /\ sj.cs_current_insts = sc.cs_current_insts /\
  se.cs_current_bb = lbl /\ se.cs_current_insts = [] /\
  compile_expr ce ty e se = (av,sm) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) shse = (av,shsm) /\
  gas_shadow_state se shse /\ gas_shadow_state sm shsm /\
  fn_has_code se sm fnc /\ fn_has_code shse shsm shfn /\
  local_ptrs_reserved ce se /\ sa.cs_next_var <= se.cs_next_var /\
  compile_ifexp_arm ce t (lowered_value_type ce e) av sm = (op,sx) /\
  emit_inst ASSIGN [op] [rv] sx = ((),sy) /\ fn_has_code sm sx fnc /\ fn_has_code sx sy fnc ==>
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfn) ce cx ty e mid
    (st0,se,sm,shse,shsm,av,jump_to lbl z,G1,tn1) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
      (z,G1,tn1) [] (OK (jump_to lbl z),G1,tn1))
Proof
  strip_tac >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
      (z,G1,tn1) [] (OK (jump_to (if sel then tl else el) z),G1,tn1)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (strip_assume_tac o SIMP_RULE (srw_ss())
       [expr_sim_full_post_def, expr_sim_full_endpoint_def]) >>
     `allocas_from lo z` by fs[ghost_inv_at_def] >>
     `op_taint tn1 cop = {}` by fs[ptr_val_ok_def, is_word_type_def] >>
     drule_all ifexp_root_jnz_origin_path >> simp[]) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `gas_admissible (eval_expr cx (if sel then a else b)) expr_vv_res_ok mid` by
    (irule ifexp_arm_raw_admissible >>
     drule_all ifexp_root_branch_admissible >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss())
    [expr_sim_full_post_def, expr_sim_full_endpoint_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (z,G1,tn1) _ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> disch_tac >>
  qpat_x_assum `lbl = (if sel then tl else el)` SUBST_ALL_TAC >>
  drule_all ifexp_selected_jump_ready >> strip_tac >>
  `( !x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
   ( !x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x)` by
     metis_tac[not_fresh_at_mono] >>
  simp[expr_vv_sim_full_pre_def] >> rpt strip_tac
  >- (first_assum (drule_then ACCEPT_TAC)) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[NoAsms, expr_sim_full_post_def, ifexp_ghost_inv_at_jump, stmt_state_rel_jump_to, expr_post_def]
QED

Triviality ifexp_scoped_condition_post:
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 sa sc
    (source : evaluation_state -> value evaluation_result)
    (es,s0,G0,tn0) P (create_operand_exit_post ctx cx) ==>
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 sa sc source
    (es,s0,G0,tn0) (\H res mid G tn z. P H res mid G tn z /\ mid.gas_obs = [])
    (\H res ee gt r. ?exc. res = INR exc /\
      create_operand_exit_post ctx cx H (INR exc : eval_result + exception) ee gt r)
Proof
  rewrite_tac[scoped_operand_outcome_def] >> strip_tac >> qexists `marks`
  >- (disj1_tac >> metis_tac[]) 
  >- (disj2_tac >> disj1_tac >> qexistsl [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> simp[] >>
      disj2_tac >> simp[] >>
      Cases_on `res` >- fs[create_operand_exit_post_def, expr_exit_def] >>
      fs[create_operand_exit_post_def] >> metis_tac[halt_exit_INR_type, expr_exit_INR_type]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

(* The arm's source is sequenced only at its successful scoped endpoint.
   The supplied physical suffix witnesses are the materialization and finish,
   not an outcome of the selected arm or of the parent. *)

Theorem ifexp_scoped_arm_conditional[local]:
  let source = eval_expr cx e;
      next = conditional_result cx;
      R = create_operand_exit_post ctx cx
  in
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 se sm
    source (mid,u,G1,tn1) P R /\
  gas_admissible (bind source next) expr_vv_res_ok mid /\
  (!marks res ee G tn z.
    (!tail. source (mid with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail) =
      (res,ee with gas_obs := tail)) /\
    storage_trace_domain cx st0 ee.storage_trace /\ create_operand_at sm z /\
    create_operand_full_scope se sm E ctx f u marks (OK z) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      P H res ee G tn z /\
      gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (u,G1,tn1) marks (OK z,G,tn)) ==>
    ?raw v. res = INL raw /\ read_result cx raw ee = (INL v,ee) /\
      !tv. (!tail. next raw (ee with gas_obs := tail) = (INL tv,ee with gas_obs := tail)) /\
        read_result cx tv ee = (INL v,ee) ==>
        ?m Gm tm t Gt tt.
          create_operand_full_scope sm sb E ctx f z [] (OK t) /\
          !H. valid_horizon cx st0 H ee.storage_trace ==>
            gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (z,G,tn) [] (OK m,Gm,tm) /\
            gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (m,Gm,tm) [] (OK t,Gt,tt) /\
            Q H (INL tv) (ee with gas_obs := []) Gt tt t) /\
  (!marks. create_operand_focus_scope se sm E ctx f u marks ==>
     create_operand_focus_scope se sb E ctx f u marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope se sm E ctx f u marks r ==>
     create_operand_full_scope se sb E ctx f u marks r) /\
  (!left z right. create_operand_full_scope se sm E ctx f u left (OK z) /\
     create_operand_focus_scope sm sb E ctx f z right ==>
     create_operand_focus_scope se sb E ctx f u (left ++ right)) /\
  (!left z right r. create_operand_full_scope se sm E ctx f u left (OK z) /\
     create_operand_full_scope sm sb E ctx f z right r ==>
     create_operand_full_scope se sb E ctx f u (left ++ right) r) ==>
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 se sb
    (bind source next) (mid,u,G1,tn1) Q R
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  irule scoped_operand_bind_all >> simp[] >>
  rpt conj_tac >> simp[evaluate_storage_trace_frame, storage_trace_frame_conditional_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_result >> qexistsl [`mid'`,`t`,`v`] >>
      simp[GSYM ignore_bind_def])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_error_result >> simp[GSYM ignore_bind_def])
  >> qexistsl [`P`,`sm`] >> simp[] >>
  reverse (rpt conj_tac >> TRY (first_assum ACCEPT_TAC))
  >- (qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ P _`
        (strip_assume_tac o ONCE_REWRITE_RULE [scoped_operand_outcome_def]) >>
      rewrite_tac[scoped_operand_outcome_def] >> qexists `marks`
      >- (disj1_tac >> metis_tac[])
      >- (disj2_tac >> disj1_tac >> qexistsl [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
          rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> simp[] >>
          Cases_on `res` >> gvs[create_operand_exit_post_def, expr_exit_def]) >>
      disj2_tac >> disj2_tac >> metis_tac[]) >>
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`z`] >> strip_tac >>
  qpat_x_assum `!marks res ee G tn z. _ ==> ?raw v. _` (drule_all_then strip_assume_tac) >>
  qexists_tac `raw` >> simp[] >>
  qpat_assum `!tail. _ = _` (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL])) >>
  `read_result cx raw (ee with gas_obs := []) = (INL v,ee with gas_obs := [])` by
    metis_tac[exprSimMemorySourceTheory.read_result_gas_obs] >>
  qpat_x_assum `res = INL raw` SUBST_ALL_TAC >>
  drule_all ifexp_arm_pure_source >> strip_tac >>
  `read_result cx ctv ee = (INL v,ee)` by
    (drule exprSimMemorySourceTheory.read_result_gas_obs >>
     disch_then (qspec_then `ee.gas_obs` mp_tac) >> simp[]) >>
  qpat_x_assum `!tail. conditional_result cx raw _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `!tv. _ ==> ?m Gm tm t Gt tt. _` (qspec_then `ctv` mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`m`,`Gm`,`tm`,`tf`,`Gf`,`tnf`] strip_assume_tac) >>
  irule ifexp_conditional_scoped_suffix >> simp[] >>
  qexistsl [`Gm`,`Gf`,`m`,`tf`,`tm`,`tnf`] >> simp[]
QED
(* The outer bind changes success payloads from the forced Boolean value to
   a VV; exceptional outcomes keep their payload and endpoint. *)
Triviality ifexp_scoped_test_then_arm:
  let source = bind (eval_expr cx c) (read_result cx);
      next = (\v. if v = BoolV T then bind (eval_expr cx a) (conditional_result cx)
                  else if v = BoolV F then bind (eval_expr cx b) (conditional_result cx)
                  else raise (Error (TypeError "not BoolV")));
      P = expr_sim_full_post (DF,lo,d,ctx,f) ce cx c (es,sa,sc,s0,cop,G0,tn0);
      R = create_operand_exit_post ctx cx
  in
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 sa sc
    source (es,s0,G0,tn0) P (create_operand_exit_post ctx cx) /\
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
  (!marks sel mid G1 tn1 z.
    (!tail. source (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL (BoolV sel),mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\ create_operand_at sc z /\
    create_operand_full_scope sa sc E ctx f s0 marks (OK z) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      P H (INL (BoolV sel)) (mid with gas_obs := []) G1 tn1 z /\
      gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (s0,G0,tn0) marks (OK z,G1,tn1)) /\
    gas_marked_exec T (ctx,f) source (es,s0) marks (INL (BoolV sel)) mid (OK z) /\
    gas_admissible (bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
      expr_vv_res_ok (mid with gas_obs := []) ==>
    scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 sc sb
      (bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
      (mid with gas_obs := [],z,G1,tn1) Q R) /\
  (!marks. create_operand_focus_scope sa sc E ctx f s0 marks ==>
     create_operand_focus_scope sa sb E ctx f s0 marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope sa sc E ctx f s0 marks r ==>
     create_operand_full_scope sa sb E ctx f s0 marks r) /\
  (!left z right. create_operand_full_scope sa sc E ctx f s0 left (OK z) /\
     create_operand_focus_scope sc sb E ctx f z right ==>
     create_operand_focus_scope sa sb E ctx f s0 (left ++ right)) /\
  (!left z right r. create_operand_full_scope sa sc E ctx f s0 left (OK z) /\
     create_operand_full_scope sc sb E ctx f z right r ==>
     create_operand_full_scope sa sb E ctx f s0 (left ++ right) r) ==>
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 sa sb
    (eval_expr cx (IfExp t c a b)) (es,s0,G0,tn0) Q R
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `scoped_operand_outcome _ _ _ _ _ _ (bind _ (read_result _)) _ P _` >>
  qpat_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ P _`
    (assume_tac o MATCH_MP ifexp_scoped_condition_post) >>
  rewrite_tac[ifexp_root_eval_forced] >> irule scoped_operand_bind_all_mixed >>
  simp[storage_trace_frame_bind, evaluate_storage_trace_frame, storage_trace_frame_read_result] >>
  rpt conj_tac
  >- (gen_tac >> BETA_TAC >> rpt IF_CASES_TAC >> simp[storage_trace_frame_bind,
        evaluate_storage_trace_frame, storage_trace_frame_conditional_result,
        storage_trace_frame_raise])
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> rewrite_tac[stmtSimForcedTheory.ignore_bind_bind_value] >>
      irule gas_exempt_cert_bind_value >> qexistsl [`mid`,`t'`,`v`] >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> rewrite_tac[stmtSimForcedTheory.ignore_bind_bind_value] >>
      irule gas_exempt_cert_error_value >> simp[]) >>
  qexistsl [`\H res ee G tn z. P H res ee G tn z /\ ee.gas_obs = []`,`sc`] >>
  simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qunabbrev_tac `P` >> rpt gen_tac >> strip_tac >>
  irule ifexp_condition_selected_callback >> simp[] >>
  qexistsl [`G0`,`c`,`ce`,`d`,`es`,`marks`,`cop`,`s0`,`sa`,`t`,`tn0`] >>
  fs[] >> metis_tac[]
QED
(* Only the scope of the selected administrative edges and the physical
   materialization/finish observers are supplied. The selected continuation
   is assembled here from the guarded children. *)
Theorem ifexp_selected_vv_scoped_intro:
  let E = gas_explicit_sites ctx shctx;
      F = (DF,lo,d,ctx,shctx,PG,f,shf);
      source = bind (eval_expr cx c) (read_result cx);
      root = IfExp t c a b;
      R = create_operand_exit_post ctx cx;
      post = (\e es st_start st_stop u av G tn H res ee G' tn' z.
        create_operand_vv_post (DF,lo,d,ctx,f) ce cx e
          (es,st_start,st_stop,u,av,G,tn) H res ee G' tn' z /\
        create_operand_at st_stop z)
  in
  body_inv (cx_tops cx) ctx ce cx /\ shadow_body_inv (cx_tops cx) ctx shctx /\
  expr_body_pre ce cx env root es /\
  (!st0 sa sc sha shsc cop s0 G0 tn0.
    expr_body_pre ce cx env c es /\ L sa sc /\
    expr_sim_full_pre F ce cx (BaseT BoolT) c es
      (st0,sa,sc,sha,shsc,cop,s0,G0,tn0) ==>
    scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 sa sc source
      (es,s0,G0,tn0)
      (expr_sim_full_post (DF,lo,d,ctx,f) ce cx c (es,sa,sc,s0,cop,G0,tn0))
      (create_operand_exit_post ctx cx)) /\
  (!sel mid st0 se sm shse shsm av u G1 tn1.
    let e = if sel then a else b in
    expr_body_pre ce cx env e mid /\ L se sm /\
    expr_vv_sim_full_pre F ce cx ty e mid (st0,se,sm,shse,shsm,av,u,G1,tn1) ==>
    scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 se sm
      (eval_expr cx e) (mid,u,G1,tn1) (post e mid se sm u av G1 tn1) R) /\
  (!st0 sa sb sha shb vv s0 G0 tn0.
    expr_vv_sim_full_pre F ce cx ty root es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) /\ L sa sb ==>
    ?cop sc shsc sj sn tl el.
      L sa sc /\ expr_sim_full_pre F ce cx (BaseT BoolT) c es
        (st0,sa,sc,sha,shsc,cop,s0,G0,tn0) /\
      emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\ fn_has_code sj sn f /\
      sj.cs_current_bb = sc.cs_current_bb /\ sj.cs_current_insts = sc.cs_current_insts /\
      (!marks. create_operand_focus_scope sa sc E ctx f s0 marks ==>
        create_operand_focus_scope sa sb E ctx f s0 marks) /\
      (!marks r. exit_result r /\ create_operand_full_scope sa sc E ctx f s0 marks r ==>
        create_operand_full_scope sa sb E ctx f s0 marks r) /\
      (!left z right. create_operand_full_scope sa sc E ctx f s0 left (OK z) /\
        create_operand_focus_scope sc sb E ctx f z right ==>
        create_operand_focus_scope sa sb E ctx f s0 (left ++ right)) /\
      (!left z right r. create_operand_full_scope sa sc E ctx f s0 left (OK z) /\
        create_operand_full_scope sc sb E ctx f z right r ==>
        create_operand_full_scope sa sb E ctx f s0 (left ++ right) r) /\
      !sel. ?se sm sx sy shse shsm av op rv.
        let e = if sel then a else b;
            lbl = if sel then tl else el in
        L se sm /\ se.cs_current_bb = lbl /\ se.cs_current_insts = [] /\
        compile_expr ce ty e se = (av,sm) /\
        compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) shse = (av,shsm) /\
        gas_shadow_state se shse /\ gas_shadow_state sm shsm /\
        fn_has_code se sm f /\ fn_has_code shse shsm shf /\
        local_ptrs_reserved ce se /\ sa.cs_next_var <= se.cs_next_var /\
        compile_ifexp_arm ce t (lowered_value_type ce e) av sm = (op,sx) /\
        emit_inst ASSIGN [op] [rv] sx = ((),sy) /\ fn_has_code sm sx f /\ fn_has_code sx sy f /\
        sc.cs_next_id <= se.cs_next_id /\ se.cs_next_id <= sb.cs_next_id /\
        (!bb inst. lookup_block sb.cs_current_bb f.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH sb.cs_current_insts) = SOME inst ==>
          inst.inst_id NOTIN frag_ids sc se) /\
        create_cut_code {} se sb /\ fn_has_code se sb f /\
        !marks mid G1 tn1 z.
          let u = jump_to lbl z in
          (!tail. source (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
            (INL (BoolV sel),mid with gas_obs := tail)) /\
          storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
          create_operand_at sc z /\ create_operand_full_scope sa sc E ctx f s0 marks (OK z) /\
          (!H. valid_horizon cx st0 H mid.storage_trace ==>
            expr_sim_full_post (DF,lo,d,ctx,f) ce cx c (es,sa,sc,s0,cop,G0,tn0)
              H (INL (BoolV sel)) mid G1 tn1 z /\
            gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (s0,G0,tn0) marks (OK z,G1,tn1)) ==>
          expr_body_pre ce cx env e mid /\
          create_operand_full_scope sc se E ctx f z [] (OK u) /\ create_cut_region se sb u /\
          (!right. create_operand_focus_scope se sm E ctx f u right ==>
            create_operand_focus_scope se sb E ctx f u right) /\
          (!right r. exit_result r /\ create_operand_full_scope se sm E ctx f u right r ==>
            create_operand_full_scope se sb E ctx f u right r) /\
          (!left j right. create_operand_full_scope se sm E ctx f u left (OK j) /\
            create_operand_focus_scope sm sb E ctx f j right ==>
            create_operand_focus_scope se sb E ctx f u (left ++ right)) /\
          (!left j right r. create_operand_full_scope se sm E ctx f u left (OK j) /\
            create_operand_full_scope sm sb E ctx f j right r ==>
            create_operand_full_scope se sb E ctx f u (left ++ right) r) /\
          (!right res ee G tn j.
            (!tail. eval_expr cx e (mid with gas_obs := gas_explicit right u.vs_gas_readings ++ tail) =
              (res,ee with gas_obs := tail)) /\
            storage_trace_domain cx st0 ee.storage_trace /\ create_operand_at sm j /\
            create_operand_full_scope se sm E ctx f u right (OK j) /\
            (!H. valid_horizon cx st0 H ee.storage_trace ==>
              post e mid se sm u av G1 tn1 H res ee G tn j /\
              gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (u,G1,tn1) right (OK j,G,tn)) ==>
            ?raw v. res = INL raw /\ read_result cx raw ee = (INL v,ee) /\
              !tv. (!tail. conditional_result cx raw (ee with gas_obs := tail) =
                    (INL tv,ee with gas_obs := tail)) /\ read_result cx tv ee = (INL v,ee) ==>
                ?m Gm tm fin Gf tf.
                  create_operand_at sx m /\
                  create_operand_full_scope sm sx E ctx f j [] (OK m) /\
                  create_operand_full_scope sx sb E ctx f m [] (OK fin) /\
                  create_operand_full_scope sm sb E ctx f j [] (OK fin) /\
                  !H. valid_horizon cx st0 H ee.storage_trace ==>
                    gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (j,G,tn) [] (OK m,Gm,tm) /\
                    gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (m,Gm,tm) [] (OK fin,Gf,tf) /\
                    post root es sa sb s0 vv G0 tn0 H (INL tv) (ee with gas_obs := []) Gf tf fin)) ==>
  !st0 sa sb sha shb vv s0 G0 tn0.
    expr_vv_sim_full_pre F ce cx ty root es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) /\ L sa sb ==>
    scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 sa sb
      (eval_expr cx root) (es,s0,G0,tn0) (post root es sa sb s0 vv G0 tn0) R
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule ifexp_body_pre_children >> strip_tac >>
  qpat_x_assum `!st0 sa sb sha shb vv s0 G0 tn0. _ ==> ?cop sc shsc sj sn tl el. _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!st0 sa sc sha shsc cop s0 G0 tn0. _ ==> scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (drule_all_then assume_tac) >>
  `gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
   MEM f ctx.ctx_functions` by fs[expr_vv_sim_full_pre_def] >>
  irule (SIMP_RULE bool_ss [LET_THM] ifexp_scoped_test_then_arm) >>
  qpat_assum `scoped_operand_outcome _ _ _ _ _ _ (bind _ (read_result _)) _ _ _`
    (irule_at Any) >> simp[] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qx_genl_tac [`marks`,`sel`,`mid`,`G1`,`tn1`,`z`] >> strip_tac >>
  qpat_x_assum `!sel. ?se sm sx sy shse shsm av op rv. _`
    (qspec_then `sel` strip_assume_tac) >>
  `!tail. bind (eval_expr cx c) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL (BoolV sel),(mid with gas_obs := []) with gas_obs := tail)` by simp[] >>
  `storage_trace_domain cx st0 (mid with gas_obs := []).storage_trace /\
   (mid with gas_obs := []).gas_obs = []` by simp[] >>
  `!H. valid_horizon cx st0 H (mid with gas_obs := []).storage_trace ==>
    expr_sim_full_post (DF,lo,d,ctx,f) ce cx c (es,sa,sc,s0,cop,G0,tn0)
      H (INL (BoolV sel)) (mid with gas_obs := []) G1 tn1 z /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (s0,G0,tn0) marks (OK z,G1,tn1)` by
    (`(mid with gas_obs := []).storage_trace = mid.storage_trace` by simp[] >>
     pop_assum (pure_rewrite_tac o single) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _ /\ gas_origin_ptr_path _ _ _ _`
       mp_tac >> simp[]) >>
  `~z.vs_halted` by
    (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
       fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  qpat_x_assum `!tail. _ = (_,mid with gas_obs := tail)` kall_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _` kall_tac >>
  qabbrev_tac `mid0 = mid with gas_obs := []` >>
  qpat_x_assum `!marks mid G1 tn1 z. _ ==> expr_body_pre _ _ _ _ _ /\ _`
    (drule_all_then strip_assume_tac) >>
  drule_all ifexp_selected_arm_after_test >> simp[] >> strip_tac >>
  qpat_x_assum `!sel mid st0 se sm shse shsm av u G1 tn1. _ ==>
     scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (drule_all_then assume_tac) >>
  irule stage_scoped_zero_prefix >> simp[] >>
  FAIL_TAC "JNZ scope and arm bind"
QED
