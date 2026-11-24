(* Scoped RawRevert at the installed value or VV interval. *)
Theory entryCreateRawRevertCase
Ancestors
  entryCreateEffectFocus entryCreateNativeFirstExit entryCreateIntervalLayout
  entryCreateRegionLift bodyFullRawRevertInterfaces gasShadowCompileStmtHelpers
  createSizeOperandCode exprSimSource vyperSystemControl vyperStorageTrace
  gasExemptCert bodyFullPreds s1PrefixDefs exprLoweringProps
  compilerInstructionSuffix gasShadowState gasExplicitSites vyperInterpreter
  vyperState fragExec exprSimDefs exprLowering builtinSystem vyperAST compileEnv
  entryCreatePathScope createSizePrefixReplay abiEncoderProps entryCreateCompletedCut
  arithmetic list gasShadow entryCreateFocusSpec
Libs
  pairLib

Theorem raw_revert_compiled_stack[local]:
  compile_expr ce ty (Call ann RawRevert [e] dflt) a = (vv,b) ==>
  vv = StackValue ann (Lit 0w)
Proof
  simp[Once compile_expr_def, compile_call_def, expr_type_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[])
QED

Theorem raw_revert_value_compile[local]:
  lower_value compile_expr ce ty (Call ann RawRevert [e] dflt) a = (op,b) ==>
  op = Lit 0w /\
  compile_expr ce ty (Call ann RawRevert [e] dflt) a = (StackValue ann (Lit 0w),b)
Proof
  simp[lower_value_def, comp_bind_def] >> pairarg_tac >> strip_tac >>
  drule raw_revert_compiled_stack >> strip_tac >>
  gvs[unwrap_value_def, comp_return_def]
QED

Theorem raw_revert_value_source[local]:
  eval_expr cx call =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (lift_option_type (dest_BytesV v) "raw_revert data")
        (\data. raise (Error (RevertData data)))) ==>
  bind (eval_expr cx call) (read_result cx) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (lift_option_type (dest_BytesV v) "raw_revert data")
        (\data. raise (Error (RevertData data))))
Proof
  disch_then SUBST1_TAC >> simp[bind_assoc] >>
  simp[FUN_EQ_THM, bind_def, raise_def] >> rpt gen_tac >>
  rpt (CASE_TAC >> simp[])
QED

Theorem raw_revert_site_scopes[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\ create_cut_region a m s /\
  cs_extends a m /\ cs_extends m b /\ create_layout a b /\
  a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id ==>
  (!marks. create_operand_focus_scope a m E ctx f s marks ==>
           create_operand_focus_scope a b E ctx f s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E ctx f s marks r ==>
             create_operand_full_scope a b E ctx f s marks r) /\
  (!left t. create_expr_prefix a m E ctx f s left t ==>
            create_expr_prefix a b E ctx f s left t) /\
  (!left t r. create_operand_full_scope a m E ctx f s left (OK t) /\
               create_operand_full_scope m b E ctx f t [] r ==>
               create_operand_full_scope a b E ctx f s left r)
Proof
  strip_tac >>
  `!u. create_cut_region a m u /\ ~create_operand_at m u ==> ~create_operand_at b u` by
    (rpt gen_tac >> strip_tac >> irule create_layout_left_stop >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> drule_all_then ACCEPT_TAC create_left_focus_lift_at) >>
  conj_tac >- (rpt strip_tac >> drule_all_then ACCEPT_TAC create_left_terminal_lift_at) >>
  conj_asm1_tac >- (rpt strip_tac >> drule_all_then ACCEPT_TAC create_left_prefix_lift_at) >>
  `!u marks z. create_expr_prefix m b E ctx f u marks z ==>
               create_expr_prefix a b E ctx f u marks z` by
    (rpt strip_tac >> irule create_expr_prefix_mono >>
     first_assum (irule_at Any) >> simp[create_prefix_step_def,frag_ids_def] >>
     metis_tac[LESS_EQ_TRANS]) >>
  rpt gen_tac >> Cases_on `r` >> simp[create_operand_full_scope_def] >>
  rpt strip_tac >> metis_tac[create_expr_prefix_append, APPEND_NIL]
QED

Theorem raw_revert_child_site[local]:
  expr_body_pre ce cx env e es /\
  expr_sim_full_pre (DF,lo,d,C,hC,PG,f,hf) ce cx ty (Call ann RawRevert [e] NONE)
    es (st0,a,b,ha,hb,op,s,G,tn) ==>
  ?data m hm.
    lower_value compile_expr ce (expr_type e) e a = (data,m) /\
    compile_raw_revert data m = ((),b) /\
    ci_mono a m /\ ci_mono m b /\
    fn_has_code a m f /\ fn_has_code m b f /\
    expr_sim_full_pre (DF,lo,d,C,hC,PG,f,hf) ce cx (expr_type e) e es
      (st0,a,m,ha,hm,data,s,G,tn)
Proof
  strip_tac >> drule expr_body_pre_gas_admissible >> strip_tac >>
  fs[expr_sim_full_pre_def] >>
  qpat_assum `lower_value _ _ _ (Call _ _ _ _) a = _`
    (strip_assume_tac o MATCH_MP raw_revert_value_compile) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr (Call _ _ _ _)) ha = _`
    (mp_tac o REWRITE_RULE [gas_shadow_expr_def]) >>
  simp[] >> disch_then (strip_assume_tac o MATCH_MP raw_revert_value_compile) >>
  `compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr (Call ann RawRevert [e] NONE)) ha =
     (StackValue ann (Lit 0w),hb)` by simp[gas_shadow_expr_def] >>
  `gas_shadow_compiles (lower_value compile_expr ce (expr_type e) e)
     (lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e))` by
     irule gas_shadow_stmt_lower_value_env >>
  drule_all raw_revert_layout_shadow >> strip_tac >>
  qexistsl_tac [`data`,`sm`,`ssm`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem raw_revert_frames[local]:
  storage_trace_frame (bind (eval_expr cx e) (read_result cx)) /\
  (!v. storage_trace_frame
    (bind (lift_option_type (dest_BytesV v) "raw_revert data")
      (\data. raise (Error (RevertData data)))))
Proof
  simp[evaluate_storage_trace_frame, storage_trace_frame_bind,
       storage_trace_frame_read_result, storage_trace_frame_lifts, storage_trace_frame_raise]
QED

Theorem raw_revert_lift_exempt[local]:
  gas_exempt_cert T tops (ctx,f)
    (vyperState$ignore_bind (vyperState$bind (eval_expr cx e) (read_result cx)) (vyperState$return ()))
    (es,s) marks (err,ee) (leaf,stop) ==>
  gas_exempt_cert T tops (ctx,f)
    (vyperState$ignore_bind (vyperState$bind (vyperState$bind (eval_expr cx e) (read_result cx)) next)
      (vyperState$return ()))
    (es,s) marks (err,ee) (leaf,stop)
Proof
  strip_tac >> pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem raw_revert_child_exit_post[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
    source (es,s,G,tn) Q (create_operand_exit_post C cx) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
    source (es,s,G,tn) Q
    (\H (res : value + exception) ee gt r. ?exc. res = INR exc /\
      create_operand_exit_post C cx H (INR exc : value + exception) ee gt r)
Proof
  simp_tac bool_ss [scoped_operand_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> simp[] >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> gen_tac >> strip_tac >> first_x_assum drule >>
      strip_tac >> simp[] >> Cases_on `res` >>
      fs[create_operand_exit_post_def, expr_exit_def]) >>
  metis_tac[]
QED

(* The four introductions are supplied by the terminal-case join.  The child
   callback is guarded by its own installed interval, not the whole Call. *)
Theorem raw_revert_scoped_from_terminal_interfaces:
  (!DF lo E C f PG tops cx st0 a m b source es s G tn Q1 Q R next.
    scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
      source (es,s,G,tn) Q1
      (\H (res : value + exception) ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
    (!left res mid G1 tn1 t.
       (!tail. source (es with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
           (res,mid with gas_obs := tail)) /\
       storage_trace_domain cx st0 mid.storage_trace /\ create_operand_at m t /\
       create_operand_full_scope a m E C f s left (OK t) /\
       (!H. valid_horizon cx st0 H mid.storage_trace ==>
         Q1 H res mid G1 tn1 t /\ gas_origin_ptr_path (DF H,lo,E,C,f,PG)
           (s,G,tn) left (OK t,G1,tn1)) ==>
       ?v. res = INL v /\
         ((?exc fin r G2 tn2.
            (!tail. next v (mid with gas_obs := tail) = ((INR exc : value + exception),fin with gas_obs := tail)) /\
            storage_trace_domain cx st0 fin.storage_trace /\ exit_result r /\
            create_operand_full_scope m b E C f t [] r /\
            (!H. valid_horizon cx st0 H fin.storage_trace ==>
               valid_horizon cx st0 H mid.storage_trace /\
               gas_origin_ptr_path (DF H,lo,E,C,f,PG) (t,G1,tn1) [] (r,G2,tn2) /\
               R H (INR exc) (fin with gas_obs := []) (G2,tn2) r)) \/
          (?err fin H. valid_horizon cx st0 H mid.storage_trace /\
            gas_exempt_cert T tops (C,f)
              (vyperState$ignore_bind (vyperState$bind source next) (vyperState$return ()))
              (es,s) left (err,fin) (f,t)))) /\
    storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
    (!marks err ee leaf stop.
       gas_exempt_cert T tops (C,f) (vyperState$ignore_bind source (vyperState$return ()))
         (es,s) marks (err,ee) (leaf,stop) ==>
       gas_exempt_cert T tops (C,f)
         (vyperState$ignore_bind (vyperState$bind source next) (vyperState$return ()))
         (es,s) marks (err,ee) (leaf,stop)) /\
    (!marks. create_operand_focus_scope a m E C f s marks ==>
       create_operand_focus_scope a b E C f s marks) /\
    (!marks r. exit_result r /\ create_operand_full_scope a m E C f s marks r ==>
       create_operand_full_scope a b E C f s marks r) /\
    (!left t. create_expr_prefix a m E C f s left t ==>
       create_expr_prefix a b E C f s left t) /\
    (!left t r. create_operand_full_scope a m E C f s left (OK t) /\
       create_operand_full_scope m b E C f t [] r ==>
       create_operand_full_scope a b E C f s left r) ==>
    scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
      (vyperState$bind source next) (es,s,G,tn) Q R) /\
  (!tops ctx ce cx f ty e a op m b E s st0 child es next.
    body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
    lower_value compile_expr ce ty e a = (op,m) /\ fn_has_code a b f /\
    (compile_raw_revert op m = ((),b) \/ compile_selfdestruct op m = ((),b)) /\
    (cs_extends a m /\ cs_extends m b /\ fn_has_code a b f ==>
       fn_has_code a m f /\ fn_has_code m b f) /\
    (!p d k before hit after.
      body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
      create_cut_code {} a m /\ fn_has_code a m f /\
      create_cut_code {} m b /\ fn_has_code m b f /\
      create_interior_visit a b E ctx f (p,d,k) s (before,hit,after) ==>
      create_interior_visit a m E ctx f (p,d,k) s (before,hit,after) \/
      ?t d1 k1 front back.
        before = front ++ back /\ create_operand_at m t /\
        RTC (create_operand_native_step a m E ctx f p) (d,k,s,[]) (d1,k1,t,front) /\
        create_expr_prefix a m E ctx f s (create_cut_marks E front) t /\
        create_interior_visit m b E ctx f (p,d1,k1) t (back,hit,after)) /\
    create_operand_cut a m E ctx f tops cx st0
      (child : evaluation_state -> value evaluation_result) (es,s) /\
    (!v. storage_trace_frame (next v : evaluation_state -> value evaluation_result)) ==>
    create_operand_cut a b E ctx f tops cx st0 (vyperState$bind child next) (es,s)) /\
  (!ce cx env e es cap a op m b f left s res mid st0 t DF lo d C G tn G1 tn1 E PG.
    expr_body_pre ce cx env e es /\ expr_type e = BaseT (BytesT (Dynamic cap)) /\
    lower_value compile_expr ce (expr_type e) e a = (op,m) /\ local_ptrs_reserved ce a /\
    compile_raw_revert op m = ((),b) /\ fn_has_code m b f /\
    (!tail. vyperState$bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
        (res,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\ create_operand_at m t /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_sim_full_post (DF,lo,d,C,f) ce cx e (es,a,m,s,op,G,tn) H res mid G1 tn1 t /\
      gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) left (OK t,G1,tn1)) ==>
    ?v exc fin r G2 tn2. res = INL v /\
      (!tail. vyperState$bind (lift_option_type (dest_BytesV v) "raw_revert data")
        (\data. vyperState$raise (Error (RevertData data))) (mid with gas_obs := tail) =
        ((INR exc : value + exception),fin with gas_obs := tail)) /\
      storage_trace_domain cx st0 fin.storage_trace /\ exit_result r /\
      create_operand_full_scope m b E C f t [] r /\
      (!H. valid_horizon cx st0 H fin.storage_trace ==>
        valid_horizon cx st0 H mid.storage_trace /\
        gas_origin_ptr_path (DF H,lo,E,C,f,PG) (t,G1,tn1) [] (r,G2,tn2) /\
        create_operand_exit_post C cx H (INR exc : value + exception)
          (fin with gas_obs := []) (G2,tn2) r)) /\
  (!cx e DF lo d ctx shctx PG func shfunc ce ty es st0 sa sb sha shb ann op s G tn tops.
    (!st. ?exc ee. eval_expr cx e st = (INR exc,ee)) /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
      ce cx ty e es (st0,sa,sb,sha,shb,StackValue ann op,s,G,tn) ==>
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
      ce cx ty e es (st0,sa,sb,sha,shb,op,s,G,tn) /\
    (scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
       (cx_tops cx) cx st0 sa sb (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
       (expr_sim_full_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s,op,G,tn))
       (create_operand_exit_post ctx cx) ==>
     scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
       (cx_tops cx) cx st0 sa sb (eval_expr cx e) (es,s,G,tn)
       (\H res ee G' tn' t.
         create_operand_vv_post (DF,lo,d,ctx,func) ce cx e
           (es,sa,sb,s,StackValue ann op,G,tn) H res ee G' tn' t /\
         t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
       (create_operand_exit_post ctx cx)) /\
    (create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
       (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s) ==>
     create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
       (eval_expr cx e) (es,s))) /\
  body_inv (cx_tops cx) ctx ce cx /\
  expr_body_pre ce cx env (Call ann RawRevert args dflt) es /\
  (!e st0 a m ha hm op s G tn.
    MEM e args /\ create_layout a m /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,hf) ce cx (expr_type e) e es
      (st0,a,m,ha,hm,op,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 a m (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
      (expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s,op,G,tn))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut a m (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
      (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s)) ==>
  (!st0 a b ha hb op s G tn.
    create_layout a b /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,hf) ce cx ty (Call ann RawRevert args dflt) es
      (st0,a,b,ha,hb,op,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 a b
      (vyperState$bind (eval_expr cx (Call ann RawRevert args dflt)) (read_result cx)) (es,s,G,tn)
      (expr_sim_full_post (DF,lo,d,ctx,f) ce cx (Call ann RawRevert args dflt) (es,a,b,s,op,G,tn))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut a b (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
      (vyperState$bind (eval_expr cx (Call ann RawRevert args dflt)) (read_result cx)) (es,s)) /\
  (!st0 a b ha hb vv s G tn.
    create_layout a b /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,hf) ce cx ty (Call ann RawRevert args dflt) es
      (st0,a,b,ha,hb,vv,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 a b (eval_expr cx (Call ann RawRevert args dflt)) (es,s,G,tn)
      (\H res ee G' tn' t.
         create_operand_vv_post (DF,lo,d,ctx,f) ce cx (Call ann RawRevert args dflt)
           (es,a,b,s,vv,G,tn) H res ee G' tn' t /\
         t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts)
      (create_operand_exit_post ctx cx) /\
    create_operand_cut a b (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
      (eval_expr cx (Call ann RawRevert args dflt)) (es,s))
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "terminal_fold") mp_tac) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "terminal_cut") mp_tac) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "selected_tail") mp_tac) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "vv_pointwise") strip_assume_tac) >>
  drule raw_revert_source_pre >> strip_tac >>
  qpat_x_assum `eval_expr _ (Call _ _ _ _) = _`
    (assume_tac o MATCH_MP raw_revert_value_source) >> gvs[] >>
  conj_asm1_tac >- suspend "value" >> suspend "vv"
QED

Resume raw_revert_scoped_from_terminal_interfaces[value]:
  rpt gen_tac >> strip_tac >>
  `expr_body_pre ce cx env e es` by
    (qpat_assum `!es'. expr_sim_inv ce cx env es' ==> expr_body_pre ce cx env e es'` irule >>
     drule exprBodyPrePropsTheory.expr_body_pre_static_facts >> simp[]) >>
  drule_all raw_revert_child_site >> strip_tac >>
  `create_layout a m` by
    (irule create_layout_subinterval >> fs[ci_mono_def] >>
     qexistsl_tac [`a`,`b`] >> simp[cs_extends_refl]) >>
  qpat_assum `expr_type e = _` (fn ty_eq =>
    qpat_x_assum `expr_sim_full_pre _ _ _ (expr_type e) e _ _`
      (assume_tac o REWRITE_RULE [ty_eq])) >>
  qpat_x_assum `!st0 a m ha hm op s G tn. create_layout _ _ /\ _ ==> _`
    (drule_at (Pat `expr_sim_full_pre _ _ _ _ _ _ _`)) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `expr_sim_full_pre _ _ _ _ (Call _ _ _ _) _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_full_pre_def]) >>
  reverse conj_tac >- suspend "cut" >> suspend "outcome"
QED

Resume raw_revert_scoped_from_terminal_interfaces[cut]:
  asm "terminal_cut" irule >>
  simp[raw_revert_frames] >>
  qexistsl_tac [`ce`,`e`,`m`,`data`,`expr_type e`] >> simp[] >>
  rpt gen_tac >> strip_tac >> irule create_interior_visit_first_exit >>
  simp[] >> qexistsl_tac [`ce`,`cx`,`cx_tops cx`] >> simp[]
QED

Resume raw_revert_scoped_from_terminal_interfaces[outcome]:
  `create_cut_code {} a m` by
    (qspecl_then [`ce`,`expr_type e`,`e`,`a`] mp_tac (cj 2 create_operand_cut_code) >>
     simp[]) >>
  `create_cut_region a m s` by
    (drule_all createSizeCutRegionTheory.create_cut_region_rules >> simp[]) >>
  fs[ci_mono_def] >>
  drule_all raw_revert_site_scopes >>
  disch_then (qspec_then `gas_explicit_sites ctx shctx` strip_assume_tac) >>
  drule raw_revert_child_exit_post >> strip_tac >>
  asm "terminal_fold" irule >> simp[raw_revert_frames,raw_revert_lift_exempt] >>
  qpat_assum `scoped_operand_outcome _ _ _ _ a m _ _ _ (\H res ee gt r. ?exc. _)`
    (irule_at Any) >> simp[] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  asm_x "selected_tail" drule_all >> strip_tac >>
  qexists_tac `v` >> simp[] >> disj1_tac >>
  qexistsl_tac [`exc`,`fin`,`r`,`G2`,`tn2`] >> simp[]
QED

Resume raw_revert_scoped_from_terminal_interfaces[vv]:
  rpt gen_tac >> strip_tac >>
  `compile_expr ce ty (Call NoneT RawRevert [e] NONE) a = (vv,b)` by
    fs[expr_vv_sim_full_pre_def] >>
  drule_then SUBST_ALL_TAC raw_revert_compiled_stack >>
  `!st. ?exc ee. eval_expr cx (Call NoneT RawRevert [e] NONE) st = (INR exc,ee)` by
    (gen_tac >> Cases_on `eval_expr cx (Call NoneT RawRevert [e] NONE) st` >>
     rename1 `eval_expr _ _ _ = (res,_)` >> Cases_on `res` >>
     gvs[] >> qpat_x_assum `eval_expr _ _ _ = (INL _,_)` mp_tac >>
     simp[raw_revert_no_success]) >>
  asm_x "vv_pointwise" (drule_at (Pat `expr_vv_sim_full_pre _ _ _ _ _ _ _`)) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qspec_then `cx_tops cx` strip_assume_tac) >>
  qpat_x_assum `!st0 a b ha hb op s G tn. create_layout _ _ /\ expr_sim_full_pre _ _ _ _ _ _ _ ==> _`
    (drule_at (Pat `expr_sim_full_pre _ _ _ _ _ _ _`)) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  conj_tac >- (first_assum irule >> simp[]) >>
  first_assum irule >> simp[]
QED

Finalise raw_revert_scoped_from_terminal_interfaces
