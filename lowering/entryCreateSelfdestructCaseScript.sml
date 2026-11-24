(* The selected address child and the installed terminal suffix. *)
Theory entryCreateSelfdestructCase
Ancestors
  entryCreateFocusSpec entryCreateIntervalLayout bodyFullCases
  gasShadowCompileStmtHelpers exprSimSource exprLoweringProps
  gasShadow gasShadowState s1PrefixDefs compileEnv vyperAST exprLowering
  entryCreateRegionLift entryCreatePathScope createSizeOperandCode
  createSizeCutRegion entryCreateCompletedCut gasExemptCert vyperInterpreter
  vyperStorageTrace selfdestructHalt exprSimDefs builtinSystem emitHelper fragExec
  list fragGasOrigin fragGasPath vyperState createSizePrefixReplay abiEncoderProps
  exprBodyPreProps vyperSystemControl gasNormalPrefix exprSimFullBundleProps
  vyperStorageFootprint stmtSimProps exprSimStack gasSummary fragGasOriginPtr
  gasContext loweringStateRelDefs
Libs pairLib

Theorem selfdestruct_compile_stack[local]:
  compile_expr ce ty (Call NoneT SelfDestructTarget [e] NONE) sa = (vv,sb) ==>
  vv = StackValue NoneT (Lit 0w)
Proof
  simp[Once compile_expr_def, compile_call_def, expr_type_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[])
QED

Theorem selfdestruct_lower_value_stack[local]:
  lower_value compile_expr ce ty (Call NoneT SelfDestructTarget [e] NONE) sa =
    (op,sb) ==>
  compile_expr ce ty (Call NoneT SelfDestructTarget [e] NONE) sa =
    (StackValue NoneT (Lit 0w),sb) /\ op = Lit 0w
Proof
  simp[lower_value_def, comp_bind_def] >> pairarg_tac >> simp[] >>
  drule_then SUBST1_TAC selfdestruct_compile_stack >>
  simp[unwrap_value_def, comp_return_def]
QED

Theorem selfdestruct_value_child_site[local]:
  expr_type e = BaseT AddressT /\
  expr_body_pre ce cx env e es /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
    (Call NoneT SelfDestructTarget [e] NONE) es
    (st0,sa,sb,sha,shb,out,s0,G0,tn0) /\ create_layout sa sb ==>
  ?op sm shm.
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
      ce cx (expr_type e) e es (st0,sa,sm,sha,shm,op,s0,G0,tn0) /\
    create_layout sa sm /\ ci_mono sa sm /\ ci_mono sm sb /\
    fn_has_code sm sb func /\ compile_selfdestruct op sm = ((),sb) /\
    compile_expr ce ty (Call NoneT SelfDestructTarget [e] NONE) sa =
      (StackValue NoneT (Lit 0w),sb)
Proof
  simp[expr_sim_full_pre_def] >> strip_tac >>
  drule selfdestruct_lower_value_stack >> strip_tac >>
  `compile_expr (gas_shadow_env T ce) ty
     (gas_shadow_expr (Call NoneT SelfDestructTarget [e] NONE)) sha =
     (StackValue NoneT (Lit 0w),shb)` by
    (qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gas_shadow_expr_def, selfdestruct_lower_value_stack]) >>
  `gas_shadow_compiles (lower_value compile_expr ce (expr_type e) e)
     (lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
       (gas_shadow_expr e))` by
    irule gas_shadow_stmt_lower_value_env >>
  drule_all selfdestruct_full_layout_shadow >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qexistsl_tac [`data`,`sm`,`ssm`] >> simp[] >>
  metis_tac[create_layout_subinterval, ci_mono_def, cs_extends_refl]
QED

Theorem selfdestruct_next_frame[local]:
  storage_trace_frame (bind (selfdestruct_tail cx v) (read_result cx))
Proof
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_selfdestruct_tail, storage_trace_frame_read_result]
QED

Theorem selfdestruct_left_exempt[local]:
  gas_exempt_cert T tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es,s) marks (err,ee) (leaf,stop) ==>
  gas_exempt_cert T tops (ctx,func)
    (ignore_bind (bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (selfdestruct_tail cx v) (read_result cx))) (return ()))
    (es,s) marks (err,ee) (leaf,stop)
Proof
  strip_tac >> rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >> fs[ignore_bind_def]
QED

Theorem selfdestruct_scope_join[local]:
  a.cs_next_id <= m.cs_next_id /\
  create_expr_prefix a b explicit ctx func s left t /\
  create_operand_full_scope m b explicit ctx func t [] r ==>
  create_operand_full_scope a b explicit ctx func s left r
Proof
  Cases_on `r` >> simp[create_operand_full_scope_def] >> strip_tac >>
  `!u ms v. create_prefix_step m b explicit ctx func u ms v ==>
            create_prefix_step a b explicit ctx func u ms v` by
    (simp[create_prefix_step_def, frag_ids_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  metis_tac[create_expr_prefix_mono, create_expr_prefix_append, APPEND_NIL]
QED

Theorem selfdestruct_left_scope[local]:
  body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\ create_layout a b /\
  lower_value compile_expr ce ty e a = (op,m) /\ fn_has_code a m func /\
  ci_mono a m /\ ci_mono m b /\ create_operand_at a s ==>
  (!marks. create_operand_focus_scope a m explicit ctx func s marks ==>
           create_operand_focus_scope a b explicit ctx func s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m explicit ctx func s marks r ==>
             create_operand_full_scope a b explicit ctx func s marks r) /\
  (!left t. create_expr_prefix a m explicit ctx func s left t ==>
            create_expr_prefix a b explicit ctx func s left t) /\
  (!left t r. create_operand_full_scope a m explicit ctx func s left (OK t) /\
              create_operand_full_scope m b explicit ctx func t [] r ==>
              create_operand_full_scope a b explicit ctx func s left r)
Proof
  strip_tac >>
  `create_cut_code {} a m` by metis_tac[create_operand_cut_code, pairTheory.SND] >>
  `create_cut_region a m s` by
    (drule_all create_cut_region_rules >> simp[GSYM create_operand_at_def]) >>
  `!u. create_cut_region a m u /\ ~create_operand_at m u ==>
       ~create_operand_at b u` by metis_tac[create_layout_left_stop, ci_mono_def] >>
  `m.cs_next_id <= b.cs_next_id /\ a.cs_next_id <= m.cs_next_id` by fs[ci_mono_def] >>
  conj_tac >- (rpt strip_tac >> irule create_left_focus_lift_at >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> irule create_left_terminal_lift_at >> metis_tac[]) >>
  `!left t. create_expr_prefix a m explicit ctx func s left t ==>
            create_expr_prefix a b explicit ctx func s left t` by
    (rpt strip_tac >> irule create_left_prefix_lift_at >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> irule selfdestruct_scope_join >>
  qexistsl_tac [`m`,`t`] >> simp[] >> fs[create_operand_full_scope_def]
QED

Theorem selfdestruct_source_site[local]:
  expr_body_pre ce cx env (Call ann SelfDestructTarget args dflt) es ==>
  ?e. args = [e] /\ ann = NoneT /\ dflt = NONE /\
      expr_type e = BaseT AddressT /\ expr_body_pre ce cx env e es /\
      eval_expr cx (Call ann SelfDestructTarget args dflt) =
        bind (bind (eval_expr cx e) (read_result cx)) (selfdestruct_tail cx)
Proof
  strip_tac >> drule selfdestruct_full_source_pre >> strip_tac >> gvs[] >>
  metis_tac[expr_body_pre_static_facts]
QED

Theorem selfdestruct_child_terminal_post[local]:
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (expr_sim_full_post (DF,lo,d,ctx,func) ce cx e (es,a,m,s,op,G,tn))
    (create_operand_exit_post ctx cx) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (\H res ee G' tn' t. ee.gas_obs = [] /\
      expr_sim_full_post (DF,lo,d,ctx,func) ce cx e (es,a,m,s,op,G,tn) H res ee G' tn' t)
    (\H res ee gt r. (?ex. res = INR ex) /\ create_operand_exit_post ctx cx H res ee gt r)
Proof
  simp_tac bool_ss [scoped_operand_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- metis_tac[]
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
      Cases_on `res` >> gvs[create_operand_exit_post_def] >>
      Cases_on `r` >> gvs[expr_exit_def, exit_result_def]) >>
  metis_tac[]
QED

Theorem selfdestruct_outer_exempt_value[local]:
  gas_exempt_cert T tops (ctx,func)
    (ignore_bind (eval_expr cx (Call ann SelfDestructTarget args dflt)) (return ()))
    (es,s) marks (err,ee) (leaf,stop) ==>
  gas_exempt_cert T tops (ctx,func)
    (ignore_bind
      (bind (eval_expr cx (Call ann SelfDestructTarget args dflt)) (read_result cx))
      (return ())) (es,s) marks (err,ee) (leaf,stop)
Proof
  strip_tac >> rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_result >> fs[ignore_bind_def]
QED

(* The tail has no value result: the physical supplier's eval_result
   exception is the very same exception after the outer read_result. *)
Theorem selfdestruct_physical_value[local]:
  storage_trace_domain cx st0 mid.storage_trace /\
  (!tail. selfdestruct_tail cx v (mid with gas_obs := tail) =
    (INR exc : eval_result + exception,fin with gas_obs := tail)) /\
  fin.storage_trace = mid.storage_trace /\
  create_operand_full_scope m b E ctx f t [] r /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (t,G,tn) [] (r,G,tn) /\
     create_operand_exit_post ctx cx H (INR exc : eval_result + exception)
       (fin with gas_obs := []) (G,tn) r) ==>
  ?exc' fin' r' G2 tn2.
    (!tail. bind (selfdestruct_tail cx v) (read_result cx) (mid with gas_obs := tail) =
       (INR exc',fin' with gas_obs := tail)) /\
    storage_trace_domain cx st0 fin'.storage_trace /\ exit_result r' /\
    create_operand_full_scope m b E ctx f t [] r' /\
    (!H. valid_horizon cx st0 H fin'.storage_trace ==>
      valid_horizon cx st0 H mid.storage_trace /\
      gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (t,G,tn) [] (r',G2,tn2) /\
      create_operand_exit_post ctx cx H (INR exc') (fin' with gas_obs := []) (G2,tn2) r')
Proof
  strip_tac >> qexistsl_tac [`exc`,`fin`,`r`,`G`,`tn`] >> simp[bind_def] >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  `exit_result r` by
    (first_assum drule >> strip_tac >>
     Cases_on `r` >> fs[create_operand_exit_post_def, expr_exit_def, exit_result_def]) >>
  simp[] >> qpat_x_assum `valid_horizon _ _ (storage_trace_horizon _) _` kall_tac >>
  rpt strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
  simp[create_operand_exit_post_def, halt_exit_def, expr_exit_INR_type]
QED

(* Narrow, site-indexed contracts for the three selected-boundary suppliers. *)
Definition selfdestruct_address_intro_def:
  selfdestruct_address_intro (DF,lo,d,ctx,shctx,PG,f,shf) ce cx e es
    (st0,a,m,ha,hm,op,s,G,tn) <=>
  !left v mid G1 tn1 t.
    expr_type e = BaseT AddressT /\
    gas_admissible
      (bind (bind (bind (eval_expr cx e) (read_result cx)) (selfdestruct_tail cx))
         (read_result cx)) expr_res_ok es /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx (expr_type e) e es
      (st0,a,m,ha,hm,op,s,G,tn) /\
    (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
      (INL v,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
        (s,G,tn) left (OK t,G1,tn1) /\
      expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s,op,G,tn)
        H (INL v : value + exception) (mid with gas_obs := []) G1 tn1 t) ==>
    valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) es.storage_trace /\
    dest_AddressV v = SOME (w2w (typed_val_to_w256 (BaseTV AddressT) v)) /\
    eval_operand op t = SOME (typed_val_to_w256 (BaseTV AddressT) v) /\
    ~t.vs_halted /\ op_taint tn1 op = {} /\ op_prov G1 op = NONE /\
    t.vs_call_ctx.cc_address = cx.txn.target /\
    t.vs_call_ctx.cc_created_in_tx = cx.txn.created_in_tx /\
    t.vs_call_ctx.cc_static = cx.txn.is_static /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    gas_value_prefix (storage_trace_horizon mid.storage_trace) T
      (ctx,f,ce,cx) (expr_type e,e) (a,m,op) (es,s) left (v,mid,t)
End

Definition selfdestruct_physical_intro_def:
  selfdestruct_physical_intro (DF,lo,d,E,ctx,f,PG) ce cx st0 (m,b,op) <=>
  !v mid t G tn w.
    compile_selfdestruct op m = ((),b) /\ fn_has_code m b f /\
    create_operand_at m t /\ ~t.vs_halted /\ eval_operand op t = SOME w /\
    op_taint tn op = {} /\ op_prov G op = NONE /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    t.vs_call_ctx.cc_address = cx.txn.target /\
    t.vs_call_ctx.cc_created_in_tx = cx.txn.created_in_tx /\
    t.vs_call_ctx.cc_static = cx.txn.is_static /\ dest_AddressV v = SOME (w2w w) /\
    (cx.txn.is_static \/ ~selfdestruct_overflows cx (w2w w) mid.accounts) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       halt_rel H cx (mid with gas_obs := []) t /\
       ghost_inv_at (DF H) lo d ce cx (mid with gas_obs := []) G tn t) ==>
  ?exc ee r.
    (!tail. selfdestruct_tail cx v (mid with gas_obs := tail) =
       (INR exc : eval_result + exception,ee with gas_obs := tail)) /\
    ee.storage_trace = mid.storage_trace /\
    create_operand_full_scope m b E ctx f t [] r /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (t,G,tn) [] (r,G,tn) /\
       create_operand_exit_post ctx cx H (INR exc : eval_result + exception)
         (ee with gas_obs := []) (G,tn) r)
End

Definition selfdestruct_overflow_intro_def:
  selfdestruct_overflow_intro (DF,lo,E,ctx,f,PG) tops ce cx ty e st0 (a,m,b,op) (es,s,G,tn) <=>
  !H left v mid t addr G1 tn1.
    compile_expr ce ty (Call NoneT SelfDestructTarget [e] NONE) a =
      (StackValue NoneT (Lit 0w),b) /\ fn_has_code a b f /\
    gas_value_prefix H T (ctx,f,ce,cx) (expr_type e,e) (a,m,op) (es,s) left (v,mid,t) /\
    dest_AddressV v = SOME addr /\ ~cx.txn.is_static /\
    selfdestruct_overflows cx addr mid.accounts /\
    valid_horizon cx st0 H es.storage_trace /\
    gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (s,G,tn) left (OK t,G1,tn1) ==>
    gas_exempt_cert T tops (ctx,f)
      (ignore_bind (eval_expr cx (Call NoneT SelfDestructTarget [e] NONE)) (return ()))
      (es,s) left (RuntimeError "transfer_value recipient overflow",mid) (f,t)
End

Theorem selfdestruct_chosen_boundary[local]:
  selfdestruct_address_intro (DF,lo,d,ctx,shctx,PG,f,shf) ce cx e es
    (st0,a,m,ha,hm,op,s,G,tn) /\
  selfdestruct_physical_intro (DF,lo,d,gas_explicit_sites ctx shctx,ctx,f,PG)
    ce cx st0 (m,b,op) /\
  selfdestruct_overflow_intro (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
    tops ce cx ty e st0 (a,m,b,op) (es,s,G,tn) /\
  expr_type e = BaseT AddressT /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx (expr_type e) e es
    (st0,a,m,ha,hm,op,s,G,tn) /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty
    (Call NoneT SelfDestructTarget [e] NONE) es (st0,a,b,ha,hb,out,s,G,tn) /\
  compile_expr ce ty (Call NoneT SelfDestructTarget [e] NONE) a =
    (StackValue NoneT (Lit 0w),b) /\
  fn_has_code m b f /\ compile_selfdestruct op m = ((),b) /\
  eval_expr cx (Call NoneT SelfDestructTarget [e] NONE) =
    bind (bind (eval_expr cx e) (read_result cx)) (selfdestruct_tail cx) ==>
  !left res mid G1 tn1 t.
    (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
      (res,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\ create_operand_at m t /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      (mid.gas_obs = [] /\
       expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s,op,G,tn)
         H res mid G1 tn1 t) /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
        (s,G,tn) left (OK t,G1,tn1)) ==>
    ?v. res = INL v /\
      ((?exc fin r G2 tn2.
        (!tail. bind (selfdestruct_tail cx v) (read_result cx) (mid with gas_obs := tail) =
          (INR exc,fin with gas_obs := tail)) /\
        storage_trace_domain cx st0 fin.storage_trace /\ exit_result r /\
        create_operand_full_scope m b (gas_explicit_sites ctx shctx) ctx f t [] r /\
        (!H. valid_horizon cx st0 H fin.storage_trace ==>
          valid_horizon cx st0 H mid.storage_trace /\
          gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
            (t,G1,tn1) [] (r,G2,tn2) /\
          create_operand_exit_post ctx cx H (INR exc : value + exception)
            (fin with gas_obs := []) (G2,tn2) r)) \/
       (?err fin H. valid_horizon cx st0 H mid.storage_trace /\
        gas_exempt_cert T tops (ctx,f)
          (ignore_bind (bind (bind (eval_expr cx e) (read_result cx))
             (\v. bind (selfdestruct_tail cx v) (read_result cx))) (return ()))
          (es,s) left (err,fin) (f,t)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `hc = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 hc mid.storage_trace` by fs[Abbr `hc`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `mid with gas_obs := [] = mid` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  `?v. res = INL v` by fs[expr_sim_full_post_def] >> gvs[] >>
  `gas_admissible (bind (bind (bind (eval_expr cx e) (read_result cx))
      (selfdestruct_tail cx)) (read_result cx)) expr_res_ok es /\ fn_has_code a b f` by
    (qpat_assum `expr_sim_full_pre _ _ _ _ (Call _ _ _ _) _ _`
       (strip_assume_tac o REWRITE_RULE [expr_sim_full_pre_def]) >>
     conj_tac >-
       (qpat_assum `eval_expr _ (Call _ _ _ _) = _` (fn eq =>
          qpat_assum `gas_admissible (bind (eval_expr _ (Call _ _ _ _)) _) _ _`
            (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `selfdestruct_address_intro _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [selfdestruct_address_intro_def]) >>
  disch_then (qspecl_then [`left`,`v`,`mid`,`G1`,`tn1`,`t`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qabbrev_tac `w = typed_val_to_w256 (BaseTV AddressT) v` >>
  Cases_on `cx.txn.is_static \/ ~selfdestruct_overflows cx (w2w w) mid.accounts`
  >- (disj1_tac >>
      qpat_x_assum `selfdestruct_physical_intro _ _ _ _ _`
        (mp_tac o REWRITE_RULE [selfdestruct_physical_intro_def]) >>
      disch_then (qspecl_then [`v`,`mid`,`t`,`G1`,`tn1`,`w`] mp_tac) >>
      (impl_tac >-
       (simp[] >> rpt strip_tac >>
        qpat_assum `!H. valid_horizon _ _ H _ ==> _`
          (qspec_then `H` (drule_then strip_assume_tac)) >>
        qpat_x_assum `expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
        pure_rewrite_tac[expr_sim_full_post_def, loweringPostsTheory.expr_post_def,
                         stmt_state_rel_def] >>
        CONV_TAC (DEPTH_CONV BETA_CONV) >>
        simp_tac bool_ss [sumTheory.INL_11] >>
        strip_tac >> drule halt_rel_from_state_rel >> simp[])) >>
      strip_tac >> irule selfdestruct_physical_value >> simp[] >> metis_tac[]) >>
  disj2_tac >> qexistsl_tac [`RuntimeError "transfer_value recipient overflow"`,`mid`,`hc`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `gas_exempt_cert T tops (ctx,f)
     (ignore_bind (eval_expr cx (Call NoneT SelfDestructTarget [e] NONE)) (return ()))
     (es,s) left (RuntimeError "transfer_value recipient overflow",mid) (f,t)` by
    (qpat_x_assum `selfdestruct_overflow_intro _ _ _ _ _ _ _ _ _`
       (irule o REWRITE_RULE [selfdestruct_overflow_intro_def]) >>
     fs[] >> qexistsl_tac [`G1`,`hc`,`w2w w`,`tn1`,`v`] >> simp[Abbr `hc`] >>
     qpat_assum `expr_type e = _` (fn eq =>
       qpat_assum `gas_value_prefix _ _ _ _ _ _ _ _` (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
  drule selfdestruct_outer_exempt_value >>
  qpat_assum `eval_expr _ (Call _ _ _ _) = _`
    (fn eq => disch_then (mp_tac o PURE_REWRITE_RULE [eq])) >>
  simp_tac bool_ss [bind_assoc]
QED

(* Instances of the common terminal rules, kept as premises until the
   terminal-case join. Their sources are the selected child and suffix. *)
Definition selfdestruct_terminal_fold_def:
  selfdestruct_terminal_fold (DF,lo,E,ctx,f,PG) tops cx (st0,a,m,b)
    (es,s,G,tn) source next Q1 Q R <=>
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a m
    source (es,s,G,tn) Q1 (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!left res mid G1 tn1 t.
    (!tail. source (es with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
      (res,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\ create_operand_at m t /\
    create_operand_full_scope a m E ctx f s left (OK t) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      Q1 H res mid G1 tn1 t /\
      gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (s,G,tn) left (OK t,G1,tn1)) ==>
    ?v. res = INL v /\
      ((?exc fin r G2 tn2.
        (!tail. next v (mid with gas_obs := tail) = (INR exc,fin with gas_obs := tail)) /\
        storage_trace_domain cx st0 fin.storage_trace /\ exit_result r /\
        create_operand_full_scope m b E ctx f t [] r /\
        (!H. valid_horizon cx st0 H fin.storage_trace ==>
          valid_horizon cx st0 H mid.storage_trace /\
          gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (t,G1,tn1) [] (r,G2,tn2) /\
          R H (INR exc) (fin with gas_obs := []) (G2,tn2) r)) \/
       (?err fin H. valid_horizon cx st0 H mid.storage_trace /\
        gas_exempt_cert T tops (ctx,f) (ignore_bind (bind source next) (return ()))
          (es,s) left (err,fin) (f,t)))) /\
  storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
  (!marks err ee leaf finish.
    gas_exempt_cert T tops (ctx,f) (ignore_bind source (return ()))
      (es,s) marks (err,ee) (leaf,finish) ==>
    gas_exempt_cert T tops (ctx,f) (ignore_bind (bind source next) (return ()))
      (es,s) marks (err,ee) (leaf,finish)) /\
  (!marks. create_operand_focus_scope a m E ctx f s marks ==>
    create_operand_focus_scope a b E ctx f s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E ctx f s marks r ==>
    create_operand_full_scope a b E ctx f s marks r) /\
  (!left t. create_expr_prefix a m E ctx f s left t ==>
    create_expr_prefix a b E ctx f s left t) /\
  (!left t r. create_operand_full_scope a m E ctx f s left (OK t) /\
    create_operand_full_scope m b E ctx f t [] r ==>
    create_operand_full_scope a b E ctx f s left r) ==>
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a b
    (bind source next) (es,s,G,tn) Q R
End

Definition selfdestruct_terminal_cut_def:
  selfdestruct_terminal_cut E ctx f tops ce cx st0 (a,m,b,op) e (es,s) <=>
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  lower_value compile_expr ce (expr_type e) e a = (op,m) /\
  fn_has_code a b f /\ compile_selfdestruct op m = ((),b) /\
  create_operand_cut a m E ctx f tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s) ==>
  create_operand_cut a b E ctx f tops cx st0
    (bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (selfdestruct_tail cx v) (read_result cx))) (es,s)
End

Theorem selfdestruct_frame[local]:
  storage_trace_frame (bind (eval_expr cx e) (read_result cx))
Proof
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_read_result, evaluate_storage_trace_frame]
QED

Theorem selfdestruct_exit_post_align[local]:
  (\H (res:value + exception) ee gt r.
    ?exc. res = INR exc /\ create_operand_exit_post ctx cx H (INR exc : value + exception) ee gt r) =
  (\H (res:value + exception) ee gt r.
    (?exc. res = INR exc) /\ create_operand_exit_post ctx cx H res ee gt r)
Proof
  simp_tac bool_ss [FUN_EQ_THM] >> rpt gen_tac >> metis_tac[]
QED

Theorem selfdestruct_value_site[local]:
  body_inv (cx_tops cx) ctx ce cx /\
  expr_body_pre ce cx env (Call NoneT SelfDestructTarget [e] NONE) es /\
  expr_type e = BaseT AddressT /\ expr_body_pre ce cx env e es /\
  eval_expr cx (Call NoneT SelfDestructTarget [e] NONE) =
    bind (bind (eval_expr cx e) (read_result cx)) (selfdestruct_tail cx) /\
  (!m hm op. selfdestruct_address_intro (DF,lo,d,ctx,shctx,PG,f,shf) ce cx e es
    (st0,a,m,ha,hm,op,s,G,tn)) /\
  (!m op. selfdestruct_physical_intro (DF,lo,d,gas_explicit_sites ctx shctx,ctx,f,PG)
    ce cx st0 (m,b,op)) /\
  (!m op. selfdestruct_overflow_intro (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
    (cx_tops cx) ce cx ty e st0 (a,m,b,op) (es,s,G,tn)) /\
  (!m Q1 Q R. selfdestruct_terminal_fold (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
    (cx_tops cx) cx (st0,a,m,b) (es,s,G,tn) (bind (eval_expr cx e) (read_result cx))
    (\v. bind (selfdestruct_tail cx v) (read_result cx)) Q1 Q R) /\
  (!m op. selfdestruct_terminal_cut (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) ce cx st0
    (a,m,b,op) e (es,s)) /\
  (!m hm op. create_layout a m /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx (expr_type e) e es
      (st0,a,m,ha,hm,op,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 a m (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
      (expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s,op,G,tn))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut a m (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
      (bind (eval_expr cx e) (read_result cx)) (es,s)) /\
  create_layout a b /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty
    (Call NoneT SelfDestructTarget [e] NONE) es (st0,a,b,ha,hb,out,s,G,tn) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
    (cx_tops cx) cx st0 a b (bind (eval_expr cx (Call NoneT SelfDestructTarget [e] NONE)) (read_result cx))
    (es,s,G,tn) (expr_sim_full_post (DF,lo,d,ctx,f) ce cx (Call NoneT SelfDestructTarget [e] NONE)
      (es,a,b,s,out,G,tn)) (create_operand_exit_post ctx cx) /\
  create_operand_cut a b (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
    (bind (eval_expr cx (Call NoneT SelfDestructTarget [e] NONE)) (read_result cx)) (es,s)
Proof
  strip_tac >> drule_all selfdestruct_value_child_site >> strip_tac >>
  rename1 `compile_selfdestruct op m = ((),b)` >>
  qpat_x_assum `!m hm op. create_layout a m /\ _ ==> _` (drule_all_then strip_assume_tac) >>
  `MEM f ctx.ctx_functions /\ fn_has_code a b f /\ create_operand_at a s` by
     fs[expr_sim_full_pre_def,create_operand_at_def] >>
  `lower_value compile_expr ce (expr_type e) e a = (op,m) /\ fn_has_code a m f` by
     fs[expr_sim_full_pre_def] >>
  drule_all selfdestruct_left_scope >>
  disch_then (qspec_then `gas_explicit_sites ctx shctx` strip_assume_tac) >>
  qpat_assum `!m hm op. selfdestruct_address_intro _ _ _ _ _ _`
    (qspecl_then [`m`,`shm`,`op`] assume_tac) >>
  qpat_assum `!m op. selfdestruct_physical_intro _ _ _ _ _`
    (qspecl_then [`m`,`op`] assume_tac) >>
  qpat_assum `!m op. selfdestruct_overflow_intro _ _ _ _ _ _ _ _ _`
    (qspecl_then [`m`,`op`] assume_tac) >>
  qpat_assum `eval_expr _ (Call _ _ _ _) = _`
    (fn eq => pure_rewrite_tac[eq]) >>
  once_rewrite_tac[bind_assoc] >>
  conj_tac
  >- (qpat_assum `!m Q1 Q R. selfdestruct_terminal_fold _ _ _ _ _ _ _ _ _ _`
        (irule o PURE_REWRITE_RULE [selfdestruct_terminal_fold_def]) >>
      asm_simp_tac bool_ss [selfdestruct_frame,selfdestruct_next_frame,selfdestruct_left_exempt] >>
      qexistsl_tac [`\H res ee G' tn' t. ee.gas_obs = [] /\
        expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s,op,G,tn) H res ee G' tn' t`,`m`] >>
      asm_simp_tac bool_ss [] >>
      reverse conj_tac >-
        (conj_tac >- first_assum ACCEPT_TAC >>
         pure_rewrite_tac[selfdestruct_exit_post_align] >>
         drule_then ACCEPT_TAC selfdestruct_child_terminal_post) >>
      rpt gen_tac >> strip_tac >>
      irule selfdestruct_chosen_boundary >>
      asm_simp_tac bool_ss [] >>
      qpat_assum `selfdestruct_address_intro _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `selfdestruct_overflow_intro _ _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `expr_sim_full_pre _ _ _ _ (Call _ _ _ _) _ _` (irule_at Any) >>
      asm_simp_tac bool_ss [] >>
      conj_tac >- metis_tac[] >>
      qpat_assum `expr_type e = _` (fn eq =>
        qpat_assum `expr_sim_full_pre _ _ _ _ e _ _` (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
  qpat_assum `!m op. selfdestruct_terminal_cut _ _ _ _ _ _ _ _ _ _`
    (irule o PURE_REWRITE_RULE [selfdestruct_terminal_cut_def]) >>
  asm_simp_tac bool_ss [] >> qexistsl_tac [`m`,`op`] >> asm_simp_tac bool_ss []
QED

Theorem selfdestruct_scoped_from_terminal_interfaces:
  (!DF lo d ctx shctx PG f shf ce cx e es st0 a m ha hm op s G tn.
    selfdestruct_address_intro (DF,lo,d,ctx,shctx,PG,f,shf) ce cx e es
      (st0,a,m,ha,hm,op,s,G,tn)) /\
  (!DF lo d E ctx f PG ce cx st0 m b op.
    selfdestruct_physical_intro (DF,lo,d,E,ctx,f,PG) ce cx st0 (m,b,op)) /\
  (!DF lo E ctx f PG tops ce cx ty e st0 a m b op es s G tn.
    selfdestruct_overflow_intro (DF,lo,E,ctx,f,PG) tops ce cx ty e st0 (a,m,b,op) (es,s,G,tn)) /\
  (!DF lo E ctx f PG tops cx st0 a m b es s G tn e Q1 Q R.
    selfdestruct_terminal_fold (DF,lo,E,ctx,f,PG) tops cx (st0,a,m,b) (es,s,G,tn)
      (bind (eval_expr cx e) (read_result cx)) (\v. bind (selfdestruct_tail cx v) (read_result cx))
      Q1 Q R) /\
  (!E ctx f tops ce cx st0 a m b op e es s.
    selfdestruct_terminal_cut E ctx f tops ce cx st0 (a,m,b,op) e (es,s)) /\
  (!DF lo d ctx shctx PG func shfunc ce cx ty e es st0 sa sb sha shb ann op s G tn tops.
    (!st. ?exc ee. eval_expr cx e st = (INR exc,ee)) /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
      ce cx ty e es (st0,sa,sb,sha,shb,StackValue ann op,s,G,tn) ==>
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
      ce cx ty e es (st0,sa,sb,sha,shb,op,s,G,tn) /\
    (scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
       (cx_tops cx) cx st0 sa sb (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
       (expr_sim_full_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s,op,G,tn))
       (create_operand_exit_post ctx cx) ==>
     scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
       (cx_tops cx) cx st0 sa sb (eval_expr cx e) (es,s,G,tn)
       (\H res ee G' tn' t.
         create_operand_vv_post (DF,lo,d,ctx,func) ce cx e
           (es,sa,sb,s,StackValue ann op,G,tn) H res ee G' tn' t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
       (create_operand_exit_post ctx cx)) /\
    (create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
       (bind (eval_expr cx e) (read_result cx)) (es,s) ==>
     create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
       (eval_expr cx e) (es,s))) /\
  body_inv (cx_tops cx) ctx ce cx /\
  expr_body_pre ce cx env (Call ann SelfDestructTarget args dflt) es /\
  (!e st0 a m ha hm op s G tn. MEM e args /\ expr_body_pre ce cx env e es /\
    create_layout a m /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx (expr_type e) e es
      (st0,a,m,ha,hm,op,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 a m (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
      (expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s,op,G,tn))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut a m (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
      (bind (eval_expr cx e) (read_result cx)) (es,s)) ==>
  (!st0 a b ha hb op s G tn. create_layout a b /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty
      (Call ann SelfDestructTarget args dflt) es (st0,a,b,ha,hb,op,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 a b (bind (eval_expr cx (Call ann SelfDestructTarget args dflt)) (read_result cx))
      (es,s,G,tn) (expr_sim_full_post (DF,lo,d,ctx,f) ce cx (Call ann SelfDestructTarget args dflt)
        (es,a,b,s,op,G,tn)) (create_operand_exit_post ctx cx) /\
    create_operand_cut a b (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
      (bind (eval_expr cx (Call ann SelfDestructTarget args dflt)) (read_result cx)) (es,s)) /\
  (!st0 a b ha hb vv s G tn. create_layout a b /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty
      (Call ann SelfDestructTarget args dflt) es (st0,a,b,ha,hb,vv,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 a b (eval_expr cx (Call ann SelfDestructTarget args dflt)) (es,s,G,tn)
      (\H res ee G' tn' t.
        create_operand_vv_post (DF,lo,d,ctx,f) ce cx (Call ann SelfDestructTarget args dflt)
          (es,a,b,s,vv,G,tn) H res ee G' tn' t /\
        t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts)
      (create_operand_exit_post ctx cx) /\
    create_operand_cut a b (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
      (eval_expr cx (Call ann SelfDestructTarget args dflt)) (es,s))
Proof
  strip_tac >> drule selfdestruct_source_site >> strip_tac >>
  qpat_x_assum `args = [_]` SUBST_ALL_TAC >>
  qpat_x_assum `ann = NoneT` SUBST_ALL_TAC >>
  qpat_x_assum `dflt = NONE` SUBST_ALL_TAC >>
  conj_asm1_tac
  >- (rpt gen_tac >> strip_tac >> irule selfdestruct_value_site >>
      qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
      asm_simp_tac bool_ss [] >>
      qpat_assum `expr_sim_full_pre _ _ _ _ (Call _ _ _ _) _ _` (irule_at Any) >>
      rpt gen_tac >> strip_tac >>
      qpat_assum `!e st0 a m ha hm op s G tn. _ ==> _` (qspecl_then [`e`,`st0`,`a`,`m`] irule) >>
      simp[] >> qexistsl_tac [`ha`,`hm`] >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  `vv = StackValue NoneT (Lit 0w)` by
    (qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
     qpat_assum `compile_expr ce _ _ a = _` (fn th =>
       ACCEPT_TAC (MATCH_MP selfdestruct_compile_stack th))) >>
  qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  `!st. ?exc ee. eval_expr cx (Call NoneT SelfDestructTarget [e] NONE) st = (INR exc,ee)` by
    (gen_tac >> Cases_on `eval_expr cx (Call NoneT SelfDestructTarget [e] NONE) st` >>
     Cases_on `q` >> gvs[] >> metis_tac[selfdestruct_no_success]) >>
  qpat_assum `!DF lo d ctx shctx PG func shfunc ce cx ty e es st0 sa sb sha shb ann op s G tn tops.
      _ /\ expr_vv_sim_full_pre _ _ _ _ _ _ _ ==> _`
    (drule_all_then (qspec_then `cx_tops cx` strip_assume_tac)) >>
  qpat_assum `!st0 a b ha hb op s G tn. create_layout a b /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  conj_tac >- (first_assum irule >> first_assum ACCEPT_TAC) >>
  first_assum irule >> first_assum ACCEPT_TAC
QED
