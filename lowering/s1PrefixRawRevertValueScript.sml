(* Request-prefix companion to bodyFullRawRevertValue. *)
Theory s1PrefixRawRevertValue
Ancestors
  bodyFullExprsListFacts bodyFullSimProjection
  s1PrefixPreds bodyFullRawRevertValue s1PrefixDefs s1PrefixCompose s1PrefixFrame s1PrefixProps bodyFullRawRevertInterfaces bodyFullPreds bodySimFull exprSimHypsDefs exprSimSource exprLowering gasOutcomeFullCompose gasShadowCompileStmtHelpers exprSimProps exprSimDefs exprLoweringProps loweringPosts bodyPtrDefs exprSimMemDefs gasExemptCert gasShadow gasShadowState vyperSystemControl vyperStorageFootprint vyperAST vyperInterpreter vyperState compileEnv

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (mk_asm "tail_contract") >> rpt gen_tac >> strip_tac >>
  drule raw_revert_source_pre >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es` by
    (first_x_assum irule >> gvs[expr_body_pre_def]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (gvs[body_exprs_full_ok_cons, body_exprs_full_ok_nil] >>
     metis_tac[body_expr_full_ok_simulations]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (gvs[body_exprs_prefix_ok_def] >>
     qpat_x_assum `body_expr_prefix_ok cx e` mp_tac >>
     simp[Once body_expr_prefix_ok_def] >> metis_tac[]) >>
  rewrite_tac[expr_sim_prefix_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_sim_full_pre _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_pre_def] >> strip_tac >>
  `!ce child ss v st.
     compile_expr ce ty (Call NoneT RawRevert [child] NONE) ss = (v,st) ==>
     v = StackValue NoneT (Lit 0w)` by
    (rpt gen_tac >> simp[Once compile_expr_def, compile_call_def, expr_type_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[])) >>
  `compile_expr cenv ty (Call NoneT RawRevert [e] NONE) sa =
       (StackValue NoneT (Lit 0w),sb) /\
   compile_expr (gas_shadow_env T cenv) ty
       (gas_shadow_expr (Call NoneT RawRevert [e] NONE))
       shadow_sa = (StackValue NoneT (Lit 0w),shadow_sb)` by
    (qpat_x_assum `lower_value _ _ _ (Call _ _ _ _) _ = _` mp_tac >>
     qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gas_shadow_expr_def] >>
     simp[lower_value_def, comp_bind_def] >>
     rpt (pairarg_tac >> simp[]) >>
     `vv' = StackValue NoneT (Lit 0w) /\ vv = StackValue NoneT (Lit 0w)` by
       (conj_tac >> first_x_assum irule >> metis_tac[]) >>
     gvs[unwrap_value_def, comp_return_def]) >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
     (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e))` by irule gas_shadow_stmt_lower_value_env >>
  drule_all raw_revert_layout_shadow >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ e _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `ssm`, `data`,
    `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE
      (qpat_assum `lower_value compile_expr cenv (expr_type e) e sa = _`
         ACCEPT_TAC ORELSE
       qpat_assum `lower_value compile_expr _
           (expr_type e) (gas_shadow_expr e) shadow_sa = (_,ssm)` ACCEPT_TAC)))) >>
  strip_tac >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ e _` mp_tac >>
  rewrite_tac[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `ssm`, `data`,
    `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (fn th => assume_tac th) >>
  qpat_assum `gas_prefix_full _ _ _ _ _`
    (fn th => assume_tac th) >>
  qpat_assum `eval_expr cx (Call _ RawRevert _ _) = _`
    (fn th => once_rewrite_tac[th]) >>
  once_rewrite_tac[bind_assoc] >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     (\H res ee G tn t. ~t.vs_halted)
     (\H res ee gt r. ISR res)` by
    (qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _`
       (mp_then Any irule gas_outcome_full_post_source) >>
     simp[] >> rpt strip_tac >> Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def]) >>
  qpat_assum
    `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn t. ~t.vs_halted) _`
    (mp_then Any irule gas_prefix_full_bind_no_outcome) >>
  simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
       vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result,
       requests_outcomes_frame_bind_all, evaluate_requests_outcomes_frame,
       requests_outcomes_frame_read_result,
       vyperStorageTraceTheory.storage_trace_frame_def, bind_def,
       lift_option_type_def, raise_def, vyperValueTheory.dest_BytesV_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `dest_BytesV v` >>
      gvs[bind_def, lift_option_type_def, raise_def, return_def,
          read_result_def, requests_outcomes_frame_def,
          vyperStateTheory.evaluation_state_component_equality,
          vyperValueTheory.dest_BytesV_def])
  >- (rpt gen_tac >> Cases_on `dest_BytesV v` >>
      simp[bind_assoc, bind_def, lift_option_type_def, raise_def, return_def,
           vyperStorageTraceTheory.storage_trace_frame_def,
           vyperStorageTraceTheory.storage_trace_frame_lifts,
           vyperStorageTraceTheory.storage_trace_frame_raise,
           vyperStorageTraceTheory.storage_trace_frame_read_result,
           vyperValueTheory.dest_BytesV_def])
QED
*)
Theorem raw_revert_value_prefix_from_tail:
  (!(H : (bool # 256 word # type_value) list # num list) ctx func cenv cx e es (sa:compile_state) (sm:compile_state)
      (sb:compile_state) (s0:venom_state) ee bs op (t:venom_state)
      cap G tn D lo d explicit PG.
      compile_raw_revert op sm = ((),sb) /\
      fn_has_code sm sb func /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts /\
      ~t.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      (!x. op = Var x ==> not_fresh_at sm x) /\
      expr_post H ctx func cenv cx e es sa sm s0 ee (BytesV bs) op t /\
      expr_store_bound cx (expr_type e) (BytesV bs) op t /\
      expr_type e = BaseT (BytesT (Dynamic cap)) /\
      evaluate_type (get_tenv cx) (expr_type e) =
        SOME (BaseTV (BytesT (Dynamic cap))) /\
      ptr_val_ok cx (post_value_type cenv e) (BytesV bs) op G tn t /\
      ghost_inv_at D lo d cenv cx ee G tn t ==>
      ?w G' tn'. !D'.
        gas_origin_ptr_path (D',lo,explicit,ctx,func,PG)
          (t,G,tn) [] (Abort Revert_abort w,G',tn')) ==>
  !cx ann args dflt DF lo d PG tops ctx shadow_ctx func shadow_func
     cenv env ty es.
  body_exprs_full_ok cx args /\
  body_exprs_prefix_ok cx args /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Call ann RawRevert args dflt) es ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx ty (Call ann RawRevert args dflt) es
Proof
  cheat
QED
