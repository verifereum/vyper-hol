(* Ordinary head preparation, shared by invariant-carrying unread recursion. *)
Theory extcallProtFrameUnread
Ancestors
  exprExtRequestUnreadCps exprExtRequestStrongCapture exprExtRequestHistory
  exprExtRequestSourceFrame exprExtRequestReadProbe exprExtRequestOperandSafety
  exprOperandVar exprSafeOperand exprLoweringProps loweringPosts exprSimProps
  exprSimWordArgs exprSimSource exprSimHypsDefs exprSimDefs compileEnv
  vyperCallOutcomeFrame vyperInterpreter vyperState gasSummary fragGasMode
  fragGasPath exprExtRequestGasBind stmtSimProps pair finite_map context
  exprLowering gasOutcome stmtSimDeclGas fragExec

Theorem extcall_protframe_unread_head:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  ci_mono sa sm /\ local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  stmt_state_rel ctx func ce cx es s0 /\
  vv_post ctx func ce cx e es sa sm s0 (ee with gas_obs := []) r vv t /\
  (!tail. eval_expr cx e (es with gas_obs := used ++ tail) =
     (INL r,ee with gas_obs := tail)) /\
  extrequest_strong_captures ctx func ce cx old_es old_rs old_vvs
    (es with gas_obs := []) sa s0 /\
  (!ty p w tv. vv = LocatedValue ty p /\
    eval_operand p.ptr_operand t = SOME w /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    (p.ptr_location = LocStorage ==>
      storage_read_live cx F (get_storage cx (ee with gas_obs := []) F) w tv) /\
    (p.ptr_location = LocTransient ==>
      storage_read_live cx T (get_storage cx (ee with gas_obs := []) T) w tv)) /\
  (!n b sz. local_region ce es.scopes s0 n b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
  (!off len.
    (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      sa.cs_next_id <= inst.inst_id /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
      compileEnv$regions_disjoint off len b sz) ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len s0.vs_memory) ==>
  stmt_state_rel ctx func ce cx (ee with gas_obs := []) t /\
  vv_post ctx func ce cx e (es with gas_obs := []) sa sm s0
    (ee with gas_obs := []) r vv t /\
  extrequest_read_frame cx (es with gas_obs := []) (ee with gas_obs := []) /\
  wb_frame ce es sa s0 t /\
  extrequest_strong_capture ctx func ce cx e r vv (ee with gas_obs := []) sm t /\
  extrequest_strong_captures ctx func ce cx old_es old_rs old_vvs
    (ee with gas_obs := []) sm t
Proof
  strip_tac >>
  `!l. vv_operand vv <> Label l` by
    (irule (cj 1 extrequest_compiler_nonlabel) >>
     goal_assum (drule_at Any) >> qexists `env` >>
     qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[CONJUNCT1 compiler_compile_var] >>
  `safe_operand sm (vv_operand vv)` by simp[safe_operand_def] >>
  `extrequest_strong_capture ctx func ce cx e r vv (ee with gas_obs := []) sm t` by
    (irule extrequest_strong_capture_intro >>
     qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     gvs[ci_mono_def] >> conj_tac
     >- (irule post_value_type_not_int_call >> metis_tac[expr_has_effect_thm]) >>
     Cases_on `vv` >> gvs[vv_operand_def]) >>
  `extrequest_read_frame cx (es with gas_obs := []) (ee with gas_obs := [])` by
    (drule extrequest_pure_expr_read_frame >>
     rewrite_tac[state_rel_frame_result] >>
     disch_then (qspecl_then
       [`cx`, `es with gas_obs := used`, `INL r`, `ee with gas_obs := []`] mp_tac) >>
     qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
     fs[extrequest_read_frame_def]) >>
  `vv_post ctx func ce cx e (es with gas_obs := []) sa sm s0
     (ee with gas_obs := []) r vv t` by simp[vv_post_initial_gas] >>
  `stmt_state_rel ctx func ce cx (ee with gas_obs := []) t /\
   wb_frame ce es sa s0 t` by (gvs[vv_post_def, wb_frame_def, locals_kept_def] >> metis_tac[]) >>
  simp[] >> irule extrequest_strong_captures_extend >>
  qpat_assum `extrequest_strong_captures _ _ _ _ _ _ _ _ sa s0` (irule_at Any) >>
  qpat_assum `vv_post _ _ _ _ _ (es with gas_obs := []) _ _ _ _ _ _ _`
    (irule_at Any) >> gvs[ci_mono_def] >> metis_tac[]
QED

Theorem extrequest_unread_resource_cps:
  !xs es sa sb vvs s0 k old_es old_rs old_vvs.
  results_case nocalls ctx func cenv cx xs /\
  compile_multi_vvs compile_expr cenv xs sa = (vvs,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\e. ~expr_has_effect e) xs /\
  EVERY (\e. nocalls ==> int_calls_expr e = []) xs /\
  (!i ee. i < LENGTH xs /\ extrequest_results_reach cx xs es i ee ==>
    expr_body_pre cenv cx env (EL i xs) ee) /\
  gas_admissible (bind (eval_expr_results cx xs) k) expr_vv_res_ok es /\
  extrequest_strong_captures ctx func cenv cx old_es old_rs old_vvs
    (es with gas_obs := []) sa s0 /\
  (!e ee sm sn t ef r vv u ty p w tv.
    vv_post ctx func cenv cx e ee sm sn t ef r vv u /\
    ~expr_has_effect e /\ vv = LocatedValue ty p /\
    eval_operand p.ptr_operand u = SOME w /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    (p.ptr_location = LocStorage ==>
      storage_read_live cx F (get_storage cx ef F) w tv) /\
    (p.ptr_location = LocTransient ==>
      storage_read_live cx T (get_storage cx ef T) w tv)) /\
  (!e ee sm sn t ef r vv u.
    vv_post ctx func cenv cx e ee sm sn t ef r vv u /\
    ~expr_has_effect e ==>
    (!n b sz. local_region cenv ee.scopes t n b sz ==>
      mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz t.vs_memory) /\
    (!off len.
      (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        sm.cs_next_id <= inst.inst_id /\
        FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
        compileEnv$regions_disjoint off len b sz) ==>
      mem_bytes_at off len u.vs_memory = mem_bytes_at off len t.vs_memory)) /\
  H s0 /\
  (!e ee sm sn t ef r vv u n.
    vv_post ctx func cenv cx e ee sm sn t ef r vv u /\
    ~expr_has_effect e /\ H t /\
    gas_marked_path F ctx func t n (OK u) ==> H u) /\
  (!rs ee t.
    extrequest_results_success cx xs es rs ee /\
    stmt_state_rel ctx func cenv cx ee t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ wb_frame cenv es sa s0 t /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ ee.gas_obs = [] /\
    extrequest_strong_captures ctx func cenv cx xs rs vvs ee sb t /\
    extrequest_strong_captures ctx func cenv cx old_es old_rs old_vvs ee sb t /\ H t ==>
    gas_outcome F (cx_tops cx) (ctx,func) (k rs) (ee,t) Q
      (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr_results cx xs) k) (es,s0) Q
    (\res ee r. expr_exit res r)
Proof
  Induct_on `xs` >> rpt gen_tac
  >- (simp[compile_multi_vvs_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >>
      `gas_outcome F (cx_tops cx) (ctx,func) (k [])
         (es with gas_obs := [],s0) Q (\res ee r. expr_exit res r)` by
        (first_x_assum irule >> simp[wb_frame_refl]) >>
      simp[Once evaluate_def, bind_return] >>
      qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_outcome_def] >> strip_tac
      >- (qexists `marks` >> disj1_tac >>
          gvs[gas_summary_at_def, gas_marked_exec_def] >> metis_tac[]) >>
      drule gas_exempt_cert_start_gas_obs >>
      disch_then (qspec_then `es.gas_obs` mp_tac) >> simp[] >> metis_tac[]) >>
  simp[results_case_def, Once compile_multi_vvs_def,
       comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  rename1 `compile_expr cenv (expr_type h) h sa = (head_vv,sm)` >>
  `expr_body_pre cenv cx env h es` by
    (qpat_x_assum `!i ee. _` (qspecl_then [`0`, `es with gas_obs := []`] mp_tac) >> simp[]) >>
  `gas_admissible (eval_expr cx h) expr_vv_res_ok es` by
    (drule_all extrequest_results_head_admissible >> simp[]) >>
  `ci_mono sa sm` by
    (mp_tac (Q.SPECL [`cenv`, `expr_type h`, `h`, `sa`]
       (cj 1 compile_expr_ci_mono)) >> simp[]) >>
  `ci_mono sm sb` by
    (qpat_x_assum `compile_multi_vvs _ _ _ _ = _` mp_tac >>
     mp_tac (Q.ISPEC `compile_expr` ci_mono_compile_multi_vvs) >>
     simp[cj 1 compile_expr_ci_mono] >> metis_tac[SND]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> gvs[ci_mono_def]) >>
  `local_ptrs_reserved cenv sm` by (drule_all compiler_ci_mono_reserved >> simp[]) >>
  `expr_vv_sim ctx func cenv cx (expr_type h) h es` by
    (gvs[expr_vv_case_def] >> first_x_assum irule >> qexists `env` >> simp[]) >>
  `gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx h) (es,s0)
    (\res ee t. ?r. res = INL r /\
      vv_post ctx func cenv cx h es sa sm s0 ee r head_vv t /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (gvs[expr_vv_sim_def] >> first_x_assum irule >> simp[]) >>
  rewrite_tac[extrequest_results_cps_cons] >>
  drule (INST_TYPE [alpha |-> ``:eval_result``] extrequest_outcome_bind_result) >>
  disch_then (qspecl_then
    [`\r. bind (eval_expr_results cx xs) (\rs. k (r::rs))`,
     `\res ee r. expr_exit res r`, `Q`] mp_tac) >> disch_then irule >>
  reverse conj_tac
  >- (rpt gen_tac >> Cases_on `rr` >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >> suspend "head_landing"
QED

Resume extrequest_unread_resource_cps[head_landing]:
  `!tail. eval_expr cx h
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (INL r, mid with gas_obs := tail)` by gvs[gas_marked_exec_def] >>
  `H t` by
    (qpat_assum `!e ee sm sn t ef r vv u n. _` irule >>
     qpat_assum `vv_post _ _ _ _ h es _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> qexists `LENGTH marks` >> gvs[gas_marked_exec_def]) >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def, gas_marked_path_def]) >>
     drule fragGasPathTheory.gas_path_normal >> simp[]) >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t /\
   vv_post ctx func cenv cx h (es with gas_obs := []) sa sm s0
     (mid with gas_obs := []) r head_vv t /\
   extrequest_read_frame cx (es with gas_obs := []) (mid with gas_obs := []) /\
   wb_frame cenv es sa s0 t /\
   extrequest_strong_capture ctx func cenv cx h r head_vv (mid with gas_obs := []) sm t /\
   extrequest_strong_captures ctx func cenv cx old_es old_rs old_vvs
     (mid with gas_obs := []) sm t` by
    (irule extcall_protframe_unread_head >>
     qpat_assum `vv_post _ _ _ _ h es _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `extrequest_strong_captures _ _ _ _ _ _ _ _ sa s0` (irule_at Any) >>
     qexistsl [`gas_explicit marks s0.vs_gas_readings`, `env`] >> simp[] >>
     qpat_assum `!e ee sm sn t ef r vv u. _` (drule_all_then strip_assume_tac) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt strip_tac >> gvs[] >>
     qpat_x_assum `!e ee sm sn t ef r u ty p w tv. _`
       (drule_all_then strip_assume_tac) >> simp[]) >>
  suspend "tail_composition"
QED

Resume extrequest_unread_resource_cps[tail_composition]:
  `gas_admissible (bind (eval_expr_results cx xs) (\rs. k (r::rs)))
     expr_vv_res_ok (mid with gas_obs := [])` by
    (drule_all extrequest_results_tail_admissible >> simp[]) >>
  `!i ee. i < LENGTH xs /\
    extrequest_results_reach cx xs (mid with gas_obs := []) i ee ==>
    expr_body_pre cenv cx env (EL i xs) ee` by
    (rpt strip_tac >> irule extrequest_results_body_pre_tail >>
     conj_tac >- simp[] >>
     qexistsl [`h`, `mid`, `r`, `es`, `gas_explicit marks s0.vs_gas_readings`] >>
     simp[]) >>
  `results_case nocalls ctx func cenv cx xs` by
    (first_x_assum irule >>
     qexistsl [`es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
               `r`, `mid with gas_obs := []`] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  qpat_x_assum `!es' sa' sb' vvs' s0' k' old_es' old_rs' old_vvs'. _` irule >>
  simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`h::old_es`, `r::old_rs`, `head_vv::old_vvs`, `sm`, `cs''`, `rest`] >>
  qpat_assum `compile_multi_vvs _ _ _ sm = _` (irule_at Any) >>
  simp[extrequest_strong_captures_cons] >>
  rpt gen_tac >> strip_tac >>
  `extrequest_results_success cx (h::xs) es (r::rs) ee` by
    (irule extrequest_results_success_cons >>
     metis_tac[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `extrequest_read_frame _ _ _`
       (strip_assume_tac o REWRITE_RULE [extrequest_read_frame_def]) >>
     fs[]) >>
  `wb_frame cenv es sa s0 t'` by
    (irule wb_frame_trans >>
     qpat_assum `wb_frame _ _ _ s0 t` (irule_at Any) >>
     qpat_assum `wb_frame _ _ sm t t'` (irule_at Any) >>
     gvs[ci_mono_def] >> metis_tac[]) >>
  qpat_x_assum `!rs ee t. _` irule >>
  simp[extrequest_strong_captures_cons]
QED
Finalise extrequest_unread_resource_cps
