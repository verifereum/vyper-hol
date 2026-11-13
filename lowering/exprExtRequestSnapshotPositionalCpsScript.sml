(* Positional arguments are read and snapshotted before the next producer. *)
Theory exprExtRequestSnapshotPositionalCps
Ancestors
  exprExtRequestSnapshotHeadCps exprExtRequestSnapshotSource
  exprExtRequestSnapshotStoreInterface exprExtRequestSnapshotProbe
  exprExtRequestStagesSource exprExtRequestKwargs exprExtRequestReplay
  exprExtRequestHistoryCompose exprSimWordArgs exprSimHyps
  exprLoweringProps gasOutcome gasExemptCert gasSummaryCompose
  exprSimMemorySource exprSimDefs loweringPosts freshWrites
  vyperState vyperInterpreter compileEnv list exprLowering
  exprExtRequestHistory gasSummary stmtSimDeclGas fragExec exprSimHypsDefs
  exprExtRequestReadProbe

Theorem extrequest_snapshot_positional_cps:
  !xs es sa sb vvs s0 k old_cells.
  exprs_case nocalls ctx func ce cx xs /\
  compile_ext_call_args compile_expr ce kws (MAP (lowered_value_type ce) xs) xs sa = (vvs,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\e. ~expr_has_effect e) (xs ++ kws) /\
  EVERY (\e. nocalls ==> int_calls_expr e = []) xs /\
  EVERY (\e. !mid. expr_sim_inv ce cx env mid ==> expr_body_pre ce cx env e mid) xs /\
  expr_sim_inv ce cx env es /\
  gas_admissible (bind (eval_exprs cx xs) k) expr_vv_res_ok es /\
  EVERY (extrequest_snapshot_cell ctx func ce cx (es with gas_obs := []) sa s0) old_cells /\
  (!e ee sm sn t ef r vv u ty p w tv.
    vv_post ctx func ce cx e ee sm sn t ef r vv u /\
    ~expr_has_effect e /\ vv = LocatedValue ty p /\
    eval_operand p.ptr_operand u = SOME w /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    (p.ptr_location = LocStorage ==> storage_read_live cx F (get_storage cx ef F) w tv) /\
    (p.ptr_location = LocTransient ==> storage_read_live cx T (get_storage cx ef T) w tv)) /\
  (!e ee sm sn t ef r vv u.
    vv_post ctx func ce cx e ee sm sn t ef r vv u /\ ~expr_has_effect e ==>
    (!n b sz. local_region ce ee.scopes t n b sz ==>
      mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz t.vs_memory) /\
    (!off len. (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      sm.cs_next_id <= inst.inst_id /\ FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
      loweringStateRelDefs$regions_disjoint off len b sz) ==>
      mem_bytes_at off len u.vs_memory = mem_bytes_at off len t.vs_memory)) /\
  (!vs ee u cells.
    MAP (\(vv,ty,tv,v). vv) cells = vvs /\
    MAP (\(vv,ty,tv,v). ty) cells = MAP (lowered_value_type ce) xs /\
    MAP (\(vv,ty,tv,v). v) cells = vs /\
    EVERY (extrequest_snapshot_cell ctx func ce cx ee sb u) (old_cells ++ cells) /\
    stmt_state_rel ctx func ce cx ee u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved ce sb /\ ee.gas_obs = [] /\
    wb_frame ce es ee sa s0 u /\
    extrequest_history_frame ce cx (es with gas_obs := []) sa s0 ee sb u /\
    (?used. !tail. eval_exprs cx xs (es with gas_obs := used ++ tail) =
      (INL vs,ee with gas_obs := tail)) ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      ((k : value list -> evaluation_state -> eval_result evaluation_result) vs) (ee,u) Q
      (\res ef result. expr_exit res result)) ==>
  gas_outcome F (cx_tops cx) (ctx,func) (bind (eval_exprs cx xs) k) (es,s0) Q
    (\res ef result. expr_exit res result)
Proof
  Induct_on `xs` >> rpt gen_tac
  >- (simp[compile_ext_call_args_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >>
      `gas_outcome F (cx_tops cx) (ctx,func) (k [])
        (es with gas_obs := [],s0) Q (\res ef result. expr_exit res result)` by
        (first_x_assum irule >>
         simp[wb_frame_refl, extrequest_history_frame_refl] >>
         qexists `[]` >> simp[Once evaluate_def, return_def,
           evaluation_state_component_equality]) >>
      simp[Once evaluate_def, bind_return] >>
      qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_outcome_def] >> strip_tac
      >- (qexists `marks` >> disj1_tac >>
          gvs[gas_summary_at_def, gas_marked_exec_def] >> metis_tac[]) >>
      drule gas_exempt_cert_start_gas_obs >>
      disch_then (qspec_then `es.gas_obs` mp_tac) >> simp[] >> metis_tac[]) >>
  strip_tac >>
  `~exprs_can_mutate ce (xs ++ kws)` by
    (irule extrequest_snapshot_tail_no_copy >> gvs[]) >>
  qpat_x_assum `compile_ext_call_args _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_ext_call_args_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_expr ce (expr_type h) h sa = (head_vv,sm)` >>
  rename1 `compile_snapshot_vv ce F _ sm = (head_sv,sn)` >>
  `ci_mono sa sm` by
    (mp_tac (Q.SPECL [`ce`, `expr_type h`, `h`, `sa`] (cj 1 compile_expr_ci_mono)) >> simp[]) >>
  `ci_mono sm sn` by metis_tac[ci_mono_compile_snapshot_vv, pairTheory.SND] >>
  rename1 `compile_ext_call_args compile_expr ce kws _ xs sn = (tail_vvs,sb)` >>
  `ci_mono sn sb` by
    (qpat_assum `compile_ext_call_args _ _ _ _ _ _ = _` mp_tac >>
     mp_tac (Q.SPECL [`xs`, `MAP (lowered_value_type ce) xs`, `compile_expr`, `ce`, `kws`, `sn`] ci_mono_compile_ext_call_args) >>
     simp[cj 1 compile_expr_ci_mono] >> metis_tac[pairTheory.SND]) >>
  `ci_mono sa sn` by metis_tac[ci_mono_trans] >>
  `fn_has_code sa sn func /\ fn_has_code sn sb func` by
    (irule fn_has_code_split >> gvs[ci_mono_def]) >>
  `expr_body_pre ce cx env h es` by metis_tac[] >>
  `expr_vv_case nocalls ctx func ce cx h` by fs[exprs_case_def] >>
  `gas_admissible (eval_expr cx h) expr_vv_res_ok es` by
    metis_tac[extrequest_snapshot_source_head_admissible, forced_expr_admissible_raw] >>
  simp[eval_exprs_cons_action, bind_assoc, bind_return] >>
  once_rewrite_tac[GSYM bind_assoc] >>
  irule extrequest_snapshot_head_cps >>
  qpat_assum `compile_expr _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_snapshot_vv _ _ _ _ = _` (irule_at Any) >>
  simp[] >>
  qexistsl [`nocalls`, `env`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `exprs_case nocalls ctx func ce cx xs` by
    (irule extrequest_snapshot_source_tail_case >> metis_tac[]) >>
  `expr_sim_inv ce cx env ee` by
    (`expr_body_pre ce cx env h (es with gas_obs := used)` by simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
     `bind (eval_expr cx h) (read_result cx) (es with gas_obs := used) = (INL v,ee)` by
       (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[]) >>
     metis_tac[exprSimSourceTheory.expr_body_pre_eval]) >>
  `gas_admissible (bind (eval_exprs cx xs) (\vs. k (v::vs))) expr_vv_res_ok ee` by
    (drule_all extrequest_snapshot_source_tail_admissible >> simp[]) >>
  `EVERY (extrequest_snapshot_cell ctx func ce cx ee sn u) old_cells` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     `extrequest_snapshot_cell ctx func ce cx (es with gas_obs := []) sa s0 e` by
       metis_tac[] >>
     irule extrequest_snapshot_cell_history >>
     qpat_assum `extrequest_snapshot_cell _ _ _ _ (es with gas_obs := []) _ _ e`
       (irule_at Any) >>
     simp[] >> metis_tac[stmt_state_rel_gas_obs]) >>
  first_x_assum irule >> simp[] >>
  qpat_assum `compile_ext_call_args _ _ _ _ _ _ = _` (irule_at Any) >>
  qexists `old_cells ++ [(head_sv,lowered_value_type ce h,tv,v)]` >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `wb_frame ce ee ef sn u q` >>
  `wb_frame ce es ef sa s0 q` by
    (irule wb_frame_trans >>
     qpat_assum `stmt_state_rel ctx func ce cx es s0` (irule_at Any) >>
     qpat_assum `wb_frame ce es ee sa s0 u` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ef sn u q` (irule_at Any) >> simp[] >>
     fs[extrequest_history_frame_def, extrequest_read_frame_def, ci_mono_def]) >>
  `extrequest_history_frame ce cx (es with gas_obs := []) sa s0 ef sb q` by
    (irule extrequest_history_frame_trans >>
     qpat_assum `extrequest_history_frame _ _ _ sa s0 ee sn u` (irule_at Any) >>
     simp[] >> metis_tac[stmt_state_rel_gas_obs]) >>
  `?total. !tail. eval_exprs cx (h::xs) (es with gas_obs := total ++ tail) =
      (INL (v::MAP (\(vv,ty,tv,v). v) cells),ef with gas_obs := tail)` by
    (drule_all extrequest_kwargs_counted_cons >> metis_tac[]) >>
  qpat_x_assum `!ee u cells. _`
    (qspecl_then [`ef`, `q`, `(head_sv,lowered_value_type ce h,tv,v)::cells`] mp_tac) >>
  simp[] >> disch_then irule >> metis_tac[]
QED
