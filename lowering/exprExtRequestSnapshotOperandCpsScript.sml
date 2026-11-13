(* Operand stages with immediate positional snapshots. *)
Theory exprExtRequestSnapshotOperandCps
Ancestors
  exprExtRequestSnapshotPositionalCps exprExtRequestSnapshotStoreInterface
  exprExtRequestTargetCps exprExtRequestStagesSource exprExtRequestReplay
  exprExtRequestKwargs exprExtRequestHistoryCompose exprExtRequestStrongCapture
  exprExtRequestHistory exprExtRequestReadProbe
  exprExtRequestShape exprSimSource exprSimHyps exprSimWordArgs
  exprSimDefs loweringPosts exprLoweringProps exprSafeOperand vyperState
  vyperInterpreter supportedExprTraverse vyperTyping compileEnv
  exprSimHypsDefs vyperTypeSystem vyperTypeCallGraph exprExtRequestGasBind
  stmtSimForRounds list rich_list pair arithmetic venomState

Theorem extrequest_snapshot_operand_cps:
  exprs_case nocalls ctx func cenv cx [a] /\
  (!s target t. eval_exprs cx [a] s = (INL target,t) ==>
    exprs_case nocalls ctx func cenv cx (TAKE (LENGTH ats) rest)) /\
  (!s target t s' vs t'.
    eval_exprs cx [a] s = (INL target,t) /\
    eval_exprs cx (TAKE (LENGTH ats) rest) s' = (INL vs,t') ==>
    exprs_case nocalls ctx func cenv cx (DROP (LENGTH ats) rest)) /\
  expr_body_pre cenv cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) (a::rest) dflt) es /\
  (nocalls ==> int_calls_expr
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) (a::rest) dflt) = []) /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr_op,s1) /\
  compile_ext_call_args compile_expr cenv (DROP (LENGTH ats) rest)
    (MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest))
    (TAKE (LENGTH ats) rest) s1 = (arg_vvs,s2) /\
  compile_ext_call_kwargs compile_expr cenv rt opts (DROP (LENGTH ats) rest) s2 =
    ((value_op,gas_op,default_op),s3) /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 s3 func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible
    (bind (bind (eval_expr cx a) (read_result cx))
      (\target. bind (eval_exprs cx (TAKE (LENGTH ats) rest))
        (\posvs. bind (eval_exprs cx (DROP (LENGTH ats) rest)) (kont target posvs))))
    expr_vv_res_ok es /\
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
        loweringStateRelDefs$regions_disjoint off len b sz) ==>
      mem_bytes_at off len u.vs_memory = mem_bytes_at off len t.vs_memory)) /\
  (!target posvs kwvs esA esB tB ee t target_addr cells.
    (?used. !tail. bind (eval_expr cx a) (read_result cx)
      (es with gas_obs := used ++ tail) = (INL target,esA with gas_obs := tail)) /\
    dest_AddressV target = SOME target_addr /\
    eval_operand addr_op t = SOME (w2w target_addr) /\ safe_operand s3 addr_op /\
    (?used. !tail. eval_exprs cx (TAKE (LENGTH ats) rest)
      (esA with gas_obs := used ++ tail) = (INL posvs,esB with gas_obs := tail)) /\
    MAP (\(vv,ty,tv,v). vv) cells = arg_vvs /\
    MAP (\(vv,ty,tv,v). ty) cells = MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest) /\
    MAP (\(vv,ty,tv,v). v) cells = posvs /\
    EVERY (extrequest_snapshot_cell ctx func cenv cx ee s3 t) cells /\
    extrequest_kwargs_post ctx func cenv cx rt opts (DROP (LENGTH ats) rest)
      esB s2 tB s3 value_op gas_op default_op [] [] [] kwvs ee t /\
    wb_frame cenv es ee sa s0 t /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    sa.cs_next_var <= s3.cs_next_var /\ sa.cs_next_id <= s3.cs_next_id ==>
    gas_outcome F (cx_tops cx) (ctx,func) (kont target posvs kwvs) (ee,t) Q
      (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx a) (read_result cx))
      (\target. bind (eval_exprs cx (TAKE (LENGTH ats) rest))
        (\posvs. bind (eval_exprs cx (DROP (LENGTH ats) rest)) (kont target posvs))))
    (es,s0) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule extrequest_body_typed >> strip_tac >>
  `expr_body_pre cenv cx env a es` by
    (irule extrequest_body_pre_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
     gvs[expr_body_pre_def]) >>
  `expr_type a = BaseT AddressT` by
    (qpat_assum `well_typed_expr _ (Call _ _ _ _)` mp_tac >>
     simp[NoAsms, Once well_typed_expr_def]) >>
  `expr_sim_case nocalls ctx func cenv cx a` by fs[exprs_case_def] >>
  `(nocalls ==> int_calls_expr a = [])` by fs[int_calls_expr_def] >>
  `gas_admissible (bind (eval_expr cx a) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  irule extrequest_target_cps >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `expr_body_pre _ _ _ a _`)) >>
  first_assum (irule_at (Pat `expr_sim_case _ _ _ _ _ _`)) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `eval_exprs cx [a] (es with gas_obs := used) = (INL [AddressV target],ee)` by
    (qpat_x_assum `!tail. bind (eval_expr cx a) _ _ = _`
      (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[extrequest_kwargs_source_cons] >>
     simp[Once evaluate_def, GSYM bind_assoc, bind_return] >>
     simp[bind_def, return_def] >> strip_tac >>
     simp[evaluation_state_component_equality]) >>
  `exprs_case nocalls ctx func cenv cx (TAKE (LENGTH ats) rest)` by metis_tac[] >>
  `gas_admissible
    (bind (eval_exprs cx (TAKE (LENGTH ats) rest))
      (\posvs. bind (eval_exprs cx (DROP (LENGTH ats) rest)) (kont (AddressV target) posvs)))
    expr_vv_res_ok ee` by
    (drule_all gas_admissible_bind_tail >> simp[]) >>
  `expr_sim_inv cenv cx env ee` by
    (qpat_x_assum `!tail. bind (eval_expr cx a) _ _ = _`
      (qspec_then `[]` mp_tac) >>
     `expr_body_pre cenv cx env a (es with gas_obs := used)` by simp[] >>
     simp[bind_def] >> strip_tac >>
     drule_all (SRULE [bind_def] expr_body_pre_eval) >> simp[]) >>
  `EVERY (\e. !mid. expr_sim_inv cenv cx env mid ==>
      expr_body_pre cenv cx env e mid) rest` by
    (drule extrequest_operand_body_pre >> simp[]) >>
  `EVERY (\e. nocalls ==> int_calls_expr e = []) rest` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `int_calls_exprs (a::rest) = []` by fs[int_calls_expr_def] >>
     metis_tac[int_calls_exprs_mem, MEM]) >>
  irule extrequest_snapshot_positional_cps >>
  first_assum (irule_at (Pat `compile_ext_call_args _ _ _ _ _ _ = _`)) >>
  qpat_assum `exprs_case _ _ _ _ _ (TAKE _ rest)` (irule_at Any) >>
  qpat_assum `expr_sim_inv cenv cx env ee` (irule_at Any) >>
  qexists `[]` >> simp[TAKE_DROP] >>
  conj_tac >- metis_tac[EVERY_TAKE] >>
  conj_tac >- metis_tac[EVERY_TAKE] >>
  conj_tac >- metis_tac[] >>
  qx_genl_tac [`pos_end`, `pos_state`, `cells`] >> strip_tac >>
  `pos_end with gas_obs := [] = pos_end` by simp[evaluation_state_component_equality] >>
  `gas_admissible (bind (eval_exprs cx (DROP (LENGTH ats) rest))
      (kont (AddressV target) (MAP (\(vv,ty,tv,v). v) cells)))
      expr_vv_res_ok pos_end` by
    (drule_all gas_admissible_bind_tail >> simp[]) >>
  `exprs_case nocalls ctx func cenv cx (DROP (LENGTH ats) rest)` by
    (qpat_assum `!tail. eval_exprs _ (TAKE _ rest) _ = _`
      (qspec_then `[]` assume_tac) >> gvs[] >> metis_tac[]) >>
  `expr_sim_inv cenv cx env pos_end` by
    (qpat_x_assum `!tail. eval_exprs _ (TAKE _ rest) _ = _`
       (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >>
     irule extrequest_exprs_preserves_inv >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[EVERY_TAKE]) >>
  qpat_assum `well_typed_expr _ (Call _ _ _ _)` mp_tac >>
  simp[NoAsms, Once well_typed_expr_def] >> strip_tac >>
  `EVERY2 (\kw e. expr_type e = ext_call_kw_type rt kw /\
      (kw = EKDefault ==> rt <> NoneT)) opts (DROP (LENGTH ats) rest)` by
    (fs[MAP_EQ_EVERY2] >> fs[LIST_REL_EL_EQN, EVERY_MEM] >> metis_tac[MEM_EL]) >>
  irule extrequest_kwargs_cps >>
  first_assum (irule_at (Pat `compile_ext_call_kwargs _ _ _ _ _ _ = _`)) >>
  qpat_assum `exprs_case _ _ _ _ _ (DROP _ rest)` (irule_at Any) >>
  qexistsl [`[]`, `[]`, `[]`, `env`] >>
  simp[extrequest_strong_captures_def] >>
  conj_tac >- metis_tac[EVERY_DROP] >>
  conj_tac >- metis_tac[EVERY_DROP] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  reverse conj_tac
  >- (rpt strip_tac >> irule extrequest_kwargs_reach_pre >> simp[] >>
      conj_tac >- metis_tac[EVERY_DROP] >> qexists `pos_end` >> simp[]) >>
  qx_genl_tac [`kwvs`, `ef`, `q`] >> strip_tac >>
  `ci_mono s1 s2` by
    (qpat_assum `compile_ext_call_args _ _ _ _ _ _ = _` mp_tac >>
     mp_tac (Q.SPECL [`TAKE (LENGTH ats) rest`,
       `MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest)`,
       `compile_expr`, `cenv`, `DROP (LENGTH ats) rest`, `s1`]
       ci_mono_compile_ext_call_args) >>
     simp[cj 1 compile_expr_ci_mono] >> metis_tac[SND]) >>
  qpat_assum `extrequest_kwargs_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SRULE [extrequest_kwargs_post_def]) >>
  `wb_frame cenv es pos_end sa s0 pos_state` by
    (irule wb_frame_trans >>
     qpat_assum `stmt_state_rel ctx func cenv cx es s0` (irule_at Any) >>
     qpat_assum `wb_frame cenv es ee sa s0 t` (irule_at Any) >>
     qpat_assum `wb_frame cenv ee pos_end s1 t pos_state` (irule_at Any) >>
     fs[extrequest_history_frame_def, extrequest_read_frame_def]) >>
  `sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `wb_frame cenv es ef sa s0 q` by
    (irule wb_frame_trans >>
     qpat_assum `stmt_state_rel ctx func cenv cx es s0` (irule_at Any) >>
     qpat_assum `wb_frame cenv es pos_end sa s0 pos_state` (irule_at Any) >>
     qpat_assum `wb_frame cenv pos_end ef s2 pos_state q` (irule_at Any) >>
     fs[extrequest_history_frame_def, extrequest_read_frame_def]) >>
  `EVERY (extrequest_snapshot_cell ctx func cenv cx ef s3 q) cells` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     `extrequest_snapshot_cell ctx func cenv cx pos_end s2 pos_state e` by
       metis_tac[] >>
     irule extrequest_snapshot_cell_history >>
     qpat_assum `extrequest_snapshot_cell _ _ _ _ pos_end _ _ e` (irule_at Any) >>
     simp[]) >>
  `safe_operand s2 addr_op` by
    (irule safe_operand_mono >> qexists `s1` >> gvs[ci_mono_def]) >>
  `safe_operand s3 addr_op` by metis_tac[safe_operand_mono] >>
  `eval_operand addr_op pos_state = SOME (w2w target)` by
    (Cases_on `addr_op` >> gvs[safe_operand_def, eval_operand_def] >>
     metis_tac[wb_frame_vars]) >>
  `eval_operand addr_op q = SOME (w2w target)` by
    (Cases_on `addr_op` >> gvs[safe_operand_def, eval_operand_def] >>
     metis_tac[wb_frame_vars]) >>
  `MAP FDOM es.scopes = MAP FDOM ef.scopes` by
    fs[extrequest_history_frame_def, extrequest_read_frame_def] >>
  `sa.cs_next_var <= s3.cs_next_var /\ sa.cs_next_id <= s3.cs_next_id` by
    decide_tac >>
  qpat_x_assum `!target posvs kwvs esA esB tB ee t target_addr cells. _`
    (qspecl_then [`AddressV target`, `MAP (\(vv,ty,tv,v). v) cells`, `kwvs`,
      `ee`, `pos_end`, `pos_state`, `ef`, `q`, `target`, `cells`] mp_tac) >>
  simp[] >> disch_then irule >> rpt conj_tac >> metis_tac[]
QED
