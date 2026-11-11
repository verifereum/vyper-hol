(* Operand stages only: positional results remain unread. *)
Theory exprExtRequestOperandCps
Ancestors
  exprExtRequestTargetCps exprExtRequestStagesSource exprExtRequestReplay
  exprExtRequestUnreadCps exprExtRequestKwargs exprExtRequestHistoryCompose
  exprExtRequestShape exprSimSource exprSimHyps exprSimWordArgs
  exprSimDefs loweringPosts exprLoweringProps exprSafeOperand vyperState
  vyperInterpreter supportedExprTraverse vyperTyping compileEnv
  exprSimHypsDefs vyperTypeSystem vyperTypeCallGraph exprExtRequestGasBind stmtSimForRounds list rich_list
  pair arithmetic venomState

Theorem extrequest_operand_cps:
  exprs_case nocalls ctx func cenv cx [a] /\
  (!s target t. eval_exprs cx [a] s = (INL target,t) ==>
    results_case nocalls ctx func cenv cx (TAKE (LENGTH ats) rest)) /\
  (!s target t s' rs t'.
    eval_exprs cx [a] s = (INL target,t) /\
    eval_expr_results cx (TAKE (LENGTH ats) rest) s' = (INL rs,t') ==>
    exprs_case nocalls ctx func cenv cx (DROP (LENGTH ats) rest)) /\
  expr_body_pre cenv cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) (a::rest) dflt) es /\
  (nocalls ==> int_calls_expr
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) (a::rest) dflt) = []) /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr_op,s1) /\
  compile_multi_vvs compile_expr cenv (TAKE (LENGTH ats) rest) s1 = (arg_vvs,s2) /\
  compile_ext_call_kwargs compile_expr cenv rt opts (DROP (LENGTH ats) rest) s2 =
    ((value_op,gas_op,default_op),s3) /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 s3 func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible
    (vyperState$bind (vyperState$bind (eval_expr cx a) (read_result cx))
      (\target. vyperState$bind (eval_expr_results cx (TAKE (LENGTH ats) rest))
        (\rs. vyperState$bind (eval_exprs cx (DROP (LENGTH ats) rest)) (kont target rs))))
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
  (!target rs vs esA esB tB ee t target_addr.
    (?used. !tail. vyperState$bind (eval_expr cx a) (read_result cx)
      (es with gas_obs := used ++ tail) = (INL target,esA with gas_obs := tail)) /\
    dest_AddressV target = SOME target_addr /\
    eval_operand addr_op t = SOME (w2w target_addr) /\ safe_operand s3 addr_op /\
    extrequest_results_success cx (TAKE (LENGTH ats) rest) esA rs esB /\
    extrequest_kwargs_post ctx func cenv cx rt opts (DROP (LENGTH ats) rest)
      esB s2 tB s3 value_op gas_op default_op
      (TAKE (LENGTH ats) rest) rs arg_vvs vs ee t /\
    wb_frame cenv es sa s0 t /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    sa.cs_next_var <= s3.cs_next_var /\ sa.cs_next_id <= s3.cs_next_id ==>
    gas_outcome F (cx_tops cx) (ctx,func) (kont target rs vs) (ee,t) Q
      (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (vyperState$bind (vyperState$bind (eval_expr cx a) (read_result cx))
      (\target. vyperState$bind (eval_expr_results cx (TAKE (LENGTH ats) rest))
        (\rs. vyperState$bind (eval_exprs cx (DROP (LENGTH ats) rest)) (kont target rs))))
    (es,s0) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  drule extrequest_body_typed >> strip_tac >>
  `expr_body_pre cenv cx env a es` by
    (irule extrequest_body_pre_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
     gvs[expr_body_pre_def]) >>
  `expr_type a = BaseT AddressT` by
    (qpat_assum `well_typed_expr _ (Call _ _ _ _)` mp_tac >>
     simp[NoAsms, Once vyperTypeSystemTheory.well_typed_expr_def]) >>
  `expr_sim_case nocalls ctx func cenv cx a` by fs[exprs_case_def] >>
  `(nocalls ==> int_calls_expr a = [])` by
    (gvs[int_calls_expr_def]) >>
  `gas_admissible (vyperState$bind (eval_expr cx a) (read_result cx))
     expr_res_ok es` by metis_tac[expr_body_pre_gas_admissible] >>
  irule extrequest_target_cps >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `expr_body_pre _ _ _ a _`)) >>
  first_assum (irule_at (Pat `expr_sim_case _ _ _ _ _ _`)) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `eval_exprs cx [a] (es with gas_obs := used) =
     (INL [AddressV target],ee)` by
    (qpat_x_assum `!tail. vyperState$bind (eval_expr cx a) _ _ = _`
       (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[extrequest_kwargs_source_cons] >>
     simp[Once evaluate_def, GSYM bind_assoc, bind_return] >>
     simp[vyperStateTheory.bind_def, vyperStateTheory.return_def] >>
     strip_tac >> simp[evaluation_state_component_equality]) >>
  `results_case nocalls ctx func cenv cx (TAKE (LENGTH ats) rest)` by
    metis_tac[] >>
  `gas_admissible
     (vyperState$bind (eval_expr_results cx (TAKE (LENGTH ats) rest))
       (\rs. vyperState$bind (eval_exprs cx (DROP (LENGTH ats) rest))
         (kont (AddressV target) rs))) expr_vv_res_ok ee` by
    (drule_all gas_admissible_bind_tail >> simp[]) >>
  `expr_sim_inv cenv cx env ee` by
    (qpat_x_assum `!tail. vyperState$bind (eval_expr cx a) _ _ = _`
       (qspec_then `[]` mp_tac) >>
     `expr_body_pre cenv cx env a (es with gas_obs := used)` by simp[] >>
     simp[vyperStateTheory.bind_def] >> strip_tac >>
     drule_all (SRULE [vyperStateTheory.bind_def]
       exprSimSourceTheory.expr_body_pre_eval) >>
     simp[]) >>
  `EVERY (\e. !mid. expr_sim_inv cenv cx env mid ==>
       expr_body_pre cenv cx env e mid) rest` by
    (drule extrequest_operand_body_pre >> simp[]) >>
  `EVERY (\e. ~expr_has_effect e) (TAKE (LENGTH ats) rest)` by
    (fs[] >> metis_tac[EVERY_TAKE]) >>
  `EVERY (\e. nocalls ==> int_calls_expr e = []) (TAKE (LENGTH ats) rest)` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `MEM e (a::rest)` by metis_tac[rich_listTheory.MEM_TAKE, listTheory.MEM] >>
     `int_calls_exprs (a::rest) = []` by fs[int_calls_expr_def] >>
     metis_tac[int_calls_exprs_mem]) >>
  irule extrequest_unread_cps >>
  simp[] >>
  first_assum (irule_at (Pat `compile_multi_vvs _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `results_case _ _ _ _ _ _`)) >>
  qexistsl [`[]`, `[]`, `[]`, `env`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  reverse conj_tac
  >- (rpt strip_tac >> irule extrequest_results_reach_pre >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[EVERY_TAKE]) >>
  rpt gen_tac >> strip_tac >>
  `?more. !tail. eval_expr_results cx (TAKE (LENGTH ats) rest)
      (ee with gas_obs := more ++ tail) = (INL rs,ee' with gas_obs := tail)` by
    (qpat_assum `extrequest_results_success _ _ _ _ _` mp_tac >>
     simp[NoAsms, extrequest_results_success_def] >> strip_tac >>
     drule_all extrequest_results_prefix_replay >> simp[]) >>
  `gas_admissible (vyperState$bind (eval_exprs cx (DROP (LENGTH ats) rest))
      (kont (AddressV target) rs)) expr_vv_res_ok ee'` by
    (drule_all gas_admissible_bind_tail >> simp[]) >>
  `exprs_case nocalls ctx func cenv cx (DROP (LENGTH ats) rest)` by
    (qpat_assum `extrequest_results_success _ _ _ _ _` mp_tac >>
     simp[NoAsms, extrequest_results_success_def] >> strip_tac >> metis_tac[]) >>
  `expr_sim_inv cenv cx env ee'` by
    (qpat_assum `extrequest_results_success _ _ _ _ _` mp_tac >>
     simp[NoAsms, extrequest_results_success_def] >> strip_tac >>
     `expr_sim_inv cenv cx env mid` by
       (irule extrequest_results_preserves_inv >>
        goal_assum (drule_at Any) >> simp[] >> metis_tac[EVERY_TAKE]) >>
     simp[]) >>
  qpat_assum `well_typed_expr _ (Call _ _ _ _)` mp_tac >>
  simp[NoAsms, Once vyperTypeSystemTheory.well_typed_expr_def] >> strip_tac >>
  `EVERY (\e. nocalls ==> int_calls_expr e = []) (DROP (LENGTH ats) rest)` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `MEM e (a::rest)` by (drule MEM_DROP_IMP >> simp[]) >>
     `int_calls_exprs (a::rest) = []` by fs[int_calls_expr_def] >>
     metis_tac[int_calls_exprs_mem]) >>
  `EVERY2 (\kw e. expr_type e = ext_call_kw_type rt kw /\
      (kw = EKDefault ==> rt <> NoneT)) opts (DROP (LENGTH ats) rest)` by
    (fs[MAP_EQ_EVERY2] >>
     fs[LIST_REL_EL_EQN, EVERY_MEM] >> metis_tac[MEM_EL]) >>
  irule extrequest_kwargs_cps >> simp[] >>
  first_assum (irule_at (Pat `compile_ext_call_kwargs _ _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `exprs_case _ _ _ _ _ _`)) >>
  qexistsl [`arg_vvs`, `rs`, `TAKE (LENGTH ats) rest`, `env`] >>
  `ee' with gas_obs := [] = ee'` by simp[evaluation_state_component_equality] >>
  simp[] >>
  conj_tac >- (fs[] >> metis_tac[EVERY_DROP]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  reverse conj_tac
  >- (rpt strip_tac >> irule extrequest_kwargs_reach_pre >> simp[] >>
      conj_tac >- metis_tac[EVERY_DROP] >> qexists `ee'` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `ci_mono s1 s2` by
    (qpat_assum `compile_multi_vvs _ _ _ _ = _` mp_tac >>
     mp_tac (Q.ISPEC `compile_expr` ci_mono_compile_multi_vvs) >>
     simp[cj 1 compile_expr_ci_mono] >> metis_tac[SND]) >>
  qpat_assum `extrequest_kwargs_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SRULE [extrequest_kwargs_post_def]) >>
  `wb_frame cenv es sa s0 t'` by
    (irule wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl [`ee`, `s1`, `t`] >> simp[]) >>
     metis_tac[]) >>
  `sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `wb_frame cenv es sa s0 t''` by
    (irule wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl [`ee'`, `s2`, `t'`] >> simp[]) >>
     metis_tac[]) >>
  `safe_operand s2 addr_op` by
    (irule safe_operand_mono >> qexists `s1` >> gvs[ci_mono_def]) >>
  `safe_operand s3 addr_op` by metis_tac[safe_operand_mono] >>
  `eval_operand addr_op t' = SOME (w2w target)` by
    (Cases_on `addr_op` >> gvs[safe_operand_def, eval_operand_def] >>
     metis_tac[wb_frame_vars]) >>
  `eval_operand addr_op t'' = SOME (w2w target)` by
    (Cases_on `addr_op` >> gvs[safe_operand_def, eval_operand_def] >>
     metis_tac[wb_frame_vars]) >>
  first_x_assum irule >> simp[] >>
  qexistsl [`ee`, `ee'`, `t'`] >> simp[] >>
  qexists `used` >> simp[]
QED
