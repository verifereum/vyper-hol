(* Retain the protected resource through the public operand-stage interfaces. *)
Theory extcallProtFrameOperand
Ancestors
  extcallProtFrameTarget extcallProtFrameUnread extcallProtFrameKwargs
  exprExtRequestOperandCps exprExtRequestStagesSource exprExtRequestReplay
  exprExtRequestHistoryCompose exprExtRequestShape exprSimSource
  exprSimHyps exprSimWordArgs exprSimDefs loweringPosts exprLoweringProps
  exprSafeOperand vyperState vyperInterpreter supportedExprTraverse
  vyperTyping compileEnv exprSimHypsDefs vyperTypeSystem vyperTypeCallGraph
  exprExtRequestGasBind stmtSimForRounds list rich_list pair arithmetic venomState loweringStateRelDefs valueEncodingDefs

Theorem extcall_protframe_operand_cps:
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
    (bind (bind (eval_expr cx a) (read_result cx))
      (\target. bind (eval_expr_results cx (TAKE (LENGTH ats) rest))
        (\rs. bind (eval_exprs cx (DROP (LENGTH ats) rest)) (kont target rs))))
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
  (!e ee sm sn t ef r vv u n.
    vv_post ctx func cenv cx e ee sm sn t ef r vv u /\ ~expr_has_effect e /\
    gas_marked_path F ctx func t n (OK u) /\
    (!pa pk. prot pa pk ==> pa + pk <= t.vs_alloca_next /\
      mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk M /\
      !i b len. FLOOKUP t.vs_allocas i = SOME (b,len) ==>
        loweringStateRelDefs$regions_disjoint pa pk b len) ==>
    !pa pk. prot pa pk ==> pa + pk <= u.vs_alloca_next /\
      mem_bytes_at pa pk u.vs_memory = mem_bytes_at pa pk M /\
      !i b len. FLOOKUP u.vs_allocas i = SOME (b,len) ==>
        loweringStateRelDefs$regions_disjoint pa pk b len) /\
  (!pa pk. prot pa pk ==> ~expr_has_effect a) /\
  (!pa pk. prot pa pk ==> pa + pk <= s0.vs_alloca_next /\
    mem_bytes_at pa pk s0.vs_memory = mem_bytes_at pa pk M /\
    !i b len. FLOOKUP s0.vs_allocas i = SOME (b,len) ==>
      loweringStateRelDefs$regions_disjoint pa pk b len) /\
  (!target rs vs esA esB tB ee t target_addr.
    (?used. !tail. bind (eval_expr cx a) (read_result cx)
      (es with gas_obs := used ++ tail) = (INL target,esA with gas_obs := tail)) /\
    dest_AddressV target = SOME target_addr /\
    eval_operand addr_op t = SOME (w2w target_addr) /\ safe_operand s3 addr_op /\
    extrequest_results_success cx (TAKE (LENGTH ats) rest) esA rs esB /\
    extrequest_kwargs_post ctx func cenv cx rt opts (DROP (LENGTH ats) rest)
      esB s2 tB s3 value_op gas_op default_op
      (TAKE (LENGTH ats) rest) rs arg_vvs vs ee t /\
    wb_frame cenv es ee sa s0 t /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    sa.cs_next_var <= s3.cs_next_var /\ sa.cs_next_id <= s3.cs_next_id /\
    (!pa pk. prot pa pk ==> pa + pk <= t.vs_alloca_next /\
      mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk M /\
      !i b len. FLOOKUP t.vs_allocas i = SOME (b,len) ==>
        loweringStateRelDefs$regions_disjoint pa pk b len) ==>
    gas_outcome F (cx_tops cx) (ctx,func) (kont target rs vs) (ee,t) Q
      (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx a) (read_result cx))
      (\target. bind (eval_expr_results cx (TAKE (LENGTH ats) rest))
        (\rs. bind (eval_exprs cx (DROP (LENGTH ats) rest)) (kont target rs))))
    (es,s0) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `!e ee sm sn t ef r vv u n. _` (mk_asm "raw_frame") >>
  qpat_x_assum `!target rs vs esA esB tB ee t target_addr. _` (mk_asm "finish") >>
  drule extrequest_body_typed >> strip_tac >>
  `expr_body_pre cenv cx env a es` by
    (irule extrequest_body_pre_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
     gvs[expr_body_pre_def]) >>
  `expr_type a = BaseT AddressT` by
    (qpat_assum `well_typed_expr _ (Call _ _ _ _)` mp_tac >>
     simp[NoAsms, Once vyperTypeSystemTheory.well_typed_expr_def]) >>
  `gas_admissible (bind (eval_expr cx a) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `(nocalls ==> int_calls_expr a = [])` by gvs[int_calls_expr_def] >>
  irule extrequest_target_resource_cps >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `expr_body_pre _ _ _ a _`)) >>
  qexistsl [`nocalls`, `\t. !pa pk. prot pa pk ==>
    pa + pk <= t.vs_alloca_next /\
    mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk M /\
    !i b len. FLOOKUP t.vs_allocas i = SOME (b,len) ==>
      loweringStateRelDefs$regions_disjoint pa pk b len`] >>
  simp[int_calls_expr_def] >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >> Cases_on `?pa pk. prot pa pk`
     >- (asm "raw_frame" drule >> simp[] >> metis_tac[]) >>
     metis_tac[]) >>
  reverse conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> suspend "target_landing"
QED

Resume extcall_protframe_operand_cps[target_landing]:
  `eval_exprs cx [a] (es with gas_obs := used) =
     (INL [AddressV target],ee)` by
    (qpat_x_assum `!tail. bind (eval_expr cx a) _ _ = _`
       (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[exprExtRequestKwargsTheory.extrequest_kwargs_source_cons] >>
     simp[Once evaluate_def, GSYM bind_assoc, bind_return] >>
     simp[vyperStateTheory.bind_def, vyperStateTheory.return_def] >>
     strip_tac >> simp[evaluation_state_component_equality]) >>
  `results_case nocalls ctx func cenv cx (TAKE (LENGTH ats) rest)` by metis_tac[] >>
  `gas_admissible (bind (eval_expr_results cx (TAKE (LENGTH ats) rest))
      (\rs. bind (eval_exprs cx (DROP (LENGTH ats) rest))
        (kont (AddressV target) rs))) expr_vv_res_ok ee` by
    (drule_all gas_admissible_bind_tail >> simp[]) >>
  `expr_sim_inv cenv cx env ee` by
    (qpat_x_assum `!tail. bind (eval_expr cx a) _ _ = _`
       (qspec_then `[]` mp_tac) >>
     `expr_body_pre cenv cx env a (es with gas_obs := used)` by simp[] >>
     simp[vyperStateTheory.bind_def] >> strip_tac >>
     drule_all (SRULE [vyperStateTheory.bind_def] exprSimSourceTheory.expr_body_pre_eval) >> simp[]) >>
  `EVERY (\e. !mid. expr_sim_inv cenv cx env mid ==>
      expr_body_pre cenv cx env e mid) rest` by
    (drule extrequest_operand_body_pre >> simp[]) >>
  `EVERY (\e. nocalls ==> int_calls_expr e = []) (TAKE (LENGTH ats) rest)` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `MEM e (a::rest)` by metis_tac[MEM_TAKE, MEM] >>
     `int_calls_exprs (a::rest) = []` by fs[int_calls_expr_def] >>
     metis_tac[int_calls_exprs_mem]) >>
  irule extrequest_unread_resource_cps >>
  first_assum (irule_at (Pat `compile_multi_vvs _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `results_case _ _ _ _ _ _`)) >>
  qexistsl [`[]`, `[]`, `[]`, `env`, `\t. !pa pk. prot pa pk ==>
    pa + pk <= t.vs_alloca_next /\
    mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk M /\
    !i b len. FLOOKUP t.vs_allocas i = SOME (b,len) ==>
      loweringStateRelDefs$regions_disjoint pa pk b len`] >> simp[] >>
  suspend "unread_contracts"
QED

Resume extcall_protframe_operand_cps[unread_contracts]:
  conj_tac >- (fs[] >> metis_tac[EVERY_TAKE]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt gen_tac >> strip_tac >> asm "raw_frame" drule >> disch_then (qspec_then `n` mp_tac) >> simp[] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac
  >- (rpt strip_tac >> irule extrequest_results_reach_pre >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[EVERY_TAKE]) >>
  rpt gen_tac >> strip_tac >> suspend "results_landing"
QED

Resume extcall_protframe_operand_cps[results_landing]:
  `EVERY (\e. ~expr_has_effect e) (TAKE (LENGTH ats) rest)` by
    (fs[] >> metis_tac[EVERY_TAKE]) >>
  `?more. !tail. eval_expr_results cx (TAKE (LENGTH ats) rest)
      (ee with gas_obs := more ++ tail) = (INL rs,ee' with gas_obs := tail)` by
    (qpat_assum `extrequest_results_success _ _ _ _ _` mp_tac >>
     simp[NoAsms, exprExtRequestUnreadCpsTheory.extrequest_results_success_def] >> strip_tac >>
     drule_all extrequest_results_prefix_replay >> simp[]) >>
  `gas_admissible (bind (eval_exprs cx (DROP (LENGTH ats) rest))
      (kont (AddressV target) rs)) expr_vv_res_ok ee'` by
    (drule_all gas_admissible_bind_tail >> simp[]) >>
  `exprs_case nocalls ctx func cenv cx (DROP (LENGTH ats) rest)` by
    (qpat_assum `extrequest_results_success _ _ _ _ _` mp_tac >>
     simp[NoAsms, exprExtRequestUnreadCpsTheory.extrequest_results_success_def] >> strip_tac >> metis_tac[]) >>
  `expr_sim_inv cenv cx env ee'` by
    (qpat_assum `extrequest_results_success _ _ _ _ _` mp_tac >>
     simp[NoAsms, exprExtRequestUnreadCpsTheory.extrequest_results_success_def] >> strip_tac >>
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
  irule extcall_protframe_kwargs_cps >>
  first_assum (irule_at (Pat `compile_ext_call_kwargs _ _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `exprs_case _ _ _ _ _ _`)) >>
  qexistsl [`prot`, `arg_vvs`, `rs`, `TAKE (LENGTH ats) rest`, `env`, `M`] >>
  `ee' with gas_obs := [] = ee'` by simp[evaluation_state_component_equality] >>
  simp[] >>
  conj_tac >- (fs[] >> metis_tac[EVERY_DROP]) >>
  conj_tac >- (asm "raw_frame" ACCEPT_TAC) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac
  >- (reverse conj_tac >- metis_tac[] >>
      rpt strip_tac >> irule extrequest_kwargs_reach_pre >> simp[] >>
      conj_tac >- metis_tac[EVERY_DROP] >> qexists `ee'` >> simp[]) >>
  rpt gen_tac >> strip_tac >> suspend "kwargs_landing"
QED

Resume extcall_protframe_operand_cps[kwargs_landing]:
  `ci_mono s1 s2` by
    (qpat_assum `compile_multi_vvs _ _ _ _ = _` mp_tac >>
     mp_tac (Q.ISPEC `compile_expr` ci_mono_compile_multi_vvs) >>
     simp[cj 1 compile_expr_ci_mono] >> metis_tac[SND]) >>
  qpat_assum `extrequest_kwargs_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SRULE [exprExtRequestKwargsTheory.extrequest_kwargs_post_def]) >>
  `!x g y a b c.
     (wb_frame cenv (x with gas_obs := g) y a b c <=> wb_frame cenv x y a b c) /\
     (wb_frame cenv y (x with gas_obs := g) a b c <=> wb_frame cenv y x a b c)` by
    simp[wb_frame_def, locals_kept_def, popped_kept_def] >>
  pop_assum (fn th => RULE_ASSUM_TAC (SRULE [th])) >>
  `!x y a b c. wb_frame cenv x y a b c ==> MAP FDOM x.scopes = MAP FDOM y.scopes` by
    simp[wb_frame_def, locals_kept_def] >>
  `wb_frame cenv es ee' sa s0 t'` by
    (irule wb_frame_trans >>
     qpat_assum `wb_frame _ _ _ _ s0 t` (irule_at Any) >>
     qpat_assum `wb_frame _ _ _ s1 t t'` (irule_at Any) >>
     metis_tac[]) >>
  `sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `wb_frame cenv es ee'' sa s0 t''` by
    (irule wb_frame_trans >>
     qpat_assum `wb_frame _ _ _ sa s0 t'` (irule_at Any) >>
     qpat_assum `wb_frame _ _ _ s2 t' t''` (irule_at Any) >>
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
  asm "finish" irule >> simp[] >>
  metis_tac[]
QED

Finalise extcall_protframe_operand_cps
