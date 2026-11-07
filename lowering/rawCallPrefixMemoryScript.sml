(* Memory-mode address and bytes argument continuation for raw_call. *)
Theory rawCallPrefixMemory
Ancestors
  rawCallArgumentMemory exprSimRawCall exprSimHash bodyMemoryPreds exprSimMemDefs
  exprSimDefs exprSimProps exprLoweringProps loweringPosts bodySim
  compileEnv venomState vyperInterpreter vyperState fragExec exprSimSource exprSimHypsDefs

Theorem raw_call_addr_data_sim_mem:
  body_inv tops ctx cenv cx /\ body_exprs_mem_ok cx (a::d::kws) /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  fn_has_code sa s2 func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!exc ee r. expr_exit (INR exc : value + exception) r ==> R (INR exc) ee r) /\
  (!gsA av esA tA gsD bs esD tD.
    bind (eval_expr cx a) (read_result cx) (es with gas_obs := gsA) = (INL av,esA) /\
    esA.gas_obs = [] /\
    expr_post ctx func cenv cx a es sa s1 s0 esA av addr tA /\
    bind (eval_expr cx d) (read_result cx) (esA with gas_obs := gsD) =
      (INL (BytesV bs),esD) /\ esD.gas_obs = [] /\
    expr_post ctx func cenv cx d esA s1 s2 tA esD (BytesV bs) data tD /\
    expr_store_bound cx (expr_type d) (BytesV bs) data tD /\
    tD.vs_current_bb = s2.cs_current_bb /\
    tD.vs_inst_idx = LENGTH s2.cs_current_insts /\
    alloca_history func tD /\ s0.vs_alloca_next <= tD.vs_alloca_next /\ ~tD.vs_halted /\
    expr_sim_inv cenv cx env esD /\ body_exprs_mem_ok cx kws ==>
    gas_outcome T (cx_tops cx) (ctx,func) (k av (BytesV bs)) (esD,tD) Q R) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx a) (read_result cx)) (\av.
     bind (bind (eval_expr cx d) (read_result cx)) (k av))) (es,s0) Q R
Proof
  strip_tac >> drule raw_call_pre_operands >> strip_tac >> gvs[] >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by
    metis_tac[ci_mono_lower_value_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `expr_body_pre cenv cx env a es` by
    (irule expr_body_pre_raw_call_arg >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _`
       (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
     fs[expr_body_pre_def]) >>
  `expr_sim_mem ctx func cenv cx (BaseT AddressT) a es` by
    (fs[body_exprs_mem_ok_def] >> metis_tac[body_expr_mem_ok_def]) >>
  `gas_admissible (bind (eval_expr cx a) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  irule raw_call_mem_value_bind >>
  qpat_assum `lower_value _ _ _ a sa = _` (irule_at Any) >> simp[] >>
  rpt strip_tac >> suspend "data"
QED

Resume raw_call_addr_data_sim_mem[data]:
  `expr_body_pre cenv cx env a (es with gas_obs := gs)` by simp[] >>
  `expr_sim_inv cenv cx env ee` by
    (irule (cj 1 expr_body_pre_base_result) >> goal_assum (drule_at Any) >>
     simp[ETA_THM] >> qexists_tac `INL v` >> fs[bind_def]) >>
  `expr_body_pre cenv cx env d ee` by
    (irule expr_body_pre_raw_call_arg >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _`
       (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  `body_exprs_mem_ok cx (d::kws)` by
    (qpat_x_assum `bind _ _ (es with gas_obs := gs) = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> strip_tac >>
     fs[body_exprs_mem_ok_def] >> metis_tac[]) >>
  `expr_sim_mem ctx func cenv cx (expr_type d) d ee` by
    (fs[body_exprs_mem_ok_def] >> metis_tac[body_expr_mem_ok_def]) >>
  `gas_admissible (bind (eval_expr cx d) (read_result cx)) expr_res_ok ee` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `stmt_state_rel ctx func cenv cx ee t` by fs[expr_post_def] >>
  `expr_sim_mem ctx func cenv cx (BaseT (BytesT (Dynamic n))) d ee` by metis_tac[] >>
  irule raw_call_mem_value_bind >>
  qpat_assum `lower_value _ _ _ d s1 = _` (irule_at Any) >> simp[] >>
  rpt strip_tac >> suspend "values"
QED

Resume raw_call_addr_data_sim_mem[values]:
  `expr_body_pre cenv cx env d (ee with gas_obs := gs')` by simp[] >>
  `expr_sim_inv cenv cx env ee'` by
    (irule (cj 1 expr_body_pre_base_result) >> goal_assum (drule_at Any) >>
     simp[] >> qexists_tac `INL v'` >> fs[bind_def]) >>
  `value_has_type (BaseTV (BytesT (Dynamic n))) v'` by
    (irule (cj 3 expr_body_pre_base_result) >> goal_assum (drule_at Any) >>
     simp[] >> qexists_tac `ee'` >> fs[bind_def]) >>
  `body_exprs_mem_ok cx kws` by
    (qpat_x_assum `bind _ _ (ee with gas_obs := gs') = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> strip_tac >>
     fs[body_exprs_mem_ok_def] >> metis_tac[]) >>
  Cases_on `v'` >> gvs[vyperTypingTheory.value_has_type_def] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`gs`,`gs'`] >> simp[] >> decide_tac
QED

Finalise raw_call_addr_data_sim_mem
