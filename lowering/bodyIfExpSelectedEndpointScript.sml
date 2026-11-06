Theory bodyIfExpSelectedEndpoint
Ancestors
  bodyIfExpArmOutcome stmtReasonVvMemory exprSimMemorySource
  vyperStatePreservation vyperInterpreter vyperState exprSimDefs
  exprSimMemDefs exprSimProps loweringPosts gasSummary fragGasMode
  fragGasPathMem gasContext context exprLowering compileEnv

Theorem ifexp_conditional_read_cases:
  !cx raw st res st'.
    (do r <- conditional_result cx raw; read_result cx r od) st = (res,st') ==>
    read_result cx raw st = (res,st') \/
    ?m. conditional_result cx raw st = (INR (Error (TypeError m)),st') /\
        res = INR (Error (TypeError m))
Proof
  rpt gen_tac >> Cases_on `raw` >>
  simp[conditional_result_def, read_result_def, bind_def, return_def, raise_def] >>
  rename1 `place_type_value cx p st` >>
  Cases_on `place_type_value cx p st` >> rename1 `place_type_value cx p st = (pr,pst)` >>
  drule place_type_value_state >> strip_tac >> gvs[] >>
  Cases_on `pr` >> simp[]
  >- (IF_CASES_TAC >> simp[read_result_def, bind_def, return_def] >>
      Cases_on `read_place cx p pst` >> rename1 `read_place cx p pst = (rr,ss)` >>
      Cases_on `rr` >> simp[read_result_def, return_def]) >>
  Cases_on `p` >>
  gvs[place_type_value_def, get_scopes_def, get_immutables_def,
      get_address_immutables_def, bind_def, return_def, lift_option_type_def,
      raise_def, AllCaseEqs()] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def])
QED

Theorem ifexp_arm_conditional_read[local]:
  read_result cx raw ee = (INL v,ee) /\
  conditional_result cx raw ee = (res,ss) /\ expr_vv_res_ok res ==>
  ?tv. res = INL tv /\ ss = ee /\
       read_result cx tv ee = (INL v,ee)
Proof
  rpt strip_tac >>
  Cases_on `(do r <- conditional_result cx raw; read_result cx r od) ee` >>
  drule ifexp_conditional_read_cases >> strip_tac >>
  imp_res_tac vyperStatePreservationTheory.conditional_result_state >>
  gvs[expr_vv_res_ok_def, bind_def, AllCaseEqs()]
QED

Theorem ifexp_arm_conditional_gas_obs[local]:
  conditional_result cx raw ee = (INL tv,ee) ==>
  !tail. conditional_result cx raw (ee with gas_obs := tail) =
    (INL tv,ee with gas_obs := tail)
Proof
  Cases_on `raw`
  >- simp[conditional_result_def, return_def]
  >- (simp[conditional_result_def, bind_def] >>
      Cases_on `place_type_value cx p ee` >>
      rename1 `place_type_value cx p ee = (pr,pst)` >>
      drule place_type_value_state >> strip_tac >> gvs[] >>
      `!tail. place_type_value cx p (ee with gas_obs := tail) =
         (pr,ee with gas_obs := tail)` by
        (Cases_on `p` >>
         gvs[place_type_value_def, get_scopes_def, get_immutables_def,
             get_address_immutables_def, bind_def, return_def,
             lift_option_type_def, raise_def, AllCaseEqs()] >>
         rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def])) >>
      simp[] >> Cases_on `pr` >> simp[] >>
      IF_CASES_TAC >> simp[return_def] >>
      Cases_on `read_place cx p ee` >>
      rename1 `read_place cx p ee = (rr,ss)` >>
      Cases_on `rr` >> simp[return_def] >> rpt strip_tac >>
      gvs[bind_def, return_def] >>
      rename1 `read_place cx p ee = (INL v,ee)` >>
      `read_result cx (PlaceR p) ee = (INL v,ee)` by
        simp[read_result_def] >>
      drule exprSimMemorySourceTheory.read_result_gas_obs >> simp[read_result_def]) >>
  simp[conditional_result_def, raise_def]
QED

Theorem ifexp_marked_conditional_of_read_mem:
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0) marks (INL raw) ee (OK s) /\
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es /\
  gas_marked_exec T (ctx,func) (read_result cx raw)
    (ee with gas_obs := [],s) [] (INL v) (ee with gas_obs := []) (OK u) ==>
  ?tv. gas_marked_exec T (ctx,func) (conditional_result cx raw)
    (ee with gas_obs := [],s) [] (INL tv) (ee with gas_obs := []) (OK u) /\
    read_result cx tv (ee with gas_obs := []) = (INL v,ee with gas_obs := [])
Proof
  strip_tac >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL raw,ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `read_result cx raw (ee with gas_obs := []) = (INL v,ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  Cases_on `conditional_result cx raw (ee with gas_obs := [])` >>
  rename1 `_ = (cr,cs)` >>
  `expr_vv_res_ok cr` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def] >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     simp[bind_def]) >>
  drule_all ifexp_arm_conditional_read >> strip_tac >> gvs[] >>
  qexists_tac `tv` >> simp[] >>
  qpat_x_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >> simp[] >>
  drule ifexp_arm_conditional_gas_obs >> simp[]
QED

Theorem ifexp_selected_marked_endpoint_mem:
  expr_type e = t /\ ~is_word_type t /\
  (~same_memory_layout ce (lowered_value_type ce e) t ==> is_bytestring_type t) /\
  compile_ifexp_arm ce t (lowered_value_type ce e) vv sm = (op,sb) /\
  (!tv. evaluate_type (get_tenv cx) t = SOME tv ==>
     type_memory_bytes ce t = type_memory_size tv /\ type_memory_size tv < 2 ** 64) /\
  (!tv. same_memory_layout ce (lowered_value_type ce e) t /\
     evaluate_type (get_tenv cx) t = SOME tv ==>
     ?avt. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME avt /\
       type_memory_size tv <= type_memory_size avt) /\
  (!gs v st. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
     (INL v,st) ==> ?tv. evaluate_type (get_tenv cx) t = SOME tv /\ value_has_type tv v) /\
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0) marks (INL raw) ee (OK s) /\
  vv_post ctx func ce cx e es sa sm s0 (ee with gas_obs := []) raw vv s /\
  vv_store_bound cx t (lowered_value_type ce e) (ee with gas_obs := []) raw vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?tv v u. gas_marked_exec T (ctx,func) (conditional_result cx raw)
      (ee with gas_obs := [],s) [] (INL tv) (ee with gas_obs := []) (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 (ee with gas_obs := []) v op u /\
    read_result cx tv (ee with gas_obs := []) = (INL v,ee with gas_obs := []) /\
    vv_store_bound cx t t (ee with gas_obs := []) tv
      (LocatedValue t (mk_ptr op LocMemory)) u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> drule vv_post_read_ok >> strip_tac >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL raw,ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `?tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ value_has_type tvt v` by
    (qpat_x_assum `!gs v st. _` irule >>
     qexistsl_tac [`gas_explicit marks s0.vs_gas_readings`,`ee with gas_obs := []`] >>
     simp[bind_def]) >>
  drule ifexp_selected_arm_path_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  `gas_marked_exec T (ctx,func) (read_result cx raw)
    (ee with gas_obs := [],s) [] (INL v) (ee with gas_obs := []) (OK u)` by
    (simp[gas_marked_exec_def, gas_marked_path_def] >>
     drule exprSimMemorySourceTheory.read_result_gas_obs >> simp[]) >>
  drule_all ifexp_marked_conditional_of_read_mem >> strip_tac >>
  qexistsl_tac [`tv`,`v`,`u`] >> simp[] >>
  fs[vv_store_bound_def] >> metis_tac[]
QED
