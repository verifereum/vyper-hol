(* Normalize selected conditional arms on their actual F-mode witness. *)
Theory bodyIntCallPostProvenanceConditionalArm
Ancestors
  bodyIntCallPostProvenanceConditional bodyIntCallPostProvenanceArmIdentity
  bodyIntCallPostProvenanceArmCopy bodyIntCallProducerInterface
  bodyIntCallPostProvenanceTypedCases
  exprSimIfExp exprSimIfExpWidenedAdapter bodyPtrIfExpLayoutRefl
  exprSimUnwrapProps exprSimProps exprLowering exprLoweringProps
  bodyIntCallCompilerTags bodyIntCallMemoryView exprSimSubscriptArrayCompose
  gasSummary fragGasMode fragGasPath gasContext exprSimUnwrap
  gasOutcome gasSummaryCompose gasExemptCert exprSimDefs fragExec
  loweringPosts context compileEnv loweringStateRelDefs
  vyperAST vyperState venomState words finite_map

Theorem intcall_ifexp_free_memory:
  vv_at ce cx ty sa sb ee tv (LocatedValue ty (mk_ptr op LocMemory)) s /\
  (!tvt. evaluate_type (get_tenv cx) ty = SOME tvt ==> dynarray_free tvt) ==>
  intcall_vv_provenance ce cx ty sa sb ee tv
    (LocatedValue ty (mk_ptr op LocMemory)) s
Proof
  simp[vv_at_def, intcall_vv_provenance_def, mk_ptr_def] >>
  rpt strip_tac >>
  qpat_x_assum `!v tvt. _` (qspecl_then [`v`, `tvt`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `w` >> simp[] >> metis_tac[]
QED

Theorem intcall_ifexp_identity_vv_at[local]:
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  post_value_type ce e = ty /\ ~is_word_type ty /\
  ((?a. vv = StackValue a op) \/
   (?a p. vv = LocatedValue a p /\ p.ptr_location = LocMemory /\
          ~is_word_type a /\ op = p.ptr_operand)) /\
  read_result cx raw ee = (INL v,ee) /\
  conditional_result cx raw ee = (INL result,ee) /\
  read_result cx result ee = (INL v,ee) ==>
  vv_at ce cx ty sa sm ee result (LocatedValue ty (mk_ptr op LocMemory)) s
Proof
  strip_tac >>
  `result = raw \/ result = Value v` by
    (drule ifexp_conditional_result_shape >> strip_tac >>
     gvs[read_result_def, return_def]) >>
  irule ifexp_vv_at_conditional >> qexistsl_tac [`raw`, `v`] >> simp[] >>
  gvs[vv_post_def, vv_at_def, mk_ptr_def, expr_val_at_def,
      local_place_at_def]
QED

Theorem intcall_ifexp_nonmemory_vv_at[local]:
  vv_post ctx func ce cx e es sa sm s0 ee raw (LocatedValue ty p) s /\
  post_value_type ce e = ty /\ p.ptr_location <> LocMemory /\
  expr_post ctx func ce cx e es sa sb s0 ee v op u /\
  read_result cx result ee = (INL v,ee) /\
  conditional_result cx raw ee = (INL result,ee) /\
  ~is_word_type ty ==>
  vv_at ce cx ty sa sb ee result (LocatedValue ty (mk_ptr op LocMemory)) u
Proof
  strip_tac >>
  `!id path. raw <> PlaceR (MemoryPlace id path)` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def, vv_at_def]) >>
  `!id path. result <> PlaceR (MemoryPlace id path)` by
    (drule ifexp_conditional_result_shape >> strip_tac >> gvs[]) >>
  irule ifexp_vv_at_of_val_at >> simp[] >> gvs[expr_post_def]
QED

Theorem intcall_ifexp_dynamic_continuation[local]:
  post_value_type ce e = expr_type e /\
  lowered_value_type ce e = expr_type e /\ ~is_word_type (expr_type e) /\
  ~is_bytestring_type (expr_type e) /\
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  intcall_vv_provenance ce cx (expr_type e) sa sm ee raw vv s /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sm = (op,sb) /\
  read_result cx raw ee = (INL v,ee) /\
  read_result cx result ee = (INL v,ee) /\
  conditional_result cx raw ee = (INL result,ee) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_exec F (ctx,func) (conditional_result cx raw)
      (ee,s) [] (INL result) ee (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    vv_at ce cx (expr_type e) sa sb ee result
      (LocatedValue (expr_type e) (mk_ptr op LocMemory)) u /\
    intcall_vv_provenance ce cx (expr_type e) sa sb ee result
      (LocatedValue (expr_type e) (mk_ptr op LocMemory)) u
Proof
  strip_tac >> Cases_on `vv`
  >- suspend "stack" >>
  rename1 `LocatedValue ann p` >> Cases_on `p.ptr_location = LocMemory`
  >- suspend "memory" >>
  suspend "copy"
QED
Resume intcall_ifexp_dynamic_continuation[stack]:
  rename1 `StackValue ann src` >>
  drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`)
    ifexp_arm_identity_continuation >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`v`, `result`, `src`] mp_tac) >>
  simp[NoAsms] >>
  asm_rewrite_tac[same_memory_layout_reflexive] >> strip_tac >>
  qpat_x_assum `sb = sm` SUBST_ALL_TAC >>
  qpat_x_assum `op = src` SUBST_ALL_TAC >>
  qexists_tac `s` >> simp[] >>
  irule intcall_ifexp_identity_vv_at >>
  goal_assum (drule_at Any) >> simp[NoAsms] >> asm_rewrite_tac[] >>
  metis_tac[]
QED
Resume intcall_ifexp_dynamic_continuation[memory]:
  `~is_word_type ann` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def, vv_holds_def]) >>
  drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`)
    ifexp_arm_identity_continuation >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`v`, `result`, `p.ptr_operand`] mp_tac) >>
  simp[NoAsms] >>
  asm_rewrite_tac[same_memory_layout_reflexive] >>
  strip_tac >>
  qpat_x_assum `sb = sm` SUBST_ALL_TAC >>
  qpat_x_assum `op = p.ptr_operand` SUBST_ALL_TAC >>
  qexists_tac `s` >> simp[] >> irule intcall_ifexp_identity_vv_at >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
Resume intcall_ifexp_dynamic_continuation[copy]:
  `ann = expr_type e` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def, vv_holds_def]) >>
  qpat_x_assum `ann = expr_type e` SUBST_ALL_TAC >>
  drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`)
    ifexp_arm_copy_continuation >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `conditional_result _ _ _ = _`)) >>
  disch_then (qspecl_then [`v`, `tv`] mp_tac) >>
  (impl_tac >- (simp[same_memory_layout_reflexive] >> fs[vv_operand_def])) >>
  strip_tac >> qexists_tac `u` >> simp[] >>
  irule intcall_ifexp_nonmemory_vv_at >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED
Finalise intcall_ifexp_dynamic_continuation

Theorem intcall_ifexp_arm_marked_suffix:
  post_value_type ce e = expr_type e /\ well_typed_expr env e /\ ~expr_has_effect e /\
  gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0) marks (INL raw) ee (OK s) /\
  vv_post ctx func ce cx e es sa sm s0 (ee with gas_obs := []) raw vv s /\
  intcall_vv_provenance ce cx (expr_type e) sa sm (ee with gas_obs := []) raw vv s /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sm = (op,sb) /\
  (~is_word_type (expr_type e) ==>
    lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
      arg_type_fits (lowered_value_type ce e) (expr_type e) \/
    same_memory_layout ce (lowered_value_type ce e) (expr_type e)) /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
      ~is_word_type (expr_type e) ==>
      type_memory_bytes ce (expr_type e) = type_memory_size tv /\
      type_memory_size tv < 2 ** 64) /\
  (!gs v es2. ~is_word_type (expr_type e) /\
    (do r <- eval_expr cx e; read_result cx r od) (es with gas_obs := gs) = (INL v,es2) ==>
    ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v) /\
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?tv v q. gas_marked_exec F (ctx,func) (conditional_result cx raw)
      (ee with gas_obs := [],s) [] (INL tv) (ee with gas_obs := []) (OK q) /\
    read_result cx tv (ee with gas_obs := []) = (INL v,ee with gas_obs := []) /\
    expr_post ctx func ce cx e es sa sb s0 (ee with gas_obs := []) v op q /\
    q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (~is_word_type (expr_type e) ==>
     vv_at ce cx (expr_type e) sa sb (ee with gas_obs := []) tv
       (LocatedValue (expr_type e) (mk_ptr op LocMemory)) q /\
     intcall_vv_provenance ce cx (expr_type e) sa sb (ee with gas_obs := []) tv
       (LocatedValue (expr_type e) (mk_ptr op LocMemory)) q)
Proof
  strip_tac >>
  Cases_on `!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==> dynarray_free tvt`
  >- suspend "free" >>
  `?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\ ~dynarray_free tvt` by
    metis_tac[] >>
  `lowered_value_type ce e = expr_type e` by
    (irule intcall_dynamic_lowered_type >> metis_tac[]) >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    suspend "types" >>
  suspend "reads"
QED
Resume intcall_ifexp_arm_marked_suffix[free]:
  drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`) ifexp_arm_marked_suffix >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexistsl_tac [`tv`, `v`, `q`] >> simp[] >> strip_tac >>
  irule intcall_ifexp_free_memory >> fs[vv_at_source_gas]
QED
Resume intcall_ifexp_arm_marked_suffix[types]:
  Cases_on `expr_type e` >>
  gvs[is_word_type_def, is_bytestring_type_def] >>
  metis_tac[evaluate_base_dynarray_free, evaluate_flag_dynarray_free]
QED
Resume intcall_ifexp_arm_marked_suffix[reads]:
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL raw,ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `~s.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `MAP FDOM es.scopes = MAP FDOM (ee with gas_obs := []).scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  Cases_on `read_result cx raw (ee with gas_obs := [])` >>
  rename1 `_ = (rr,ss)` >>
  `ss = ee with gas_obs := []` by metis_tac[read_result_state] >> gvs[] >>
  reverse (Cases_on `rr`) >- metis_tac[vv_post_failed_read] >>
  rename1 `read_result cx raw _ = (INL v,_)` >>
  Cases_on `conditional_result cx raw (ee with gas_obs := [])` >>
  rename1 `_ = (cr,cs)` >>
  `expr_vv_res_ok cr` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def] >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     simp[bind_def]) >>
  drule_all ifexp_arm_conditional_read >> strip_tac >> gvs[] >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    intcall_ifexp_dynamic_continuation >>
  simp[] >> strip_tac >>
  qexistsl_tac [`tv`, `v`, `u`] >> simp[]
QED
Finalise intcall_ifexp_arm_marked_suffix

Theorem intcall_ifexp_arm_outcome:
  !ctx func cenv cx ty e es1 sa sm sb vv op u.
    post_value_type cenv e = expr_type e /\ well_typed_expr env e /\ ~expr_has_effect e /\
    (!sa sm vv u.
      compile_expr cenv ty e sa = (vv,sm) /\
      fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      gas_admissible (eval_expr cx e) expr_vv_res_ok es1 /\
      stmt_state_rel ctx func cenv cx es1 u /\ ~u.vs_halted /\
      u.vs_current_bb = sa.cs_current_bb /\
      u.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es1,u)
        (\res ee t. ?tv. res = INL tv /\
          vv_post ctx func cenv cx e es1 sa sm u ee tv vv t /\
          t.vs_current_bb = sm.cs_current_bb /\
          t.vs_inst_idx = LENGTH sm.cs_current_insts /\
          intcall_vv_provenance cenv cx (expr_type e) sa sm ee tv vv t)
        (\res ee r. expr_exit res r)) /\
    compile_expr cenv ty e sa = (vv, sm) /\
    compile_ifexp_arm cenv (expr_type e) (lowered_value_type cenv e) vv sm = (op, sb) /\
    (~is_word_type (expr_type e) ==>
      lowered_value_type cenv e = expr_type e \/
      is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type cenv e) /\
      arg_type_fits (lowered_value_type cenv e) (expr_type e) \/
      same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
       ~is_word_type (expr_type e) ==>
       type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
       type_memory_size tvt < 2 ** 64) /\
    (!gs v es2. ~is_word_type (expr_type e) /\
       (do r <- eval_expr cx e; read_result cx r od)
         (es1 with gas_obs := gs) = (INL v, es2) ==>
       ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\ value_has_type tvt v) /\
    gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es1 /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es1 u /\ ~u.vs_halted /\
    u.vs_current_bb = sa.cs_current_bb /\ u.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (bind (eval_expr cx e) (conditional_result cx)) (es1,u)
      (\res ee t. ?tv v. res = INL tv /\ read_result cx tv ee = (INL v,ee) /\
        expr_post ctx func cenv cx e es1 sa sb u ee v op t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (~is_word_type (expr_type e) ==>
          vv_at cenv cx (expr_type e) sa sb ee tv
            (LocatedValue (expr_type e) (mk_ptr op LocMemory)) t /\
          intcall_vv_provenance cenv cx (expr_type e) sa sb ee tv
            (LocatedValue (expr_type e) (mk_ptr op LocMemory)) t))
      (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  `ci_mono sm sb` by
    (qspecl_then [`cenv`, `expr_type e`, `lowered_value_type cenv e`, `vv`, `sm`]
      mp_tac ci_mono_compile_ifexp_arm >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (drule (cj 1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es1` by
    metis_tac[ifexp_arm_raw_admissible] >>
  qpat_x_assum `!sa sm vv u. _` (qspecl_then [`sa`, `sm`, `vv`, `u`] mp_tac) >>
  simp[] >> rewrite_tac[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> gvs[gas_summary_at_def]
      >- suspend "success" >> suspend "exception") >>
  suspend "exempt"
QED
Resume intcall_ifexp_arm_outcome[success]:
  drule (SRULE [] intcall_ifexp_arm_marked_suffix) >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`sb`, `op`, `env`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexistsl_tac [`INL tv'`, `es_end with gas_obs := []`, `OK q`] >> simp[] >>
  `marks = marks ++ []` by simp[] >> pop_assum SUBST1_TAC >>
  irule gas_marked_exec_bind_normal >> goal_assum drule >> simp[]
QED
Resume intcall_ifexp_arm_outcome[exception]:
  Cases_on `res`
  >- (Cases_on `r` >> gvs[expr_exit_def]) >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >>
  irule gas_marked_exec_bind_exception >> goal_assum drule
QED
Resume intcall_ifexp_arm_outcome[exempt]:
  disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  once_rewrite_tac[GSYM ignore_bind_def] >>
  irule gas_exempt_cert_error_result >> simp[ignore_bind_def]
QED
Finalise intcall_ifexp_arm_outcome
