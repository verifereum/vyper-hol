Theory exprSimIfExpWidenedSelectedCounted
Ancestors
  exprSimIfExpWidenedArmCounted exprSimIfExpWidenedSource
  exprSimIfExpWidenedCounted exprSimUnwrap exprOperandVar
  exprSimDefs exprSimSubscriptMap gasSummary gasOutcome fragExec
  stmtReasonVvMemory exprSimIfExpWidenedAdapter gasContext
  fragGasPath vyperEvalExprPreservesScopesDom
  exprSimIfExpWidenedArm exprSimIfExpCompat exprSimUnwrapProps
  exprSimSource exprSimProps exprSimHyps exprSimHypsDefs exprLoweringProps
  exprLowering compileEnv loweringPosts vyperAST vyperState context fragGasMode

Theorem compile_selected_ifexp_post_path:
  (~expr_has_effect (IfExp (expr_type e) c a b) ==> ~expr_has_effect e) /\
  expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL tvv,ee) /\
  read_result cx tvv ee = (INL v,ee) /\
  compile_expr ce ty e sc = (vv,sa) /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sc /\ local_ptrs_reserved ce origin /\
  local_ptrs_reserved ce sa /\ local_ptrs_rel func ce es.scopes s0 /\
  origin.cs_next_var <= sa.cs_next_var /\ origin.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  vv_post ctx func ce cx e es origin sa s0 ee tvv vv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    type_memory_bytes ce (expr_type e) = type_memory_size tv /\
    type_memory_size tv < dimword (:256)) ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    expr_post ctx func ce cx (IfExp (expr_type e) c a b)
      es origin sb s0 ee v op q /\
    (~is_word_type (expr_type e) ==> vv_at ce cx (expr_type e) origin sb ee tvv
      (LocatedValue (expr_type e) (mk_ptr op LocMemory)) q) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  Cases_on `is_word_type (expr_type e) \/
    same_memory_layout ce (lowered_value_type ce e) (expr_type e)`
  >- (irule compile_nocopy_ifexp_post_path >> metis_tac[]) >>
  fs[] >> Cases_on `is_bytestring_type (expr_type e)`
  >- (irule compile_bytes_ifexp_post_path >> metis_tac[expr_has_effect_thm]) >>
  `lowered_value_type ce e <> expr_type e` by
    (strip_tac >> fs[same_memory_layout_def, punnable_reflexive]) >>
  `?ann fid args drv. e = Call ann (IntCall fid) args drv` by
    (drule expr_body_pre_var_types_well_formed >> disch_then assume_tac >>
     qspecl_then [`ce`, `e`, `env`] mp_tac ifexp_lowered_type_classify >>
     (impl_tac >- (gvs[expr_body_pre_def, expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >> metis_tac[])) >> metis_tac[]) >>
  `post_value_type ce e = lowered_value_type ce e /\
   type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e)` by
    (gvs[vyperASTTheory.expr_type_def] >>
     drule_all ifexp_intcall_copy_source >> simp[]) >>
  `~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e)` by
    (irule aggregate_widen_source >> metis_tac[]) >>
  `post_value_type ce e <> expr_type e` by metis_tac[] >>
  `(do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee)` by
    simp[ignore_bind_def, bind_def] >>
  `?src. expr_post ctx func ce cx e es origin sa s0 ee v src s /\
    (!st. unwrap_value ce vv st = (src,st)) /\
    (!x. src = Var x ==> not_fresh_at sa x)` by
    (qpat_x_assum `_ ==> ~expr_has_effect e` kall_tac >>
     drule_all compile_changed_physical_unwrap_shape >> strip_tac >>
     drule_all vv_post_read_result >> disch_then (fs o single) >>
     gvs[]
     >- (qexists_tac `op'` >>
         simp[unwrap_value_def, comp_return_def] >> conj_tac
         >- (irule expr_post_of_vv_post_stack >> metis_tac[vv_post_read_result]) >>
         metis_tac[cj 1 compiler_compile_var, vv_operand_def]) >>
     qexists_tac `p.ptr_operand` >>
     simp[unwrap_value_def, comp_return_def] >> conj_tac
     >- (irule expr_post_of_vv_post_memory >> metis_tac[vv_post_read_result]) >>
     metis_tac[cj 1 compiler_compile_var, vv_operand_def]) >>
  qpat_x_assum `e = Call _ _ _ _` kall_tac >>
  qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` mp_tac >>
  simp[compile_ifexp_arm_def, comp_bind_def] >>
  pairarg_tac >> simp[comp_bind_def] >>
  simp[compile_store_memory_def, comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> simp[comp_return_def] >> strip_tac >>
  gvs[] >> irule changed_aggregate_post_path >> metis_tac[expr_has_effect_thm]
QED

Theorem selected_ifexp_arm_outcome:
  (~expr_has_effect (IfExp (expr_type e) c a b) ==> ~expr_has_effect e) /\
  expr_body_pre ce cx env e es /\
  expr_vv_sim ctx func ce cx ty e es /\
  compile_expr ce ty e sc = (vv,sa) /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sa = (op,sb) /\
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es /\
  fn_has_code sc sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sc /\ local_ptrs_rel func ce es.scopes s0 /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sc.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sc.cs_current_insts /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    type_memory_bytes ce (expr_type e) = type_memory_size tv /\
    type_memory_size tv < dimword (:256)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (conditional_result cx)) (es,s0)
    (\res ee t. ?tv v. res = INL tv /\ read_result cx tv ee = (INL v,ee) /\
      expr_post ctx func ce cx (IfExp (expr_type e) c a b)
        es sc sb s0 ee v op t /\
      (~is_word_type (expr_type e) ==> vv_at ce cx (expr_type e) sc sb ee tv
        (LocatedValue (expr_type e) (mk_ptr op LocMemory)) t) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `cs_extends sc sa /\ sc.cs_next_var <= sa.cs_next_var /\
   sc.cs_next_id <= sa.cs_next_id` by metis_tac[compile_expr_extends] >>
  `cs_extends sa sb` by
    (mp_tac ci_mono_compile_ifexp_arm >>
     disch_then (qspecl_then [`ce`, `expr_type e`, `lowered_value_type ce e`, `vv`, `sa`] mp_tac) >>
     simp[ci_mono_def]) >>
  `fn_has_code sc sa func /\ fn_has_code sa sb func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[conditional_raw_admissible] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_def] >> disch_then drule_all >>
  strip_tac >> irule gas_outcome_bind_result_exec >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
  conj_tac >- (rpt gen_tac >> Cases_on `res` >> simp[]) >>
  reverse conj_tac >- (simp[] >> metis_tac[]) >>
  rpt gen_tac >> simp[] >> strip_tac >>
  `gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0) marks
    (INL v) (mid with gas_obs := []) (OK t)` by
    fs[gas_marked_exec_def] >>
  drule_all conditional_marked_read_success >> strip_tac >>
  gvs[] >>
  `expr_vv_res_ok (INL tv)` by
    (drule_all gas_marked_continuation_admissible >>
     simp[gas_admissible_def] >> disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  drule vv_post_read_ok >> strip_tac >>
  `read_result cx v (mid with gas_obs := []) = (INL v',mid with gas_obs := [])` by
    (drule_at (Pat `read_result _ _ _ = _`) conditional_readable_admissible >>
     disch_then (drule_at (Pat `conditional_result _ _ _ = _`)) >>
     simp[expr_vv_res_ok_def] >> metis_tac[]) >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL v,mid with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `local_ptrs_reserved ce sa` by metis_tac[local_ptrs_reserved_next_var] >>
  `~t.vs_halted` by
    (fs[gas_marked_exec_def, gas_marked_path_def] >> metis_tac[cj 1 gas_path_normal]) >>
  `vv_post ctx func ce cx e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)
    sc sa s0 (mid with gas_obs := []) v vv t` by
    (fs[vv_post_def, locals_kept_def, popped_kept_def] >> metis_tac[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  drule_at (Pat `eval_expr _ _ _ = _`) compile_selected_ifexp_post_path >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  simp[] >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`)) >>
  simp[] >>
  disch_then (qspecl_then [`env`, `c`, `b`, `a`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `expr_post ctx func ce cx (IfExp (expr_type e) c a b)
    es sc sb s0 (mid with gas_obs := []) v' op q` by
    (fs[expr_post_def, locals_kept_def, popped_kept_def] >> metis_tac[]) >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL tv`, `mid with gas_obs := []`, `OK q`] >>
  simp[gas_marked_exec_def] >>
  drule conditional_result_gas_obs >> simp[] >>
  rpt strip_tac >> irule exprSimIfExpWidenedProvenanceTheory.vv_at_conditional_result >>
  metis_tac[]
QED
