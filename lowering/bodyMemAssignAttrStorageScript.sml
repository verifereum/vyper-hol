(* Memory case of the body induction, assignment to a base target
   (bodyMemAssign's dispatch): a word field of a storage or transient struct (S1's body_assign_attr_storage). *)
Theory bodyMemAssignAttrStorage
Ancestors
  bodyMemoryPreds bodyMemAugAssignAttrStorage vyperInterpreter vyperState
  vyperStorageBackend loweringPosts exprSimProps compileEnv venomExecSemantics venomState
  exprSimMemUnwrap exprSimVVFrame bodyMemEmitOpFrame context emitHelperProps
  exprLoweringProps exprSimMemDefs exprBopSimProps freshWrites
  gasOutcome gasSummary gasSummaryCompose fragGasMode fragGasPath
  exprSimDefs exprSimMemorySource exprSimUnwrapProps list rich_list
Libs
  monadsyntax

Theorem eval_assign_attr_toplevel_action_mem_src[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
  struct_field_slot fs fld = SOME (off, ftv) ==>
  eval_stmt cx
    (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e) =
  bind (bind (eval_expr cx e) (read_result cx))
    (write_storage_slot cx tr (n2w slot + n2w off) ftv)
Proof
  strip_tac >>
  `!es. eval_target_place cx
    (AttributeTarget (TopLevelNameTarget (src,id)) fld) es =
    (INL (StoragePlace tr (n2w slot + n2w off) ftv), es)` by
    (gen_tac >> irule (cj 1 eval_target_place_attr_toplevel_field_mem_src) >>
     goal_assum (drule_at Any) >> simp[]) >>
  simp[Once evaluate_def, FUN_EQ_THM, bind_def] >> qx_gen_tac `st` >>
  Cases_on `eval_expr cx e st` >> Cases_on `q` >> simp[] >>
  simp[write_place_def, bind_def] >>
  Cases_on `read_result cx x' r` >> Cases_on `q` >> simp[]
QED

Theorem vv_at_start_var_mem_src[local]:
  vv_at ce cx ty (sa with cs_next_var := n) sb es tv vv s <=>
  vv_at ce cx ty sa sb es tv vv s
Proof
  Cases_on `vv` >> simp[vv_at_def, expr_val_at_def]
QED

Theorem vv_post_rebase_mem_src[local]:
  vv_post ctx func ce cx e es sa sm s0 ee tv vv s ==>
  vv_post ctx func ce cx e ee (sa with cs_next_var := sm.cs_next_var)
    sm s ee tv vv s
Proof
  simp[vv_post_def, vv_at_start_var_mem_src, locals_kept_refl]
QED

Theorem expr_post_rebased_operand_mem_src[local]:
  expr_post ctx func ce cx e ee (sa with cs_next_var := sm.cs_next_var)
    sb s ee v op u /\
  (?x. dst = Var x /\ not_fresh_at sm x) /\
  eval_operand dst s = SOME w ==>
  eval_operand dst u = SOME w
Proof
  strip_tac >> gvs[eval_operand_def] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def] >> strip_tac >>
  first_x_assum irule >> gvs[not_fresh_at_def]
QED

Theorem unwrap_value_rebased_read_mem_src[local]:
  unwrap_value cenv vv sm = (op,sb) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  is_word_type (expr_type e) /\
  (?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (?x. dst = Var x /\ not_fresh_at sm x) /\
  eval_operand dst s = SOME w ==>
  ?v u. gas_marked_exec T (ctx,func) (read_result cx tv) (ee,s)
          [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e ee (sa with cs_next_var := sm.cs_next_var)
      sb s ee v op u /\
    expr_store_bound cx (expr_type e) v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    eval_operand dst u = SOME w
Proof
  strip_tac >>
  drule vv_post_rebase_mem_src >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `local_ptrs_reserved cenv (sa with cs_next_var := sm.cs_next_var)` by
    (qpat_x_assum `local_ptrs_reserved cenv sm` mp_tac >>
     simp_tac (srw_ss()) [local_ptrs_reserved_def, not_fresh_at_def] >>
     metis_tac[]) >>
  qpat_x_assum `vv_post _ _ _ _ _ es _ _ _ _ _ _ _` kall_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_marked_read_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`v`, `u`] >> simp[] >>
  irule expr_post_rebased_operand_mem_src >> goal_assum (drule_at Any) >> gvs[]
QED

Theorem expr_post_rebased_compose_mem_src[local]:
  vv_post ctx func ce cx e es sa sm s0 ee tv vv s /\
  local_ptrs_reserved ce sa /\ local_ptrs_rel func ce es.scopes s0 /\
  sa.cs_next_var <= sm.cs_next_var /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  expr_post ctx func ce cx e ee (sa with cs_next_var := sm.cs_next_var)
    sb s ee v op u ==>
  expr_post ctx func ce cx e es sa sb s0 ee v op u
Proof
  strip_tac >>
  `!n b sz. local_region ce ee.scopes s n b sz ==>
             local_region ce es.scopes s0 n b sz` by
    (rpt strip_tac >> irule local_region_frame >> conj_tac
     >- (qexists_tac `func` >> simp[]) >>
     qexistsl_tac [`sa`, `ee.scopes`, `s`] >> simp[] >>
     qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def]) >>
  `locals_kept ce es s0 u` by
    (irule locals_kept_trans >> goal_assum (drule_at Any) >>
     qexistsl_tac [`sa`, `s`] >>
     qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def, expr_post_def] >> metis_tac[]) >>
  gvs[vv_post_def, expr_post_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at (sa with cs_next_var := sm.cs_next_var) x` by
        (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      first_x_assum irule >> simp[] >> metis_tac[])
  >- metis_tac[] >>
  rpt strip_tac >>
  `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
  `mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz s.vs_memory` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem vv_post_emit_cursor_mem_src[local]:
  vv_post ctx func ce cx e es sa sm s0 ee tv vv s /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\
  sm.cs_next_id <= sn.cs_next_id /\ ~not_fresh_at sm x /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) ==>
  vv_post ctx func ce cx e es sa sn s0 ee tv vv
    (update_var x w s with vs_inst_idx := n)
Proof
  simp[ vv_post_inst_idx] >> metis_tac[vv_post_update_var]
QED

Theorem vv_store_bound_frame_mem_src[local]:
  vv_store_bound cx ty lt es tv vv s /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  s.vs_alloca_next <= t.vs_alloca_next ==>
  vv_store_bound cx ty lt es tv vv t
Proof
  Cases_on `vv` >> simp[vv_operand_def, vv_store_bound_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem vv_post_add_path_mem_src[local]:
  emit_op ADD [Lit kb; Lit ko] sm = (dst,sn) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\
  vv_post ctx func ce cx e es sa sm s0 ee tv vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee tv vv s /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    vv_post ctx func ce cx e es sa sn s0 ee tv vv t /\
    vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee tv vv t /\
    eval_operand dst t = SOME (kb + ko) /\
    (?x. dst = Var x /\ not_fresh_at sn x) /\
    alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts
Proof
  strip_tac >>
  `local_ptrs_reserved ce sm` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `stmt_state_rel ctx func ce cx ee s` by fs[vv_post_def] >>
  `step_inst_base
     (mk_inst sm.cs_next_id ADD [Lit kb; Lit ko]
       [STRING #"%" (toString sm.cs_next_var)]) s =
     OK (update_var (STRING #"%" (toString sm.cs_next_var)) (kb + ko) s)` by
    simp[step_inst_base_def, venomInstTheory.mk_inst_def, exec_pure2_def,
         eval_operand_def, wordsTheory.WORD_ADD_COMM] >>
  drule_at (Pat `emit_op _ _ _ = _`) emit_op_word_path_frame_mem >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (qspec_then `kb + ko` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (gvs[] >> irule vv_post_update_var >>
      conj_tac >- simp[] >> qexists_tac `sm` >>
      drule emitted_insts_emit_op >> strip_tac >>
      simp[] >> simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj]) >>
  irule vv_store_bound_frame_mem_src >> goal_assum (drule_at Any) >>
  simp[] >> gvs[] >>
  irule literal_operand_frame >>
  reverse conj_tac >- simp[update_var_def] >>
  qexists_tac `sm` >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED

Theorem vv_post_add_read_mem_src[local]:
  emit_op ADD [Lit kb; Lit ko] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,sb) /\
  fn_has_code sm sn func /\ fn_has_code sn sb func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  local_ptrs_rel func ce es.scopes s0 /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\ ee.gas_obs = [] /\
  vv_post ctx func ce cx e es sa sm s0 ee tv vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee tv vv s /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) /\
  is_word_type (expr_type e) /\
  (?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. gas_marked_exec T (ctx,func) (read_result cx tv) (ee,s)
          [] (INL v) ee (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op u /\
    expr_store_bound cx (expr_type e) v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    eval_operand dst u = SOME (kb + ko)
Proof
  strip_tac >>
  drule_all vv_post_add_path_mem_src >> strip_tac >>
  `sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sn z` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `sm` >> simp[]) >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_rebased_read_mem_src >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ sn _ _ _ _ _`)) >>
  disch_then (qspecl_then [`kb + ko`, `dst`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  strip_tac >> qexistsl_tac [`v`, `u`] >> simp[] >> conj_tac
  >- (irule gas_marked_exec_zero_prefix_mem_src >>
      goal_assum (drule_at Any) >>
      `ee with gas_obs := [] = ee` by
        simp[vyperStateTheory.evaluation_state_component_equality] >> simp[]) >>
  irule expr_post_rebased_compose_mem_src >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem compile_expr_add_read_outcome_mem_src[local]:
  expr_vv_sim_mem ctx func ce cx ty e es /\
  compile_expr ce ty e sa = (vv,sm) /\
  emit_op ADD [Lit kb; Lit ko] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  is_word_type (expr_type e) /\
  (?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee u. ?v. res = INL v /\
      expr_post ctx func ce cx e es sa sb s0 ee v op u /\
      expr_store_bound cx (expr_type e) v op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
      eval_operand dst u = SOME (kb + ko))
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (drule (cj 1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (drule (cj 1 compile_expr_grows) >> simp[]) >>
  `local_ptrs_rel func ce es.scopes s0` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_mem_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `s0`] mp_tac) >> simp[] >>
  rewrite_tac[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> gvs[gas_summary_at_def]
      >- (rename1 `vv_post _ _ _ _ _ _ _ _ _ _ tv vv t` >>
          `~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          `MAP FDOM es.scopes = MAP FDOM (es_end with gas_obs := []).scopes` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
             strip_tac >> first_x_assum (qspec_then `[]` assume_tac) >>
             drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >>
             simp[]) >>
          drule_at (Pat `emit_op _ _ _ = _`) vv_post_add_read_mem_src >>
          disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
          disch_then (qspecl_then [`sb`, `op`] mp_tac) >>
          impl_tac >- simp[] >> strip_tac >>
          qexistsl_tac [`INL v`, `es_end with gas_obs := []`, `OK u`] >>
          simp[] >>
          `marks = marks ++ []` by simp[] >> pop_assum SUBST1_TAC >>
          irule gas_marked_exec_bind_normal >> goal_assum drule >> simp[]) >>
      Cases_on `res`
      >- (Cases_on `r` >> gvs[expr_exit_def]) >>
      rename1 `expr_exit (INR exc) r` >>
      `expr_res_ok (INR exc : value + exception)` by
        (Cases_on `exc` >> Cases_on `r` >>
         gvs[expr_exit_def, expr_res_ok_def, AllCaseEqs()] >>
         Cases_on `e'` >> gvs[expr_exit_def, expr_res_ok_def]) >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >>
      simp[GSYM expr_exit_exception_transport] >>
      irule gas_marked_exec_bind_exception >> goal_assum drule) >>
  disj2_tac >> metis_tac[force_exempt_cert]
QED

Theorem body_assign_attr_storage_mem:
  !cx nsid fld e fty d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    supported_storage_field_write tops nsid fld /\
    type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
      SOME (Type fty) /\
    is_word_type fty ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e)) es
Proof
  cheat
QED
