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
  stmtSimAssignAttrStorage stmtSimForced stmtSimDefs stmtSimProps
  accountsRelProps vyperStorageLayoutSafety bodyMemAssignTopWord
  exprSimTopLevelProps exprSimUnwrap exprLowering emitHelper
  vyperTypeSystem supportedTypes fragExec stmtSimAssignStorage bodyMemoryDefs
  bodySim bodyExprPreFacts bodyStorageMetadata vyperTypeEnv
  exprSimFieldLayout exprSimAttributeFields supportedStmtTraverse supportedStmts
  supportedExprs vyperTypeExprResult vyperTypeExprSoundness vyperTypeInvariants
  vyperLookup vyperTypeCallGraph supportedExprForms stmtSimAssignAttr
  exprSimSource exprSimHypsDefs gasContext vyperPlaceResultTyping
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
  `locals_kept ce es ee s0 u` by
    (irule locals_kept_trans >> goal_assum (drule_at Any) >>
     qexistsl_tac [`sa`, `s`] >>
     qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def, expr_post_def] >> metis_tac[]) >>
  gvs[vv_post_def, expr_post_def] >> rpt conj_tac
  >- (strip_tac >> irule expr_val_own_start_mono >>
      qexists_tac `sa with cs_next_var := sm.cs_next_var` >> simp[])
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

Theorem compile_assign_attr_storage_mem[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid), id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_var_type (src,id) = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld =
    SOME (fty,fsz) /\
  is_word_type fty /\ expr_type e = fty /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  struct_field_slot fs fld = SOME (off,ftv) /\
  evaluate_type (get_tenv cx) fty = SOME ftv /\
  struct_field_offset_slots
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld = off /\
  (!gs v ee. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gs) = (INL v,ee) ==> value_has_type ftv v) /\
  expr_vv_sim_mem ctx func cenv cx (expr_type e) e es ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e))
    (eval_stmt cx
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e)) es
Proof
  strip_tac >>
  `is_word_type (expr_type e)` by simp[] >>
  `type_slot_size ftv = 1` by metis_tac[word_type_slot_size] >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  `FLOOKUP cenv.ce_module_vars (src,id) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (irule toplevel_storage_ce_vars >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  drule_all assign_attr_storage_code_parts >> strip_tac >> gvs[] >>
  drule_all eval_assign_attr_toplevel_action_mem_src >>
  disch_then (qspec_then `e` (fn th =>
    RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th])) >>
  drule forced_then_admissible >> strip_tac >>
  qabbrev_tac `off = struct_field_offset_slots
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld` >>
  `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn su /\
   cs_extends su sb` by
    (drule (cj 1 compile_expr_grows) >> strip_tac >>
     qspecl_then [`cenv`, `vv`, `sn`] mp_tac ci_mono_unwrap_value >>
     simp[ci_mono_def] >> strip_tac >>
     simp[] >> metis_tac[cs_appends_emit_helpers, cs_appends_def]) >>
  `cs_extends sa sn /\ cs_extends sa su /\ cs_extends sm su /\
   cs_extends sm sb /\ cs_extends sn sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\
   fn_has_code sn su func /\ fn_has_code su sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `~block_is_terminated sb` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> Cases_on `su.cs_current_insts` >> Cases_on `tr` >>
     gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
         venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (drule (cj 1 compile_expr_grows) >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     qspecl_then [`cenv`, `vv`, `sn`] mp_tac ci_mono_unwrap_value >>
     simp[ci_mono_def] >> strip_tac >>
     drule emitted_insts_emit_void >> strip_tac >> decide_tac) >>
  irule forced_then_outcome >> conj_tac
  >- (rpt strip_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]) >>
  qexists_tac `\v ee t.
    expr_post ctx func cenv cx e es sa su s0 ee v op t /\
    expr_store_bound cx (expr_type e) v op t /\
    t.vs_current_bb = su.cs_current_bb /\
    t.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    eval_operand dst t = SOME (n2w slot + n2w off)` >>
  conj_tac >- suspend "store" >>
  BETA_TAC >> irule compile_expr_add_read_outcome_mem_src >>
  simp[] >>
  qexistsl_tac [`sm`, `sn`, `expr_type e`, `vv`] >> simp[]
QED

Resume compile_assign_attr_storage_mem[store]:
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `value_has_type ftv v` by metis_tac[] >>
  `encode_value ftv v = SOME [(0, typed_val_to_w256 ftv v)]` by
    (irule encode_value_word_typed >> metis_tac[]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `eval_operand op t = SOME (typed_val_to_w256 ftv v)` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `!u sto. storage_dead cx tr
    (update_storage (n2w slot + n2w off) u sto) = storage_dead cx tr sto` by
    (rpt gen_tac >> irule storage_dead_update_struct_word_field >>
     qexistsl_tac [`fld`, `fs`, `ftv`, `src`, `id`] >>
     simp[declared_storage_region_def]) >>
  Cases_on `write_storage_slot cx tr (n2w slot + n2w off) ftv v ee` >>
  rename1 `_ = (res,ee')` >>
  drule_all stmt_state_rel_write_storage_word >> strip_tac >> gvs[] >>
  `ee'.gas_obs = [] /\ ee'.scopes = ee.scopes` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     simp[write_storage_slot_eq] >> Cases_on `tr` >>
     Cases_on `cx.txn.is_static` >> simp[set_storage_def] >> strip_tac >> gvs[]) >>
  `ee' with gas_obs := [] = ee'` by
    simp[evaluation_state_component_equality] >>
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  drule_at (Pat `emit_void _ _ _ = _`) storage_store_op_path_mem >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `gas_marked_path T ctx func t 0 (OK u)` >>
  qexistsl_tac [`INL ()`, `ee'`, `OK u`] >>
  conj_tac >- fs[write_storage_slot_gas_obs] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disj1_tac >> simp[stmt_lands_def, cenv_top_ext_refl] >>
  irule return_buf_frame_frame >>
  qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[] >> metis_tac[]
QED

Finalise compile_assign_attr_storage_mem

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
  Cases_on `nsid` >> rename1 `TopLevelNameTarget (src,id)` >> rpt strip_tac >>
  `supported_expr tops e` by gvs[supported_stmt_def, supported_assignment_def] >>
  `!ts vis mut id ty init.
     MEM (VariableDecl vis mut id ty init) ts /\
     (mut = Storage \/ mut = Transient) ==>
     find_var_decl_by_name id ts <> NONE` by
    (Induct >> simp[] >> Cases >> rw[find_var_decl_by_name_def] >> metis_tac[]) >>
  `src = NONE /\ find_var_decl_by_name id tops <> NONE /\
   ?mut sid slot. MEM (VariableDecl Private mut id (StructT sid) slot) tops` by
    (qpat_x_assum `supported_storage_field_write _ _ _` mp_tac >>
     simp[supported_storage_field_write_def, supported_storage_fields_def] >>
     Cases_on `supported_variable_decl tops (src,id)` >> simp[] >>
     rename1 `SOME x` >> PairCases_on `x` >>
     drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
     Cases_on `x0` >> Cases_on `x1` >> Cases_on `x2` >> Cases_on `x3` >>
     simp[] >> metis_tac[]) >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)` by
    fs[body_inv_def] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  `?tgt_ty. type_place_target env (TopLevelNameTarget (NONE,id)) = SOME (Type tgt_ty) /\
    attribute_type env.type_defs tgt_ty fld = SOME fty` by
    gvs[type_place_target_AttributeTarget, AllCaseEqs()] >>
  `expr_type e = fty` by
    (qpat_x_assum `type_stmt _ _ _ = SOME _` mp_tac >>
     simp[type_stmt_def, atarget_accepts_def] >>
     metis_tac[type_widens_to_word]) >>
  gvs[type_place_target_TopLevelNameTarget]
  >- (qpat_x_assum `env_consistent _ _ _`
        (strip_assume_tac o REWRITE_RULE [env_consistent_def, env_context_consistent_def]) >>
      first_x_assum drule >> strip_tac >> gvs[]) >>
  drule_all env_consistent_toplevel_storage_static >> strip_tac >>
  drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  rename1 `find_var_decl_by_name id tops = SOME (StorageVarDecl tr _, _)` >>
  `tgt_ty = StructT sid` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >> drule_all build_maps_variable >> strip_tac >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld =
    SOME (expr_type e,fsz)` by metis_tac[attribute_type_struct_field] >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `lookup_var_slot_from_layout _ _ _ _ = SOME lslot` >>
  rename1 `evaluate_type _ (StructT sid) = SOME stv` >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_type >> strip_tac >>
  drule struct_field_slot_exists >> strip_tac >>
  rename1 `struct_field_slot fs fld = SOME (off,ftv)` >>
  drule_all struct_field_offset_slots_eq >> strip_tac >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `well_typed_expr env e` by gvs[type_stmt_def, atarget_accepts_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_assignment_exists_def, int_calls_stmt_def,
         int_calls_atarget_def, int_calls_expr_def, body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  `expr_vv_sim_mem ctx func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_mem_ok_def] >>
  irule compile_assign_attr_storage_mem >> simp[] >>
  rpt strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval) >> strip_tac >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def,
      value_runtime_typed_def]
QED
