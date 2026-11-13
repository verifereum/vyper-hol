(* Counted assignment of an empty value through a computed place. *)
Theory bodyMemAssignPlaceEmpty
Ancestors
  bodyMemPlaceMemoryStore bodyMemPlaceStorageStore
  augAssignPlaceMemoryContinuation bodyMemoryDefs bodySimAugPlaceLoad
  stmtSimAugAssignPlaceMemory stmtSimAugAssignPlaceStorage stmtSimAssignStorage
  placeMemoryLiveRegion loweringPosts exprSimHypsDefs exprSimProps
  exprLoweringProps loweringStateRelDefs freshWrites stmtLoweringMono stmtLowering
  memoryLocalRhsProps stmtSimDeclMem stmtSimDeclCompose stmtSimProps
  assignEffectfulIndexCode stmtSimAssignMem exprSimMemDefs
  vyperStoragePlaceProvenance vyperTypeDefaults vyperStorageFrame
  fragGasSeqAbort fragGasPathMem fragGasMode fragGasPath fragExec gasSummary gasOutcome gasContext
  exprOperandVar
  targetPlaceSimMem targetPlaceSimCases stmtSimDefs exprSimDefs
  vyperInterpreter vyperState vyperValue vyperTypeSystem vyperExprNoControl vyperTypeInvariants
  venomExecSemantics venomInst venomState instMemFrontier memSafeRun
  emitHelper emitHelperProps compileEnv context words list rich_list
Libs
  monadsyntax

Theorem empty_place_memory_frontier[local]:
  place_ptr_rel ce cx s (PlaceR p) w (SOME LocMemory) (Type ty) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ has_length_word ty /\
  stmt_state_rel ctx func ce cx ee s /\
  write_place cx p (default_value tv) ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
     lookup_scopes id ee.scopes = SOME entry /\ ce.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type) ==>
  w2n w + 32 <= s.vs_alloca_next
Proof
  strip_tac >>
  `32 <= type_memory_size tv` by
    (mp_tac (Q.SPECL [`get_tenv cx`,`ty`,`tv`,`w2n w`,
       `(mstore (w2n w) 0w s).vs_memory`] memory_length_word_layout) >>
     simp[valueEncodingPropsTheory.mstore_mem_word_at_same]) >>
  drule_all memory_place_live_region >> strip_tac >>
  `b + len <= s.vs_alloca_next` by
    (drule_all body_local_region_frontier >> simp[]) >>
  decide_tac
QED

Theorem empty_place_store_run_mem[local]:
  target_post ctx func ce cx es sa st s0 ee (PlaceR p) (Type ty)
    (dst,SOME loc,SOME (ValPT ty)) s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ has_length_word ty /\
  compile_store_at_loc ce.ce_imm_alloca dst (Lit 0w) (SOME loc) st = ((),sf) /\
  write_place cx p (default_value tv) ee = (INL (),ff) /\
  expr_sim_inv ce cx env ee /\ acyclic_struct_metadata ce.ce_struct_fields /\
  local_ptrs_reserved ce st /\ storage_place_region cx p /\
  (!id path entry t0. p = MemoryPlace id path /\
     lookup_scopes id ee.scopes = SOME entry /\ ce.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  fn_has_code st sf func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx ff t /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
      FLOOKUP t.vs_allocas aid = SOME b) /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next = t.vs_alloca_next
Proof
  strip_tac >>
  `?w. eval_operand dst s = SOME w /\
       place_ptr_rel ce cx s (PlaceR p) w (SOME loc) (Type ty)` by
    fs[target_post_def] >>
  `stmt_state_rel ctx func ce cx ee s /\
   (!x. dst = Var x ==> not_fresh_at st x)` by fs[target_post_def] >>
  `alloca_inv s` by metis_tac[stmt_state_rel_def] >>
  Cases_on `loc = LocMemory`
  >- (gvs[] >> `w2n w + 32 <= s.vs_alloca_next` by
        (drule_all empty_place_memory_frontier >> simp[]) >>
      irule place_store_empty_memory_run_mem >> simp[] >>
      qexistsl_tac [`dst`,`tv`,`ty`,`ee`,`env`,`ce.ce_imm_alloca`,`p`,`w`] >> simp[]) >>
  `(loc = LocStorage \/ loc = LocTransient)` by
    (Cases_on `p` >> gvs[place_ptr_rel_def, slot_loc_def] >>
     Cases_on `b` >> gvs[slot_loc_def]) >>
  mp_tac (Q.INST [`imm` |-> `ce.ce_imm_alloca`, `dst_op` |-> `dst`,
    `cenv` |-> `ce`, `dty` |-> `ty`, `dtv` |-> `tv`,
    `sa` |-> `st`, `sb` |-> `sf`] place_store_empty_storage_run_mem) >>
  simp[] >> strip_tac >> qexists_tac `t` >> simp[]
QED

Theorem assign_empty_source:
  well_typed_expr env e /\ env.type_defs = get_tenv cx /\
  is_empty_value_expr e /\ has_length_word (expr_type e) /\
  type_widens_to env.type_defs (expr_type e) ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  eval_stmt cx (Assign (BaseTarget bt) e) =
    vyperState$bind (eval_target_place cx bt) (\p. write_place cx p (default_value tv))
Proof
  strip_tac >> simp[FUN_EQ_THM] >> qx_gen_tac `st` >>
  `vyperState$bind (eval_expr cx e) (read_result cx) st =
    (INL (default_value tv),st)` by
    (irule (REWRITE_RULE [ETA_AX] memory_rhs_empty_read_destination) >> metis_tac[]) >>
  simp[Once evaluate_def, GSYM bind_assoc, ETA_AX] >> fs[bind_def]
QED

Theorem empty_memory_write_success:
  lookup_scopes id ee.scopes = SOME entry /\
  write_place cx (MemoryPlace id path) v ee = (res,ff) /\
  stmt_res_ok lctx res ==>
  res = INL ()
Proof
  strip_tac >> Cases_on `evaluate_subscripts entry.type entry.value path`
  >- metis_tac[aug_place_memory_write_success] >>
  qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
  simp[write_place_def, get_scopes_def, bind_def, lift_option_type_def,
       type_check_def, assert_def, lift_sum_def, set_scopes_def,
       return_def, raise_def, AllCaseEqs()] >>
  Cases_on `find_containing_scope id ee.scopes` >>
  gvs[return_def, raise_def, stmt_res_ok_def] >>
  rename1 `find_containing_scope id ee.scopes = SOME data` >> PairCases_on `data` >>
  `data2 = entry` by
    metis_tac[vyperLookupTheory.find_containing_scope_lookup, optionTheory.SOME_11] >>
  gvs[ignore_bind_def, bind_def, assert_def, return_def, raise_def,
      set_scopes_def, replace_memory_entry_def, AllCaseEqs(), stmt_res_ok_def]
QED

Theorem empty_place_store_gas_obs[local]:
  place_ptr_rel ce cx s (PlaceR p) w (SOME loc) (Type ty) /\
  write_place cx p v ee = (res,ff) ==>
  !tail. write_place cx p v (ee with gas_obs := tail) =
    (res,ff with gas_obs := tail)
Proof
  Cases_on `p` >> simp[place_ptr_rel_def] >> rpt strip_tac
  >- (fs[write_place_def] >> simp[write_storage_slot_gas_obs]) >>
  drule aug_place_memory_write_gas_obs >> simp[]
QED

Theorem empty_place_store_outcome_mem[local]:
  target_post ctx func ce cx es sa st s0 ee (PlaceR p) (Type ty)
    (dst,SOME loc,SOME (ValPT ty)) s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ has_length_word ty /\
  compile_store_at_loc ce.ce_imm_alloca dst (Lit 0w) (SOME loc) st = ((),sf) /\
  expr_sim_inv ce cx env ee /\ acyclic_struct_metadata ce.ce_struct_fields /\
  local_ptrs_reserved ce st /\ storage_place_region cx p /\
  (!id path entry t0. p = MemoryPlace id path /\
     lookup_scopes id ee.scopes = SOME entry /\ ce.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  gas_admissible (write_place cx p (default_value tv)) (stmt_res_ok lctx) ee /\
  fn_has_code st sf func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func) (write_place cx p (default_value tv))
    (ee,s)
    (\res ff t. res = INL () /\ stmt_state_rel ctx func ce cx ff t /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      alloca_history func t /\ s.vs_alloca_next = t.vs_alloca_next)
    (\res ff r. !tail. stmt_exit RetQ (ff with gas_obs := tail) res r)
Proof
  strip_tac >>
  `?w. eval_operand dst s = SOME w /\
    place_ptr_rel ce cx s (PlaceR p) w (SOME loc) (Type ty)` by fs[target_post_def] >>
  Cases_on `write_place cx p (default_value tv) ee` >>
  rename1 `write_place cx p (default_value tv) ee = (res,ff)` >>
  `stmt_res_ok lctx res` by
    (drule gas_admissible_result >> disch_then irule >>
     qexistsl_tac [`ff`,`ee.gas_obs`] >> simp[]) >>
  `!tail. write_place cx p (default_value tv) (ee with gas_obs := tail) =
    (res,ff with gas_obs := tail)` by metis_tac[empty_place_store_gas_obs] >>
  Cases_on `p`
  >- suspend "storage"
  >- (rename1 `MemoryPlace id path` >>
      `?entry. lookup_scopes id ee.scopes = SOME entry` by
        (Cases_on `lookup_scopes id ee.scopes`
         >- fs[target_post_def, place_readable_def, read_place_def,
               get_scopes_def, bind_def, lift_option_type_def,
               lift_sum_def, return_def, raise_def] >> simp[]) >>
      `res = INL ()` by (drule_all empty_memory_write_success >> simp[]) >>
      suspend "normal_memory") >>
  gvs[place_ptr_rel_def]
QED
Resume empty_place_store_outcome_mem[storage]:
  rename1 `StoragePlace tr slot tv'` >>
  `tv' = tv` by gvs[place_ptr_rel_def] >>
  qpat_x_assum `tv' = tv` SUBST_ALL_TAC >>
  `~cx.txn.is_static` by
    fs[target_post_def, stmt_state_rel_def, state_rel_def] >>
  `value_has_type tv (default_value tv)` by
    metis_tac[vyperTypeDefaultsTheory.default_value_has_type_thm] >>
  `res = INL ()` by
    (gvs[write_place_def] >>
     mp_tac (Q.SPECL [`cx`,`tr`,`slot`,`tv`,`default_value tv`,`ee`]
       write_storage_slot_succeeds) >> simp[]) >>
  suspend "normal_storage"
QED
Resume empty_place_store_outcome_mem[normal_memory]:
  qpat_x_assum `res = INL ()` SUBST_ALL_TAC >>
  drule_all empty_place_store_run_mem >> strip_tac >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`INL ()`,`ff`,`OK t`] >>
  simp[exprSimWordArgsTheory.stmt_state_rel_gas_obs]
QED
Resume empty_place_store_outcome_mem[normal_storage]:
  qpat_x_assum `res = INL ()` SUBST_ALL_TAC >>
  drule_all empty_place_store_run_mem >> strip_tac >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`INL ()`,`ff`,`OK t`] >>
  simp[exprSimWordArgsTheory.stmt_state_rel_gas_obs]
QED
Finalise empty_place_store_outcome_mem[local]

Theorem empty_target_admissible:
  gas_admissible (vyperState$bind (eval_target_place cx bt) k) (stmt_res_ok lctx) es ==>
  gas_admissible (eval_target_place cx bt) target_place_res_ok es
Proof
  rw[gas_admissible_def] >> Cases_on `res`
  >- simp[target_place_res_ok_def] >>
  rename1 `eval_target_place cx bt _ = (INR ex,ee)` >>
  `no_control_exc ex` by metis_tac[eval_target_place_no_control] >>
  `stmt_res_ok lctx (INR ex)` by
    (first_x_assum (qspec_then `gs` mp_tac) >>
     simp[bind_def] >> metis_tac[]) >>
  Cases_on `ex` >> gvs[no_control_exc_def, stmt_res_ok_def, target_place_res_ok_def]
QED

Theorem empty_store_admissible:
  gas_admissible (vyperState$bind (eval_target_place cx bt) k) (stmt_res_ok lctx) es /\
  (!tail. eval_target_place cx bt (es with gas_obs := prefix ++ tail) =
    (INL p,mid with gas_obs := tail)) ==>
  gas_admissible (k p) (stmt_res_ok lctx) mid
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  qpat_x_assum `!gs res ee. vyperState$bind _ _ _ = _ ==> _`
    (qspec_then `prefix ++ gs` mp_tac) >>
  simp[bind_def] >> metis_tac[]
QED

Theorem compile_assign_place_empty_stmt_frag_mem:
  target_sim_mem ctx func ce cx env bt es /\
  target_indices_pre ce cx env bt /\ expr_sim_inv ce cx env es /\
  well_typed_expr env e /\ type_place_target env bt = SOME (Type ty) /\
  type_widens_to env.type_defs (expr_type e) ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  has_length_word (expr_type e) /\ is_empty_value_expr e ==>
  stmt_frag_mem d ctx func cx lctx RetQ ce
    (stmt_env ce lctx ret_ty (Assign (BaseTarget bt) e))
    (eval_stmt cx (Assign (BaseTarget bt) e)) es
Proof
  strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `has_length_word ty` by metis_tac[type_widens_to_has_length_word] >>
  `eval_stmt cx (Assign (BaseTarget bt) e) =
    vyperState$bind (eval_target_place cx bt) (\p. write_place cx p (default_value tv))` by
    metis_tac[assign_empty_source] >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule stmt_env_assign >> strip_tac >> gvs[] >>
  `?r st. compile_get_target_ptr compile_expr ce bt sa = (r,st) /\
    compile_store_at_loc ce.ce_imm_alloca (FST r) (Lit 0w) (FST (SND r)) st = ((),sb)` by
    metis_tac[assign_effectful_empty_code] >>
  `ci_mono sa st /\ ci_mono st sb` by
    metis_tac[ci_mono_compile_get_target_ptr, cj 2 ci_mono_stmt_helpers, pairTheory.SND] >>
  `fn_has_code sa st func /\ fn_has_code st sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_mid, cs_extends_refl]) >>
  `local_ptrs_reserved ce st` by
    metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    metis_tac[empty_target_admissible] >>
  irule aug_place_target_mem_continuation >> simp[] >> (conj_tac
  >- (rpt strip_tac >> Cases_on `res`
      >- fs[expr_exit_def] >>
      rename1 `expr_exit (INR ex) rr` >> qexists_tac `ex` >>
      simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type])) >>
  qexistsl_tac [`ce`,`env`,`r`,`sa`,`st`,`ty`] >> simp[] >>
  suspend "target"
QED
Resume compile_assign_place_empty_stmt_frag_mem[target]:
  rpt gen_tac >> strip_tac >>
  `~t.vs_halted` by metis_tac[gas_marked_path_exec, gas_path_normal] >>
  `eval_target_place cx bt
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ mid.gas_obs) =
    (INL p,mid)` by (qpat_x_assum `!tail. eval_target_place _ _ _ = _`
      (qspec_then `mid.gas_obs` mp_tac) >> simp[]) >>
  `expr_sim_inv ce cx env mid` by
    (irule aug_place_target_inv >>
     goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >> simp[]) >>
  `storage_place_region cx p` by metis_tac[eval_target_place_region] >>
  `!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id mid.scopes = SOME entry /\ ce.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    metis_tac[aug_place_entry_type_agrees] >>
  `gas_admissible (write_place cx p (default_value tv)) (stmt_res_ok lctx) mid` by
    (irule (BETA_RULE (Q.INST [`k` |-> `\p. write_place cx p (default_value tv)`]
       empty_store_admissible)) >>
     qexistsl_tac [`bt`,`es`,`gas_explicit marks s0.vs_gas_readings`] >> simp[]) >>
  `?dst loc. r = (dst,SOME loc,SOME (ValPT ty)) /\
    (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient)` by
    (PairCases_on `r` >> fs[target_post_def, exprLoweringTheory.value_type_place_def] >>
     Cases_on `p` >> fs[place_ptr_rel_def, slot_loc_def] >>
     Cases_on `b` >> gvs[slot_loc_def]) >> gvs[] >>
  `~block_is_terminated sb` by
    (gvs[compile_store_at_loc_def] >>
     irule emit_void_nonterminator_open >> goal_assum (drule_at Any) >>
     simp[is_terminator_def]) >>
  `gas_outcome T (cx_tops cx) (ctx,func) (write_place cx p (default_value tv))
    (mid,t)
    (\res ff u. res = INL () /\ stmt_state_rel ctx func ce cx ff u /\
      (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x t) /\
      (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
        FLOOKUP u.vs_allocas aid = SOME b) /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next = u.vs_alloca_next)
    (\res ff rr. !tail. stmt_exit RetQ (ff with gas_obs := tail) res rr)` by
    (drule_all empty_place_store_outcome_mem >> simp[]) >>
  irule gas_outcome_post_mono >> goal_assum (drule_at Any) >>
  simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 `stmt_state_rel ctx func ce cx ff u` >>
  simp[stmt_lands_def, cenv_top_ext_def] >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x u = SOME w` by
    (fs[target_post_def] >> metis_tac[compiler_ci_mono_not_fresh]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP u.vs_allocas aid = SOME b` by (fs[target_post_def] >> metis_tac[]) >>
  `return_buf_frame d ce sb u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s0`,`sa`] >>
     fs[ci_mono_def] >> decide_tac) >> simp[]
QED
Finalise compile_assign_place_empty_stmt_frag_mem
