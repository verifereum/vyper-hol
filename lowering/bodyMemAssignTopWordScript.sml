(* Memory case of the body induction, assignment to a base target
   (bodyMemAssign's dispatch): a storage or transient variable of a word
   type (S1's body_assign_toplevel_word).  The lowering evaluates e and
   stores its word with one SSTORE or TSTORE at the variable's slot, which
   touches no memory. *)
Theory bodyMemAssignTopWord
Ancestors
  gasStorage vyperStorageTrace vyperStorageFootprint
  supportedExprTraverse allocLimits allocLimitsProps
  bodySim vyperTypeCallGraph
  bodyMemoryPreds bodyMemoryDefs bodyDeclMemoryCounted bodyDeclMemoryCore
  allocaFootprint instMemFrontier memSafeRun exprSimMemDefs exprSimSource
  bodyExprPreFacts stmtSimAssignStorage stmtSimForced exprSimTopLevelProps
  accountsRelProps exprSimUnwrap bodyStorageMetadata
  vyperTypeEnv vyperStorageLayoutSafety vyperStorageBackend
  stmtSimProps stmtSimDefs exprSimDefs loweringPosts
  gasOutcome gasSummary fragGasMode fragGasPath gasContext
  exprSimHypsDefs exprLoweringProps emitHelperProps emitHelper exprLowering
  compileEnv loweringStateRelDefs fragExecMem supportedStmtTraverse supportedStmts supportedExprs
  supportedTypes vyperTypeExprResult vyperTypeExprSoundness vyperTypeInvariants
  vyperTypeSystem vyperLookup vyperInterpreter vyperState
  venomExecSemantics venomInst venomState list rich_list finite_map
Libs
  monadsyntax

(* The SSTORE or TSTORE of w at slot, run on a memory-safe path in a
   non-static call: it touches no memory and lands at the stored state
   exactly.  It needs no horizon, which the frag proof lacks when the
   stored trace has none. *)
Theorem assign_storage_store_path_mem:
  !ctx func tr slot op w s st st'.
    emit_void (if tr then TSTORE else SSTORE) [Lit slot; op] st = ((), st') /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    eval_operand op s = SOME w /\ alloca_history func s /\ alloca_inv s /\
    ~s.vs_call_ctx.cc_static ==>
    ?t. t = ((if tr then tstore slot w s else sstore slot w s)
             with vs_inst_idx := LENGTH st'.cs_current_insts) /\
        ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. lookup_var x t = lookup_var x s) /\
        t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
        alloca_history func t /\
        gas_marked_path T ctx func s 0 (OK t)
Proof
  rpt strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  qabbrev_tac `u = if tr then tstore slot w s else sstore slot w s` >>
  `step_inst_base (mk_inst st.cs_next_id (if tr then TSTORE else SSTORE)
     [Lit slot; op] []) s = OK u` by
    (Cases_on `tr` >>
     gvs[Abbr `u`, step_inst_base_opcode_eqs, exec_write2_def, mk_inst_def,
         eval_operand_def]) >>
  `run_inst_seq (emitted_insts st st') s = OK u` by
    simp[run_inst_seq_def] >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    (drule emit_void_mem_ok >> disch_then irule >>
     Cases_on `tr` >>
     simp[below_frontier_no_ranges, inst_dload_in_section_other,
          mk_inst_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts st st')` by
    (Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH st'.cs_current_insts)) /\
   ~u.vs_halted /\ u.vs_current_bb = st'.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[is_terminator_def] >>
     qexists_tac `st` >> simp[is_terminator_def]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule body_store_memory_history >> simp[is_terminator_def] >>
     qexistsl_tac [`s`, `st`] >> Cases_on `tr` >> simp[is_terminator_def]) >>
  qexists_tac `u with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[gas_marked_path_def] >>
  Cases_on `tr` >> simp[Abbr `u`, lookup_var_def, sstore_def, tstore_def, LET_THM]
QED

(* self.x = e for a storage or transient variable x the lowering holds in
   one word and e of x's declared word type, for every outcome, on a
   memory-safe path: e's errors exit, and on a value its word is stored at
   x's slot.  The memory twin of compile_assign_storage_typed_stmt_frag. *)
Theorem compile_assign_storage_typed_stmt_frag_mem:
  !d ctx func cx lctx RetQ cenv ty src id e es ts tr typ id_str slot
   tvt vtyp.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    expr_type e = typ /\ is_word_type typ /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME vtyp /\
    is_word_type vtyp /\
    (!gs v es1.
       (do result <- eval_expr cx e; read_result cx result od)
         (es with gas_obs := gs) = (INL v, es1) ==>
       value_has_type tvt v) /\
    expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (TopLevelNameTarget (src, id))) e))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src, id))) e))
      es
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_type e = typ` (SUBST_ALL_TAC o SYM) >>
  `type_slot_size tvt = 1` by metis_tac[word_type_slot_size] >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_initial >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by metis_tac[] >>
  `FLOOKUP cenv.ce_module_vars (src, id) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (irule toplevel_storage_ce_vars >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  drule_all assign_storage_word_code_parts >> strip_tac >>
  rename1 `lower_value _ _ _ _ sa = (op, sB)` >> gvs[] >>
  drule_all eval_assign_toplevel_action >>
  disch_then (qspec_then `e` (fn th =>
    RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th])) >>
  drule forced_then_admissible >> strip_tac >>
  `~block_is_terminated sb` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> Cases_on `sB.cs_current_insts` >> Cases_on `tr` >>
     gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
         venomInstTheory.mk_inst_def, is_terminator_def]) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> strip_tac >>
     drule emitted_insts_emit_void >> strip_tac >> decide_tac) >>
  irule forced_then_outcome >>
  qexists_tac `\H v ee t.
    expr_post H ctx func cenv cx e es sa sB s0 ee v op t /\
    expr_store_bound cx (expr_type e) v op t /\
    t.vs_current_bb = sB.cs_current_bb /\
    t.vs_inst_idx = LENGTH sB.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` >>
  rpt conj_tac
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >>
      irule vyperStorageTraceTheory.storage_trace_frame_ignore_bind >>
      simp[vyperStorageTraceTheory.storage_trace_frame_event,
           vyperStorageTraceTheory.storage_trace_frame_write_storage_slot])
  >~ [`expr_exit (INR _) _`]
  >- (rpt strip_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type])
  >~ [`gas_outcome _ _ _ _ _ _ _ _ _`]
  >- (qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
      disch_then (qspecl_then [`st0`, `sa`, `sB`, `op`, `s0`] mp_tac) >>
      simp[]) >>
  suspend "store"
QED

Resume compile_assign_storage_typed_stmt_frag_mem[store]:
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  rename1 `valid_horizon cx st0 H1 ee.storage_trace` >>
  `value_has_type tvt v` by metis_tac[] >>
  `encode_value tvt v = SOME [(0, typed_val_to_w256 tvt v)]` by
    (irule encode_value_word_typed >> metis_tac[]) >>
  `well_formed_type_value tvt` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee t /\
       storage_well_formed_on cx ee (FST H)` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==>
                      expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     rewrite_tac[expr_post_def] >> strip_tac >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==>
                   expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H1` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  rewrite_tac[expr_post_def] >> strip_tac >>
  `eval_operand op t = SOME (typed_val_to_w256 tvt v)` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `~t.vs_call_ctx.cc_static /\ ~cx.txn.is_static` by
    (qpat_x_assum `stmt_state_rel H1 _ _ _ _ ee t` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[stmt_state_rel_def, state_rel_def]) >>
  `alloca_inv t` by
    (qpat_x_assum `stmt_state_rel H1 _ _ _ _ ee t` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[stmt_state_rel_def]) >>
  Cases_on `write_storage_slot cx tr (n2w slot) tvt v ee` >>
  rename1 `_ = (res, ee0)` >>
  `res = INL ()` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     simp[write_storage_slot_eq]) >>
  pop_assum SUBST_ALL_TAC >>
  `ee0.gas_obs = [] /\ ee0.scopes = ee.scopes` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     simp[write_storage_slot_eq] >> Cases_on `tr` >>
     simp[set_storage_def] >> strip_tac >> gvs[]) >>
  qabbrev_tac `ef = ee0 with storage_trace :=
    ee.storage_trace ++ [StorageRoot tr slot tvt]` >>
  `ef with gas_obs := [] = ef` by
    simp[Abbr `ef`, evaluation_state_component_equality] >>
  `ef.storage_trace = ee.storage_trace ++ [StorageRoot tr slot tvt]` by
    simp[Abbr `ef`] >>
  `ef.scopes = ee.scopes` by simp[Abbr `ef`] >>
  `!tail. ignore_bind (record_storage_event (StorageRoot tr slot tvt))
            (write_storage_slot cx tr (n2w slot) tvt v) (ee with gas_obs := tail) =
          (INL (), ef with gas_obs := tail)` by
    (gen_tac >>
     simp[ignore_bind_def, bind_def, record_storage_event_def, return_def] >>
     `write_storage_slot cx tr (n2w slot) tvt v (ee with gas_obs := tail) =
        (INL (), ee0 with gas_obs := tail)` by
       fs[write_storage_slot_gas_obs] >>
     drule write_storage_slot_storage_trace >>
     disch_then (qspec_then `ee.storage_trace ++ [StorageRoot tr slot tvt]`
       mp_tac) >>
     simp[Abbr `ef`]) >>
  qspecl_then [`ctx`, `func`, `tr`, `n2w slot`, `op`,
    `typed_val_to_w256 tvt v`, `t`, `sB`, `sb`] mp_tac
    assign_storage_store_path_mem >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  qexistsl_tac [`INL ()`, `ef`, `OK u`] >>
  rpt conj_tac
  >- (BETA_TAC >> first_assum ACCEPT_TAC)
  >- first_assum ACCEPT_TAC >>
  disj1_tac >> qexists_tac `u` >> conj_tac >- REFL_TAC >>
  qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H ee.storage_trace /\
   MEM (tr, n2w slot, tvt) (FST H) /\ regions_consistent (FST H)` by
    (qpat_x_assum `valid_horizon _ _ H _` mp_tac >>
     simp[vyperStorageFootprintTheory.valid_horizon_def,
          vyperStorageFootprintTheory.storage_observations_ok_def,
          vyperStorageFootprintTheory.storage_trace_regions_def,
          listTheory.EVERY_APPEND]) >>
  `stmt_state_rel H ctx func cenv cx ee t /\
   storage_well_formed_on cx ee (FST H)` by metis_tac[] >>
  `!u0 st. storage_dead H tr (update_storage (n2w slot) u0 st) =
           storage_dead H tr st` by
    (rpt gen_tac >>
     metis_tac[accountsRelPropsTheory.storage_dead_update_word_region]) >>
  qspecl_then [`H`, `func`, `cenv`, `cx`, `ee`, `t`, `tr`, `n2w slot`, `tvt`,
    `v`, `typed_val_to_w256 tvt v`, `INL ()`, `ee0`, `ctx`]
    mp_tac stmt_state_rel_write_storage_word >>
  impl_tac >- simp[] >> strip_tac >>
  `storage_well_formed_on cx ee0 (FST H)` by
    metis_tac[vyperStorageFootprintTheory.typed_write_preserves_storage_well_formed_on] >>
  `storage_well_formed_on cx ef (FST H)` by
    (`ef.accounts = ee0.accounts /\ ef.tStorage = ee0.tStorage` by
       simp[Abbr `ef`] >>
     metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends]) >>
  `stmt_state_rel H ctx func cenv cx ef u` by
    (qpat_x_assum `u = _` SUBST1_TAC >>
     simp[Abbr `ef`, stmt_state_rel_inst_idx]) >>
  BETA_TAC >>
  qpat_x_assum `ef with gas_obs := [] = ef`
    (fn th => REWRITE_TAC [th]) >>
  qexists_tac `cenv` >> rpt conj_tac
  >- simp[stmt_lands_def]
  >- first_assum ACCEPT_TAC
  >- simp[]
  >- simp[cenv_top_ext_refl]
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (rpt strip_tac >> metis_tac[])
  >- (rpt strip_tac >> metis_tac[])
  >- (irule return_buf_frame_frame >>
      qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[] >> metis_tac[])
  >- first_assum ACCEPT_TAC
  >- simp[]
QED

Finalise compile_assign_storage_typed_stmt_frag_mem

Theorem body_assign_toplevel_word_mem:
  !cx nsid e d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_stmt_safe tops (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget (TopLevelNameTarget nsid)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    supported_scalar_target tops nsid ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) es
Proof
  Cases_on `nsid` >> rename1 `TopLevelNameTarget (src, id)` >>
  rpt strip_tac >>
  `supported_expr tops e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  `!ts vis mut id ty init.
     MEM (VariableDecl vis mut id ty init) ts /\
     (mut = Storage \/ mut = Transient) ==>
     find_var_decl_by_name id ts <> NONE` by
    (Induct >> simp[] >> Cases >> rw[find_var_decl_by_name_def] >>
     metis_tac[]) >>
  `src = NONE /\ find_var_decl_by_name id tops <> NONE /\
   ?vis mut ty slot. MEM (VariableDecl vis mut id ty slot) tops /\
     is_word_type ty` by
    (qpat_x_assum `supported_scalar_target _ _` mp_tac >>
     simp[supported_scalar_target_def] >>
     Cases_on `supported_variable_decl tops (src, id)` >> simp[] >>
     rename1 `SOME x` >> PairCases_on `x` >>
     Cases_on `x0` >> Cases_on `x1` >> Cases_on `x3` >> simp[] >>
     strip_tac >> drule supported_variable_decl_mem >> strip_tac >>
     `find_var_decl_by_name id tops <> NONE` by metis_tac[] >>
     gvs[supported_full_word_type_def] >> first_assum (irule_at Any) >>
     simp[is_word_type_def]) >>
  gvs[] >>
  `get_module_code cx NONE = SOME tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE, id) =
     build_var_type_map tops (NONE, id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  Cases_on `type_place_target env (TopLevelNameTarget (NONE, id))` >>
  gvs[type_stmt_def, atarget_accepts_def] >>
  rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> gvs[] >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (qpat_x_assum `env_consistent _ _ _`
        (strip_assume_tac o REWRITE_RULE [env_consistent_def,
           env_context_consistent_def]) >>
      first_x_assum drule >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  `t = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >> rename1 `FLOOKUP env.toplevel_vtypes _ = SOME (Type ty)` >>
  `expr_type e = ty` by metis_tac[type_widens_to_word] >>
  qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
    SIMP_RULE std_ss [body_stmt_safe_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, supported_iterator_exists_def,
      supported_assert_exists_def, supported_raise_exists_def,
      supported_expr_exists_def, int_calls_stmt_def, int_calls_atarget_def,
      int_calls_iterator_def, int_calls_assert_reason_def, int_calls_raise_reason_def,
      listTheory.EVERY_APPEND, listTheory.EVERY_CONJ,
      DE_MORGAN_THM, GSYM expr_has_evm_run_def]) >>
  qpat_assum `stmt_exprs_ok _ _` (strip_assume_tac o
    SIMP_RULE std_ss [stmt_exprs_ok_def, alloc_limits_stmt_def,
      alloc_limits_iterator_def, alloc_limits_assert_def, alloc_limits_raise_def,
      alloc_limits_expr_def]) >>
  imp_res_tac alloc_limits_expr_not_extcode >>
  `supported_program tops` by gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_assignment_exists_def, int_calls_stmt_def,
         int_calls_atarget_def, int_calls_expr_def, body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  `expr_sim_mem ctx func cenv cx ty e es` by
    metis_tac[body_expr_mem_ok_def] >>
  irule compile_assign_storage_typed_stmt_frag_mem >> simp[] >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `IS_SOME (evaluate_type _ _)`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  rename1 `lookup_var_slot_from_layout _ _ _ _ = SOME slot'` >>
  rename1 `evaluate_type _ ty = SOME tvt` >>
  qexistsl_tac [`slot'`, `tvt`] >> simp[] >> rpt strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def,
      value_runtime_typed_def]
QED
