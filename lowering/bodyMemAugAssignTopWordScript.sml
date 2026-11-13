(* Memory case of the body induction, augmented assignment
   (bodyMemAugAssign's dispatch): a word storage or transient variable
   (S1's body_augassign_toplevel_word).  The lowering loads x with an
   SLOAD or TLOAD, lowers e at x's type, runs the operator and stores the
   result with an SSTORE or TSTORE; neither touches memory, so the pieces
   compose as in bodyMemAugAssignLocal. *)
Theory bodyMemAugAssignTopWord
Ancestors
  supportedExprTraverse allocLimitsProps
  bodySim vyperTypeCallGraph
  bodyMemoryPreds bodyMemoryDefs bodyMemAssignTopWord bodyDeclMemoryCounted
  bodyDeclMemoryCore allocaFootprint instMemFrontier memSafeRun
  bodyBinopFamiliesMemory bodyBinopFragMemory
  gasStorage vyperStorageTrace vyperStorageFootprint stmtSimAugAssignStorage
  exprSimMemDefs exprSimSource exprSimHyps bodyExprPreFacts
  stmtSimAugAssign stmtSimAssignStorage exprSimTopLevelProps
  accountsRelProps exprSimUnwrap exprSimProps bodyStorageMetadata
  vyperTypeEnv vyperStorageLayoutSafety vyperStorageBackend
  exprBopSimDefs exprBopSimProps
  gasOutcome gasContext gasExemptCert gasSummary gasSummaryCompose
  fragGasMode fragGasPath fragGasPathMem fragGasSeq
  stmtSimProps exprSimHypsDefs stmtSimDefs exprSimDefs loweringPosts
  allocLimits fragExec fragExecMem localPtrsProps freshWrites
  exprOpenPrimitives exprOperandVar
  exprLowering exprBopLowering stmtLowering emitHelper emitHelperProps
  exprLoweringProps compileEnv loweringStateRelDefs valueEncoding
  supportedStmtTraverse supportedStmts supportedExprs supportedTypes
  vyperInterpreter vyperState vyperValue vyperValueOperation vyperContext
  vyperExprNoControl vyperTypeSystem vyperTyping
  vyperTypeExprResult vyperTypeExprSoundness
  vyperTypeInvariants vyperTypeBuiltins vyperTypeStatePreservation
  vyperLookup vyperAST
  venomExecSemantics venomExecProofs venomInst venomState
  list rich_list finite_map pred_set
Libs
  monadsyntax

(* ===== The load of x, on a memory-safe path ===== *)

Theorem augassign_storage_load_frame_mem[local]:
  emit_op (if tr then TLOAD else SLOAD) [Lit slot] sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel H ctx func cenv cx es s0 /\
  alloca_history func s0 /\
  is_word_type ty /\ storage_holds cx tr ty (Value v) slot es s0 /\
  evaluate_type (get_tenv cx) ty = SOME tvt ==>
  ?t. gas_marked_path T ctx func s0 0 (OK t) /\
    eval_operand op t = SOME (typed_val_to_w256 tvt v) /\
    stmt_state_rel H ctx func cenv cx es t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ alloca_history func t /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s0) /\
    t.vs_allocas = s0.vs_allocas /\ t.vs_alloca_next = s0.vs_alloca_next /\
    (?out. op = Var out /\ not_fresh_at sb out) /\
    t.vs_accounts = s0.vs_accounts /\ t.vs_transient = s0.vs_transient /\
    t.vs_requests = s0.vs_requests /\ t.vs_call_ctx = s0.vs_call_ctx
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `w = if tr then tload slot s0 else sload slot s0` >>
  `run_inst_seq (emitted_insts sa sb) s0 = OK (update_var out w s0)` by
    (Cases_on `tr` >>
     FIRST [simp[Abbr `w`, Abbr `out`, run_inst_seq_def,
                 step_inst_base_opcode_eqs,
                 mk_inst_def, exec_read1_def, eval_operand_def]]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s0` by
    (drule emit_op_mem_ok >> disch_then irule >> Cases_on `tr` >>
     simp[below_frontier_no_ranges, mk_inst_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  `gas_path_mem ctx func s0 0
     (OK (update_var out w s0 with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   ~(update_var out w s0).vs_halted /\
   (update_var out w s0).vs_current_bb = sb.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  `alloca_inv s0` by fs[stmt_state_rel_def] >>
  `alloca_history func
     (update_var out w s0 with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s0`, `sa`] >> Cases_on `tr` >>
     simp[mk_inst_def, is_terminator_def]) >>
  `w = typed_val_to_w256 tvt v` by
    (simp[Abbr `w`] >> irule storage_holds_load >> metis_tac[]) >>
  `not_local_ptr cenv es.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
     qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es (update_var out w s0)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  qexists_tac `update_var out w s0 with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[gas_marked_path_def, stmt_state_rel_inst_idx, eval_operand_def] >>
  gvs[update_var_def] >>
  simp[Abbr `out`, lookup_var_def, FLOOKUP_UPDATE] >>
  rw[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED

(* ===== The statement ===== *)

(* Premise change from the old statement: e's simulation is at the state
   after the target's place was looked up, which records x's root in the
   storage trace (S1's compile_augassign_toplevel_case has e's simulation
   there too).  Before: expr_sim_mem ... (es with gas_obs := gs).  After:
   the same at (es with storage_trace := es.storage_trace ++
   [StorageRoot tr slot tvt]) with gas_obs := gs. *)
Theorem compile_augassign_toplevel_mem:
  !d ctx func cx lctx RetQ cenv ty0 env ty src id bop e es
   ts tr id_str slot tvt vtyp.
    (!gs. expr_sim_mem ctx func cenv cx ty e
       ((es with storage_trace :=
           es.storage_trace ++ [StorageRoot tr slot tvt])
        with gas_obs := gs)) /\
    expr_body_pre cenv cx env e es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) ty = SOME tvt /\
    well_formed_type env.type_defs ty /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME vtyp /\ is_word_type vtyp /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0
         (AugAssign ty (TopLevelNameTarget (src, id)) bop e))
      (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  reverse (Cases_on `storage_trace_domain cx st0
     (es.storage_trace ++ [StorageRoot tr slot tvt])`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      drule_all stmtSimAugAssignStorageTheory.augassign_toplevel_bad_root >>
      simp[]) >>
  `!H. valid_horizon cx st0 H (es.storage_trace ++ [StorageRoot tr slot tvt]) ==>
       valid_horizon cx st0 H es.storage_trace /\
       MEM (tr,n2w slot,tvt) (FST H) /\ regions_consistent (FST H)` by
    (rpt gen_tac >> strip_tac >>
     fs[vyperStorageFootprintTheory.valid_horizon_def,
        vyperStorageFootprintTheory.storage_observations_ok_def,
        vyperStorageFootprintTheory.storage_trace_regions_def]) >>
  qabbrev_tac `H1 = storage_trace_horizon
    (es.storage_trace ++ [StorageRoot tr slot tvt])` >>
  `valid_horizon cx st0 H1 (es.storage_trace ++ [StorageRoot tr slot tvt])` by
    fs[Abbr `H1`, vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `valid_horizon cx st0 H1 es.storage_trace /\
   MEM (tr,n2w slot,tvt) (FST H1) /\ regions_consistent (FST H1)` by
    (qpat_assum `!H. valid_horizon _ _ H (_ ++ _) ==> _`
       (qspec_then `H1` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `stmt_state_rel H1 ctx func cenv cx es s0 /\
   storage_well_formed_on cx es (FST H1)` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `H1` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `contract_storage_well_formed cx es /\ storage_layout_safe cx /\
   storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[expr_sim_inv_def, stmt_state_rel_def, state_rel_def] >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  drule_all toplevel_storage_read_decodes >> strip_tac >>
  drule_all stmtSimAugAssignStorageTheory.augassign_toplevel_code_parts >> strip_tac >> gvs[] >>
  suspend "load"
QED

Resume compile_augassign_toplevel_mem[load]:
  `cs_extends sa s1` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_binop_grows >> strip_tac >>
  `cs_extends s3 sb` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends s1 s3 /\ cs_extends s1 sb /\ cs_extends s2 sb /\
   cs_extends sa s2 /\ cs_extends sa s3` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  rename1 `read_storage_slot cx tr (n2w slot) tvt es = (INL v0,es)` >>
  `storage_holds cx tr ty (Value v0) (n2w slot) es s0` by
    (irule stmtSimAugAssignStorageTheory.declared_storage_holds_value >>
     metis_tac[]) >>
  drule_all augassign_storage_load_frame_mem >> strip_tac >>
  `read_storage_slot cx tr (n2w slot) tvt
     (es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt]) =
   (INL v0, es with storage_trace :=
              es.storage_trace ++ [StorageRoot tr slot tvt])` by
    (irule stmtSimAugAssignStorageTheory.read_storage_slot_storage_trace >>
     first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H (es.storage_trace ++ [StorageRoot tr slot tvt]) ==>
       stmt_state_rel H ctx func cenv cx
         ((es with storage_trace :=
             es.storage_trace ++ [StorageRoot tr slot tvt])
          with gas_obs := []) t /\
       storage_well_formed_on cx
         ((es with storage_trace :=
             es.storage_trace ++ [StorageRoot tr slot tvt])
          with gas_obs := []) (FST H)` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       (qpat_assum `!H. valid_horizon _ _ H (_ ++ _) ==> _`
          (qspec_then `H` mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
     `stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H)` by
       (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
          (qspec_then `H` mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
     `stmt_state_rel H ctx func cenv cx es t` by
       (irule exprLoweringPropsTheory.stmt_state_rel_fields_transport >>
        qexistsl_tac [`H1`, `s0`] >> rpt conj_tac >> metis_tac[]) >>
     `storage_well_formed_on cx
        ((es with storage_trace :=
            es.storage_trace ++ [StorageRoot tr slot tvt])
         with gas_obs := []) (FST H) <=>
      storage_well_formed_on cx es (FST H)` by
       (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >>
        simp[]) >>
     fs[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
     ((es with storage_trace :=
         es.storage_trace ++ [StorageRoot tr slot tvt])
      with gas_obs := [])` by
    (simp[] >>
     drule_all stmtSimAugAssignStorageTheory.augassign_toplevel_rhs_admissible >>
     simp[]) >>
  `gas_marked_path F ctx func s0 0 (OK t)` by
    (irule gas_marked_path_from_mem >> fs[gas_marked_path_def]) >>
  `!marks.
     gas_bad_storage_at cx st0 (bind (eval_expr cx e) (read_result cx))
       ((es with storage_trace :=
           es.storage_trace ++ [StorageRoot tr slot tvt])
        with gas_obs := []) t marks ==>
     gas_bad_storage_at cx st0
       (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e))
       es s0 marks` by
    (gen_tac >> strip_tac >>
     drule_all stmtSimAugAssignStorageTheory.augassign_toplevel_rhs_bad_storage >>
     simp[]) >>
  qpat_x_assum `!gs. expr_sim_mem _ _ _ _ _ _ _`
    (qspec_then `[]` (mp_tac o REWRITE_RULE [expr_sim_mem_def])) >>
  disch_then (qspecl_then [`st0`, `s1`, `s2`, `rhs_op`, `t`] mp_tac) >>
  impl_tac
  >- (qpat_assum `!H. valid_horizon _ _ H _ ==>
        stmt_state_rel H _ _ _ _ (_ with gas_obs := []) t /\ _` mp_tac >>
      simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >> metis_tac[])
  >- suspend "rhs_summary" >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  `gas_marked_exec T (ctx,func)
     (eval_target_place cx (TopLevelNameTarget (src,id))) (es,s0) []
     (INL (StoragePlace tr (n2w slot) tvt))
     (es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt])
     (OK t)` by
    (irule stmtSimAugAssignStorageTheory.augassign_toplevel_place_exec >>
     metis_tac[]) >>
  irule stmtSimAugAssignStorageTheory.augassign_toplevel_rhs_exempt >>
  metis_tac[]
QED

Resume compile_augassign_toplevel_mem[rhs_summary]:
  qexists_tac `marks` >>
  Cases_on `gas_bad_storage_at cx st0 (bind (eval_expr cx e) (read_result cx))
              ((es with storage_trace :=
                  es.storage_trace ++ [StorageRoot tr slot tvt])
               with gas_obs := []) t marks`
  >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >> disj1_tac >>
  qpat_x_assum `gasSummary$gas_summary_at _ _ _ _ _ _ _`
    (strip_assume_tac o BETA_RULE o REWRITE_RULE [gas_summary_at_def]) >>
  `storage_trace_domain cx st0 es_end.storage_trace` by
    (CCONTR_TAC >>
     metis_tac[gasStorageTheory.gas_bad_storage_at_counted_prefix]) >>
  `?H2. valid_horizon cx st0 H2 es_end.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  simp[gas_summary_at_def]
  >- suspend "rhs_normal" >>
  `expr_exit res r` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_exit _ _`
       (qspec_then `H2` mp_tac) >> simp[]) >>
  `?ex. res = INR ex` by (Cases_on `res` >> fs[expr_exit_def]) >> gvs[] >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >> conj_tac
  >- (irule stmtSimAugAssignStorageTheory.augassign_toplevel_rhs_exception_exec >> metis_tac[]) >>
  disj2_tac >> simp[] >> rpt strip_tac >> simp[stmt_exit_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_augassign_toplevel_mem[rhs_normal]:
  gvs[] >> rename1 `gas_marked_exec _ _ _ _ _ _ ee (OK u)` >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `H2` mp_tac) >> impl_tac >- simp[] >>
  strip_tac >> gvs[] >>
  `bind (eval_expr cx e) (read_result cx)
     ((es with storage_trace :=
         es.storage_trace ++ [StorageRoot tr slot tvt])
      with gas_obs := gas_explicit marks t.vs_gas_readings) =
       (INL v, ee with gas_obs := [])` by
    (drule gas_marked_exec_observation >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H (es.storage_trace ++ [StorageRoot tr slot tvt])` by
    (rpt strip_tac >>
     qpat_x_assum `bind (eval_expr cx e) _ _ = _` assume_tac >>
     drule_at (Pos (el 2)) vyperStorageFootprintTheory.valid_horizon_frame >>
     simp[stmtSimAugAssignTheory.augassign_rhs_trace_frame]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post H ctx func cenv cx e
         ((es with storage_trace :=
             es.storage_trace ++ [StorageRoot tr slot tvt])
          with gas_obs := []) s1 s2 t (ee with gas_obs := []) v rhs_op u` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `valid_horizon cx st0 H2 (es.storage_trace ++ [StorageRoot tr slot tvt])` by
    metis_tac[] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with <|gas_obs := gas_explicit marks t.vs_gas_readings;
                storage_trace :=
                  es.storage_trace ++ [StorageRoot tr slot tvt]|>) =
       (INL v, ee with gas_obs := [])` by
    (qpat_x_assum `bind (eval_expr cx e) (read_result cx) _ = _` mp_tac >>
     simp[]) >>
  `expr_res_ok (bop_result cx ty bop [ty; expr_type e] v0 v
     (ee with gas_obs := []))` by
    (drule_all stmtSimAugAssignStorageTheory.augassign_toplevel_binop_admissible >>
     simp[]) >>
  `well_formed_type_value tvt` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `value_has_type tvt v0` by
    metis_tac[read_storage_slot_success_type] >>
  `word_value v0` by metis_tac[word_value_type_typed] >>
  `type_bits ty MOD 8 = 0` by metis_tac[well_formed_type_bits] >>
  `expr_body_pre cenv cx env e
     (es with <|gas_obs := gas_explicit marks t.vs_gas_readings;
                storage_trace :=
                  es.storage_trace ++ [StorageRoot tr slot tvt]|>)` by
    simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >>
  strip_tac >> gvs[] >>
  rename1 `value_has_type etv v` >>
  drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
  `!n. expr_int_literal e = SOME n ==> v = IntV n` by
    metis_tac[eval_expr_int_literal_agrees] >>
  `(bop = ShL \/ bop = ShR ==> ?i. v = IntV i /\ 0 <= i)` by
    (disch_then (fn th =>
       qpat_x_assum `_ ==> shift_amount_ok e` (assume_tac o C MP th)) >>
     drule_all eval_expr_shift_amount >> simp[]) >>
  suspend "binop"
QED

Resume compile_augassign_toplevel_mem[binop]:
  `binop_frag_val_mem ctx func cenv cx bop ty ty NONE
     (if bop = Exp then expr_int_literal e else NONE)
     [ty; expr_type e] v0 v (ee with gas_obs := [])` by
    (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `ty`,
       `TopLevelName ty (src, id)`, `e`, `v0`, `v`, `ee with gas_obs := []`,
       `tvt`, `etv`] mp_tac binop_frag_typed_mem >>
     simp[vyperASTTheory.expr_type_def, expr_int_literal_def] >>
     disch_then irule >>
     strip_tac >> gvs[nonneg_int_literal_def, GSYM expr_int_literal_value] >>
     Cases_on `expr_int_literal e` >> gvs[]) >>
  `expr_post H2 ctx func cenv cx e
     ((es with storage_trace :=
         es.storage_trace ++ [StorageRoot tr slot tvt])
      with gas_obs := []) s1 s2 t (ee with gas_obs := []) v rhs_op u` by
    metis_tac[] >>
  `eval_operand (Var out) t = SOME (val_to_w256 v0)` by
    simp[typed_val_to_w256_word_value] >>
  `eval_operand rhs_op u = SOME (val_to_w256 v)` by
    (irule expr_val_rel_word >>
     fs[expr_post_def] >> goal_assum (drule_at Any) >>
     simp[word_value_type_word]) >>
  `eval_operand (Var out) u = SOME (val_to_w256 v0)` by
    (irule eval_operand_frame >> simp[] >>
     qexistsl_tac [`s1`, `t`] >> gvs[expr_post_def]) >>
  `not_fresh_at s2 out /\ local_ptrs_reserved cenv s2` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, local_ptrs_reserved_next_var] >>
  `~u.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `binop_frag_val_mem _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [binop_frag_val_mem_def, binop_frag_mem_def]) >>
  disch_then (qspecl_then [`st0`, `s2`, `s3`, `Var out`, `rhs_op`, `res_op`, `u`]
    mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac
      >- metis_tac[compile_lower_value_var] >>
      rpt strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
                      expr_post H _ _ _ _ e _ _ _ _ _ _ _ _`
        (drule_then mp_tac) >>
      simp[expr_post_def, stmt_state_rel_start_gas_obs]) >>
  strip_tac >- suspend "operator_normal" >> suspend "operator_exit"
QED

Resume compile_augassign_toplevel_mem[operator_normal]:
  gvs[] >> rename1 `eval_operand res_op s = SOME (val_to_w256 result)` >>
  `bop_result cx ty bop [ty; expr_type e] v0 v ee =
     case evaluate_binop
       (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
       tvt bop v0 v of
       INL x => INL x | INR err => INR (Error err)` by
    (irule bop_result_augassign >>
     metis_tac[word_value_not_bytes, word_value_type_typed]) >>
  `evaluate_binop
     (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
     tvt bop v0 v = INL result` by gvs[AllCaseEqs()] >>
  `value_has_type tvt result` by
    (mp_tac (Q.INST [`t1` |-> `ty`, `t2` |-> `expr_type e`,
       `tenv` |-> `get_tenv cx`, `result_tv` |-> `tvt`,
       `tv1` |-> `tvt`, `tv2` |-> `etv`, `tv` |-> `tvt`,
       `v1` |-> `v0`, `v2` |-> `v`, `v` |-> `result`,
       `u` |-> `case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u`]
       well_typed_binop_success_type) >> simp[]) >>
  `type_slot_size tvt = 1` by metis_tac[word_type_slot_size] >>
  `eval_operand res_op s = SOME (typed_val_to_w256 tvt result)` by
    simp[typed_val_to_w256_word_value] >>
  `encode_value tvt result = SOME [(0, typed_val_to_w256 tvt result)]` by
    metis_tac[encode_value_word_typed] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) s /\
       storage_well_formed_on cx (ee with gas_obs := []) (FST H)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ s /\ _`
       (qspec_then `H` mp_tac) >>
     simp[stmt_state_rel_start_gas_obs]) >>
  `stmt_state_rel H2 ctx func cenv cx (ee with gas_obs := []) s` by
    metis_tac[] >>
  `~s.vs_call_ctx.cc_static /\ ~cx.txn.is_static` by
    fs[stmt_state_rel_def, state_rel_def] >>
  Cases_on `write_storage_slot cx tr (n2w slot) tvt result
    (ee with gas_obs := [])` >>
  rename1 `_ = (wres, fin)` >>
  `wres = INL ()` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     simp[write_storage_slot_eq]) >>
  pop_assum SUBST_ALL_TAC >>
  `fin.gas_obs = [] /\ fin.scopes = ee.scopes` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     simp[write_storage_slot_eq] >> Cases_on `tr` >>
     Cases_on `cx.txn.is_static` >>
     simp[set_storage_def] >> strip_tac >> gvs[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  suspend "store"
QED

Resume compile_augassign_toplevel_mem[store]:
  mp_tac (Q.SPECL [`ctx`, `func`, `tr`, `n2w slot`, `res_op`,
    `typed_val_to_w256 tvt result`, `s`, `s3`, `sb`] assign_storage_store_path_mem) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `last` strip_assume_tac) >>
  `gas_marked_path T ctx func u 0 (OK last)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `gas_marked_exec T (ctx,func) (bind (eval_expr cx e) (read_result cx))
     ((es with storage_trace :=
         es.storage_trace ++ [StorageRoot tr slot tvt])
      with gas_obs := [],t) marks (INL v) ee (OK u)` by
    (qpat_assum `gas_marked_exec _ _ (bind (eval_expr _ _) _) _ _ _ _ _`
       mp_tac >> simp[]) >>
  `gas_marked_exec T (ctx,func)
     (bind (lift_sum (evaluate_binop
       (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
       tvt bop v0 v)) (write_storage_slot cx tr (n2w slot) tvt))
     (ee with gas_obs := [],u) [] (INL ()) fin (OK last)` by
    (irule stmtSimAugAssignStorageTheory.augassign_storage_continuation_exec >>
     simp[lift_sum_def, bind_def, return_def]) >>
  `gas_marked_exec T (ctx,func)
     (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e))
     (es,s0) marks (INL ()) fin (OK last)` by
    (irule stmtSimAugAssignStorageTheory.augassign_toplevel_rhs_normal_exec >> metis_tac[]) >>
  qexistsl_tac [`INL ()`, `fin`, `OK last`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disj1_tac >> qexists_tac `last` >> conj_tac >- REFL_TAC >>
  qx_gen_tac `H` >> strip_tac >>
  suspend "post"
QED

Resume compile_augassign_toplevel_mem[post]:
  `valid_horizon cx st0 H ee.storage_trace` by
    (qpat_x_assum `valid_horizon _ _ H _` mp_tac >> simp[]) >>
  `valid_horizon cx st0 H (es.storage_trace ++ [StorageRoot tr slot tvt])` by
    metis_tac[] >>
  `MEM (tr,n2w slot,tvt) (FST H) /\ regions_consistent (FST H)` by
    (qpat_assum `!H. valid_horizon _ _ H (_ ++ _) ==> valid_horizon _ _ H _ /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) s /\
   storage_well_formed_on cx (ee with gas_obs := []) (FST H)` by metis_tac[] >>
  `!u' sto. storage_dead H tr (update_storage (n2w slot) u' sto) =
            storage_dead H tr sto` by
    (rpt gen_tac >> irule storage_dead_update_word_region >> simp[]) >>
  qspecl_then [`H`, `func`, `cenv`, `cx`, `ee with gas_obs := []`, `s`, `tr`,
    `n2w slot`, `tvt`, `result`, `typed_val_to_w256 tvt result`,
    `INL ()`, `fin`, `ctx`] mp_tac stmt_state_rel_write_storage_word >>
  impl_tac >- simp[] >> strip_tac >>
  `storage_well_formed_on cx fin (FST H)` by
    (`well_formed_type_value tvt` by
       metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
     metis_tac[vyperStorageFootprintTheory.typed_write_preserves_storage_well_formed_on]) >>
  `sa.cs_next_var <= s1.cs_next_var` by
    (qpat_x_assum `emit_op _ _ sa = _` mp_tac >>
     disch_then (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
     simp[]) >>
  `s3.cs_next_var <= sb.cs_next_var` by
    (qpat_x_assum `emit_void _ _ s3 = _` mp_tac >>
     disch_then (strip_assume_tac o MATCH_MP emitted_insts_emit_void) >>
     simp[]) >>
  `~block_is_terminated sb` by
    (qpat_x_assum `emit_void _ _ s3 = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> Cases_on `s3.cs_current_insts` >> Cases_on `tr` >>
     gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
         venomInstTheory.mk_inst_def, is_terminator_def]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x last = SOME w` by
    (rpt strip_tac >>
     `lookup_var x t = SOME w` by metis_tac[] >>
     `not_fresh_at s1 x /\ not_fresh_at s2 x` by
       metis_tac[freshWritesTheory.not_fresh_at_mono,
                 arithmeticTheory.LESS_EQ_TRANS] >>
     `lookup_var x u = SOME w` by
       (qpat_x_assum `expr_post H2 _ _ _ _ e _ _ _ _ _ _ _ _` mp_tac >>
        simp[expr_post_def]) >>
     metis_tac[]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP last.vs_allocas aid = SOME b` by
    (rpt strip_tac >>
     `FLOOKUP u.vs_allocas aid = SOME b` by
       (qpat_x_assum `expr_post H2 _ _ _ _ e _ _ _ _ _ _ _ _` mp_tac >>
        simp[expr_post_def] >> metis_tac[]) >>
     metis_tac[]) >>
  `s0.vs_alloca_next <= last.vs_alloca_next` by decide_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by decide_tac >>
  qexists_tac `cenv` >> rpt conj_tac
  >- simp[stmt_lands_def]
  >- first_assum ACCEPT_TAC
  >- simp[]
  >- simp[cenv_top_ext_refl]
  >- (Cases_on `tr` >>
      gvs[stmt_state_rel_inst_idx, sstore_def, tstore_def, LET_THM])
  >- (qpat_x_assum `storage_well_formed_on cx fin (FST H)` mp_tac >> simp[])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (irule return_buf_frame_frame >>
      qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
QED

Resume compile_augassign_toplevel_mem[operator_exit]:
  `bop_result cx ty bop [ty; expr_type e] v0 v ee =
     case evaluate_binop
       (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
       tvt bop v0 v of
       INL x => INL x | INR err => INR (Error err)` by
    (irule bop_result_augassign >>
     metis_tac[word_value_not_bytes, word_value_type_typed]) >>
  Cases_on `evaluate_binop
       (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
       tvt bop v0 v`
  >- (gvs[] >> fs[expr_exit_def, exit_result_def]) >>
  gvs[] >>
  `gas_marked_exec T (ctx,func) (bind (eval_expr cx e) (read_result cx))
     ((es with storage_trace :=
         es.storage_trace ++ [StorageRoot tr slot tvt])
      with gas_obs := [],t) marks (INL v) ee (OK u)` by
    (qpat_assum `gas_marked_exec _ _ (bind (eval_expr _ _) _) _ _ _ _ _`
       mp_tac >> simp[]) >>
  `gas_marked_exec T (ctx,func)
     (bind (lift_sum (evaluate_binop
       (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
       tvt bop v0 v)) (write_storage_slot cx tr (n2w slot) tvt))
     (ee with gas_obs := [],u) [] (INR (Error y)) (ee with gas_obs := []) r` by
    (irule stmtSimAugAssignStorageTheory.augassign_storage_continuation_exec >>
     simp[lift_sum_def, bind_def, raise_def]) >>
  qexistsl_tac [`INR (Error y)`, `ee with gas_obs := []`, `r`] >>
  conj_tac
  >- (irule stmtSimAugAssignStorageTheory.augassign_toplevel_rhs_normal_exec >> metis_tac[]) >>
  disj2_tac >> simp[stmt_exit_def] >>
  metis_tac[expr_exit_INR_type]
QED

Finalise compile_augassign_toplevel_mem

Theorem body_augassign_toplevel_word_mem:
  !cx ty src id bop e d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_stmt_safe tops (AugAssign ty (TopLevelNameTarget (src,id)) bop e) /\
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (TopLevelNameTarget (src, id)) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_mem_ok cx e) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (AugAssign ty (TopLevelNameTarget (src, id)) bop e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AugAssign ty (TopLevelNameTarget (src, id)) bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src, id)) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty (TopLevelNameTarget (src, id)) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    supported_scalar_target tops (src, id) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty (TopLevelNameTarget (src, id)) bop e))
      (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) es
Proof
  rpt strip_tac >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  `!ts vis mut id ty init.
     MEM (VariableDecl vis mut id ty init) ts /\
     (mut = Storage \/ mut = Transient) ==>
     find_var_decl_by_name id ts <> NONE` by
    (Induct >> simp[] >> Cases >> rw[find_var_decl_by_name_def] >>
     metis_tac[]) >>
  `src = NONE /\ find_var_decl_by_name id tops <> NONE /\
   ?vis mut dty slot. MEM (VariableDecl vis mut id dty slot) tops /\
     is_word_type dty` by
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
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE, id) =
     build_var_type_map tops (NONE, id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `type_place_target env (TopLevelNameTarget (NONE, id)) = SOME (Type ty) /\
   well_typed_expr env e /\ assignable_type env.type_defs ty /\
   well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
   (bop = Exp ==> nonneg_int_literal e) /\
   (bop = ShL ==> shift_amount_ok e) /\ (bop = ShR ==> shift_amount_ok e)` by
    (gvs[type_stmt_def, well_typed_target_def, DISJ_IMP_THM, AllCaseEqs()] >>
     metis_tac[stmtSimAugAssignTheory.augassign_operand_ok_operands]) >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (qpat_x_assum `env_consistent _ _ _`
        (strip_assume_tac o REWRITE_RULE [env_consistent_def,
           env_context_consistent_def]) >>
      first_x_assum drule >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  rename1 `find_var_decl_by_name id tops = SOME (StorageVarDecl tr _, _)` >>
  `dty = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `lookup_var_slot_from_layout _ _ _ _ = SOME slot'` >>
  rename1 `evaluate_type _ ty = SOME tvt` >>
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
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supportedExprTraverseTheory.supported_expr_exists_def,
         int_calls_stmt_def, int_calls_expr_def, body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  `?v0. read_storage_slot cx tr (n2w slot') tvt es = (INL v0, es)` by
    (irule toplevel_storage_read_decodes >>
     gvs[expr_sim_inv_def] >> metis_tac[]) >>
  drule_all stmtSimAugAssignStorageTheory.eval_target_place_toplevel >> strip_tac >>
  `body_expr_mem_ok cx e` by
    (first_x_assum irule >> simp[read_place_def] >> metis_tac[]) >>
  `!gs. expr_sim_mem ctx func cenv cx ty e
     ((es with storage_trace :=
         es.storage_trace ++ [StorageRoot tr slot' tvt])
      with gas_obs := gs)` by
    (gen_tac >>
     qpat_x_assum `body_expr_mem_ok cx e`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [body_expr_mem_ok_def]) >>
     disch_then (qspecl_then [`tops`, `ctx`, `func`, `cenv`, `env`, `ty`,
       `(es with storage_trace :=
           es.storage_trace ++ [StorageRoot tr slot' tvt])
        with gas_obs := gs`] mp_tac) >>
     impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> simp[]) >>
     simp[]) >>
  irule compile_augassign_toplevel_mem >> simp[DISJ_IMP_THM] >>
  conj_tac
  >- (gen_tac >> first_x_assum (qspec_then `gs` mp_tac) >> simp[]) >>
  qexists_tac `env` >> simp[] >>
  metis_tac[assignable_type_well_formed]
QED
