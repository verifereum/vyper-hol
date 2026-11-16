Theory bodyMemPopToplevelSim
Ancestors
  bodyMemPopToplevelPath bodyUnopFragMemory storageCopyGasPath
  exprSimMemDefs exprSimPopStorage
  exprSimDefs exprSimProps loweringPosts exprSimLen exprSimTopLevelProps
  exprSimHyps exprSimHypsDefs exprLoweringProps exprLowering compileEnv loweringStateRelDefs
  vyperInterpreter vyperStorageBackend vyperStorageLayoutSafety vyperStorage
  vyperState venomState venomExecSemantics venomInst accountsRelProps
  gasOutcome gasSummary gasStorage fragGasMode fragGasPathMem
  vyperStorageTrace vyperStorageFootprint vyperFiniteStoragePreservation
  vyperTypeValues
  list words finite_map fragExec

Theorem pop_mem_updated_state_rel_cursor:
  stmt_state_rel H ctx func cenv cx es s /\
  MEM (tr,w,ArrayTV tv (Dynamic n)) (FST H) /\
  local_ptrs_reserved cenv sa /\
  u = (if tr then tstore w (n2w (w2n (lookup_storage w (get_storage cx es tr)) - 1)) s
       else sstore w (n2w (w2n (lookup_storage w (get_storage cx es tr)) - 1)) s)
        with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q s) ==>
  stmt_state_rel H ctx func cenv cx
    (set_storage cx es tr
      (apply_writes w [(0,n2w (w2n (lookup_storage w (get_storage cx es tr)) - 1))]
        (get_storage cx es tr))) u
Proof
  strip_tac >>
  `stmt_state_rel H ctx func cenv cx es (s with vs_inst_idx := u.vs_inst_idx)` by
    metis_tac[stmt_state_rel_inst_idx] >>
  `!q. not_fresh_at sa q ==>
       lookup_var q u = lookup_var q (s with vs_inst_idx := u.vs_inst_idx)` by
    (simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `u = (if tr then tstore w (n2w (w2n (lookup_storage w (get_storage cx es tr)) - 1))
                     (s with vs_inst_idx := u.vs_inst_idx)
       else sstore w (n2w (w2n (lookup_storage w (get_storage cx es tr)) - 1))
                     (s with vs_inst_idx := u.vs_inst_idx))
        with vs_vars := u.vs_vars` by
    (Cases_on `tr` >> gvs[tstore_def, sstore_def, LET_THM]) >>
  metis_tac[pop_storage_updated_state_rel]
QED

Theorem pop_mem_positive_holds_cursor:
  stmt_state_rel H ctx func cenv cx es s /\
  regions_consistent (FST H) /\ storage_well_formed_on cx es (FST H) /\
  MEM (tr,w,ArrayTV tv (Dynamic n)) (FST H) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  len = w2n (lookup_storage w (get_storage cx es tr)) /\ 0 < len /\
  elem = w + n2w (1 + (len - 1) * type_slot_size tv) /\
  u = (if tr then tstore w (n2w (len - 1)) s else sstore w (n2w (len - 1)) s)
        with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> ==>
  storage_holds cx tr ann (PlaceR (StoragePlace tr elem tv)) elem
    (set_storage cx es tr (apply_writes w [(0,n2w (len - 1))] (get_storage cx es tr))) u
Proof
  strip_tac >>
  `stmt_state_rel H ctx func cenv cx es (s with vs_inst_idx := u.vs_inst_idx)` by
    metis_tac[stmt_state_rel_inst_idx] >>
  `u = (if tr then tstore w (n2w (len - 1)) (s with vs_inst_idx := u.vs_inst_idx)
       else sstore w (n2w (len - 1)) (s with vs_inst_idx := u.vs_inst_idx))
        with vs_vars := u.vs_vars` by
    (Cases_on `tr` >> gvs[tstore_def, sstore_def, LET_THM]) >>
  metis_tac[pop_storage_positive_holds]
QED

Theorem compile_pop_storage_normalized_vv_sim_mem:
  expr_sim_pre cenv cx env (Pop ann (TopLevelNameTarget (src,id))) es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (ArrayT ann (Dynamic n)), name) /\
  lookup_var_slot_from_layout cx tr src name = SOME slot /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  evaluate_type (get_tenv cx) (ArrayT ann (Dynamic n)) = SOME (ArrayTV tv (Dynamic n)) ==>
  expr_vv_sim_mem ctx func cenv cx ty (Pop ann (TopLevelNameTarget (src,id))) es
Proof
  rw[expr_vv_sim_mem_def] >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_initial >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by metis_tac[] >>
  `expr_sim_inv cenv cx env es` by fs[expr_sim_pre_def] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
   alloca_inv s0 /\ s0.vs_call_ctx.cc_static = cx.txn.is_static` by
    (qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE
         [stmt_state_rel_def, state_rel_def, call_ctx_rel_def]) >>
     asm_rewrite_tac[]) >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  drule_all pop_storage_compiler_facts >> strip_tac >>
  `elem_size_in_location cenv (if tr then LocTransient else LocStorage) ann =
    type_slot_size tv` by (irule pop_storage_element_size >> metis_tac[]) >>
  drule_all compile_expr_pop_storage >> strip_tac >> gvs[] >>
  Cases_on `compile_dynarray_pop (Lit (n2w slot)) 1 (type_slot_size tv)
    cenv.ce_is_ctor cenv.ce_imm_alloca (if tr then LocTransient else LocStorage) sa` >>
  gvs[] >>
  reverse (Cases_on `storage_trace_domain cx st0
    (es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))])`)
  >- (Cases_on `cx.txn.is_static`
      >- (drule_all eval_pop_storage_static >> strip_tac >>
          rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
          simp[gasStorageTheory.gas_bad_storage_at_def, LET_THM, COND_RAND] >>
          rw[]) >>
      drule_all eval_pop_storage >> strip_tac >>
      rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gasStorageTheory.gas_bad_storage_at_def, LET_THM, COND_RAND] >>
      rw[]) >>
  `?H1. valid_horizon cx st0 H1 (es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))])` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `valid_horizon cx st0 H1 es.storage_trace /\
   storage_observations_ok cx H1 (es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))])` by
    (pop_assum mp_tac >> simp[vyperStorageFootprintTheory.valid_horizon_def]) >>
  pop_assum strip_assume_tac >>
  `MEM (tr,n2w slot,ArrayTV tv (Dynamic n)) (FST H1)` by
    metis_tac[vyperFiniteStoragePreservationTheory.storage_observations_ok_root,
              listTheory.MEM_APPEND, listTheory.MEM] >>
  `stmt_state_rel H1 ctx func cenv cx es s0` by metis_tac[] >>
  `(if tr then tload (n2w slot) s0 else sload (n2w slot) s0) =
     lookup_storage (n2w slot) (get_storage cx es tr)` by
    (irule pop_declared_header_load >> metis_tac[]) >>
  Cases_on `lookup_storage (n2w slot) (get_storage cx es tr) = 0w`
  >- (`!tail. eval_expr cx (Pop ann (TopLevelNameTarget (src,id)))
          (es with gas_obs := tail) =
        (INR (Error (RuntimeError "pop empty storage array")),
         (es with storage_trace := es.storage_trace ++
            [StorageRoot tr slot (ArrayTV tv (Dynamic n))]) with gas_obs := tail)` by
        (gen_tac >> Cases_on `cx.txn.is_static`
         >- (drule_all eval_pop_storage_static >>
             simp[pop_storage_gas_obs, evaluation_state_component_equality]) >>
         drule_all eval_pop_storage >>
         simp[LET_THM, pop_storage_gas_obs, evaluation_state_component_equality]) >>
      `(if tr then tload (n2w slot) s0 else sload (n2w slot) s0) = 0w` by
        metis_tac[] >>
      drule_all dynarray_pop_storage_empty_path_mem >>
      disch_then (qspec_then `ctx` strip_assume_tac) >>
      rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >>
      disj2_tac >> disj1_tac >> rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR (Error (RuntimeError "pop empty storage array"))`,
                    `es with storage_trace := es.storage_trace ++
                       [StorageRoot tr slot (ArrayTV tv (Dynamic n))]`,
                    `Abort a t`] >>
      conj_tac
      >- (rewrite_tac[gas_marked_exec_def] >> conj_tac
          >- (gen_tac >>
              gvs[pop_storage_gas_obs, evaluation_state_component_equality])
          >- (qpat_x_assum `gas_path_mem _ _ _ _ _` mp_tac >>
              simp[gas_marked_path_def])) >>
      disj2_tac >> simp[exit_result_def, expr_exit_def, halt_exit_def]) >>
  suspend "positive"
QED
Resume compile_pop_storage_normalized_vv_sim_mem[positive]:
  `(if tr then tload (n2w slot) s0 else sload (n2w slot) s0) <> 0w` by
    metis_tac[] >>
  Cases_on `cx.txn.is_static`
  >- suspend "static" >>
  `~s0.vs_call_ctx.cc_static` by simp[] >>
  drule_all eval_pop_storage >> strip_tac >>
  drule_all dynarray_pop_storage_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule dynarray_pop_storage_shape >> strip_tac >> gvs[] >>
  `0 < w2n (lookup_storage (n2w slot) (get_storage cx es tr))` by
    (Cases_on `lookup_storage (n2w slot) (get_storage cx es tr)` >> gvs[]) >>
  `lookup_storage (n2w slot) (get_storage cx es tr) - 1w =
   n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1)` by
    (Cases_on `lookup_storage (n2w slot) (get_storage cx es tr)` >>
     gvs[GSYM n2w_sub]) >>
  `t = (if tr then tstore (n2w slot)
       (n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1)) s0
     else sstore (n2w slot)
       (n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1)) s0)
     with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>` by
    (Cases_on `tr` >> fs[] >> metis_tac[]) >>
  `lookup_var x6 t = SOME (n2w slot + n2w
    (1 + (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1) * type_slot_size tv))` by
    (fs[eval_operand_def] >>
     pure_asm_rewrite_tac [] >>
     pure_rewrite_tac[word_add_n2w, word_mul_n2w, arithmeticTheory.ADD_ASSOC] >>
     AP_TERM_TAC >>
     once_rewrite_tac[arithmeticTheory.MULT_COMM] >> decide_tac) >>
  qmatch_asmsub_abbrev_tac `lookup_var x6 t = SOME elem` >>
  `elem = n2w slot + n2w (1 + (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1) * type_slot_size tv)` by
    simp[Abbr `elem`] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (PlaceR (StoragePlace tr elem tv))`,
    `set_storage cx es tr (apply_writes (n2w slot) [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))] (get_storage cx es tr)) with storage_trace := es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))]`,
    `OK t`] >>
  conj_tac
  >- (rewrite_tac[gas_marked_exec_def] >> conj_tac
      >- (gen_tac >>
          gvs[pop_storage_gas_obs, evaluation_state_component_equality,
              Abbr `elem`])
      >- (qpat_x_assum `gas_path_mem _ _ _ _ _` mp_tac >>
          simp[gas_marked_path_def])) >>
  disj1_tac >> qexists_tac `t` >> simp_tac (srw_ss()) [] >>
  gen_tac >> strip_tac >>
  `valid_horizon cx st0 H es.storage_trace /\ regions_consistent (FST H) /\
   storage_observations_ok cx H (es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))])` by
    (pop_assum mp_tac >> simp[vyperStorageFootprintTheory.valid_horizon_def]) >>
  pop_assum strip_assume_tac >>
  `MEM (tr,n2w slot,ArrayTV tv (Dynamic n)) (FST H)` by
    metis_tac[vyperFiniteStoragePreservationTheory.storage_observations_ok_root,
              listTheory.MEM_APPEND, listTheory.MEM] >>
  `stmt_state_rel H ctx func cenv cx es s0 /\
   storage_well_formed_on cx es (FST H)` by metis_tac[] >>
  pop_assum strip_assume_tac >>
  `well_formed_type_value (ArrayTV tv (Dynamic n))` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `storage_well_formed_on cx (set_storage cx es tr (apply_writes (n2w slot) [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))] (get_storage cx es tr))) (FST H)` by
    metis_tac[pop_storage_end_storage_wf] >>
  `storage_well_formed_on cx
     ((set_storage cx es tr (apply_writes (n2w slot) [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))] (get_storage cx es tr)) with storage_trace := es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))]) with gas_obs := []) (FST H)` by
    (`((set_storage cx es tr (apply_writes (n2w slot) [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))] (get_storage cx es tr)) with storage_trace := es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))]) with gas_obs := []).accounts =
      (set_storage cx es tr (apply_writes (n2w slot) [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))] (get_storage cx es tr))).accounts /\
      ((set_storage cx es tr (apply_writes (n2w slot) [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))] (get_storage cx es tr)) with storage_trace := es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))]) with gas_obs := []).tStorage =
      (set_storage cx es tr (apply_writes (n2w slot) [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))] (get_storage cx es tr))).tStorage` by simp[] >>
     metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends]) >>
  `stmt_state_rel H ctx func cenv cx (set_storage cx es tr (apply_writes (n2w slot) [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))] (get_storage cx es tr))) t` by
    (irule pop_mem_updated_state_rel_cursor >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx
     ((set_storage cx es tr (apply_writes (n2w slot) [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))] (get_storage cx es tr)) with storage_trace := es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))]) with gas_obs := []) t` by
    (irule pop_ssr_gas_obs >> simp[] >> first_assum ACCEPT_TAC) >>
  `storage_holds cx tr ann (PlaceR (StoragePlace tr elem tv)) elem (set_storage cx es tr (apply_writes (n2w slot) [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))] (get_storage cx es tr))) t` by
    (irule pop_mem_positive_holds_cursor >> metis_tac[]) >>
  `storage_holds cx tr ann (PlaceR (StoragePlace tr elem tv)) elem
     ((set_storage cx es tr (apply_writes (n2w slot) [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))] (get_storage cx es tr)) with storage_trace := es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))]) with gas_obs := []) t` by
    (irule pop_storage_holds_end >> first_assum ACCEPT_TAC) >>
  `((set_storage cx es tr (apply_writes (n2w slot) [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))] (get_storage cx es tr)) with storage_trace := es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))]) with gas_obs := []).scopes = es.scopes` by
    (Cases_on `tr` >> simp[vyperStorageBackendTheory.set_storage_def]) >>
  `!id path. PlaceR (StoragePlace tr elem tv) <> PlaceR (MemoryPlace id path)` by
    simp[] >>
  rpt conj_tac
  >- (irule pop_storage_vv_post >> rpt conj_tac >> metis_tac[])
  >- (irule vv_store_bound_nonmem >> Cases_on `tr` >> simp[contextTheory.mk_ptr_def])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >>
  qpat_x_assum `t.vs_alloca_next = _`
    (fn th => rewrite_tac[th, arithmeticTheory.LESS_EQ_REFL])
QED

Resume compile_pop_storage_normalized_vv_sim_mem[static]:
  `s0.vs_call_ctx.cc_static` by simp[] >>
  drule dynarray_pop_storage_shape >> strip_tac >> gvs[] >>
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0]` by fs[ALL_DISTINCT] >>
  `?u. run_inst_seq (emitted_insts sa r) s0 = Abort ExHalt_abort u` by
    (simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
     irule dynarray_pop_storage_run_static >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa r) s0` by
    (irule dynarray_pop_storage_mem_ok >> goal_assum (drule_at Any)) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) (emitted_insts sa r)` by
    (irule dynarray_pop_storage_opcodes >> goal_assum (drule_at Any)) >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa r)
          (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions)` by
    (irule storage_copy_code_prefix >>
     simp[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  drule_at (Pat `run_inst_seq _ _ = Abort _ _`) run_inst_seq_abort_zero_path_mem >>
  disch_then (qspecl_then [`ctx`,`func`,`bb`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all eval_pop_storage_static >> strip_tac >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "write in static context"))`,
    `es with storage_trace := es.storage_trace ++
       [StorageRoot tr slot (ArrayTV tv (Dynamic n))]`,
    `Abort ExHalt_abort (u with vs_inst_idx := j)`] >>
  simp[gas_marked_exec_def, exit_result_def, expr_exit_def, halt_exit_def,
       pop_storage_gas_obs, evaluation_state_component_equality]
QED

Finalise compile_pop_storage_normalized_vv_sim_mem
