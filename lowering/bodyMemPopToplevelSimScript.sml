Theory bodyMemPopToplevelSim
Ancestors
  bodyMemPopToplevelPath exprSimMemDefs exprSimPopStorage
  exprSimDefs exprSimProps loweringPosts exprSimLen exprSimTopLevelProps
  exprSimHyps exprSimHypsDefs exprLoweringProps exprLowering compileEnv loweringStateRelDefs
  vyperInterpreter vyperStorageBackend vyperStorageLayoutSafety vyperStorage
  vyperState venomState venomExecSemantics venomInst accountsRelProps
  gasOutcome gasSummary fragGasMode fragGasPathMem
  list words finite_map fragExec

Theorem pop_mem_updated_state_rel_cursor:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid id [] = SOME (tr,w,ArrayTV tv (Dynamic n)) /\
  local_ptrs_reserved cenv sa /\
  u = (if tr then tstore w (n2w (w2n (lookup_storage w (get_storage cx es tr)) - 1)) s
       else sstore w (n2w (w2n (lookup_storage w (get_storage cx es tr)) - 1)) s)
        with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q s) ==>
  stmt_state_rel ctx func cenv cx
    (set_storage cx es tr
      (apply_writes w [(0,n2w (w2n (lookup_storage w (get_storage cx es tr)) - 1))]
        (get_storage cx es tr))) u
Proof
  strip_tac >> irule pop_storage_updated_state_rel >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`s with vs_inst_idx := u.vs_inst_idx`, `sa`] >>
  simp[stmt_state_rel_inst_idx, lookup_var_def] >>
  Cases_on `tr` >> gvs[tstore_def, sstore_def, LET_THM]
QED

Theorem pop_mem_positive_holds_cursor:
  expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid id [] = SOME (tr,w,ArrayTV tv (Dynamic n)) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  len = w2n (lookup_storage w (get_storage cx es tr)) /\ 0 < len /\
  elem = w + n2w (1 + (len - 1) * type_slot_size tv) /\
  u = (if tr then tstore w (n2w (len - 1)) s else sstore w (n2w (len - 1)) s)
        with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> ==>
  storage_holds cx tr ann (PlaceR (StoragePlace tr elem tv)) elem
    (set_storage cx es tr (apply_writes w [(0,n2w (len - 1))] (get_storage cx es tr))) u
Proof
  strip_tac >> irule pop_storage_positive_holds >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`cenv`, `ctx`, `env`, `func`, `s with vs_inst_idx := u.vs_inst_idx`] >>
  simp[stmt_state_rel_inst_idx] >>
  Cases_on `tr` >> gvs[tstore_def, sstore_def, LET_THM]
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
  `expr_sim_inv cenv cx env es` by fs[expr_sim_pre_def] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
   ~cx.txn.is_static /\ alloca_inv s0` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  drule_all pop_storage_compiler_facts >> strip_tac >>
  `elem_size_in_location cenv (if tr then LocTransient else LocStorage) ann =
    type_slot_size tv` by (irule pop_storage_element_size >> metis_tac[]) >>
  drule_all compile_expr_pop_storage >> strip_tac >> gvs[] >>
  Cases_on `compile_dynarray_pop (Lit (n2w slot)) 1 (type_slot_size tv)
    cenv.ce_is_ctor cenv.ce_imm_alloca (if tr then LocTransient else LocStorage) sa` >>
  gvs[] >>
  `declared_storage_region cx src id [] = SOME (tr,n2w slot,ArrayTV tv (Dynamic n))` by
    simp[declared_storage_region_def] >>
  drule_all pop_declared_header_load >> strip_tac >>
  drule_all eval_pop_storage >> strip_tac >>
  Cases_on `lookup_storage (n2w slot) (get_storage cx es tr) = 0w`
  >- (`(if tr then tload (n2w slot) s0 else sload (n2w slot) s0) = 0w` by simp[] >>
      drule_all dynarray_pop_storage_empty_path_mem >>
      disch_then (qspec_then `ctx` strip_assume_tac) >>
      simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR (Error (RuntimeError "pop empty storage array"))`,
                    `es`, `Abort a t`] >>
      simp[gas_marked_exec_def, gas_marked_path_def, exit_result_def,
           expr_exit_def, LET_THM, pop_storage_gas_obs]) >>
  suspend "positive"
QED
Resume compile_pop_storage_normalized_vv_sim_mem[positive]:
  `(if tr then tload (n2w slot) s0 else sload (n2w slot) s0) <> 0w` by simp[] >>
  `~s0.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
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
  qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ _ _ post _` >>
  `vv_post ctx func cenv cx (Pop ann (TopLevelNameTarget (src,id))) es sa r s0
    (set_storage cx es tr
      (apply_writes (n2w slot)
        [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))]
        (get_storage cx es tr)) with gas_obs := [])
    (PlaceR (StoragePlace tr elem tv))
    (LocatedValue ann (mk_ptr (Var x6) (if tr then LocTransient else LocStorage))) t` by
    (irule pop_storage_vv_post >> simp[] >>
     conj_tac
     >- (irule pop_mem_updated_state_rel_cursor >> metis_tac[]) >>
     irule pop_storage_holds_gas_obs >>
     irule pop_mem_positive_holds_cursor >>
     simp[Abbr `elem`] >> conj_tac
     >- metis_tac[] >>
     qexistsl_tac [`cenv`, `ctx`, `env`, `func`, `s0`] >> simp[] >>
     qpat_x_assum `t.vs_inst_idx = _` (fn th => once_rewrite_tac[GSYM th]) >>
     Cases_on `tr` >> fs[] >> first_assum ACCEPT_TAC) >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL (PlaceR (StoragePlace tr elem tv))`,
    `set_storage cx es tr (apply_writes (n2w slot)
       [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))]
       (get_storage cx es tr))`, `OK t`] >>
  simp[gas_marked_exec_def, gas_marked_path_def, LET_THM,
       pop_storage_gas_obs, Abbr `post`] >>
  conj_tac
  >- (simp[Abbr `elem`] >> AP_TERM_TAC >> AP_TERM_TAC >>
      once_rewrite_tac[arithmeticTheory.MULT_COMM] >> decide_tac) >>
  irule vv_store_bound_nonmem >> Cases_on `tr` >> simp[contextTheory.mk_ptr_def]
QED
Finalise compile_pop_storage_normalized_vv_sim_mem
