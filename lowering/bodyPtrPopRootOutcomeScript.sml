Theory bodyPtrPopRootOutcome
Ancestors
  bodyPtrPopRootEntry bodyPtrPopRootPost bodyPtrPopRootEndpoint bodyPtrPopZeroAbort
  bodyPtrPopCountedTransfer bodyPtrPopSliceTransfer bodyPtrPopReturned bodyPtrPopEmittedTransfer
  appendStorageGhostPtr appendStorageSourcePtr fragExec vyperStorage vyperValue venomExecSemantics
  exprSimPopStorage storageCopyGasPath bodyPtrDefs fragGasPathPtr
  exprSimDefs exprSimHypsDefs exprSimSource exprSimTopLevelProps exprLoweringProps compileEnv context venomState venomInst
  list rich_list vyperStorageLayoutSafety vyperStorageBackend

Theorem compile_pop_storage_normalized_ptr:
  expr_sim_pre cenv cx env (Pop ann (TopLevelNameTarget (src,id))) es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (ArrayT ann (Dynamic n)), name) /\
  lookup_var_slot_from_layout cx tr src name = SOME slot /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  evaluate_type (get_tenv cx) (ArrayT ann (Dynamic n)) = SOME (ArrayTV tv (Dynamic n)) ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann (TopLevelNameTarget (src,id))) es
Proof
  rw[expr_vv_sim_ptr_def] >>
  `expr_sim_inv cenv cx env es` by fs[expr_sim_pre_def] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
   ~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  drule_all pop_storage_compiler_facts >> strip_tac >>
  `elem_size_in_location cenv (if tr then LocTransient else LocStorage) ann =
    type_slot_size tv` by (irule pop_storage_element_size >> metis_tac[]) >>
  drule_all compile_expr_pop_storage >> strip_tac >> gvs[] >>
  Cases_on `compile_dynarray_pop (Lit (n2w slot)) 1 (type_slot_size tv)
    cenv.ce_is_ctor cenv.ce_imm_alloca (if tr then LocTransient else LocStorage) sa` >>
  drule dynarray_pop_storage_shape >> strip_tac >> gvs[] >>
  `declared_storage_region cx src id [] = SOME (tr,n2w slot,ArrayTV tv (Dynamic n))` by
    simp[declared_storage_region_def] >>
  drule_all pop_declared_header_load >> strip_tac >>
  drule_all eval_pop_storage >> strip_tac >>
  qpat_x_assum `!ty sa' ann'. _` kall_tac >>
  qpat_x_assum `FLOOKUP cenv.ce_module_vars _ = _` kall_tac >>
  qpat_x_assum `cenv.ce_hashmap_info _ = _` kall_tac >>
  qpat_x_assum `cenv.ce_module_var_type _ = _` kall_tac >>
  qspecl_then [`sa`, `r`, `func`] mp_tac storage_copy_code_prefix >>
  impl_tac >- simp[same_blocks_def, IS_PREFIX_APPEND] >> strip_tac >>
  `key_taint (if tr then tn0.t_trans else tn0.t_stor) (n2w slot) = {}` by
    (irule declared_header_key_taint_empty >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `s0` >>
     fs[ghost_inv_def, stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
        type_slot_size_def]) >>
  Cases_on `lookup_storage (n2w slot) (get_storage cx es tr) = 0w`
  >- suspend "empty" >> suspend "positive"
QED

Resume compile_pop_storage_normalized_ptr[empty]:
  `?a s'. run_inst_seq (emitted_insts sa r) s0 = Abort a s'` by
    (simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
     irule dynarray_pop_storage_run_empty >> simp[]) >>
  `?Gf tnf. inst_seq_ptr (cx_dead cx) 0 ctx func PG G0 tn0
    (emitted_insts sa r) s0 Gf tnf` by
    (simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
     irule_at Any (SRULE [APPEND] pop_root_slice_transfer_empty) >> simp[]) >>
  `?j. gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 0 Gf tnf
    (Abort a (s' with vs_inst_idx := j))` by
    (irule pop_root_abort_counted_zero >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "pop empty storage array"))`,
    `es`, `Gf`, `tnf`, `Abort a (s' with vs_inst_idx := j)`] >>
  simp[exit_result_def, expr_exit_def, get_storage_gas_obs, set_storage_gas_obs]
QED

Resume compile_pop_storage_normalized_ptr[positive]:
  `(if tr then tload (n2w slot) s0 else sload (n2w slot) s0) <> 0w` by simp[] >>
  `~s0.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0]` by simp[] >>
  drule_all dynarray_pop_storage_run >>
  disch_then (qspecl_then [`sa.cs_next_id`, `type_slot_size tv`] strip_assume_tac) >>
  `run_inst_seq (emitted_insts sa r) s0 = OK u` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6]` by simp[] >>
  drule_all pop_root_emitted_transfer_nonempty >>
  disch_then (qspecl_then [`func`, `PG`, `G0`, `cx_dead cx`] strip_assume_tac) >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 0 Gf tnf
    (OK (u with vs_inst_idx := s0.vs_inst_idx + 9))` by
    (irule pop_root_run_counted >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  suspend "endpoint"
QED

Resume compile_pop_storage_normalized_ptr[endpoint]:
  `!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q s0` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  qpat_x_assum `run_inst_seq (emitted_insts _ _) _ = _` kall_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` kall_tac >>
  qabbrev_tac `len = w2n (lookup_storage (n2w slot) (get_storage cx es tr))` >>
  `0 < len` by
    (unabbrev_all_tac >> Cases_on `lookup_storage (n2w slot) (get_storage cx es tr)` >> gvs[]) >>
  `lookup_storage (n2w slot) (get_storage cx es tr) - 1w = n2w (len - 1)` by
    (unabbrev_all_tac >> Cases_on `lookup_storage (n2w slot) (get_storage cx es tr)` >>
     gvs[GSYM wordsTheory.n2w_sub]) >>
  `u = (if tr then tstore (n2w slot) (n2w (len - 1)) s0
        else sstore (n2w slot) (n2w (len - 1)) s0) with vs_vars := u.vs_vars` by
    (Cases_on `tr` >> fs[] >> metis_tac[]) >>
  `u.vs_current_bb = s0.vs_current_bb` by
    (qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >>
     Cases_on `tr` >> simp[sstore_def, tstore_def]) >>
  qabbrev_tac `elem : bytes32 = n2w slot + n2w (1 + (len - 1) * type_slot_size tv)` >>
  `lookup_var x6 u = SOME elem` by
    (simp[Abbr `elem`] >> PURE_ASM_REWRITE_TAC [] >>
     pure_rewrite_tac[wordsTheory.word_add_n2w, wordsTheory.word_mul_n2w, arithmeticTheory.ADD_ASSOC] >>
     simp_tac (srw_ss()) [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM,
       arithmeticTheory.MULT_COMM]) >>
  suspend "post"
QED

Resume compile_pop_storage_normalized_ptr[post]:
  qabbrev_tac `ee = set_storage cx es tr
    (apply_writes (n2w slot) [(0,n2w (len - 1))] (get_storage cx es tr)) with gas_obs := []` >>
  `vv_post ctx func cenv cx (Pop ann (TopLevelNameTarget (src,id))) es sa r s0 ee
    (PlaceR (StoragePlace tr elem tv))
    (LocatedValue ann (mk_ptr (Var x6) (if tr then LocTransient else LocStorage))) u` by
    (simp[Abbr `ee`] >> irule pop_root_positive_post >>
     goal_assum (drule_at Any) >> simp[Abbr `len`, Abbr `elem`] >> metis_tac[]) >>
  `s0.vs_call_ctx.cc_address = cx.txn.target` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `ee.scopes = es.scopes` by simp[Abbr `ee`, set_storage_def] >>
  `ghost_kept cenv es sa G0 tn0 s0 Gf tnf` by
    (irule pop_root_endpoint_kept >> simp[] >> qexists_tac `xs` >> simp[]) >>
  `lookup_storage (n2w slot) (if tr then contract_transient s0 else contract_storage s0) =
   lookup_storage (n2w slot) (get_storage cx es tr)` by
    (Cases_on `tr` >> fs[tload_def, sload_def, contract_transient_def, contract_storage_def]) >>
  `ghost_inv d cenv cx ee Gf tnf u` by
    (irule pop_root_endpoint_ghost >>
     goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >> simp[] >>
     qexists_tac `xs ++ [x0;x1;x2;x3;x4;x5;x6]` >>
     simp[EVERY_APPEND, Abbr `len`, MEM_APPEND] >>
     rpt strip_tac >> fs[]) >>
  suspend "returned"
QED

Resume compile_pop_storage_normalized_ptr[returned]:
  `stor_taint_ok cx tn0 s0` by fs[ghost_inv_def] >>
  `ptr_vv_ok cx ann (PlaceR (StoragePlace tr elem tv))
    (LocatedValue ann (mk_ptr (Var x6) (if tr then LocTransient else LocStorage)))
    ee Gf tnf u` by
    (irule pop_declared_returned_place >> simp[] >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     simp[Abbr `len`, Abbr `elem`, eval_operand_def] >>
     qexistsl [`env`, `tn0`, `n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1)`] >>
     qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >>
     Cases_on `tr` >>
     fs[contract_transient_def, contract_storage_def, sstore_def, tstore_def,
        sload_def, tload_def, vfmStateTheory.lookup_account_def]) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl [`INL (PlaceR (StoragePlace tr elem tv))`, `ee`, `Gf`, `tnf`,
    `OK (u with vs_inst_idx := s0.vs_inst_idx + 9)`] >>
  simp[exit_result_def, contextTheory.mk_ptr_def, vyperASTTheory.expr_type_def,
    get_storage_gas_obs, set_storage_gas_obs] >>
  conj_tac
  >- (simp[Abbr `ee`, Abbr `elem`, NoAsms] >>
      simp_tac (srw_ss()) [arithmeticTheory.MULT_COMM, arithmeticTheory.ADD_COMM]) >>
  `ee with gas_obs := [] = ee` by simp[Abbr `ee`] >> simp[] >>
  conj_tac >- fs[contextTheory.mk_ptr_def] >>
  conj_tac
  >- (qpat_x_assum `ghost_inv d cenv cx ee Gf tnf u` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[ghost_inv_def, ptr_covers_def, stor_taint_ok_def, lookup_var_def] >>
      Cases_on `d` >- (simp[return_buf_ptr_def] >> metis_tac[]) >>
      PairCases_on `x` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def] >> metis_tac[]) >>
  Cases_on `tr` >> fs[ptr_vv_ok_def, contextTheory.mk_ptr_def, eval_operand_def, lookup_var_def]
QED

Finalise compile_pop_storage_normalized_ptr
