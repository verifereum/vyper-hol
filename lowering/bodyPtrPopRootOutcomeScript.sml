Theory bodyPtrPopRootOutcome
Ancestors
  bodyPtrPopRootEntry bodyPtrPopRootPost bodyPtrPopRootEndpoint bodyPtrPopZeroAbort
  bodyPtrPopCountedTransfer bodyPtrPopSliceTransfer bodyPtrPopReturned bodyPtrPopEmittedTransfer
  appendStorageGhostPtr stmtSimAppendStorageCompose fragExec vyperStorage vyperValue venomExecSemantics
  exprSimPopStorage storageCopyGasPath bodyPtrDefs fragGasPathPtr
  exprSimDefs exprSimHypsDefs exprSimSource exprSimTopLevelProps exprLoweringProps compileEnv loweringStateRelDefs context venomState venomInst
  list rich_list vyperStorageLayoutSafety vyperStorageBackend
  vyperStorageFootprint vyperFiniteStoragePreservation gasSummaryComposePtr gasStorage
  fragGasSeqPtr

(* Any horizon that observed the header root reads the header from the
   Venom backend and leaves the header key untainted. *)
Theorem pop_root_header_facts[local]:
  valid_horizon cx st0 H1
    (es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))]) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H) /\
     ghost_inv H d cenv cx es G0 tn0 s0) /\
  declared_storage_region cx src id [] = SOME (tr,n2w slot,ArrayTV tv (Dynamic n)) ==>
  (if tr then tload (n2w slot) s0 else sload (n2w slot) s0) =
    lookup_storage (n2w slot) (get_storage cx es tr) /\
  ~s0.vs_call_ctx.cc_static /\ s0.vs_call_ctx.cc_address = cx.txn.target /\
  key_taint (if tr then tn0.t_trans else tn0.t_stor) (n2w slot) = {}
Proof
  strip_tac >>
  `valid_horizon cx st0 H1 es.storage_trace /\
   storage_observations_ok cx H1
     (es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))])` by
    (qpat_x_assum `valid_horizon _ _ _ _` mp_tac >> simp[valid_horizon_def]) >>
  `MEM (StorageRoot tr slot (ArrayTV tv (Dynamic n)))
     (es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))])` by simp[] >>
  `MEM (tr,n2w slot,ArrayTV tv (Dynamic n)) (FST H1)` by
    (drule_all storage_observations_ok_root >> simp[]) >>
  `stmt_state_rel H1 ctx func cenv cx es s0 /\ ghost_inv H1 d cenv cx es G0 tn0 s0` by
    metis_tac[] >>
  `~s0.vs_call_ctx.cc_static /\ s0.vs_call_ctx.cc_address = cx.txn.target` by
    (qpat_x_assum `stmt_state_rel H1 _ _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def, state_rel_def, call_ctx_rel_def]) >>
  `stor_taint_ok H1 cx tn0 s0` by
    (qpat_x_assum `ghost_inv H1 _ _ _ _ _ _ _` mp_tac >> simp[ghost_inv_def]) >>
  `0 < type_slot_size (ArrayTV tv (Dynamic n))` by simp[type_slot_size_def] >>
  drule_all pop_declared_header_load >> strip_tac >>
  drule_all declared_header_key_taint_empty >> simp[]
QED

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
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gas_bad_storage_at_initial >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by
    (fs[vyperStorageFootprintTheory.storage_trace_domain_def] >> metis_tac[]) >>
  `expr_sim_inv cenv cx env es` by fs[expr_sim_pre_def] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\ ~cx.txn.is_static` by
    (`stmt_state_rel H0 ctx func cenv cx es s0` by metis_tac[] >>
     pop_assum mp_tac >> simp[stmt_state_rel_def, state_rel_def]) >>
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
  qpat_x_assum `!ty sa' ann'. _` kall_tac >>
  qpat_x_assum `FLOOKUP cenv.ce_module_vars _ = _` kall_tac >>
  qpat_x_assum `cenv.ce_hashmap_info _ = _` kall_tac >>
  qpat_x_assum `cenv.ce_module_var_type _ = _` kall_tac >>
  qspecl_then [`sa`, `r`, `func`] mp_tac storage_copy_code_prefix >>
  impl_tac >- simp[same_blocks_def, IS_PREFIX_APPEND] >> strip_tac >>
  Cases_on `lookup_storage (n2w slot) (get_storage cx es tr) = 0w`
  >- suspend "empty" >> suspend "positive"
QED

(* The horizon-independent run facts, read through any horizon that
   observed the header root. *)
Resume compile_pop_storage_normalized_ptr[empty]:
  `!tail. eval_expr cx (Pop ann (TopLevelNameTarget (src,id))) (es with gas_obs := gas_explicit [] s0.vs_gas_readings ++ tail) =
     (INR (Error (RuntimeError "pop empty storage array")),
      (es with storage_trace :=
         es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))])
        with gas_obs := tail)` by
    (gen_tac >> drule_all eval_pop_storage >>
     disch_then (fn th => simp[th, LET_THM, pop_storage_gas_obs,
       vyperStateTheory.evaluation_state_component_equality])) >>
  reverse (Cases_on `?H1. valid_horizon cx st0 H1
    (es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))])`)
  >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      qpat_x_assum `!tail. eval_expr _ _ _ = _`
        (mp_then Any mp_tac gas_bad_storage_at_no_horizon) >>
      impl_tac >- fs[] >> simp[]) >>
  suspend "root"
QED

Resume compile_pop_storage_normalized_ptr[root]:
  `(if tr then tload (n2w slot) s0 else sload (n2w slot) s0) = 0w /\
   key_taint (if tr then tn0.t_trans else tn0.t_stor) (n2w slot) = {}` by
    (qpat_x_assum `?H1. _` strip_assume_tac >> drule_all pop_root_header_facts >>
     simp[]) >>
  `?a s'. run_inst_seq (emitted_insts sa r) s0 = Abort a s'` by
    (simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
     irule dynarray_pop_storage_run_empty >> simp[]) >>
  qabbrev_tac `Gf = DRESTRICT (DRESTRICT (DRESTRICT G0 (COMPL {x0})) (COMPL {x1}))
    (COMPL {x2})` >>
  qabbrev_tac `tnf = tn0 with t_var := tn0.t_var |+ (x0,{}) |+ (x1,{}) |+ (x2,{})` >>
  `!D. inst_seq_ptr D 0 ctx func PG G0 tn0 (emitted_insts sa r) s0 Gf tnf` by
    (gen_tac >> simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
     irule (SRULE [APPEND] pop_root_slice_transfer_empty) >>
     simp[Abbr `Gf`, Abbr `tnf`]) >>
  `?j. !D lo PG' G tn G' tn'.
     inst_seq_ptr D lo ctx func PG' G tn (emitted_insts sa r) s0 G' tn' ==>
     gas_path_ptr D lo ctx func PG' G tn s0 0 G' tn'
       (Abort a (s' with vs_inst_idx := j))` by
    (irule pop_root_abort_counted_zero >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl [`INR (Error (RuntimeError "pop empty storage array"))`,
    `es with storage_trace :=
       es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))]`,
    `Gf`, `tnf`, `Abort a (s' with vs_inst_idx := j)`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >- (simp[] >> metis_tac[]) >>
  disj2_tac >> simp[exit_result_def, expr_exit_def]
QED

Resume compile_pop_storage_normalized_ptr[positive]:
  `w2n (lookup_storage (n2w slot) (get_storage cx es tr)) <> 0` by
    (Cases_on `lookup_storage (n2w slot) (get_storage cx es tr)` >> gvs[]) >>
  `!tail. eval_expr cx (Pop ann (TopLevelNameTarget (src,id))) (es with gas_obs := gas_explicit [] s0.vs_gas_readings ++ tail) =
     (INL (PlaceR (StoragePlace tr (n2w slot + n2w (1 +
        (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1) *
          type_slot_size tv)) tv)),
      (set_storage cx es tr
         (apply_writes (n2w slot)
           [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))]
           (get_storage cx es tr))
       with storage_trace :=
         es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))])
        with gas_obs := tail)` by
    (gen_tac >> drule_all eval_pop_storage >>
     disch_then (fn th => simp[th, LET_THM, pop_storage_gas_obs,
       vyperStateTheory.evaluation_state_component_equality])) >>
  reverse (Cases_on `?H1. valid_horizon cx st0 H1
    (es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))])`)
  >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      qpat_x_assum `!tail. eval_expr _ _ _ = _`
        (mp_then Any mp_tac gas_bad_storage_at_no_horizon) >>
      impl_tac >- fs[] >> simp[]) >>
  suspend "run"
QED

Resume compile_pop_storage_normalized_ptr[run]:
  `(if tr then tload (n2w slot) s0 else sload (n2w slot) s0) =
     lookup_storage (n2w slot) (get_storage cx es tr) /\
   ~s0.vs_call_ctx.cc_static /\ s0.vs_call_ctx.cc_address = cx.txn.target /\
   key_taint (if tr then tn0.t_trans else tn0.t_stor) (n2w slot) = {}` by
    (qpat_x_assum `?H1. _` strip_assume_tac >> drule_all pop_root_header_facts >>
     simp[]) >>
  `(if tr then tload (n2w slot) s0 else sload (n2w slot) s0) <> 0w` by simp[] >>
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0]` by simp[] >>
  drule_all dynarray_pop_storage_run >>
  disch_then (qspecl_then [`sa.cs_next_id`, `type_slot_size tv`] strip_assume_tac) >>
  `run_inst_seq (emitted_insts sa r) s0 = OK u` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6]` by simp[] >>
  drule_all pop_root_emitted_transfer_nonempty >>
  disch_then (qspecl_then [`func`, `PG`, `G0`, `cx_dead H0 cx`] strip_assume_tac) >>
  `!D. inst_seq_ptr D 0 ctx func PG G0 tn0 (emitted_insts sa r) s0 Gf tnf` by
    (gen_tac >>
     drule_all pop_root_emitted_transfer_nonempty >>
     disch_then (qspecl_then [`func`, `PG`, `G0`, `D`]
       (qx_choosel_then [`Gd`, `tnd`, `xsd`] strip_assume_tac)) >>
     `Gd = Gf /\ tnd = tnf` by
       (irule inst_seq_ptr_ghost_unique >> metis_tac[]) >>
     gvs[]) >>
  `!D. gas_path_ptr D 0 ctx func PG G0 tn0 s0 0 Gf tnf
     (OK (u with vs_inst_idx := s0.vs_inst_idx + 9))` by
    (gen_tac >> irule pop_root_run_counted >> simp[] >>
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
  `ghost_kept cenv es sa G0 tn0 s0 Gf tnf` by
    (irule pop_root_endpoint_kept >> simp[] >> qexists_tac `xs` >> simp[]) >>
  `lookup_storage (n2w slot) (if tr then contract_transient s0 else contract_storage s0) =
   lookup_storage (n2w slot) (get_storage cx es tr)` by
    (Cases_on `tr` >> fs[tload_def, sload_def, contract_transient_def, contract_storage_def]) >>
  `well_formed_type_value (ArrayTV tv (Dynamic n))` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  qabbrev_tac `ee = set_storage cx es tr
    (apply_writes (n2w slot) [(0,n2w (len - 1))] (get_storage cx es tr)) with
    storage_trace := es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))]` >>
  `(ee with gas_obs := []).scopes = es.scopes` by
    (simp[Abbr `ee`] >> Cases_on `tr` >> simp[set_storage_def]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl [`INL (PlaceR (StoragePlace tr elem tv))`, `ee`, `Gf`, `tnf`,
    `OK (u with vs_inst_idx := s0.vs_inst_idx + 9)`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> strip_tac >>
  `valid_horizon cx st0 H es.storage_trace /\ regions_consistent (FST H) /\
   storage_observations_ok cx H
     (es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))])` by
    (qpat_x_assum `valid_horizon cx st0 H _` mp_tac >> simp[Abbr `ee`, valid_horizon_def]) >>
  `stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
   ghost_inv H d cenv cx es G0 tn0 s0` by metis_tac[] >>
  `MEM (StorageRoot tr slot (ArrayTV tv (Dynamic n)))
     (es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))])` by simp[] >>
  `MEM (tr,n2w slot,ArrayTV tv (Dynamic n)) (FST H)` by
    (drule_all storage_observations_ok_root >> simp[]) >>
  `storage_well_formed_on cx (set_storage cx es tr
     (apply_writes (n2w slot) [(0,n2w (len - 1))] (get_storage cx es tr))) (FST H)` by
    (unabbrev_all_tac >> irule pop_storage_end_storage_wf >> metis_tac[]) >>
  `vv_post H ctx func cenv cx (Pop ann (TopLevelNameTarget (src,id))) es sa r s0
     (ee with gas_obs := []) (PlaceR (StoragePlace tr elem tv))
     (LocatedValue ann (mk_ptr (Var x6) (if tr then LocTransient else LocStorage))) u` by
    (unabbrev_all_tac >> irule pop_root_positive_post >> metis_tac[]) >>
  suspend "horizon"
QED

Resume compile_pop_storage_normalized_ptr[horizon]:
  `ghost_inv H d cenv cx (ee with gas_obs := []) Gf tnf u` by
    (irule pop_root_endpoint_ghost >>
     goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `MEM _ (FST _)`)) >>
     goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >> simp[] >>
     qexists_tac `xs ++ [x0;x1;x2;x3;x4;x5;x6]` >>
     simp[EVERY_APPEND, Abbr `len`, MEM_APPEND] >>
     rpt strip_tac >> fs[]) >>
  `stor_taint_ok H cx tn0 s0` by
    (qpat_x_assum `ghost_inv H d cenv cx es G0 tn0 s0` mp_tac >> simp[ghost_inv_def]) >>
  `ptr_vv_ok cx ann (PlaceR (StoragePlace tr elem tv))
    (LocatedValue ann (mk_ptr (Var x6) (if tr then LocTransient else LocStorage)))
    (ee with gas_obs := []) Gf tnf u` by
    (irule pop_declared_returned_place >> simp[] >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `MEM _ (FST _)`)) >>
     simp[Abbr `len`, Abbr `elem`, eval_operand_def] >>
     qexistsl [`tn0`, `n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1)`] >>
     qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >>
     Cases_on `tr` >>
     fs[contract_transient_def, contract_storage_def, sstore_def, tstore_def,
        sload_def, tload_def, vfmStateTheory.lookup_account_def]) >>
  conj_tac >- simp[] >>
  disj1_tac >>
  simp[contextTheory.mk_ptr_def, vyperASTTheory.expr_type_def] >>
  conj_tac >- fs[contextTheory.mk_ptr_def] >>
  conj_tac
  >- (qpat_x_assum `ghost_inv H d cenv cx (ee with gas_obs := []) Gf tnf u` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[ghost_inv_def, ptr_covers_def, stor_taint_ok_def, lookup_var_def] >>
      Cases_on `d` >- (simp[return_buf_ptr_def] >> metis_tac[]) >>
      PairCases_on `x` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def] >> metis_tac[]) >>
  Cases_on `tr` >> fs[ptr_vv_ok_def, contextTheory.mk_ptr_def, eval_operand_def, lookup_var_def]
QED

Finalise compile_pop_storage_normalized_ptr
