Theory bodyMemPopToplevelSim
Ancestors
  bodyMemPopToplevelPath exprSimMemDefs exprSimPopStorage
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
  declared_storage_region cx mid id [] = SOME (tr,w,ArrayTV tv (Dynamic n)) /\
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
  strip_tac >> irule pop_storage_updated_state_rel >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`s with vs_inst_idx := u.vs_inst_idx`, `sa`] >>
  simp[stmt_state_rel_inst_idx, lookup_var_def] >>
  Cases_on `tr` >> gvs[tstore_def, sstore_def, LET_THM]
QED

Theorem pop_mem_positive_holds_cursor:
  expr_sim_inv cenv cx env es /\
  stmt_state_rel H ctx func cenv cx es s /\
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

(* Popping a declared dynamic array at its root keeps every observed region
   decodable; the region is the root the evaluation just observed. *)
Theorem pop_mem_pop_place[local]:
  ~cx.txn.is_static /\
  0 < w2n (lookup_storage (n2w slot) (get_storage cx es tr)) ==>
  pop_place cx (StoragePlace tr (n2w slot) (ArrayTV tv (Dynamic n))) es =
    (INL (PlaceR (StoragePlace tr
       (n2w slot + n2w (1 + (w2n (lookup_storage (n2w slot)
          (get_storage cx es tr)) - 1) * type_slot_size tv)) tv)),
     set_storage cx es tr
       (apply_writes (n2w slot)
         [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))]
         (get_storage cx es tr)))
Proof
  strip_tac >>
  simp[pop_place_def, get_storage_backend_eq, bind_def, ignore_bind_def,
       check_def, assert_def, return_def, write_storage_slot_eq,
       encode_value_def, encode_base_to_slot_def, integer_wordTheory.i2w_def] >>
  Cases_on `tr` >>
  gvs[vyperStorageBackendTheory.set_storage_def,
      vyperStorageBackendTheory.get_storage_def]
QED

Theorem pop_mem_end_storage_wf[local]:
  regions_consistent (FST (H : (bool # bytes32 # type_value) list # num list)) /\
  storage_well_formed_on cx es (FST H) /\
  storage_observations_ok cx H
    (es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))]) /\
  well_formed_type_value (ArrayTV tv (Dynamic n)) /\
  ~cx.txn.is_static /\
  0 < w2n (lookup_storage (n2w slot) (get_storage cx es tr)) ==>
  storage_well_formed_on cx
    (set_storage cx es tr
      (apply_writes (n2w slot)
        [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))]
        (get_storage cx es tr))) (FST H)
Proof
  strip_tac >>
  drule_all pop_mem_pop_place >> strip_tac >>
  `!b sl leaf. StoragePlace tr (n2w slot) (ArrayTV tv (Dynamic n)) =
      StoragePlace b sl leaf ==>
    ?offset tv' path delta.
      MEM (StorageRoot b offset tv')
        (es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))]) /\
      storage_subregion tv' path delta leaf /\ sl = n2w offset + n2w delta` by
    (rpt strip_tac >> gvs[] >>
     qexistsl_tac [`slot`, `ArrayTV tv (Dynamic n)`, `[]`, `0`] >>
     simp[vyperStoragePlaceRegionTheory.storage_subregion_def]) >>
  `runtime_place_typed cx es (StoragePlace tr (n2w slot) (ArrayTV tv (Dynamic n)))
     (ArrayTV tv (Dynamic n))` by
    simp[vyperPlaceTypingTheory.runtime_place_typed_storage] >>
  metis_tac[vyperFiniteStoragePreservationTheory.pop_place_preserves_storage_well_formed_on]
QED

Theorem pop_mem_rss_end[local]:
  read_storage_slot cx b sl tv st = (INL v, st) ==>
  read_storage_slot cx b sl tv ((st with storage_trace := o') with gas_obs := g) =
    (INL v, (st with storage_trace := o') with gas_obs := g)
Proof
  Cases_on `b` >>
  simp[read_storage_slot_def, get_storage_backend_def, get_transient_storage_def,
       get_accounts_def, bind_def, lift_option_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def])
QED

Theorem pop_mem_storage_holds_end[local]:
  storage_holds cx tr t (PlaceR (StoragePlace tr' sl tvv)) w es s ==>
  storage_holds cx tr t (PlaceR (StoragePlace tr' sl tvv)) w
    ((es with storage_trace := o') with gas_obs := g) s
Proof
  rw[loweringPostsTheory.storage_holds_def, read_result_def, read_place_def] >>
  qexistsl_tac [`tvt`, `v`] >>
  `get_storage cx ((es with storage_trace := o') with gas_obs := g) tr =
   get_storage cx es tr` by
    (Cases_on `tr` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  gvs[pop_mem_rss_end]
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
   ~cx.txn.is_static /\ alloca_inv s0` by
    (qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def, state_rel_def]) >>
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
      disj2_tac >> simp[exit_result_def, expr_exit_def]) >>
  suspend "positive"
QED
Resume compile_pop_storage_normalized_vv_sim_mem[positive]:
  `(if tr then tload (n2w slot) s0 else sload (n2w slot) s0) <> 0w` by simp[] >>
  `~s0.vs_call_ctx.cc_static` by
    (qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def, state_rel_def]) >>
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
  disj1_tac >> qexists_tac `t` >> simp[] >>
  gen_tac >> strip_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_x_assum `valid_horizon _ _ _ (_ ++ _)` mp_tac >>
     simp[vyperStorageFootprintTheory.valid_horizon_def]) >>
  `regions_consistent (FST H) /\
   storage_observations_ok cx H (es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))])` by
    (qpat_x_assum `valid_horizon _ _ _ (_ ++ _)` mp_tac >>
     simp[vyperStorageFootprintTheory.valid_horizon_def]) >>
  `stmt_state_rel H ctx func cenv cx es s0 /\
   storage_well_formed_on cx es (FST H)` by metis_tac[] >>
  pop_assum strip_assume_tac >>
  `well_formed_type_value (ArrayTV tv (Dynamic n))` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `storage_well_formed_on cx (set_storage cx es tr (apply_writes (n2w slot) [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))] (get_storage cx es tr))) (FST H)` by
    metis_tac[pop_mem_end_storage_wf] >>
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
    (irule pop_mem_positive_holds_cursor >>
     simp[Abbr `elem`] >> conj_tac
     >- metis_tac[] >>
     qexistsl_tac [`cenv`, `ctx`, `env`, `func`, `s0`] >> simp[] >>
     qpat_x_assum `t.vs_inst_idx = _` (fn th => once_rewrite_tac[GSYM th]) >>
     Cases_on `tr` >> fs[] >> first_assum ACCEPT_TAC) >>
  `storage_holds cx tr ann (PlaceR (StoragePlace tr elem tv)) elem
     ((set_storage cx es tr (apply_writes (n2w slot) [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))] (get_storage cx es tr)) with storage_trace := es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))]) with gas_obs := []) t` by
    (irule pop_mem_storage_holds_end >> first_assum ACCEPT_TAC) >>
  `((set_storage cx es tr (apply_writes (n2w slot) [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage cx es tr)) - 1))] (get_storage cx es tr)) with storage_trace := es.storage_trace ++ [StorageRoot tr slot (ArrayTV tv (Dynamic n))]) with gas_obs := []).scopes = es.scopes` by
    (Cases_on `tr` >> simp[set_storage_def]) >>
  `!id path. PlaceR (StoragePlace tr elem tv) <> PlaceR (MemoryPlace id path)` by
    simp[] >>
  rpt conj_tac
  >- (irule pop_storage_vv_post >> rpt conj_tac >> metis_tac[])
  >- (irule vv_store_bound_nonmem >> Cases_on `tr` >> simp[contextTheory.mk_ptr_def]) >>
  fs[]
QED

Finalise compile_pop_storage_normalized_vv_sim_mem
