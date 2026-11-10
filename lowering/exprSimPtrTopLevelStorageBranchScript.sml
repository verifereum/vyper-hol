(* Source and compiler premises for the storage aggregate pointer branch. *)
Theory exprSimPtrTopLevelStorageBranch
Ancestors
  exprSimPtrTopLevelStorageSemantic exprSimPtrTopLevelStorageFrame
  exprSimTopLevelStorage exprSimUnwrapProps exprSimPtrTopLevelStorageAlloc
  vyperTypeGlobalLookupSoundness vyperStorageLayoutSafety
  exprSimHypsDefs exprSimTopLevelProps accountsRelProps exprSimMemorySource
  vyperInterpreter vyperLookupStorage vyperAST context vyperState
  exprSimHyps exprLowering exprLoweringProps compileEnv loweringStateRelDefs loweringPosts exprSimSource
  bodyPtrDefs exprSimPtrTopLevelStorageCopy words pred_set venomState storageDecodeMemory
  exprSimPtrTopLevelStorageDecode exprSimStorageCopy

Theorem toplevel_storage_branch_source:
  expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  read_storage_slot cx tr (n2w slot) tv es = (INL v,es) /\
  stmt_state_rel ctx fn cenv cx es s ==>
  typ = ann /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  slots_in_range (get_storage cx es tr) (w2n ((n2w slot):bytes32)) tv /\
  (!st. storage_read_live cx tr st (n2w slot) tv) /\
  w2n ((n2w slot):bytes32) + type_slot_size tv <= dimword (:256) /\
  vv_post ctx fn cenv cx (TopLevelName ann (src,id)) es sa sa s
    (es with gas_obs := []) (Value v)
    (LocatedValue ann (mk_ptr (Lit (n2w slot))
      (if tr then LocTransient else LocStorage))) s
Proof
  strip_tac >>
  `typ = ann` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     metis_tac[TopLevelName_storage_decl_type_eq]) >> gvs[] >>
  `slots_in_range (get_storage cx es tr) (w2n ((n2w slot):bytes32)) tv` by
    (irule toplevel_storage_slots_in_range >>
     gvs[expr_sim_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `declared_storage_region cx src id [] = SOME (tr,n2w slot,tv)` by
    simp[declared_storage_region_def] >>
  `storage_layout_safe cx` by fs[expr_sim_pre_def, expr_sim_inv_def] >>
  `w2n ((n2w slot):bytes32) + type_slot_size tv <= dimword (:256)` by
    (drule_all storage_layout_safe_region_nonoverflow >> simp[]) >>
  `!st. storage_read_live cx tr st (n2w slot) tv` by
    (gen_tac >> irule declared_storage_region_read_live >>
     qexistsl [`src`, `id`, `[]`] >> simp[declared_storage_region_def]) >>
  gvs[] >>
  `read_result cx (PlaceR (StoragePlace tr (n2w slot) tv)) es = (INL v,es)` by
    simp[read_result_def, read_place_def] >>
  `read_result cx (PlaceR (StoragePlace tr (n2w slot) tv))
    (es with gas_obs := []) = (INL v,es with gas_obs := [])` by
    (drule read_result_gas_obs >>
     disch_then (qspec_then `[]` ACCEPT_TAC)) >>
  drule vv_post_read_result >> disch_then (fn th => rewrite_tac[GSYM th]) >>
  irule toplevel_storage_value_post >> simp[]
QED

Theorem toplevel_storage_branch_compile:
  expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  read_storage_slot cx tr (n2w slot) tv es = (INL v,es) /\
  stmt_state_rel ctx fn cenv cx es s /\ ~is_word_type ann /\
  lower_value compile_expr cenv ty (TopLevelName ann (src,id)) sa = (op,sb) ==>
  compile_ensure_in_memory (Lit (n2w slot))
    (if tr then LocTransient else LocStorage)
    (type_memory_bytes cenv ann) (type_slot_size tv)
    cenv.ce_is_ctor cenv.ce_imm_alloca sa = (op,sb) /\
  type_memory_bytes cenv ann = 32 * type_slot_size tv /\
  type_memory_size tv <= type_memory_bytes cenv ann /\
  type_memory_bytes cenv ann < dimword (:256)
Proof
  strip_tac >> drule_all toplevel_storage_branch_source >>
  disch_then (qspec_then `sa` strip_assume_tac) >>
  `expr_body_pre cenv cx env (TopLevelName ann (src,id)) es` by
    metis_tac[expr_sim_pre_body_pre] >>
  drule_all toplevel_storage_copy_capacity >> strip_tac >>
  drule_all toplevel_storage_copy_word_count >> strip_tac >>
  `type_memory_size tv <= type_memory_bytes cenv ann` by
    (drule expr_body_pre_copy_ok >> simp[expr_type_def]) >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  Cases_on `tr` >>
  gvs[lower_value_def, comp_bind_def, compile_expr_def, expr_type_def,
      unwrap_value_def, mk_ptr_def]
QED

Theorem toplevel_storage_backend_taint_dead:
  stor_taint_ok cx tn s ==>
  !tr k j. (k,j) IN toplevel_copy_source_taint
    (if tr then LocTransient else LocStorage) tn ==>
    storage_dead cx tr
      (if tr then contract_transient s else contract_storage s) (w2n k) j
Proof
  strip_tac >> Cases >> rpt gen_tac >> strip_tac >>
  gvs[stor_taint_ok_def, cx_dead_def, toplevel_copy_source_taint_def,
      SUBSET_DEF, pairTheory.FORALL_PROD] >>
  Cases_on `s.vs_call_ctx.cc_address = cx.txn.target` >>
  gvs[contract_storage_def, contract_transient_def, vfmStateTheory.lookup_account_def] >>
  metis_tac[]
QED

Theorem toplevel_storage_branch_taint_live:
  ghost_inv d cenv cx es G tn s /\
  (!st. storage_read_live cx tr st a tv) /\
  w2n a + type_slot_size tv <= dimword (:256) ==>
  !i j. i < type_slot_size tv /\ j < 32 /\
    (a+n2w i,j) IN toplevel_copy_source_taint
      (if tr then LocTransient else LocStorage) tn ==>
    dead_bytes (if tr then contract_transient s else contract_storage s)
      (w2n a) tv (w2n a+i) j
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `stor_taint_ok cx tn s` by fs[ghost_inv_def] >>
  drule toplevel_storage_backend_taint_dead >>
  disch_then (qspecl_then [`tr`, `a+n2w i`, `j`] mp_tac) >> simp[] >>
  `w2n (a+n2w i) = w2n a+i` by
    (`w2n a+i < dimword (:256)` by decide_tac >>
     `a+n2w i = n2w (w2n a+i)` by metis_tac[word_add_n2w, n2w_w2n] >>
     asm_rewrite_tac[w2n_n2w] >> simp[]) >>
  simp[] >> strip_tac >>
  `w2n a <= w2n a+i /\ w2n a+i < w2n a+type_slot_size tv` by decide_tac >>
  fs[storage_read_live_def] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem toplevel_storage_range_dead_bytes:
  storage_range_agree st rt a tv ==>
  !k j. dead_bytes rt (w2n a) tv k j = dead_bytes st (w2n a) tv k j
Proof
  strip_tac >> rpt gen_tac >> irule (cj 1 dead_bytes_live_frame) >>
  rpt strip_tac >>
  `i < dimword (:256)` by fs[storage_range_agree_def] >>
  qpat_x_assum `storage_range_agree _ _ _ _` mp_tac >>
  simp[storage_range_agree_def] >>
  disch_then (qspec_then `n2w i` mp_tac) >> simp[]
QED

Theorem toplevel_storage_live_memory_range:
  storage_range_agree st rt a tv /\
  storage_live_memory rt (w2n a) tv b mem ==>
  storage_live_memory st (w2n a) tv b mem
Proof
  strip_tac >> drule toplevel_storage_range_dead_bytes >> strip_tac >>
  simp[storage_live_memory_def, copy_bytes_def] >> rpt strip_tac >>
  `w2n a+i < dimword (:256)` by fs[storage_range_agree_def] >>
  `~dead_bytes rt (w2n a) tv (w2n a+i) b'` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  qpat_x_assum `storage_live_memory _ _ _ _ _` mp_tac >>
  simp[storage_live_memory_def, copy_bytes_def] >>
  disch_then (qspecl_then [`i`, `b'`] mp_tac) >> simp[] >>
  disch_then SUBST1_TAC >>
  qpat_x_assum `storage_range_agree _ _ _ _` mp_tac >>
  simp[storage_range_agree_def] >> strip_tac >>
  qpat_x_assum `!k b. _` (qspecl_then [`n2w (w2n a+i)`, `b'`] mp_tac) >>
  simp[vyperStorageTheory.read_slot_def]
QED

Theorem toplevel_storage_copy_robust_contents:
  stor_taint_ok cx tn u /\
  (!st. storage_read_live cx tr st a tv) /\
  well_formed_type_value tv /\ slots_in_range st (w2n a) tv /\
  decode_value st (w2n a) tv = SOME v /\
  storage_range_agree st
    (if tr then contract_transient u else contract_storage u) a tv /\
  copy_prefix (if tr then LocTransient else LocStorage)
    a b (type_slot_size tv) u (type_slot_size tv) t /\
  tnf.t_mem SUBSET toplevel_copy_taint_bound
    (if tr then LocTransient else LocStorage) a b tn (type_slot_size tv) ==>
  !mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
    val_in_memory tv v b mem
Proof
  strip_tac >>
  `w2n a+type_slot_size tv <= dimword (:256)` by fs[storage_range_agree_def] >>
  `!i. i < type_slot_size tv ==> w2n (a+n2w i) = w2n a+i` by
    (rpt strip_tac >>
     `w2n a+i < dimword (:256)` by decide_tac >>
     `a+n2w i = n2w (w2n a+i)` by metis_tac[word_add_n2w, n2w_w2n] >>
     asm_rewrite_tac[w2n_n2w] >> simp[]) >>
  `storage_live_memory (if tr then contract_transient u else contract_storage u)
    (w2n a) tv b t.vs_memory` by
    (irule toplevel_copy_prefix_live_memory >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> Cases_on `tr` >>
     gvs[copy_runtime_word_def, vyperStorageTheory.read_slot_def,
         tload_def, sload_def, contract_transient_def, contract_storage_def,
         vfmStateTheory.lookup_account_def] >> rpt strip_tac >>
     `a+n2w i = n2w (i+w2n a)` by metis_tac[word_add_n2w, n2w_w2n,
       arithmeticTheory.ADD_COMM] >> simp[]) >>
  `storage_live_memory st (w2n a) tv b t.vs_memory` by
    metis_tac[toplevel_storage_live_memory_range] >>
  `!i j. i < type_slot_size tv /\ j < 32 /\
     (a+n2w i,j) IN toplevel_copy_source_taint
       (if tr then LocTransient else LocStorage) tn ==>
     dead_bytes st (w2n a) tv (w2n a+i) j` by
    (rpt strip_tac >>
     drule toplevel_storage_backend_taint_dead >>
     disch_then (qspecl_then [`tr`, `a+n2w i`, `j`] mp_tac) >> simp[] >>
     drule toplevel_storage_range_dead_bytes >> strip_tac >>
     fs[storage_read_live_def] >>
     `w2n a <= w2n a+i /\ w2n a+i < w2n a+type_slot_size tv` by decide_tac >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `!i j. i < type_slot_size tv /\ j < 32 /\ b+32*i+j IN tnf.t_mem ==>
     dead_bytes st (w2n a) tv (w2n a+i) j` by
    metis_tac[toplevel_copy_taint_dead_bytes] >>
  rpt strip_tac >> irule toplevel_storage_decode_robust >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  metis_tac[arithmeticTheory.ADD_COMM, arithmeticTheory.ADD_ASSOC]
QED


Theorem toplevel_local_footprint_forward[local]:
  stmt_state_rel ctx fn cenv cx es s ==>
  (!name b sz i. local_region cenv es.scopes s name b sz /\
    b <= i /\ i < b+sz ==> i NOTIN writes) ==>
  !name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    (!i. w2n w <= i /\ i < w2n w+val_footprint entry.type entry.value ==>
      i NOTIN writes)
Proof
  metis_tac[toplevel_local_footprint_disjoint]
QED

Theorem toplevel_backend_location[local]:
  (((if tr then LocTransient else LocStorage) = LocTransient) = tr) /\
  ((if tr then LocTransient else LocStorage) = LocStorage \/
   (if tr then LocTransient else LocStorage) = LocTransient)
Proof
  Cases_on `tr` >> simp[]
QED

Theorem compile_toplevel_storage_aggregate_sim_ptr:
  expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  read_storage_slot cx tr (n2w slot) tv es = (INL v,es) /\
  ~is_word_type ann ==>
  expr_sim_ptr d ctx PG fn cenv cx ty (TopLevelName ann (src,id)) es
Proof
  strip_tac >> rw[expr_sim_ptr_def] >>
  drule_all toplevel_storage_branch_source >>
  disch_then (qspec_then `sa` strip_assume_tac) >>
  drule_all toplevel_storage_branch_compile >> strip_tac >>
  `storage_holds cx tr ann (Value v) (n2w slot) (es with gas_obs := []) s0` by
    (fs[vv_post_def, vv_holds_def, vv_at_def, mk_ptr_def, eval_operand_def,
        expr_type_def] >> Cases_on `tr` >> gvs[expr_type_def]) >>
  gvs[expr_type_def] >>
  drule (toplevel_storage_ensure_ptr_post_effects
    |> Q.INST [`e` |-> `TopLevelName ann (src,id)`,
               `loc` |-> `if tr then LocTransient else LocStorage`]
    |> SRULE [expr_type_def, toplevel_backend_location]) >> simp[] >> disch_then drule_all >>
    disch_then (qspecl_then [`tn0`, `PG`, `G0`, `cx_dead cx`] strip_assume_tac) >>
    `stor_taint_ok cx tn0 u` by
      (fs[ghost_inv_def, stor_taint_ok_def]) >>
    `storage_holds cx tr ann (Value v) (n2w slot) (es with gas_obs := []) u` by
      gvs[storage_holds_def, contract_transient_def, contract_storage_def] >>
    `well_formed_type_value tv` by
      metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
    `decode_value (get_storage cx es tr) (w2n ((n2w slot):bytes32)) tv = SOME v` by
      (fs[vyperStorageBackendTheory.read_storage_slot_eq, AllCaseEqs()]) >>
    `storage_range_agree (get_storage cx es tr)
       (if tr then contract_transient u else contract_storage u) (n2w slot) tv` by
      (Cases_on `tr` >>
       gvs[storage_holds_def, vyperStorageBackendTheory.get_storage_def]) >>
    `!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
       val_in_memory tv v (w2n w) mem` by
      (rpt strip_tac >> irule toplevel_storage_copy_robust_contents >>
       rpt (goal_assum (drule_at Any)) >> simp[]) >>
    `val_wf tv v` by fs[expr_post_def, expr_val_at_def, expr_type_def] >>
    `val_store_size tv v <= 32 * type_slot_size tv` by
      (drule exprSimPropsTheory.val_store_size_le >> decide_tac) >>
    `ptr_val_ok cx ann v (Var p) Gf tnf t /\
     ptr_buf_ok cenv (TopLevelName ann (src,id)) (Var p) Gf t` by
      (irule toplevel_storage_copy_pointer_post >>
       rpt (goal_assum (drule_at Any)) >> simp[]) >>
    `!name b len. local_region cenv es.scopes s0 name b len ==>
       local_region cenv es.scopes u name b len` by
      (simp[local_region_def] >> rpt strip_tac >>
       `not_fresh_at sa p'` by metis_tac[local_ptrs_reserved_def] >>
       metis_tac[]) >>
    `!name b len i. local_region cenv es.scopes s0 name b len /\
       b <= i /\ i < b+len ==> i NOTIN toplevel_copy_region (w2n w) (type_slot_size tv)` by
      (simp[toplevel_copy_region_def] >> rpt strip_tac >>
       `regions_disjoint (w2n w) (32*type_slot_size tv) b len` by metis_tac[] >>
       fs[regions_disjoint_def] >> decide_tac) >>
    `!i. i NOTIN toplevel_copy_region (w2n w) (type_slot_size tv) ==>
       mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s0.vs_memory` by
      (gvs[copy_prefix_def, toplevel_copy_region_def] >> rpt strip_tac >>
       first_x_assum irule >> decide_tac) >>
    `!i. i NOTIN toplevel_copy_region (w2n w) (type_slot_size tv) /\
       i IN tnf.t_mem ==> i IN tn0.t_mem` by
      (fs[SUBSET_DEF, toplevel_copy_taint_bound_def, toplevel_copy_region_def,
          toplevel_copy_translated_taint_def] >> rpt strip_tac >>
       first_x_assum drule >> simp[] >> rpt strip_tac >> gvs[] >> decide_tac) >>
    qpat_assum `stmt_state_rel _ _ _ _ es s0`
      (mp_then Any mp_tac toplevel_local_footprint_forward) >>
    disch_then (qspec_then `toplevel_copy_region (w2n w) (type_slot_size tv)` mp_tac) >>
    simp[] >> disch_then assume_tac >> fs[] >>
    `ghost_inv d cenv cx (es with gas_obs := []) Gf tnf t` by
      (irule toplevel_ghost_inv_memory_frame >>
       qexistsl_tac [`G0`, `es`, `s0`, `sa`, `tn0`,
         `toplevel_copy_region (w2n w) (type_slot_size tv)`] >>
       simp[] >>
       qpat_assum `!name entry p sz w. _` (fn fp =>
         qpat_assum `!name b len i. local_region _ _ s0 _ _ _ /\ _ ==> _` (fn ex =>
           POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[fp,ex]))) >>
    `ghost_kept cenv es sa G0 tn0 s0 Gf tnf` by
      (irule toplevel_ghost_kept_memory_frame >>
       conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
       qexists_tac `toplevel_copy_region (w2n w) (type_slot_size tv)` >>
       simp[] >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
       rpt strip_tac >>
       `regions_disjoint (w2n w) (32*type_slot_size tv) off sz` by metis_tac[] >>
       fs[regions_disjoint_def, toplevel_copy_region_def] >> decide_tac) >>
    rewrite_tac[fragGasPathPtrTheory.gas_outcome_ptr_def] >>
    qexists_tac `[]` >> disj1_tac >>
    rewrite_tac[fragGasPathPtrTheory.gas_summary_ptr_at_def] >>
    qexistsl_tac [`INL v`, `es`, `Gf`, `tnf`, `OK t`] >>
    simp[] >> conj_tac
    >- (Cases_on `tr` >> gvs[] >>
        simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
             return_def, raise_def, read_result_def, read_place_def,
             vyperStorageBackendTheory.read_storage_slot_eq,
             vyperStorageBackendTheory.get_storage_def] >>
        fs[vyperStorageBackendTheory.get_storage_def]) >>
    gvs[]
QED
