(* Source and compiler premises for the storage aggregate pointer branch. *)
Theory exprSimPtrTopLevelStorageBranch
Ancestors
  exprSimPtrTopLevelStorageSemantic exprSimPtrTopLevelStorageFrame
  exprSimTopLevelStorage exprSimUnwrapProps exprSimPtrTopLevelStorageAlloc
  vyperTypeGlobalLookupSoundness vyperStorageLayoutSafety
  exprSimHypsDefs exprSimTopLevelProps accountsRelProps exprSimMemorySource
  vyperInterpreter vyperLookupStorage vyperAST context vyperState
  exprSimHyps exprLowering exprLoweringProps compileEnv loweringPosts exprSimSource
  bodyPtrDefs exprSimPtrTopLevelStorageCopy words pred_set venomState

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
  `~dead_bytes rt (w2n a) tv (w2n a+i) b'` by metis_tac[] >>
  qpat_x_assum `storage_live_memory _ _ _ _ _` mp_tac >>
  simp[storage_live_memory_def, copy_bytes_def] >>
  disch_then (qspecl_then [`i`, `b'`] mp_tac) >> simp[] >>
  disch_then SUBST1_TAC >>
  qpat_x_assum `storage_range_agree _ _ _ _` mp_tac >>
  simp[storage_range_agree_def] >>
  disch_then (qspecl_then [`n2w (w2n a+i)`, `b'`] mp_tac) >>
  simp[vyperStorageTheory.read_slot_def]
QED
