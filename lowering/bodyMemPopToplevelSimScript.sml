Theory bodyMemPopToplevelSim
Ancestors
  bodyMemPopToplevelPath exprSimMemDefs exprSimPopStorage
  exprSimDefs exprSimProps loweringPosts exprSimLen exprSimTopLevelProps
  exprSimHyps exprSimHypsDefs exprLoweringProps exprLowering compileEnv
  vyperInterpreter vyperStorageBackend vyperStorageLayoutSafety vyperStorage
  vyperState venomState venomExecSemantics venomInst accountsRelProps
  gasOutcome gasSummary fragGasMode fragGasPathMem
  list words finite_map fragExec

Theorem pop_mem_storage_gas_obs[local]:
  get_storage cx (es with gas_obs := g) tr = get_storage cx es tr /\
  set_storage cx (es with gas_obs := g) tr X =
    set_storage cx es tr X with gas_obs := g
Proof
  Cases_on `tr` >> simp[get_storage_def, set_storage_def]
QED

Theorem pop_mem_ssr_gas_obs[local]:
  stmt_state_rel ctx func cenv cx es s ==>
  stmt_state_rel ctx func cenv cx (es with gas_obs := g) s
Proof
  strip_tac >> drule msg_gas_state_frame >>
  disch_then (qspecl_then [`s.vs_gas_readings`, `s.vs_inst_idx`, `g`] mp_tac) >>
  simp[NoAsms]
QED

Theorem pop_mem_storage_holds_gas_obs[local]:
  storage_holds cx tr t (PlaceR (StoragePlace tr' sl tvv)) w es s ==>
  storage_holds cx tr t (PlaceR (StoragePlace tr' sl tvv)) w
    (es with gas_obs := g) s
Proof
  rw[storage_holds_def, read_result_def, read_place_def] >>
  qexistsl_tac [`tvt`, `v`] >> simp[len_rss_obs, pop_mem_storage_gas_obs]
QED

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
