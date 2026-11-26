(* The slot Pop result uses the same header write, cursor and ghosts as the
   supplied physical run. Its pointer denotes the removed element. *)
Theory bodyPopSlotPostMods
Ancestors
  bodyPopSlotRepresentationMods bodyPopSlotFrameMods bodyWriteTargetStageMods
  bodyFullPostsMods exprSimMemDefs exprSimPopNestedBase exprSimPopStorage
  accountsRelProps targetPlaceLive stateRelProj sourceUnitExecution
  loweringStateRelDefs vyperStorageFootprint vyperStorageBackend
  bodyPtrDefs bodyFullShadowBodyInv ptrDiscipline venomState venomExecSemantics
  loweringPosts exprLoweringProps context vyperAST words

Theorem pop_slot_located_post[local]:
  stmt_state_rel H ctx func cenv cx ef u /\
  immutable_frame_mods func cenv cx ef u /\
  storage_well_formed_on cx ef (FST H) /\ wb_frame cenv es ef sa s0 u /\
  storage_holds cx tr ann (PlaceR (StoragePlace tr elem tv)) elem ef u /\
  lookup_var out u = SOME elem ==>
  vv_post_mods H ctx func cenv cx (Pop ann bt) es sa sb s0 ef
    (PlaceR (StoragePlace tr elem tv)) (LocatedValue ann (mk_ptr (Var out) (slot_loc tr))) u
Proof
  Cases_on `tr` >>
  simp[vv_post_mods_def, vv_holds_mods_def, vv_holds_def, vv_at_def,
       vv_place_ptr_mods_def, vv_place_ptr_def, wb_frame_def, slot_loc_def,
       mk_ptr_def, eval_operand_def, expr_type_def] >>
  strip_tac >> first_assum ACCEPT_TAC
QED

Theorem pop_slot_pre_dead[local]:
  ghost_inv_at_mods D lo d cenv cx ee G tn s /\ dead_lo_ok_mods H D lo cenv cx /\
  s.vs_call_ctx.cc_address = cx.txn.target /\
  (key,b) IN (if tr then tn.t_trans else tn.t_stor) ==>
  storage_dead H tr (if tr then contract_transient s else contract_storage s) (w2n key) b
Proof
  Cases_on `tr` >>
  gvs[ghost_inv_at_mods_def, stor_taint_ok_at_def, dead_lo_ok_mods_def,
      cx_dead_def, contract_transient_def, contract_storage_def,
      vfmStateTheory.lookup_account_def, pred_setTheory.SUBSET_DEF] >>
  strip_tac
  >- (qpat_assum `!x. x IN tn.t_trans ==> _` (qspec_then `(key,b)` mp_tac) >>
      qpat_assum `D.d_trans = _` (fn th => pure_rewrite_tac [th]) >>
      simp[pred_setTheory.IN_GSPEC]) >>
  qpat_assum `!x. x IN tn.t_stor ==> _` (qspec_then `(key,b)` mp_tac) >>
  qpat_assum `D.d_stor = _` (fn th => pure_rewrite_tac [th]) >>
  simp[pred_setTheory.IN_GSPEC]
QED

Theorem pop_slot_removed_dead[local]:
  storage_read_live (H : (bool # bytes32 # type_value) list # num list)
    tr st slot (ArrayTV tv (Dynamic n)) /\
  len = w2n (lookup_storage slot st) /\ 0 < len /\ len <= n /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256) /\
  elem = slot + n2w (1 + (len - 1) * type_slot_size tv) /\
  storage_dead H tr st (w2n key) b /\
  w2n elem <= w2n key /\ w2n key < w2n elem + type_slot_size tv ==>
  dead_bytes (update_storage slot new st) (w2n elem) tv (w2n key) b
Proof
  strip_tac >>
  `storage_read_live H tr st elem tv` by
    (qpat_assum `elem = _` (once_rewrite_tac o single) >>
     once_rewrite_tac[arithmeticTheory.ADD_COMM |> Q.SPECL [`1`,`(len - 1) * type_slot_size tv`]] >>
     irule nested_pop_live_dynamic_element >>
     conj_tac >- decide_tac >> qexists `n` >> simp[] >> decide_tac) >>
  `w2n elem + type_slot_size tv <= dimword(:256) /\
   (type_slot_size tv = 0 \/ w2n slot < w2n elem)` by
    (qpat_assum `elem = _` (once_rewrite_tac o single) >>
     irule pop_array_last_bounds >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists `n` >> simp[]) >>
  `dead_bytes (update_storage slot new st) (w2n elem) tv (w2n key) b =
   dead_bytes st (w2n elem) tv (w2n key) b` by
    (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
     irule nested_pop_lookup_frame >> qexistsl [`w2n (elem:bytes32)`,`type_slot_size tv`] >>
     decide_tac) >>
  qpat_assum `dead_bytes (update_storage _ _ _) _ _ _ _ = _`
    (once_rewrite_tac o single) >>
  qpat_x_assum `storage_read_live H tr st elem tv`
    (drule o REWRITE_RULE [storage_read_live_def]) >> simp[]
QED

Theorem pop_slot_ptr_endpoint[local]:
  evaluate_type (get_tenv cx) ann = SOME tv /\
  lookup_var out u = SOME elem /\ op_taint tn' (Var out) = {} /\
  u = (if tr then tstore slot new s else sstore slot new s)
       with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!key b. (key,b) IN (if tr then tn'.t_trans else tn'.t_stor) /\
     w2n elem <= w2n key /\ w2n key < w2n elem + type_slot_size tv ==>
     dead_bytes (update_storage slot new
       (if tr then contract_transient s else contract_storage s)) (w2n elem) tv (w2n key) b) ==>
  ptr_vv_ok cx ann (PlaceR (StoragePlace tr elem tv))
    (LocatedValue ann (mk_ptr (Var out) (slot_loc tr))) ef G' tn' u
Proof
  strip_tac >>
  simp[ptr_vv_ok_def, mk_ptr_def, eval_operand_def] >>
  qpat_assum `u = _` (once_rewrite_tac o single) >>
  Cases_on `tr` >>
  simp[slot_loc_def, sstore_def, tstore_def, contract_transient_def, contract_storage_def,
       vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >>
  qpat_x_assum `!key b. _ ==> dead_bytes _ _ _ _ _` mp_tac >>
  simp[contract_transient_def, contract_storage_def, vfmStateTheory.lookup_account_def] >>
  strip_tac >> first_x_assum irule >> simp[]
QED

Theorem pop_slot_positive_post_mods:
  MEM (StorageRoot tr offset root) ee.storage_trace /\
  storage_subregion root path delta (ArrayTV tv (Dynamic n)) /\
  slot = n2w offset + n2w delta /\
  well_formed_type_value (ArrayTV tv (Dynamic n)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic n))) /\
    w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword (:256) /\
    slots_in_range (get_storage cx ee tr) (w2n slot) (ArrayTV tv (Dynamic n)) /\
    storage_range_agree (get_storage cx ee tr)
      (if tr then contract_transient s else contract_storage s) slot (ArrayTV tv (Dynamic n))) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  len = w2n (lookup_storage slot (get_storage cx ee tr)) /\ 0 < len /\ len <= n /\
  ~cx.txn.is_static /\
  (if tr then tload slot s else sload slot s) = lookup_storage slot (get_storage cx ee tr) /\
  raw = (if tr then tstore slot (tload slot s - 1w) s
         else sstore slot (sload slot s - 1w) s) with vs_vars := raw.vs_vars /\
  lookup_var out raw = SOME (slot + 1w +
    ((if tr then tload slot s else sload slot s) - 1w) * n2w (type_slot_size tv)) /\
  u = (raw with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  u.vs_current_bb = sb.cs_current_bb /\ alloca_history func u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  op_taint tn' (Var out) = {} /\
  tn'.t_mem = tn.t_mem /\ tn'.t_imm = tn.t_imm /\
  tn'.t_stor = (if tr then tn.t_stor else key_update tn.t_stor slot {}) /\
  tn'.t_trans = (if tr then key_update tn.t_trans slot {} else tn.t_trans) /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sm s0
       ee (PlaceR (StoragePlace tr slot (ArrayTV tv (Dynamic n))))
       (Type (ArrayT ann (Dynamic n))) dst G0 tn0 G tn s) ==>
  let elem = slot + n2w (1 + (len - 1) * type_slot_size tv);
      ef = set_storage cx ee tr (apply_writes slot [(0,n2w (len - 1))]
             (get_storage cx ee tr));
      result = PlaceR (StoragePlace tr elem tv);
      vv = LocatedValue ann (mk_ptr (Var out) (slot_loc tr)) in
    (!tail. pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n)))
       (ee with gas_obs := tail) = (INL result,ef with gas_obs := tail)) /\
    ef.storage_trace = ee.storage_trace /\ ef.gas_obs = ee.gas_obs /\
    !H. valid_horizon cx st0 H ef.storage_trace ==>
      vv_post_mods H ctx func cenv cx (Pop ann bt) es sa sb s0 ef result vv u /\
      vv_store_bound cx (post_value_type cenv (Pop ann bt))
        (lowered_value_type cenv (Pop ann bt)) ef result vv u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ef G' tn' u /\
      ptr_vv_ok cx (post_value_type cenv (Pop ann bt)) result vv ef G' tn' u /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  pure_rewrite_tac [LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `elem = slot + n2w (1 + (len - 1) * type_slot_size tv)` >>
  qabbrev_tac `ef = set_storage cx ee tr (apply_writes slot [(0,n2w (len - 1))]
    (get_storage cx ee tr))` >>
  `elem = slot + n2w (1 + (len - 1) * type_slot_size tv)` by simp[Abbr `elem`] >>
  `ef = set_storage cx ee tr (apply_writes slot [(0,n2w (len - 1))]
    (get_storage cx ee tr))` by simp[Abbr `ef`] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> storage_place_observed _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) ee =
      (INL (PlaceR (StoragePlace tr elem tv)),ef) /\
   (!tail. pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n)))
       (ee with gas_obs := tail) =
       (INL (PlaceR (StoragePlace tr elem tv)), ef with gas_obs := tail)) /\
   ef.storage_trace = ee.storage_trace /\ ef.gas_obs = ee.gas_obs /\
   lookup_var out u = SOME elem /\
   storage_holds cx tr ann (PlaceR (StoragePlace tr elem tv)) elem ef u` by
    (drule_all_then mp_tac pop_slot_representation_mods >> simp[Abbr `elem`, Abbr `ef`]) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qx_gen_tac `H` >> disch_tac >>
  suspend "frame"
QED

Resume pop_slot_positive_post_mods[frame]:
  `valid_horizon cx st0 H ee.storage_trace` by
    (qpat_x_assum `valid_horizon _ _ H ef.storage_trace` mp_tac >>
     qpat_assum `ef.storage_trace = _` (fn th => pure_rewrite_tac [th]) >>
     disch_then ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> storage_place_observed _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qabbrev_tac `new = n2w (len - 1):bytes32` >>
  `(if tr then tload slot s else sload slot s) - 1w = new` by
    (`n2w (len - 1) = (n2w len - 1w : bytes32)` by
       (irule wordsTheory.n2w_sub >> decide_tac) >>
     simp_tac bool_ss [Abbr `new`] >>
     qpat_assum `n2w (len - 1) = _` (fn th => pure_once_rewrite_tac [th]) >>
     qpat_assum `(if tr then _ else _) = lookup_storage _ _`
       (fn th => pure_rewrite_tac [th]) >>
     qpat_assum `len = w2n _`
       (fn th => simp_tac bool_ss [th,wordsTheory.n2w_w2n])) >>
  `u = (if tr then tstore slot new s else sstore slot new s)
       with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>` by
    (qpat_assum `u = raw with vs_inst_idx := _` (fn th => simp_tac std_ss [th]) >>
     qpat_assum `raw = _ with vs_vars := _`
       (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     qpat_assum `(if tr then _ else _) - 1w = new` mp_tac >>
     Cases_on `tr` >> simp_tac (srw_ss()) []) >>
  `ef = (set_storage cx ee tr (apply_writes slot [(0,new)] (get_storage cx ee tr)))
        with storage_trace := ee.storage_trace` by
    (Cases_on `tr` >> simp[Abbr `ef`, Abbr `new`, set_storage_def]) >>
  `new = n2w (w2n (lookup_storage slot (get_storage cx ee tr)) - 1)` by
    (qpat_assum `len = w2n _` (fn th => simp_tac bool_ss [Abbr `new`,th])) >>
  `stmt_state_rel H ctx func cenv cx ef u /\ immutable_frame_mods func cenv cx ef u /\
   storage_well_formed_on cx ef (FST H) /\ wb_frame cenv es ef sa s0 u /\
   ghost_inv_at_mods (DF H) lo d cenv cx ef G' tn' u /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'` by
    (irule pop_slot_write_frame_mods >>
     rpt (first_assum (irule_at Any)) >>
     qexistsl [`sm`,`dst`,`bt`,`Type (ArrayT ann (Dynamic n))`,`G`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!h. valid_horizon _ _ h ee.storage_trace ==> write_target_post_mods
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` (drule_then (strip_assume_tac o MATCH_MP write_target_post_view_mods))) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by
    (qpat_assum `u = _` (once_rewrite_tac o single) >>
     Cases_on `tr` >> simp[sstore_def,tstore_def]) >>
  simp_tac (srw_ss()) [post_value_type_def, expr_type_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (irule pop_slot_located_post >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (Cases_on `tr` >> simp_tac (srw_ss()) [vv_store_bound_def,mk_ptr_def,slot_loc_def])
  >- (qpat_assum `u = raw with vs_inst_idx := _` (fn th => simp_tac (srw_ss()) [th])) >>
  suspend "pointer"
QED

Resume pop_slot_positive_post_mods[pointer]:
  irule pop_slot_ptr_endpoint >> rpt (first_assum (irule_at Any)) >>
  qx_genl_tac [`key`,`b`] >> strip_tac >>
  `s.vs_call_ctx.cc_address = cx.txn.target` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx ee s`
       (mp_tac o MATCH_MP state_rel_call_ctx_rel o MATCH_MP stmt_state_rel_state_rel) >>
     simp_tac bool_ss [call_ctx_rel_def]) >>
  qpat_assum `!H. dead_lo_ok_mods H _ _ _ _` (qspec_then `H` assume_tac) >>
  `(key,b) IN (if tr then tn.t_trans else tn.t_stor)` by
    (qpat_x_assum `(key,b) IN _` mp_tac >>
     qpat_assum `tn'.t_trans = _` (fn th => pure_once_rewrite_tac [th]) >>
     qpat_assum `tn'.t_stor = _` (fn th => pure_once_rewrite_tac [th]) >>
     Cases_on `tr` >> simp_tac (srw_ss()) [key_update_def,pred_setTheory.IN_GSPEC]) >>
  `storage_dead H tr (if tr then contract_transient s else contract_storage s) (w2n key) b` by
    (irule pop_slot_pre_dead >>
     qpat_assum `ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s` (irule_at Any) >>
     rpt (first_assum (irule_at Any))) >>
  irule pop_slot_removed_dead >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`H`,`len`,`n`,`tr`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `len = w2n _` (fn th => pure_once_rewrite_tac [th]) >>
      AP_TERM_TAC >>
      qpat_assum `(if tr then _ else _) = lookup_storage _ _` (mp_tac o SYM) >>
      Cases_on `tr` >> simp_tac (srw_ss()) [tload_def,sload_def,contract_storage_def,contract_transient_def]) >>
  irule storage_place_observed_read_live >>
  simp_tac (srw_ss()) [vyperValueTheory.type_slot_size_def] >>
  conj_tac >- decide_tac >> first_assum ACCEPT_TAC
QED

Finalise pop_slot_positive_post_mods
