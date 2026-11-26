(* The keyword replay selects a later source and machine endpoint for the
   existing positional rows. It does not change their compiler intervals. *)
Theory bodyExtKeywordPackingRowsMods
Ancestors
  bodyExtPosSavedRowMods gasOutcomeFull vyperStorageFootprint vyperStorageTrace
  vyperEvalExprPreservesScopesDom vyperStorageBackend
  exprSimHypsDefs loweringPosts bodyPtrDefs list

Triviality keyword_replay_horizon:
  eval_exprs cx kw_es (ee with gas_obs := obs) = (INL kws,ke) /\
  valid_horizon cx st0 H ke.storage_trace ==>
  valid_horizon cx st0 H ee.storage_trace
Proof
  strip_tac >>
  `storage_trace_frame (eval_exprs cx kw_es)` by simp[evaluate_storage_trace_frame] >>
  drule_all storage_trace_frame_prefix >> strip_tac >>
  fs[] >> metis_tac[valid_horizon_append]
QED

Triviality keyword_row_at_index:
  LENGTH av = LENGTH xs /\
  LIST_REL (\(e,sv) v. ext_pos_saved_row_mods lo cenv cx kw_es a b H e sv v ee G tn t)
    (ZIP (xs,av)) vs /\ i < LENGTH xs ==>
  ext_pos_saved_row_mods lo cenv cx kw_es a b H
    (EL i xs) (EL i av) (EL i vs) ee G tn t
Proof
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  `EL i (ZIP (xs,av)) = (EL i xs,EL i av)` by (irule EL_ZIP >> simp[]) >>
  `i < LENGTH xs /\ i < LENGTH av` by simp[] >>
  qpat_assum `!n. n < LENGTH xs /\ n < LENGTH av ==> _`
    (qspec_then `i` (drule_then mp_tac)) >>
  qpat_assum `EL i (ZIP (xs,av)) = _` (fn th => pure_rewrite_tac[th]) >>
  simp[pairTheory.UNCURRY]
QED

Theorem ext_keyword_packing_rows_mods:
  LENGTH av = LENGTH xs /\
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env ee /\
  local_ptrs_reserved cenv s2 /\
  s2.cs_next_var <= s5.cs_next_var /\ s2.cs_next_id <= s5.cs_next_id /\
  wb_frame cenv ee ke s2 u zg /\ ghost_kept_at lo cenv ee s2 G2 tn2 u Gg tng /\
  u.vs_alloca_next <= zg.vs_alloca_next /\ zg.vs_labels = u.vs_labels /\
  eval_exprs cx kw_es (ee with gas_obs := obs) = (INL kws,ke) /\
  storage_trace_domain cx st0 ke.storage_trace /\
  (!obs' kws'. ~exprs_can_mutate cenv kw_es /\
     eval_exprs cx kw_es (ee with gas_obs := obs') = (INL kws',ke) ==>
     ke.scopes = ee.scopes /\ ke.immutables = ee.immutables /\
     (!tr. get_storage cx ke tr = get_storage cx ee tr)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee u /\
     LIST_REL (\(e,sv) v. ext_pos_saved_row_mods lo cenv cx kw_es sa s2 H e sv v ee G2 tn2 u)
       (ZIP (xs,av)) vs) /\
  (!H. valid_horizon cx st0 H ke.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ke zg /\ immutable_frame_mods func cenv cx ke zg /\
     ghost_inv_at_mods (DF H) lo d cenv cx ke Gg tng zg /\ dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!H e sv v.
     contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env ee /\
     ext_pos_saved_row_mods lo cenv cx kw_es sa s2 H e sv v ee G2 tn2 u /\
     local_ptrs_reserved cenv s2 /\
     s2.cs_next_var <= s5.cs_next_var /\ s2.cs_next_id <= s5.cs_next_id /\
     wb_frame cenv ee ke s2 u zg /\ ghost_kept_at lo cenv ee s2 G2 tn2 u Gg tng /\
     (!x w. not_fresh_at s2 x /\ lookup_var x u = SOME w ==> lookup_var x zg = SOME w) /\
     (!aid b. FLOOKUP u.vs_allocas aid = SOME b ==> FLOOKUP zg.vs_allocas aid = SOME b) /\
     u.vs_alloca_next <= zg.vs_alloca_next /\ zg.vs_labels = u.vs_labels /\
     MAP FDOM ke.scopes = MAP FDOM ee.scopes /\
     (~exprs_can_mutate cenv kw_es ==> ke.scopes = ee.scopes /\ ke.immutables = ee.immutables /\
        (!tr. get_storage cx ke tr = get_storage cx ee tr)) /\
     stmt_state_rel H ctx func cenv cx ee u /\ stmt_state_rel H ctx func cenv cx ke zg /\
     immutable_frame_mods func cenv cx ke zg /\
     ghost_inv_at_mods (DF H) lo d cenv cx ke Gg tng zg /\ dead_lo_ok_mods H (DF H) lo cenv cx ==>
     ext_pos_saved_row_mods lo cenv cx kw_es sa s5 H e sv v ke Gg tng zg) ==>
  !i. i < LENGTH xs ==>
    ext_pos_saved_row_mods lo cenv cx kw_es sa s5 (storage_trace_horizon ke.storage_trace)
      (EL i xs) (EL i av) (EL i vs) ke Gg tng zg /\
    (!H. valid_horizon cx st0 H ke.storage_trace ==>
      vv_storage_live H cx (EL i av) ke zg) /\
    (!H. valid_horizon cx st0 H ke.storage_trace ==>
      ext_pos_saved_row_mods lo cenv cx kw_es sa s5 H
        (EL i xs) (EL i av) (EL i vs) ke Gg tng zg)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MAP FDOM ke.scopes = MAP FDOM ee.scopes` by
    (drule eval_exprs_preserves_scopes_dom >> simp[]) >>
  `~exprs_can_mutate cenv kw_es ==> ke.scopes = ee.scopes /\ ke.immutables = ee.immutables /\
     (!tr. get_storage cx ke tr = get_storage cx ee tr)` by
    (disch_tac >>
     qpat_assum `!obs' kws'. ~exprs_can_mutate _ _ /\ _ ==> _`
       (qspecl_then [`obs`,`kws`] mp_tac) >> simp[]) >>
  qx_gen_tac `i` >> disch_tac >>
  `!H. valid_horizon cx st0 H ke.storage_trace ==>
     ext_pos_saved_row_mods lo cenv cx kw_es sa s5 H
       (EL i xs) (EL i av) (EL i vs) ke Gg tng zg` by
    (qx_gen_tac `H` >> disch_tac >>
     `valid_horizon cx st0 H ee.storage_trace` by
       (drule_all_then ACCEPT_TAC keyword_replay_horizon) >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H ke.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     `ext_pos_saved_row_mods lo cenv cx kw_es sa s2 H
       (EL i xs) (EL i av) (EL i vs) ee G2 tn2 u` by
       (drule_all keyword_row_at_index >> simp[]) >>
     qpat_assum `!H e sv v. _ ==> ext_pos_saved_row_mods _ _ _ _ _ s5 H e sv v _ _ _ _`
       irule >>
     qpat_assum `wb_frame cenv ee ke s2 u zg`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [wb_frame_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (first_x_assum irule >> fs[storage_trace_domain_def]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ext_pos_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then (mp_tac o REWRITE_RULE [ext_pos_saved_row_mods_def])) >>
  simp[Excl "vv_storage_live_def"]
QED
