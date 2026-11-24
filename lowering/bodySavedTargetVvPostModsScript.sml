(* Keep the original VV and allocation interval across a read-only target. *)
Theory bodySavedTargetVvPostMods
Ancestors
  bodyFullPostsMods targetPurePostTransport stateRelProj exprBopSimProps
  exprSimWordArgs exprSimProps exprLoweringProps loweringStateRelDefs
  loweringPosts compileEnv context vyperState vyperStorageBackend

Theorem saved_linked_operand_exists[local]:
  vv_holds_mods ce cx ty raw vv es s ==>
  ?w. eval_operand (vv_operand vv) s = SOME w
Proof
  Cases_on `vv` >> simp[vv_holds_mods_def]
  >- metis_tac[target_saved_operand_exists] >>
  rename1 `p.ptr_location = LocCode` >> Cases_on `p.ptr_location = LocCode` >>
  simp[vv_operand_def] >> metis_tac[target_saved_operand_exists,vv_operand_def]
QED

Theorem saved_linked_holds_frame[local]:
  vv_holds_mods ce cx ty raw vv mid s /\ vv_at ce cx ty sa sm mid raw vv s /\
  wb_frame ce mid mid sm s u /\
  (!w. eval_operand (vv_operand vv) s = SOME w ==>
       eval_operand (vv_operand vv) u = SOME w) /\
  vv_storage_live H cx vv mid s /\
  storage_rel H cx.txn.target mid u /\ transient_rel H cx.txn.target mid u ==>
  vv_holds_mods ce cx ty raw vv mid u
Proof
  strip_tac >> Cases_on `vv` >> fs[vv_holds_mods_def]
  >- (irule target_saved_holds_frame >> qexistsl [`H`,`s`,`sa`,`sm`] >> simp[]) >>
  rename1 `p.ptr_location = LocCode` >> Cases_on `p.ptr_location = LocCode` >> fs[]
  >- (fs[vv_operand_def,immutable_holds_mods_def,immutable_holds_def] >> metis_tac[]) >>
  irule target_saved_holds_frame >> qexistsl [`H`,`s`,`sa`,`sm`] >> simp[]
QED

Theorem saved_linked_holds_oracles[local]:
  vv_holds_mods ce cx ty raw vv
    (mid with <|gas_obs := gs; outcomes := os; requests := rq;
                logs := lg; storage_trace := st|>) s <=>
  vv_holds_mods ce cx ty raw vv mid s
Proof
  Cases_on `vv` >> simp[vv_holds_mods_def, target_saved_holds_oracles] >>
  rename1 `p.ptr_location = LocCode` >> Cases_on `p.ptr_location = LocCode` >>
  simp[immutable_holds_mods_def, immutable_holds_def,
       SRULE [] target_saved_read_oracles]
QED

Theorem saved_linked_place_frame[local]:
  vv_place_ptr_mods ce cx mid s raw vv /\ ee.immutables = mid.immutables /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  (!id q sz w. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var q) sz) /\
        lookup_var q s = SOME w ==> lookup_var q u = SOME w) ==>
  vv_place_ptr_mods ce cx ee u raw vv
Proof
  Cases_on `vv` >> Cases_on `raw` >> simp[vv_place_ptr_mods_def]
  >- (rename1 `PlaceR place` >> Cases_on `place` >>
      simp[vv_place_ptr_def,vv_operand_def] >> metis_tac[]) >>
  simp[vv_place_ptr_def,vv_operand_def]
QED

Theorem saved_target_same_source_frame[local]:
  wb_frame ce mid ee sm s u /\ ee.scopes = mid.scopes ==>
  wb_frame ce mid mid sm s u
Proof
  strip_tac >> fs[wb_frame_def,locals_kept_def,popped_kept_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem saved_target_vv_post_mods:
  vv_post_mods H ctx func cenv cx e es sa sm s0 mid raw vv s /\
  stmt_state_rel H ctx func cenv cx ee u /\
  immutable_frame_mods func cenv cx ee u /\
  storage_well_formed_on cx ee (FST H) /\
  wb_frame cenv mid ee sm s u /\
  ee = mid with <|gas_obs := gs; outcomes := os; requests := rq;
                   logs := lg; storage_trace := st|> /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!l. vv_operand vv <> Label l) /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ vv_storage_live H cx vv mid s ==>
  vv_post_mods H ctx func cenv cx e ee sa sm u ee raw vv u /\
  vv_storage_live H cx vv ee u /\ wb_frame cenv es ee sa s0 u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  qpat_x_assum `ee = _` (mk_asm "oracles") >>
  `ee.scopes = mid.scopes /\ ee.immutables = mid.immutables` by
    (asm "oracles" (once_rewrite_tac o single) >> simp[]) >>
  drule_all_then assume_tac saved_target_same_source_frame >>
  `wb_frame cenv es mid sa s0 s` by
    (pure_rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by fs[locals_kept_def] >>
  `wb_frame cenv es ee sa s0 u` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ es s0`
       (mp_then Any irule wb_frame_trans) >> asm_rewrite_tac[] >>
     qexistsl [`mid`,`sm`,`s`] >> asm_rewrite_tac[]) >>
  `!w. eval_operand (vv_operand vv) s = SOME w ==>
       eval_operand (vv_operand vv) u = SOME w` by
    (rpt strip_tac >> irule eval_operand_frame >> simp[] >>
     qexistsl [`sm`,`s`] >> fs[wb_frame_def] >> first_assum ACCEPT_TAC) >>
  drule_then strip_assume_tac saved_linked_operand_exists >>
  `eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s` by simp[] >>
  `vv_storage_live H cx vv mid u` by
    (irule target_saved_storage_live_frame >> metis_tac[]) >>
  `vv_storage_live H cx vv ee u` by
    (asm "oracles" (once_rewrite_tac o single) >>
     simp[SRULE [] target_saved_regions_oracles]) >>
  simp[vv_post_mods_def] >>
  rpt conj_tac
  >- suspend "holds"
  >- suspend "at"
  >- suspend "place"
  >> suspend "own"
QED

Resume saved_target_vv_post_mods[holds]:
  asm "oracles" (once_rewrite_tac o single) >> simp[saved_linked_holds_oracles] >>
  irule saved_linked_holds_frame >> simp[] >>
  qexistsl [`H`,`s`,`sa`,`sm`] >> simp[] >>
  qpat_assum `stmt_state_rel _ _ _ _ _ ee u`
    (mp_tac o MATCH_MP stmt_state_rel_state_rel) >>
  asm "oracles" (once_rewrite_tac o single) >>
  simp[state_rel_def,storage_rel_def,transient_rel_def]
QED

Resume saved_target_vv_post_mods[at]:
  asm "oracles" (once_rewrite_tac o single) >> simp[SRULE [] target_saved_regions_oracles] >>
  irule (cj 1 target_saved_value_region_frame) >> simp[] >>
  qexistsl [`func`,`s`,`sm`] >> simp[] >>
  metis_tac[stmt_state_rel_local_ptrs_alloca,local_ptrs_reserved_next_var]
QED

Resume saved_target_vv_post_mods[place]:
  irule saved_linked_place_frame >> simp[] >> qexistsl [`mid`,`s`] >> simp[] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `local_ptrs_reserved cenv sm`
    (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
  qpat_assum `wb_frame cenv mid mid sm s u`
    (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  first_x_assum irule >> asm_rewrite_tac[] >>
  qpat_x_assum `!n1 n2 p sz1 sz2. _` drule >> simp[]
QED

Resume saved_target_vv_post_mods[own]:
  strip_tac >>
  asm "oracles" (once_rewrite_tac o single) >> simp[SRULE [] target_saved_regions_oracles] >>
  irule (cj 2 target_saved_value_region_frame) >> simp[] >>
  qexistsl [`func`,`s`,`sm`] >> simp[] >>
  metis_tac[stmt_state_rel_local_ptrs_alloca,local_ptrs_reserved_next_var]
QED
Finalise saved_target_vv_post_mods
