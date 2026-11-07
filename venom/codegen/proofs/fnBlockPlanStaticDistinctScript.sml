Theory fnBlockPlanStaticDistinct
Ancestors
  fnLineageStatic indexedLists finite_map livenessDefs stackPlanGen
  cfgNormSupplyProofs venomInst list livenessTerminationProofs dfAnalyzeDefs dfHelperDefs
  fnFrameStepsPhi

Definition distinct_phi_maps_acc_def:
  distinct_phi_maps_acc src n phis acc =
    FOLDL (\(om,mm) (i,phi).
      (FOLDL (\m (l,v). m |+ (v,i)) om (phi_pairs phi.inst_operands),
       case FIND (\(l,v). l = src) (phi_pairs phi.inst_operands) of
         NONE => mm | SOME (_,v) => mm |+ (i,v)))
      acc (MAPi (\k phi. (n+k,phi)) phis)
End

Theorem distinct_phi_maps_acc_cons[local]:
  distinct_phi_maps_acc src n (phi::phis) (om,mm) =
  distinct_phi_maps_acc src (SUC n) phis
    (FOLDL (\m (l,v). m |+ (v,n)) om (phi_pairs phi.inst_operands),
     case FIND (\(l,v). l = src) (phi_pairs phi.inst_operands) of
       NONE => mm | SOME (_,v) => mm |+ (n,v))
Proof
  simp[distinct_phi_maps_acc_def, MAPi_def, combinTheory.o_DEF] >>
  AP_TERM_TAC >> irule MAPi_CONG >> simp[]
QED

Theorem distinct_phi_maps_acc_consistent[local]:
  !phis n om mm src.
    phi_uses_disjoint phis /\
    (!i v. FLOOKUP mm i = SOME v ==> FLOOKUP om v = SOME i) /\
    (!i v phi. FLOOKUP mm i = SOME v /\ MEM phi phis ==>
      ~MEM v (inst_uses phi)) ==>
    !i v. FLOOKUP (SND (distinct_phi_maps_acc src n phis (om,mm))) i = SOME v ==>
      FLOOKUP (FST (distinct_phi_maps_acc src n phis (om,mm))) v = SOME i
Proof
  Induct >- simp[distinct_phi_maps_acc_def] >>
  rpt gen_tac >> strip_tac >> simp[distinct_phi_maps_acc_cons] >>
  first_x_assum match_mp_tac >>
  gvs[phi_uses_disjoint_def] >>
  Cases_on `FIND (\(l,v). l = src) (phi_pairs h.inst_operands)`
  >- (simp[phi_pair_updates_lookup] >>
      rpt conj_tac >> rpt gen_tac >> strip_tac >>
      gvs[MEM_MAP, pairTheory.EXISTS_PROD, inst_uses_def] >>
      metis_tac[MEM_phi_pairs_SND_operand_vars]) >>
  rename1 `FIND _ _ = SOME selected` >> PairCases_on `selected` >>
  drule FIND_SOME_MEM >> strip_tac >>
  simp[phi_pair_updates_lookup, FLOOKUP_UPDATE] >>
  gvs[EVERY_MEM] >>
  conj_tac >> rpt gen_tac >> Cases_on `n = i` >>
  gvs[MEM_MAP, pairTheory.EXISTS_PROD, inst_uses_def] >>
  metis_tac[MEM_phi_pairs_SND_operand_vars]
QED

Theorem build_phi_maps_matching_consistent:
  !phis src om mm i v.
    phi_uses_disjoint phis /\ build_phi_maps src phis = (om,mm) /\
    FLOOKUP mm i = SOME v ==> FLOOKUP om v = SOME i
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`phis`, `0`, `FEMPTY`, `FEMPTY`, `src`]
    mp_tac distinct_phi_maps_acc_consistent >> simp[] >>
  `distinct_phi_maps_acc src 0 phis (FEMPTY,FEMPTY) = build_phi_maps src phis` by
    (simp[NoAsms, distinct_phi_maps_acc_def, build_phi_maps_def] >>
     AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
     simp[FUN_EQ_THM, pairTheory.FORALL_PROD] >>
     rpt gen_tac >>
     Cases_on `FIND (\(l,v). l = src) (phi_pairs phi.inst_operands)` >>
     gvs[AllCaseEqs()]) >>
  gvs[]
QED

Theorem phi_input_fold_distinct[local]:
  !live acc placed om mm.
    ALL_DISTINCT live /\ ALL_DISTINCT acc /\
    (!i v. FLOOKUP mm i = SOME v ==> FLOOKUP om v = SOME i) /\
    (!v i. MEM v acc /\ FLOOKUP om v = SOME i ==> MEM i placed) /\
    (!v. MEM v acc /\ FLOOKUP om v = NONE ==> ~MEM v live) ==>
    ALL_DISTINCT (FST (FOLDL (\(acc,placed) v.
      case FLOOKUP om v of
        NONE => (acc ++ [v],placed)
      | SOME i => if MEM i placed then (acc,placed)
                  else case FLOOKUP mm i of
                         NONE => (acc,placed)
                       | SOME w => (acc ++ [w],i::placed))
      (acc,placed) live))
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  gvs[] >> Cases_on `FLOOKUP om h`
  >- (simp[] >> first_x_assum irule >>
      simp[ALL_DISTINCT_APPEND] >>
      rpt conj_tac >> rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[]) >>
  rename1 `FLOOKUP om h = SOME idx` >>
  Cases_on `MEM idx placed`
  >- (simp[] >> first_x_assum irule >> metis_tac[]) >>
  Cases_on `FLOOKUP mm idx`
  >- (simp[] >> first_x_assum irule >> metis_tac[]) >>
  simp[] >> first_x_assum irule >>
  simp[ALL_DISTINCT_APPEND] >>
  rename1 `FLOOKUP mm idx = SOME chosen` >>
  `FLOOKUP om chosen = SOME idx` by metis_tac[] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  metis_tac[optionTheory.SOME_11, optionTheory.NOT_SOME_NONE]
QED

Theorem distinct_pair_projection:
  (\(x:'a,y:'b). x) = FST
Proof
  simp[FUN_EQ_THM, pairTheory.FORALL_PROD]
QED

Theorem input_vars_from_ALL_DISTINCT:
  !src instrs live.
    phi_uses_disjoint (collect_phis instrs) /\ ALL_DISTINCT live ==>
    ALL_DISTINCT (input_vars_from src instrs live)
Proof
  rpt gen_tac >> strip_tac >> simp[input_vars_from_def] >>
  Cases_on `NULL (collect_phis instrs)` >- simp[] >> simp[] >>
  Cases_on `build_phi_maps src (collect_phis instrs)` >>
  rename1 `build_phi_maps _ _ = (om,mm)` >> simp[] >>
  rewrite_tac[distinct_pair_projection] >>
  irule phi_input_fold_distinct >> simp[] >>
  metis_tac[build_phi_maps_matching_consistent]
QED

Theorem distinct_list_union[local]:
  ALL_DISTINCT xs /\ ALL_DISTINCT ys ==> ALL_DISTINCT (list_union xs ys)
Proof
  simp[list_union_def, ALL_DISTINCT_APPEND, FILTER_ALL_DISTINCT, MEM_FILTER]
QED

Theorem distinct_fold_union[local]:
  !ls acc. EVERY ALL_DISTINCT ls /\ ALL_DISTINCT acc ==>
    ALL_DISTINCT (FOLDL list_union acc ls)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[distinct_list_union]
QED

Theorem distinct_backward_fold[local]:
  !instrs idx acc im.
    ALL_DISTINCT acc /\ (!k vs. FLOOKUP im k = SOME vs ==> ALL_DISTINCT vs) ==>
    ALL_DISTINCT (FST (df_fold_backward (liveness_transfer bbs) (lbl:string) instrs idx acc im)) /\
    (!k vs. FLOOKUP (SND (df_fold_backward (liveness_transfer bbs) (lbl:string) instrs idx acc im)) k = SOME vs ==>
       ALL_DISTINCT vs)
Proof
  Induct >- (rw[df_fold_backward_def, FLOOKUP_UPDATE] >>
             gvs[AllCaseEqs()] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> disch_then (qspec_then `idx+1` mp_tac) >>
  simp[Once df_fold_backward_def] >>
  Cases_on `df_fold_backward (liveness_transfer bbs) lbl instrs (idx+1) acc im` >>
  simp[] >> strip_tac >>
  once_rewrite_tac[df_fold_backward_def] >> simp[] >>
  rw[FLOOKUP_UPDATE, liveness_transfer_def, live_update_ALL_DISTINCT] >>
  gvs[AllCaseEqs()] >> metis_tac[live_update_ALL_DISTINCT]
QED

Definition distinct_live_state_def:
  distinct_live_state st <=>
    !k vs. FLOOKUP st.ds_inst k = SOME vs ==> ALL_DISTINCT vs
End

Theorem distinct_live_query[local]:
  distinct_live_state st ==> ALL_DISTINCT (df_at [] st lbl i)
Proof
  rw[distinct_live_state_def, df_at_def] >>
  Cases_on `FLOOKUP st.ds_inst (lbl,i)` >> simp[] >> metis_tac[]
QED

Theorem distinct_liveness_block[local]:
  EVERY (\bb. phi_uses_disjoint (collect_phis bb.bb_instructions)) bbs /\
  distinct_live_state st ==> distinct_live_state (liveness_block bbs cfg lbl st)
Proof
  strip_tac >>
  `!succ. ALL_DISTINCT (liveness_edge_transfer bbs succ lbl (df_at [] st succ 0))` by
    (gen_tac >> simp[liveness_edge_transfer_def] >>
     Cases_on `lookup_block succ bbs`
     >- simp[distinct_live_query] >>
     rename1 `lookup_block succ bbs = SOME target_bb` >>
     simp[] >> irule input_vars_from_ALL_DISTINCT >>
     simp[distinct_live_query] >>
     gvs[EVERY_MEM] >> metis_tac[selected_block_mem]) >>
  simp[liveness_block_def] >> pairarg_tac >> simp[distinct_live_state_def] >>
  qmatch_asmsub_abbrev_tac `df_fold_block _ _ _ _ out` >>
  `ALL_DISTINCT out` by
    (simp[Abbr `out`] >> irule distinct_fold_union >> simp[EVERY_MAP, EVERY_MEM]) >>
  `!k vs. FLOOKUP inst_map k = SOME vs ==> ALL_DISTINCT vs` by
    (qpat_x_assum `df_fold_block _ _ _ _ _ = _` mp_tac >>
     simp[df_fold_block_def] >> strip_tac >>
     mp_tac distinct_backward_fold >>
     disch_then (qspecl_then
       [`case lookup_block lbl bbs of NONE => [] | SOME bb => bb.bb_instructions`,
        `0`,`out`,`FEMPTY`] mp_tac) >> simp[] >> metis_tac[]) >>
  rw[df_flookup_funion] >> gvs[AllCaseEqs(), distinct_live_state_def] >> metis_tac[]
QED

Theorem distinct_live_fuel[local]:
  !fuel wl st.
    EVERY (\bb. phi_uses_disjoint (collect_phis bb.bb_instructions)) bbs /\
    distinct_live_state st ==>
    distinct_live_state (SND (wl_iterate_fuel fuel (liveness_changed bbs)
      (liveness_block bbs cfg) (cfg_preds_of cfg) wl st))
Proof
  Induct >- simp[worklistDefsTheory.wl_iterate_fuel_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `wl`
  >- simp[worklistDefsTheory.wl_iterate_fuel_def] >>
  simp[worklistDefsTheory.wl_iterate_fuel_def] >>
  Cases_on `liveness_changed bbs h st (liveness_block bbs cfg h st)` >>
  simp[worklistDefsTheory.wl_step_def] >>
  first_x_assum irule >> simp[distinct_liveness_block]
QED

Theorem analyzed_live_vars_ALL_DISTINCT:
  codegen_ready_fn fn ==> ALL_DISTINCT (live_vars_at (liveness_analyze fn) lbl i)
Proof
  strip_tac >> simp[liveness_analyze_def, live_vars_at_def] >>
  irule distinct_live_query >>
  qx_choose_then `fuel` (SUBST1_TAC o SYM)
    liveness_recompute_fuel_agreement >>
  simp[liveness_recompute_fuel_def] >> irule distinct_live_fuel >>
  simp[init_df_state_def, distinct_live_state_def, EVERY_MEM] >>
  metis_tac[phi_codegen_uses_disjoint]
QED

Theorem ready_edge_inputs_ALL_DISTINCT:
  codegen_ready_fn fn /\ lookup_block target fn.fn_blocks = SOME target_bb ==>
  ALL_DISTINCT (input_vars_from src target_bb.bb_instructions
    (live_vars_at (liveness_analyze fn) target 0))
Proof
  strip_tac >> irule input_vars_from_ALL_DISTINCT >>
  simp[analyzed_live_vars_ALL_DISTINCT] >>
  irule phi_codegen_uses_disjoint >> metis_tac[selected_block_mem]
QED
