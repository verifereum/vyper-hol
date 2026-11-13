Theory concretizePtrHistoryUsed
Ancestors
  concretizePtrUsedProduction concretizePtrUsedDemand
  concretizeAnalysisLivenessClosure frameHistoryInstructions frameCfgBoundary
  frameExecutionHistory frameHistoryCfg contextCodegenRel venomInstProps venomWf
  venomExecSemantics venomState venomInst list rich_list finite_map

(* Instruction chronology retains backedges even when their labels coincide. *)
Inductive ptr_history_route:
[~refl:]
  (!fn i s. active_inst fn i s ==> ptr_history_route fn i s i s)
[~advance:]
  (!fn i s j t k u. ptr_history_route fn i s j t /\
    active_inst fn k u /\ u.vs_current_bb = t.vs_current_bb /\
    t.vs_inst_idx <= u.vs_inst_idx ==>
    ptr_history_route fn i s k u)
[~edge:]
  (!fn i s j t k u. ptr_history_route fn i s j t /\
    active_inst fn k u /\ fn_cfg_edge fn t.vs_current_bb u.vs_current_bb ==>
    ptr_history_route fn i s k u)
End

Definition ptr_history_ordered_def:
  ptr_history_ordered fn h i s <=>
    !j t. MEM (j,t) h ==> ptr_history_route fn j t i s
End

Theorem ptr_history_ordered_singleton:
  active_inst fn i s ==> ptr_history_ordered fn [(i,s)] i s
Proof
  simp[ptr_history_ordered_def] >> metis_tac[ptr_history_route_rules]
QED

Theorem ptr_history_ordered_advance:
  ptr_history_ordered fn h i s /\ active_inst fn j t /\
  t.vs_current_bb = s.vs_current_bb /\ s.vs_inst_idx <= t.vs_inst_idx ==>
  ptr_history_ordered fn (h ++ [(j,t)]) j t
Proof
  simp[ptr_history_ordered_def] >> rpt strip_tac >>
  metis_tac[ptr_history_route_rules]
QED

Theorem ptr_history_ordered_edge:
  ptr_history_ordered fn h i s /\ active_inst fn j t /\
  fn_cfg_edge fn s.vs_current_bb t.vs_current_bb ==>
  ptr_history_ordered fn (h ++ [(j,t)]) j t
Proof
  simp[ptr_history_ordered_def] >> rpt strip_tac >>
  metis_tac[ptr_history_route_rules]
QED

Theorem ptr_history_ordered_invariant:
  !vs0 ctx stk PG G tn fn inst s hs h.
  frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
  EVERY wf_function ctx.ctx_functions ==>
  MEM fn ctx.ctx_functions /\ ptr_history_ordered fn h inst s /\
  LIST_REL (\f h0. MEM f.cf_fn ctx.ctx_functions /\
    ptr_history_ordered f.cf_fn h0 f.cf_inst f.cf_state) stk hs
Proof
  ho_match_mp_tac frame_history_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> disch_tac
  >- (drule lookup_function_MEM >> strip_tac >> simp[] >>
      irule ptr_history_ordered_singleton >> simp[])
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume ptr_history_ordered_invariant[next]:
  gvs[] >> drule_all step_preserves_control_flow >> strip_tac >>
  irule ptr_history_ordered_advance >> simp[] >>
  first_assum (irule_at (Pos last)) >> simp[]
QED

Resume ptr_history_ordered_invariant[block]:
  gvs[] >> `wf_function fn` by metis_tac[EVERY_MEM] >>
  drule_all active_terminator_cfg_transition >> strip_tac >>
  irule ptr_history_ordered_edge >> simp[] >>
  first_assum (irule_at (Pos last)) >> simp[]
QED

Resume ptr_history_ordered_invariant[call]:
  gvs[] >> drule lookup_function_MEM >> strip_tac >> simp[] >>
  irule ptr_history_ordered_singleton >> simp[]
QED

Resume ptr_history_ordered_invariant[ret]:
  gvs[] >> drule return_binding_current_bb >> strip_tac >>
  irule ptr_history_ordered_advance >> simp[] >>
  first_assum (irule_at (Pos last)) >> simp[]
QED

Finalise ptr_history_ordered_invariant

Definition ptr_history_cfg_ok_def:
  ptr_history_cfg_ok fn cfg <=>
    (!bb. MEM bb fn.fn_blocks ==>
      bb.bb_instructions <> [] /\
      FIND (\b. b.bb_label = bb.bb_label) fn.fn_blocks = SOME bb /\
      MEM bb.bb_label cfg.cfg_dfs_pre /\ MEM bb.bb_label cfg.cfg_dfs_post) /\
    (!x y. fn_cfg_edge fn x y ==>
      MEM y (cfg_succs_of cfg x) /\ MEM x (cfg_preds_of cfg y))
End

Theorem ptr_history_scan_member:
  !lbls. FIND (\b. b.bb_label = bb.bb_label) blocks = SOME bb /\
    MEM bb.bb_label lbls ==> MEM bb (ml_scan_blocks blocks lbls)
Proof
  Induct >- simp[ml_scan_blocks_def] >>
  rpt gen_tac >> pure_rewrite_tac [MEM] >> strip_tac
  >- (qpat_x_assum `bb.bb_label = h` (SUBST_ALL_TAC o SYM) >>
      simp[ml_scan_blocks_def]) >>
  simp[ml_scan_blocks_def] >>
  Cases_on `FIND (\b. b.bb_label = h) blocks` >> simp[]
QED

Theorem ptr_history_path_snoc[local]:
  !b. ptr_used_path cfg b path c /\ MEM c (cfg_preds_of cfg d) ==>
    ptr_used_path cfg b (path ++ [d]) d
Proof
  Induct_on `path` >> simp[ptr_used_path_def] >> metis_tac[]
QED

Definition ptr_history_crossed_def:
  ptr_history_crossed fn cfg b c <=>
    ?path pred pbb.
      ptr_used_path cfg b path pred /\
      (!lbl. MEM lbl path ==> ?bb.
        MEM bb (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre) /\
        bb.bb_label = lbl /\ bb.bb_instructions <> []) /\
      FIND (\bb. bb.bb_label = pred) fn.fn_blocks = SOME pbb /\
      MEM pred (cfg_preds_of cfg c)
End

Theorem ptr_history_crossed_start[local]:
  ptr_history_cfg_ok fn cfg /\ active_inst fn i s /\
  fn_cfg_edge fn s.vs_current_bb t.vs_current_bb ==>
  ptr_history_crossed fn cfg s.vs_current_bb t.vs_current_bb
Proof
  simp[ptr_history_cfg_ok_def, active_inst_def, ptr_history_crossed_def] >>
  rpt strip_tac >> qexistsl_tac [`[]`, `s.vs_current_bb`, `bb`] >>
  simp[ptr_used_path_def] >> metis_tac[]
QED

Theorem ptr_history_crossed_extend[local]:
  ptr_history_cfg_ok fn cfg /\ active_inst fn i s /\
  ptr_history_crossed fn cfg b s.vs_current_bb /\
  fn_cfg_edge fn s.vs_current_bb t.vs_current_bb ==>
  ptr_history_crossed fn cfg b t.vs_current_bb
Proof
  simp[ptr_history_cfg_ok_def, active_inst_def, ptr_history_crossed_def] >>
  rpt strip_tac >>
  qexistsl_tac [`path ++ [s.vs_current_bb]`, `s.vs_current_bb`, `bb`] >>
  simp[] >> conj_tac
  >- (irule ptr_history_path_snoc >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[ptr_history_scan_member]) >>
  metis_tac[]
QED

Theorem ptr_history_route_shape:
  !fn i s j t. ptr_history_route fn i s j t ==>
  active_inst fn i s /\ active_inst fn j t /\
  !cfg. ptr_history_cfg_ok fn cfg ==>
    (s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx <= t.vs_inst_idx) \/
    ptr_history_crossed fn cfg s.vs_current_bb t.vs_current_bb
Proof
  ho_match_mp_tac ptr_history_route_ind >> rpt conj_tac >> rpt gen_tac
  >- simp[]
  >- (strip_tac >> simp[] >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >>
      gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  strip_tac >> simp[] >> rpt strip_tac >> first_x_assum drule >> strip_tac
  >- metis_tac[ptr_history_crossed_start] >>
  metis_tac[ptr_history_crossed_extend]
QED

Theorem ptr_history_route_used:
  ptr_history_route fn seed ss inst s /\ ptr_history_cfg_ok fn cfg /\
  ml_used_gen a bp mems seed ==>
  MEM a (ml_lookup
    (SND (ml_iterate_fuel (concretize_memloc_fuel fn) bp mems sizes pallocas cfg fn FEMPTY FEMPTY))
    (s.vs_current_bb,s.vs_inst_idx))
Proof
  strip_tac >> drule ptr_history_route_shape >> strip_tac >>
  first_x_assum (qspec_then `cfg` mp_tac) >> simp[] >> strip_tac
  >- (gvs[active_inst_def] >>
      `bb = bb'` by (gvs[ptr_history_cfg_ok_def] >> metis_tac[optionTheory.SOME_11]) >>
      gvs[] >> qpat_x_assum `bb.bb_label = s.vs_current_bb` (SUBST_ALL_TAC o SYM) >>
      irule ptr_used_production_seed_records >>
      gvs[ptr_history_cfg_ok_def] >> metis_tac[]) >>
  gvs[active_inst_def, ptr_history_crossed_def] >>
  qpat_x_assum `bb'.bb_label = s.vs_current_bb` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `bb.bb_label = ss.vs_current_bb` (SUBST_ALL_TAC o SYM) >>
  irule ptr_used_production_path_records >>
  `EVERY (\bb. bb.bb_instructions <> []) fn.fn_blocks` by
    gvs[ptr_history_cfg_ok_def, EVERY_MEM] >>
  fs[ptr_history_cfg_ok_def] >>
  qexistsl_tac [`ss.vs_inst_idx`, `path`, `pbb`, `pred`, `bb`] >>
  simp[] >>
  metis_tac[ptr_history_scan_member]
QED

Theorem ptr_history_current_used:
  frame_history vs0 ctx stk PG G tn fn inst s hs h /\
  EVERY wf_function ctx.ctx_functions /\ ptr_history_cfg_ok fn cfg /\
  MEM (seed,ss) h /\ ml_used_gen a bp mems seed ==>
  MEM a (ml_lookup
    (SND (ml_iterate_fuel (concretize_memloc_fuel fn) bp mems sizes pallocas cfg fn FEMPTY FEMPTY))
    (s.vs_current_bb,s.vs_inst_idx))
Proof
  rpt strip_tac >> irule ptr_history_route_used >> simp[] >>
  drule ptr_history_ordered_invariant >> simp[] >> strip_tac >>
  gvs[ptr_history_ordered_def] >> metis_tac[]
QED

Theorem ptr_history_saved_used:
  frame_history vs0 ctx stk PG G tn fn inst s hs h /\
  EVERY wf_function ctx.ctx_functions /\ n < LENGTH stk /\
  ptr_history_cfg_ok (EL n stk).cf_fn cfg /\
  MEM (seed,ss) (EL n hs) /\ ml_used_gen a bp mems seed ==>
  MEM a (ml_lookup
    (SND (ml_iterate_fuel (concretize_memloc_fuel (EL n stk).cf_fn)
      bp mems sizes pallocas cfg (EL n stk).cf_fn FEMPTY FEMPTY))
    ((EL n stk).cf_state.vs_current_bb,(EL n stk).cf_state.vs_inst_idx))
Proof
  rpt strip_tac >> irule ptr_history_route_used >> simp[] >>
  drule ptr_history_ordered_invariant >> simp[] >> strip_tac >>
  gvs[LIST_REL_EL_EQN, ptr_history_ordered_def] >> metis_tac[]
QED
