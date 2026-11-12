(* Boundaries for correlated owned target-prefix coverage. *)
Theory lowerDloadOwnedTransitionBoundary
Ancestors
  lowerDloadSafetyRelation lowerDloadSafetyAmbient lowerDloadSafetyLocations
  lowerDloadSafetyRootCoverage lowerDloadReturnAlignment
  lowerDloadSafetyOwnership finite_map list o1PassContract
  o1ContractLowerDload contextCodegenRel venomInst venomExecSemantics
  lowerDloadSafetyEntry lowerDloadSafetyWriteCoverage lowerDloadConfiguredOrigins
  venomState ptrDiscipline
Libs lowerDloadOwnedTransitionPackageLib lowerDloadReturnPackageLib

Theorem ld_owned_self_stable:
  ld_global lo A (f::fs) /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) (f::fs) /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
    list_precedes (EL j (f::fs)).lf_fn.fn_name
                  (EL k (f::fs)).lf_fn.fn_name names) /\
  (!g. MEM g fs ==> FRANGE g.lf_H SUBSET ld_slots A fs /\
    (!a. MEM (SOME a) g.lf_Q ==> a IN ld_slots A fs)) ==>
  ^ld_probe_stable lo P Sigma names fs f A A (f::fs)
Proof
  simp[] >> metis_tac[]
QED

Theorem ld_owned_prefix_pack:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t0 A frames N /\
  ^ld_probe_stable lo P Sigma names fs f0 A0 A frames /\
  fn' = ld_image (HD frames) /\
  ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
  ld_prefix C' fn' X p h t0 t /\ active_inst fn' ti t ==>
  ^ld_owned lo P C C' vs0 Sigma names fn' ti t
Proof
  simp[] >> strip_tac >>
  `active_inst fn' (EL h X) t` by metis_tac[lowerDloadSafetyKernelTheory.ld_prefix_active] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks)` by
    (`o1_ctx_shape C` by fs[] >>
     `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
       (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
     qpat_x_assum `fn' = FST _` (fn th => rewrite_tac[th]) >>
     Cases_on `lower_dload_function_supply (Sigma fn.fn_name) fn` >>
     drule lower_dload_function_supply_labels >> simp[fn_labels_def]) >>
  `ti = EL h X` by
    (drule_all ld_active_lookup >> strip_tac >>
     qpat_x_assum `active_inst fn' (EL h X) t` kall_tac >>
     drule_all ld_active_lookup >> simp[get_instruction_def]) >>
  simp[] >>
  qexistsl_tac [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`,`t0`,`A`,`frames`,`N`,`X`,`p`,`h`] >>
  gvs[] >> metis_tac[]
QED

Theorem ld_point_owned:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ^ld_probe_point lo P C C' vs0 stk fn fn' cs fs f0 A0 Sigma names bb t /\
  active_inst fn' ti t ==>
  ^ld_owned lo P C C' vs0 Sigma names fn' ti t
Proof
  strip_tac >> qmatch_goalsub_abbrev_tac `Goal` >>
  fs[] >> drule_all (SRULE [] ld_owned_prefix_pack) >> gvs[Abbr `Goal`]
QED

Theorem ld_transfer_point_owned:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ^ld_transfer_point lo P C C' vs0 stk fn fn' source fs f0 A0 Sigma names bb t /\
  active_inst fn' ti t ==>
  ^ld_owned lo P C C' vs0 Sigma names fn' ti t
Proof
  strip_tac >> qmatch_goalsub_abbrev_tac `Goal` >>
  fs[] >> drule_all (SRULE [] ld_owned_prefix_pack) >> gvs[Abbr `Goal`]
QED

Theorem ld_owned_root:
  o1_run_state_ok vs0 /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  fn' = FST (lower_dload_function_supply (Sigma fn.fn_name) fn) /\
  enters_block fn'
    (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t /\
  active_inst fn' ti t ==>
  ^ld_owned lo P C C' vs0 Sigma names fn' ti t
Proof
  strip_tac >>
  Cases_on `lower_dload_function_supply (Sigma fn.fn_name) fn` >> gvs[] >>
  `enters_block fn
    (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t` by
    (irule lower_dload_function_supply_enters_block_origin >> metis_tac[]) >>
  `t = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` by
    (irule ld_enters_entry >> simp[] >> metis_tac[]) >>
  `t.vs_inst_idx = 0` by simp[] >>
  `?inst. active_inst fn inst t` by
    (irule ld_active_zero_origin >> metis_tac[]) >>
  drule_all ld_sync_entry >>
  disch_then (qspecl_then [`Sigma fn.fn_name`,`lo`] strip_assume_tac) >>
  `fn' = ld_image f` by simp[ld_image_def] >>
  drule_all ld_pair_zero_witness >>
  disch_then (qspec_then `C'` strip_assume_tac) >>
  simp[] >>
  qexistsl_tac [`[]`,`[]`,`FEMPTY`,`entry_taint`,`fn`,`inst`,`t`,`t`,
               `FEMPTY`,`[f]`,`1`,`X`,`p`,`0`] >>
  simp[] >> rpt strip_tac >> gvs[]
QED
