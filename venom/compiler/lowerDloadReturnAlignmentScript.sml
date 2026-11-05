(* Shared package supply boundaries; activity/control boundaries follow here. *)
Theory lowerDloadReturnAlignment
Ancestors
  lowerDloadReturnInterfaceProbe lowerDloadConfiguredOrigins
  lowerDloadExpansionEndpoint lowerDloadSafetyLocations lowerDloadSafetyKernel
  venomExecSemantics venomInst venomWf o1ContractLowerDload list
Libs
  lowerDloadReturnPackageLib

Theorem ld_sync_supply_covered:
  (!f. MEM f C.ctx_functions ==> ir_supply_covers_fn (Sigma f.fn_name) f) /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames ==>
  ir_supply_covers_fn (HD frames).lf_supply fn
Proof
  strip_tac >> drule ld_sync_active >> strip_tac >>
  `MEM (HD frames) frames` by (Cases_on `frames` >> gvs[]) >>
  `MEM fn C.ctx_functions` by
    (qpat_x_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ld_sync_def, EVERY_MEM] >> metis_tac[]) >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

(* The production specialization changes only Ambient, not Point/Terminal. *)
Theorem ld_covered_package_induction:
  ^ld_package_induction ^ld_covered_ambient ^ld_probe_point ^ld_probe_terminal
Proof
  MATCH_ACCEPT_TAC ld_return_package_induction
QED

val _ = List.app (fn th => if null (hyp th) then ()
            else raise Fail "return package supply boundary has hypotheses")
  [ld_sync_supply_covered, ld_covered_package_induction];

Theorem ld_successful_body_fetch:
  ^ld_probe_guard C k bb t ==>
  ?ti. get_instruction bb t.vs_inst_idx = SOME ti
Proof
  simp[] >> strip_tac >>
  Cases_on `get_instruction bb t.vs_inst_idx` >> simp[] >>
  qpat_x_assum `run_block_non_phis _ _ _ _ = _` mp_tac >>
  simp[Once run_block_non_phis_def]
QED

Theorem ld_point_alignment:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ^ld_probe_point lo P C C' vs0 stk fn fn' cs fs f0 A0 Sigma names bb t ==>
  ?PG G tn inst s t0 A frames N X p h.
    ld_sync lo P C vs0 stk PG G tn fn inst s t0 A frames N /\
    ^ld_probe_stable lo P Sigma names fs f0 A0 A frames /\
    fn' = ld_image (HD frames) /\
    ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
    ld_prefix C' fn' X p h t0 t /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
    ld_return_cont C fn cs s /\
    ir_supply_covers_fn (HD frames).lf_supply fn /\
    active_inst fn inst s /\
    h < LENGTH X /\ t0.vs_inst_idx = p /\ t.vs_inst_idx = p+h /\
    active_inst fn' (EL h X) t /\
    get_instruction bb t.vs_inst_idx = SOME (EL h X)
Proof
  simp[] >> strip_tac >>
  `ir_supply_covers_fn (HD frames).lf_supply fn` by
    (irule ld_sync_supply_covered >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `t0.vs_inst_idx = p` by
    (Cases_on `frames` >> gvs[] >> irule ld_sync_envelope_position >>
     metis_tac[]) >>
  `active_inst fn inst s` by metis_tac[ld_sync_source] >>
  `h < LENGTH X /\ active_inst fn' (EL h X) t /\ t.vs_inst_idx = p+h` by
    metis_tac[ld_prefix_bound, ld_prefix_active, ld_prefix_position] >>
  `get_instruction bb t.vs_inst_idx = SOME (EL h X)` by
    (`ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks)` by
       (gvs[ld_image_def] >>
        Cases_on `lower_dload_function_supply (Sigma fn.fn_name) fn` >>
        drule lower_dload_function_supply_labels >> simp[fn_labels_def]) >>
     drule_all ld_active_lookup >> simp[get_instruction_def] >> metis_tac[]) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
