(* Shared package supply boundaries; activity/control boundaries follow here. *)
Theory lowerDloadReturnAlignment
Ancestors
  lowerDloadReturnInterfaceProbe lowerDloadConfiguredOrigins
  lowerDloadExpansionEndpoint lowerDloadSafetyLocations lowerDloadSafetyKernel
  venomExecSemantics venomInst venomWf o1ContractLowerDload
  stepWriteFootprintForward memSafeRun ptrDiscipline contextCodegenRel
  venomExecProofs o1PassContract irSupply passSharedDefs venomFnScheduleRunner list
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

Theorem ld_guard_non_revert:
  ^ld_probe_guard C k bb t ==> ~revert_forward_at bb t.vs_inst_idx
Proof
  simp[] >> strip_tac >> strip_tac >>
  drule revert_forward_at_no_normal >> metis_tac[]
QED

Theorem ld_envelope_revert_forward:
  lower_dload_function_supply u fn = (g,v) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  EVERY inst_wf (fn_insts fn) /\ ir_supply_covers_fn u fn /\
  ld_envelope u fn s s.vs_inst_idx X p /\ in_revert_forward fn s /\
  t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = p ==>
  in_revert_forward g t
Proof
  simp[ld_envelope_def, in_revert_forward_def] >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL bi fn.fn_blocks)` by
    (irule MEM_lookup_block >> simp[MEM_EL] >> metis_tac[]) >>
  gvs[] >> drule lower_dload_function_supply_block_at >>
  disch_then (qspec_then `bi` mp_tac) >> simp[] >> strip_tac >>
  `MEM (EL bi fn.fn_blocks) fn.fn_blocks` by
    (simp[MEM_EL] >> metis_tac[]) >>
  `EVERY inst_wf (EL bi fn.fn_blocks).bb_instructions` by
    (gvs[fn_insts_def, fn_insts_blocks_def, EVERY_MEM] >>
     metis_tac[fn_insts_blocks_MEM]) >>
  `!inst w. MEM inst (EL bi fn.fn_blocks).bb_instructions /\
     MEM (Var w) inst.inst_operands ==> MEM w u0.irs_used_vars` by
    (rpt strip_tac >> irule lower_dload_blocks_supply_used_vars_mono >>
     goal_assum (drule_at Any) >>
     fs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >>
     first_x_assum irule >>
     simp[fn_ir_vars_def, block_ir_vars_def, inst_ir_vars_def,
          MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     qexistsl_tac [`EL bi fn.fn_blocks`,`inst`] >>
     simp[inst_uses_def, MEM_operand_vars_eq_Var]) >>
  Cases_on `lower_dload_insts_supply u0
    (TAKE s.vs_inst_idx (EL bi fn.fn_blocks).bb_instructions)` >>
  drule_all lower_dload_insts_supply_revert_at >> strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) g.fn_blocks)` by
    (drule lower_dload_function_supply_labels >> simp[fn_labels_def]) >>
  qexists_tac `(EL bi fn.fn_blocks) with bb_instructions := is` >>
  conj_tac
  >- (irule MEM_lookup_block >> simp[] >>
      qpat_x_assum `g.fn_blocks = _` SUBST1_TAC >> simp[]) >>
  fs[]
QED

(* Aligned point boundary: all premises are exported by point alignment. *)
Theorem ld_guarded_source_non_revert:
  lower_dload_function_supply u fn = (g,v) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  EVERY inst_wf (fn_insts fn) /\ ir_supply_covers_fn u fn /\
  active_inst fn inst s /\ ld_envelope u fn s s.vs_inst_idx X p /\
  h < LENGTH X /\ t.vs_inst_idx = p+h /\
  t.vs_current_bb = s.vs_current_bb /\
  lookup_block t.vs_current_bb g.fn_blocks = SOME bb /\
  ^ld_probe_guard C k bb t ==> ~in_revert_forward fn s
Proof
  strip_tac >> strip_tac >>
  `?sb. lookup_block s.vs_current_bb fn.fn_blocks = SOME sb /\
         get_instruction sb s.vs_inst_idx = SOME inst` by
    (drule_all ld_active_lookup >> metis_tac[get_instruction_def]) >>
  `inst.inst_opcode = RETURNDATACOPY \/ inst.inst_opcode = REVERT` by
    (fs[in_revert_forward_def] >> gvs[] >>
     drule_all revert_forward_at_opcode >> simp[]) >>
  `X = [inst]` by (irule ld_envelope_ordinary >> simp[] >> metis_tac[]) >>
  `h = 0` by fs[] >>
  `in_revert_forward g t` by (irule ld_envelope_revert_forward >> simp[] >> metis_tac[]) >>
  drule ld_guard_non_revert >> gvs[in_revert_forward_def]
QED
