Theory lowerDloadTopEntryControl
Ancestors
  lowerDloadConfiguredSelection lowerDloadCoverageInvariant
  lowerDloadControlPosition lowerDloadSupplySegment o1ContractLowerDload
  lowerDloadDefs o1PassContract
  contextCodegenRel venomExecSemantics venomInst venomState list

Theorem lower_dload_top_entry_control:
  lower_dload_function_supply a fn = (gn,b) /\
  fn_entry_label fn = SOME lbl /\ first_block_no_phi fn /\
  z = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                 vs_inst_idx := 0|> /\
  enters_block gn z t /\ lookup_block lbl gn.fn_blocks = SOME gb /\
  t.vs_inst_idx < LENGTH gb.bb_instructions ==>
  t = z /\ enters_block fn z t /\
  ?bb i post code tail amid aend.
    lookup_block lbl fn.fn_blocks = SOME bb /\
    bb.bb_instructions = i::post /\
    lower_dload_block_supply a bb = (gb,aend) /\
    lower_dload_inst_supply a i = (code,amid) /\
    lower_dload_insts_supply amid post = (tail,aend) /\
    gb.bb_instructions = code ++ tail /\ code <> [] /\
    active_inst fn i t /\
    EL t.vs_inst_idx gb.bb_instructions = HD code
Proof
  strip_tac >>
  `enters_block fn z t` by
    metis_tac[lower_dload_function_supply_enters_block] >>
  Cases_on `fn.fn_blocks` >>
  gvs[fn_entry_label_def, entry_block_def, first_block_no_phi_def] >>
  qpat_x_assum `lower_dload_function_supply a fn = _` mp_tac >>
  Cases_on `lower_dload_block_supply a h` >>
  Cases_on `lower_dload_blocks_supply r t'` >>
  simp[lower_dload_function_supply_def, lower_dload_blocks_supply_def] >>
  strip_tac >> gvs[] >>
  `q.bb_label = h.bb_label` by
    gvs[lower_dload_block_supply_def, AllCaseEqs()] >>
  gvs[lookup_block_def, FIND_thm] >>
  qpat_x_assum `enters_block fn _ t` mp_tac >>
  simp[enters_block_def, lookup_block_def, FIND_thm] >>
  Cases_on `h.bb_instructions`
  >- (simp[eval_phis_def, phi_prefix_length_def] >> strip_tac >>
      gvs[lower_dload_block_supply_def, lower_dload_insts_supply_def]) >>
  simp[eval_phis_def, phi_prefix_length_def] >> strip_tac >> gvs[] >>
  Cases_on `lower_dload_inst_supply a h'` >>
  Cases_on `lower_dload_insts_supply r' t''` >>
  gvs[lower_dload_block_supply_def, lower_dload_insts_supply_def] >>
  `q <> []` by metis_tac[lower_dload_inst_supply_nonempty] >>
  simp[] >> conj_tac
  >- (simp[active_inst_def] >> qexists_tac `h` >> simp[]) >>
  Cases_on `q` >> gvs[]
QED

Theorem lower_dload_top_entry_annotated:
  lower_dload_function_supply a fn = (gn,b) /\
  fn_entry_label fn = SOME lbl /\ first_block_no_phi fn /\
  z = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                 vs_inst_idx := 0|> /\
  enters_block gn z t /\ lookup_block lbl gn.fn_blocks = SOME gb /\
  t.vs_inst_idx < LENGTH gb.bb_instructions /\
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  t.vs_allocas = FEMPTY ==>
  ?bb i post code tail amid aend.
    lookup_block lbl fn.fn_blocks = SOME bb /\
    bb.bb_instructions = i::post /\
    lower_dload_block_supply a bb = (gb,aend) /\
    lower_dload_inst_supply a i = (code,amid) /\
    lower_dload_insts_supply amid post = (tail,aend) /\
    gb.bb_instructions = code ++ tail /\ code <> [] /\
    EL t.vs_inst_idx gb.bb_instructions = HD code /\
    ld_annotated_reachable vs0 ctx [] 0 FEMPTY [] FEMPTY
      entry_taint fn i t
Proof
  strip_tac >> drule_all lower_dload_top_entry_control >> strip_tac >>
  `ld_annotated_reachable vs0 ctx [] 0 FEMPTY [] FEMPTY
     entry_taint fn i t` by
    (qpat_x_assum `z = _` SUBST_ALL_TAC >>
     drule_all ld_frame_data_source_entry >> simp[]) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
