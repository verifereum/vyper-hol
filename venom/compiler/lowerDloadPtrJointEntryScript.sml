(* Actual supply-threaded entry control witnesses. *)
Theory lowerDloadPtrJointEntry
Ancestors
  lowerDloadPtrPhi lowerDloadPtrRel o1ContractLowerDload
  contextCodegenRel venomExecSemantics venomExecProofs venomInst lowerDloadDefs list rich_list

Theorem dload_insts_entry_control[local]:
  !xs q ys q'. lower_dload_insts_supply q xs = (ys,q') /\
    phi_prefix_length ys < LENGTH ys ==>
  ?i emitted after.
    phi_prefix_length xs < LENGTH xs /\
    i = EL (phi_prefix_length xs) xs /\
    lower_dload_insts_supply q (TAKE (phi_prefix_length xs) xs) =
      (TAKE (phi_prefix_length xs) xs,q) /\
    lower_dload_inst_supply q i = (emitted,after) /\
    emitted <> [] /\ HD emitted = EL (phi_prefix_length ys) ys
Proof
  Induct >> simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (`lower_dload_inst_supply q h = ([h],q)` by
        (irule lower_dload_inst_supply_special >> simp[]) >>
      gvs[] >> gvs[phi_prefix_length_def] >>
      `phi_prefix_length outs < LENGTH outs` by decide_tac >>
      first_x_assum drule_all >> strip_tac >>
      qexistsl [`emitted`,`after`] >>
      simp[Once lower_dload_insts_supply_def]) >>
  `out <> []` by metis_tac[lower_dload_inst_supply_nonempty] >>
  Cases_on `out` >- gvs[] >>
  `h'.inst_opcode <> PHI` by
    (strip_tac >> drule lower_dload_inst_supply_control >> simp[] >> metis_tac[]) >>
  gvs[phi_prefix_length_def] >> simp[lower_dload_insts_supply_def]
QED

Theorem dload_blocks_entry_supply[local]:
  !bs q cs q' lbl b'.
  lower_dload_blocks_supply q bs = (cs,q') /\
  lookup_block lbl cs = SOME b' ==>
  ?bi b u'. bi < LENGTH bs /\ b = EL bi bs /\ b.bb_label = lbl /\
    lookup_block lbl bs = SOME b /\
    lower_dload_block_supply
      (SND (lower_dload_blocks_supply q (TAKE bi bs))) b = (b',u')
Proof
  Induct >- simp[lower_dload_blocks_supply_def, lookup_block_def, FIND_thm] >>
  rpt gen_tac >>
  simp[Once lower_dload_blocks_supply_def, AllCaseEqs()] >> strip_tac >>
  `bb'.bb_label = h.bb_label` by
    (gvs[lower_dload_block_supply_def, AllCaseEqs()] >> simp[]) >>
  gvs[lookup_block_def, FIND_thm] >> Cases_on `h.bb_label = lbl` >> gvs[]
  >- (qexists_tac `0` >> simp[lower_dload_blocks_supply_def]) >>
  first_x_assum drule >> simp[lookup_block_def] >>
  disch_then drule >> strip_tac >>
  qexists_tac `SUC bi` >>
  simp[Once lower_dload_blocks_supply_def, AllCaseEqs()] >>
  Cases_on `lower_dload_blocks_supply s1 (TAKE bi bs)` >> gvs[]
QED

Theorem dload_phis_control[local]:
  !xs s s'. eval_phis s xs = OK s' ==>
    s'.vs_current_bb = s.vs_current_bb /\ s'.vs_prev_bb = s.vs_prev_bb
Proof
  Induct >> simp[Once eval_phis_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  gvs[AllCaseEqs()] >> strip_tac >>
  first_x_assum drule >> gvs[venomStateTheory.update_var_def]
QED

Theorem dload_enters_block_control_match:
  lower_dload_function_supply q f = (g,q') /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  enters_block f s s1 /\ enters_block g t t1 /\
  s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
  active_inst g j t1 ==>
  ?i emitted. dload_control_match q f g s1 t1 i emitted 0 /\ j = HD emitted
Proof
  strip_tac >>
  qpat_x_assum `enters_block g t t1` mp_tac >>
  simp[enters_block_def] >> strip_tac >>
  drule dload_phis_control >> strip_tac >>
  `MEM bb g.fn_blocks` by metis_tac[lookup_block_def, FIND_MEM] >>
  `t1.vs_current_bb = t.vs_current_bb` by simp[] >>
  `t1.vs_prev_bb = t.vs_prev_bb` by simp[] >>
  `t1.vs_inst_idx = phi_prefix_length bb.bb_instructions` by simp[] >>
  qpat_x_assum `active_inst g j t1` mp_tac >>
  simp[active_inst_def] >> strip_tac >>
  `lookup_block t.vs_current_bb g.fn_blocks = SOME bb'` by
    (irule MEM_lookup_block >> simp[]) >>
  `bb' = bb` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `?gbs. lower_dload_blocks_supply q f.fn_blocks = (g.fn_blocks,gbs)` by
    (gvs[lower_dload_function_supply_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all dload_blocks_entry_supply >> strip_tac >>
  drule lower_dload_block_supply_phi_exact >> strip_tac >>
  qpat_x_assum `enters_block f s s1` mp_tac >>
  simp[enters_block_def] >> strip_tac >> gvs[] >>
  drule dload_phis_control >> strip_tac >>
  `?aq. lower_dload_insts_supply
      (SND (lower_dload_blocks_supply q (TAKE bi f.fn_blocks)))
      (EL bi f.fn_blocks).bb_instructions = (bb.bb_instructions,aq)` by
    (qpat_x_assum `lower_dload_block_supply _ _ = _` mp_tac >>
     simp[lower_dload_block_supply_def, AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by metis_tac[] >>
  drule_all dload_insts_entry_control >> strip_tac >>
  qexistsl [`i`,`emitted`] >> simp[] >>
  simp[dload_control_match_def] >>
  qexists_tac `bi` >> simp[] >>
  qexists_tac `after` >>
  gvs[active_inst_def] >> conj_tac
  >- (Cases_on `emitted` >> gvs[]) >> conj_tac
  >- (qexists_tac `EL bi f.fn_blocks` >> simp[EL_MEM]) >>
  qexists_tac `bb` >> Cases_on `emitted` >> gvs[]
QED
