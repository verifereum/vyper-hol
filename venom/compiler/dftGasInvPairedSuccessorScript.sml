Theory dftGasInvPairedSuccessor
Ancestors
  dftGasInvPairedPrefix dftGasInvPrefixRun dftGasInvPrefixReach
  dftGasInvReturnReflect dftGasInvContextConvert dftGasInvBlockInit
  dftGasOracleDefs dftRunRel dftScheduleOrder dftStructural dftFrontEquiv
  venomExecSemantics venomExecProofs venomInst venomState venomWf
  contextCodegenRel list rich_list

Theorem inv_block_reachable_exit[local]:
  !k s first.
    LENGTH bb.bb_instructions - s.vs_inst_idx = k /\
    MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    get_instruction bb s.vs_inst_idx = SOME first /\
    ev_reachable orc initial ctx p d fn first s /\
    ev_block orc p d fuel ctx bb s = OK before ==>
    ?term t. ev_reachable orc initial ctx p d fn term t /\
      active_inst fn term t /\ is_terminator term.inst_opcode /\
      ev_step orc p d fuel ctx term t = OK before /\ ~before.vs_halted
Proof
  completeInduct_on `k` >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `ev_block _ _ _ _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[ev_block_def] >> simp[] >>
  Cases_on `ev_step orc p d fuel ctx first s` >> simp[] >>
  rename1 `ev_step orc p d fuel ctx first s = OK u` >>
  Cases_on `is_terminator first.inst_opcode` >> simp[]
  >- (strip_tac >> gvs[AllCaseEqs()] >> qexistsl_tac [`first`, `s`] >> simp[] >>
      simp[active_inst_def] >> qexists_tac `bb` >> gvs[get_instruction_def]) >>
  strip_tac >>
  `u.vs_current_bb = s.vs_current_bb` by metis_tac[ev_step_nonterm_current_bb] >>
  `?nextinst. get_instruction bb (SUC s.vs_inst_idx) = SOME nextinst` by
    (qpat_x_assum `ev_block _ _ _ _ _ _ _ = OK before` mp_tac >>
     once_rewrite_tac[ev_block_def] >>
     Cases_on `get_instruction bb (SUC s.vs_inst_idx)` >> simp[]) >>
  `ev_reachable orc initial ctx p d fn nextinst
    (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule ev_reachable_next >> simp[] >> conj_tac
     >- (simp[active_inst_def] >> qexists_tac `bb` >> gvs[get_instruction_def]) >>
     qexistsl_tac [`fuel`, `first`] >> simp[] >>
     simp[active_inst_def] >> qexists_tac `bb` >> gvs[get_instruction_def]) >>
  first_x_assum (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- (gvs[get_instruction_def] >> decide_tac)) >>
  disch_then irule >> conj_tac >- simp[] >>
  goal_assum (drule_at (Pat `ev_reachable _ _ _ _ _ _ _ _`)) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem inv_nonphi_prefix_lt[local]:
  !xs. (?i. MEM i xs /\ i.inst_opcode <> PHI) ==>
    phi_prefix_length xs < LENGTH xs
Proof
  Induct >> simp[phi_prefix_length_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[phi_prefix_length_def] >> metis_tac[]
QED

Theorem inv_related_successor_entry:
  dft_fn_rel fn fn' /\ enters_block fn' before nextentry ==>
  enters_block fn before nextentry /\
  ?bb first. lookup_block nextentry.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_label = nextentry.vs_current_bb /\ MEM bb fn.fn_blocks /\
    get_instruction bb nextentry.vs_inst_idx = SOME first /\
    active_inst fn first nextentry
Proof
  strip_tac >>
  qpat_x_assum `enters_block _ _ _` mp_tac >> simp[enters_block_def] >> strip_tac >>
  rename1 `lookup_block before.vs_current_bb fn'.fn_blocks = SOME bb'` >>
  `?bb. lookup_block before.vs_current_bb fn.fn_blocks = SOME bb /\ dft_block_rel bb bb'` by
    (`LIST_REL dft_block_rel fn.fn_blocks fn'.fn_blocks` by gvs[dft_fn_rel_def] >>
     drule dft_block_rel_lookup_block >>
     disch_then (qspec_then `before.vs_current_bb` mp_tac) >>
     Cases_on `lookup_block before.vs_current_bb fn.fn_blocks` >> gvs[]) >>
  drule_all inv_lookup_phis >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = before.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `bb_well_formed bb` by gvs[dft_fn_rel_def, wf_function_def, EVERY_MEM] >>
  `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by
    (irule inv_nonphi_prefix_lt >> qexists_tac `LAST bb.bb_instructions` >>
     gvs[bb_well_formed_def] >> conj_tac >- metis_tac[LAST_MEM] >>
     Cases_on `(LAST bb.bb_instructions).inst_opcode` >> gvs[is_terminator_def]) >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  conj_tac
  >- (simp[enters_block_def] >> metis_tac[]) >>
  qexistsl_tac [`bb`, `EL nextentry.vs_inst_idx bb.bb_instructions`] >>
  gvs[get_instruction_def, active_inst_def] >> metis_tac[]
QED

Theorem inv_paired_successor:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  dft_fn_rel fn fn' /\
  lookup_block entry.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block entry.vs_current_bb fn'.fn_blocks = SOME bb' /\
  entry.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
  get_instruction bb entry.vs_inst_idx = SOME first /\
  ev_reachable orc initial C p d fn first entry /\
  inv_ev_prefix orc p d C' bb' n entry t /\
  get_instruction bb' t.vs_inst_idx = SOME term /\
  is_terminator term.inst_opcode /\
  ev_step orc p d fuel C' term t = OK before /\
  ~before.vs_halted /\ enters_block fn' before nextentry ==>
  enters_block fn before nextentry /\
  ?sourcefirst. active_inst fn sourcefirst nextentry /\
    ev_reachable orc initial C p (SUC d) fn sourcefirst nextentry
Proof
  strip_tac >>
  `ev_block orc p d fuel C' bb' t = OK before` by
    (once_rewrite_tac[ev_block_def] >> simp[]) >>
  `?joined. ev_block orc p d joined C' bb' entry = OK before` by
    (drule inv_ev_prefix_suffix >> disch_then drule >> simp[]) >>
  `ev_block orc p d joined C bb' entry = OK before` by
    (irule inv_ev_block_context_convert >> simp[] >>
     qexists_tac `C'` >> simp[] >>
     metis_tac[inv_ev_blocks_return_reflect]) >>
  `ev_block orc p d joined C bb entry = OK before` by
    (irule inv_lookup_block_init_reflect >> simp[] >>
     goal_assum (drule_at (Pat `dft_fn_rel _ _`)) >>
     goal_assum (drule_at (Pat `lookup_block _ _ = SOME bb'`)) >> simp[]) >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = entry.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `?exitinst exitstate. ev_reachable orc initial C p d fn exitinst exitstate /\
    active_inst fn exitinst exitstate /\ is_terminator exitinst.inst_opcode /\
    ev_step orc p d joined C exitinst exitstate = OK before /\ ~before.vs_halted` by
    (irule inv_block_reachable_exit >> simp[] >>
     goal_assum (drule_at (Pat `ev_block _ _ _ _ _ _ _ = OK before`)) >>
     goal_assum (drule_at (Pat `ev_reachable _ _ _ _ _ _ _ _`)) >> simp[]) >>
  drule_all inv_related_successor_entry >> strip_tac >> simp[] >>
  goal_assum (drule_at (Pat `active_inst _ _ nextentry`)) >>
  irule ev_reachable_block >> simp[] >> metis_tac[]
QED
