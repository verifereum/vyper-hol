Theory dftGasInvReachSlice
Ancestors
  dftGasInvPrefixRun dftGasInvPrefixReach dftGasInvFlexibleTrace dftGasInvReturnReflect
  dftGasOracleDefs dftRunRel venomExecProofs venomWf venomInst
  venomState contextCodegenRel list rich_list

Theorem inv_ev_prefix_context_reflect:
  !n a b. LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  inv_ev_prefix orc p d C' bb n a b ==>
  inv_ev_prefix orc p d C bb n a b
Proof
  Induct >> simp[inv_ev_prefix_suc] >> rpt strip_tac >>
  `ev_step orc p d fuel C inst a = OK u` by
    (irule inv_ev_step_success_reflect >> simp[] >> metis_tac[]) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  first_x_assum irule >> simp[]
QED

Theorem inv_active_lookup[local]:
  wf_function fn /\ active_inst fn inst s ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_label = s.vs_current_bb /\ MEM bb fn.fn_blocks /\
    get_instruction bb s.vs_inst_idx = SOME inst
Proof
  rw[active_inst_def] >> qexists_tac `bb` >>
  simp[get_instruction_def] >> irule MEM_lookup_block >>
  gvs[wf_function_def, fn_labels_def]
QED

Theorem inv_entry_slice[local]:
  wf_function fn /\ enters_block fn before entry /\
  active_inst fn first entry ==>
  ?bb. lookup_block entry.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_label = entry.vs_current_bb /\ MEM bb fn.fn_blocks /\
    entry.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
    get_instruction bb entry.vs_inst_idx = SOME first
Proof
  rpt strip_tac >> drule_all inv_active_lookup >> strip_tac >>
  qexists_tac `bb` >> simp[] >>
  qpat_x_assum `enters_block _ _ _` mp_tac >>
  simp[enters_block_def] >> strip_tac >>
  drule eval_phis_preserves_current_bb >> strip_tac >> gvs[]
QED

Theorem inv_ev_reachable_slice:
  !orc initial ctx p d fn inst t.
  ev_reachable orc initial ctx p d fn inst t ==> wf_function fn ==>
  ?before entry first bb n.
    enters_block fn before entry /\
    ev_reachable orc initial ctx p d fn first entry /\
    lookup_block entry.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_label = entry.vs_current_bb /\ MEM bb fn.fn_blocks /\
    entry.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
    get_instruction bb entry.vs_inst_idx = SOME first /\
    get_instruction bb t.vs_inst_idx = SOME inst /\
    t.vs_current_bb = entry.vs_current_bb /\
    t.vs_inst_idx = entry.vs_inst_idx + n /\
    inv_ev_prefix orc p d ctx bb n entry t
Proof
  ho_match_mp_tac ev_reachable_strongind >> rpt strip_tac
  >- ( drule_all inv_entry_slice >> strip_tac >>
      rename1 `active_inst fn inst entry` >>
      qexistsl_tac [`initial with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>`, `entry`, `inst`, `bb`, `0`] >> simp[] >>
      irule ev_reachable_entry >> metis_tac[])
  >- ( first_x_assum drule >> strip_tac >>
      rename1 `ev_step orc p d fuel ctx inst current = OK result` >>
      `result.vs_current_bb = current.vs_current_bb` by
        metis_tac[ev_step_nonterm_current_bb] >>
      `get_instruction bb (SUC current.vs_inst_idx) = SOME inst'` by
        (qpat_x_assum `active_inst _ _ current` kall_tac >>
         drule_at (Pat `active_inst _ _ _`) inv_active_lookup >>
         simp[] >> strip_tac >> gvs[]) >>
      `inv_ev_prefix orc p d ctx bb (SUC 0) current
        (result with vs_inst_idx := SUC current.vs_inst_idx)` by
        (pure_rewrite_tac[GSYM arithmeticTheory.ONE, inv_ev_prefix_suc,
           inv_ev_prefix_zero] >> metis_tac[]) >>
      drule_all inv_ev_prefix_compose >> strip_tac >>
      qexistsl_tac [`before`, `entry`, `first`, `bb`, `n + 1`] >>
      `SUC current.vs_inst_idx = entry.vs_inst_idx + (n + 1)` by decide_tac >>
      simp[NoAsms] >> rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC, decide_tac, metis_tac[arithmeticTheory.ONE]])
  >- ( drule_all inv_entry_slice >> strip_tac >>
      rename1 `enters_block fn before entry` >>
      qexistsl_tac [`before`, `entry`, `inst'`, `bb`, `0`] >> simp[] >>
      irule ev_reachable_block >> metis_tac[])
  >> drule_all inv_entry_slice >> strip_tac >>
  rename1 `enters_block callee before entry` >>
  rename1 `active_inst callee first entry` >>
  qexistsl_tac [`before`, `entry`, `first`, `bb`, `0`] >> simp[] >>
  irule ev_reachable_callee >> metis_tac[]
QED

Theorem inv_ev_prefix_ftrace:
  !n a b. inv_ev_prefix orc p d ctx bb n a b ==>
  inv_ev_ftrace orc p d ctx
    (TAKE n (DROP a.vs_inst_idx bb.bb_instructions)) a b
Proof
  Induct >> simp[inv_ev_prefix_suc, inv_ev_ftrace_def] >> rpt strip_tac >>
  `DROP a.vs_inst_idx bb.bb_instructions =
    inst :: DROP (SUC a.vs_inst_idx) bb.bb_instructions` by
    (gvs[get_instruction_def] >> simp[DROP_CONS_EL]) >>
  simp[inv_ev_ftrace_def] >> goal_assum (drule_at Any) >> simp[] >>
  first_x_assum drule >> simp[]
QED

Theorem inv_ev_reachable_context_slice:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  ev_reachable orc initial C' p d fn inst t /\ wf_function fn ==>
  ?before entry first bb n.
    enters_block fn before entry /\
    ev_reachable orc initial C' p d fn first entry /\
    lookup_block entry.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_label = entry.vs_current_bb /\ MEM bb fn.fn_blocks /\
    entry.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
    get_instruction bb entry.vs_inst_idx = SOME first /\
    get_instruction bb t.vs_inst_idx = SOME inst /\
    t.vs_current_bb = entry.vs_current_bb /\
    t.vs_inst_idx = entry.vs_inst_idx + n /\
    inv_ev_prefix orc p d C' bb n entry t /\
    inv_ev_prefix orc p d C bb n entry t /\
    inv_ev_ftrace orc p d C
      (TAKE n (DROP entry.vs_inst_idx bb.bb_instructions)) entry t
Proof
  rpt strip_tac >> drule_all inv_ev_reachable_slice >> strip_tac >>
  drule_all inv_ev_prefix_context_reflect >> strip_tac >>
  drule inv_ev_prefix_ftrace >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem inv_ev_reachable_function_mem:
  !orc initial ctx p d fn inst t.
  ev_reachable orc initial ctx p d fn inst t ==> MEM fn ctx.ctx_functions
Proof
  ho_match_mp_tac ev_reachable_ind >> rpt strip_tac >>
  gvs[lookup_function_def] >> metis_tac[FIND_MEM]
QED
