Theory simplifyCfgFixupGasEvents
Ancestors
  simplifyCfgFixupSemantics simplifyCfgFragments gasEvents rich_list list
  venomExecSemantics venomInst simplifyCfgFixupStatic simplifyCfgDefs
  simplifyCfgPhiBlockSemantics simplifyCfgPhiConsumer simplifyCfgFixupPrefixes
  simplifyCfgAvailability cfgTransform venomWf o1PassLift venomExecProofs
  venomExecProps analysisSimProofsBase

Theorem scfg_gas_events_block_suffix:
  !b s b' n C owner.
  LENGTH b.bb_instructions = LENGTH b'.bb_instructions /\
  DROP s.vs_inst_idx b.bb_instructions = DROP s.vs_inst_idx b'.bb_instructions ==>
  gas_events_block n C owner b s = gas_events_block n C owner b' s
Proof
  rpt gen_tac >>
  measureInduct_on `LENGTH b.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  Cases_on `s.vs_inst_idx < LENGTH b.bb_instructions`
  >- (`EL s.vs_inst_idx b.bb_instructions = EL s.vs_inst_idx b'.bb_instructions` by
        metis_tac[HD_DROP] >>
      once_rewrite_tac[gas_events_block_def] >> simp[get_instruction_def] >>
      Cases_on `step_inst n C (EL s.vs_inst_idx b'.bb_instructions) s` >> simp[] >>
      IF_CASES_TAC >> simp[] >> first_x_assum irule >> simp[] >>
      metis_tac[DROP_SUC]) >>
  once_rewrite_tac[gas_events_block_def] >> simp[get_instruction_def]
QED

Theorem scfg_iprefix_silent_replay:
  !C bb s t. scfg_iprefix C bb s t ==>
  (!j i. s.vs_inst_idx <= j /\ j < t.vs_inst_idx /\
     get_instruction bb j = SOME i ==>
     i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE) ==>
  !n owner. exec_block n C bb s = exec_block n C bb t /\
    gas_events_block n C owner bb s = gas_events_block n C owner bb t
Proof
  ho_match_mp_tac scfg_iprefix_strongind >> conj_tac
  >- simp[] >>
  rpt gen_tac >> strip_tac >> disch_tac >>
  drule scfg_iprefix_index >> simp[] >> strip_tac >>
  `i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE` by
    (first_assum irule >> qexists_tac `s.vs_inst_idx` >> simp[]) >>
  `!n. step_inst n C i s = OK u` by
    metis_tac[step_inst_non_invoke] >>
  `!j i. SUC s.vs_inst_idx <= j /\ j < t.vs_inst_idx /\
     get_instruction bb j = SOME i ==>
     i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!j i. s.vs_inst_idx <= j /\ _ ==> _`
       (qspecl_then [`j`, `i'`] mp_tac) >> simp[]) >>
  rpt gen_tac >>
  qpat_x_assum `(!j i. _) ==> _` mp_tac >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qspecl_then [`n`, `owner`] strip_assume_tac) >>
  conj_tac
  >- (CONV_TAC (LAND_CONV (REWR_CONV exec_block_def)) >> simp[]) >>
  CONV_TAC (LAND_CONV (REWR_CONV gas_events_block_def)) >>
  simp[gas_events_step_def]
QED

Theorem scfg_fix_phis_gas_events_tail:
  bb.bb_instructions = ps ++ tail /\
  EVERY (\i. i.inst_opcode <> PHI) tail /\
  LENGTH ps <= s.vs_inst_idx ==>
  gas_events_block n C owner (fix_phis_in_block actual_preds bb) s =
  gas_events_block n C owner bb s
Proof
  strip_tac >>
  `LENGTH (fix_phis_in_block actual_preds bb).bb_instructions =
   LENGTH bb.bb_instructions` by metis_tac[scfg_fix_phis_length] >>
  irule scfg_gas_events_block_suffix >> simp[] >>
  irule LIST_EQ >> simp[EL_DROP] >> rpt strip_tac >>
  `s.vs_inst_idx + x = LENGTH ps + (s.vs_inst_idx + x - LENGTH ps)` by decide_tac >>
  `s.vs_inst_idx + x - LENGTH ps < LENGTH tail` by gvs[] >>
  drule_all scfg_fix_phis_tail_el >> simp[EL_APPEND]
QED

Theorem scfg_fix_phis_snapshot_observation[local]:
  bb.bb_instructions = ps ++ tail /\
  EVERY (\i. i.inst_opcode = PHI) ps /\
  EVERY (\i. i.inst_opcode <> PHI) tail /\
  rs = FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) ps /\
  cs = FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode <> PHI) ps /\
  EVERY (\i. i.inst_opcode = ASSIGN) (MAP (fix_phi_inst actual_preds) cs) /\
  eval_phis s ps = OK u /\
  eval_phis s (MAP (fix_phi_inst actual_preds) rs) = OK v /\
  scfg_iprefix C (fix_phis_in_block actual_preds bb)
    (v with vs_inst_idx := LENGTH rs)
    (u with vs_inst_idx := LENGTH rs + LENGTH cs) ==>
  run_block n C (fix_phis_in_block actual_preds bb) s = run_block n C bb s /\
  (case eval_phis s (fix_phis_in_block actual_preds bb).bb_instructions of
     OK z => gas_events_block n C owner (fix_phis_in_block actual_preds bb)
       (z with vs_inst_idx := phi_prefix_length (fix_phis_in_block actual_preds bb).bb_instructions)
   | _ => []) =
  (case eval_phis s bb.bb_instructions of
     OK z => gas_events_block n C owner bb
       (z with vs_inst_idx := phi_prefix_length bb.bb_instructions)
   | _ => [])
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode = PHI) (MAP (fix_phi_inst actual_preds) rs) /\
   EVERY (\i. i.inst_opcode <> PHI) (MAP (fix_phi_inst actual_preds) cs ++ tail) /\
   LENGTH rs + LENGTH cs = LENGTH ps` by
    (irule scfg_fix_phis_prefix_shape >> metis_tac[]) >>
  `(fix_phis_in_block actual_preds bb).bb_instructions =
    MAP (fix_phi_inst actual_preds) rs ++
    (MAP (fix_phi_inst actual_preds) cs ++ tail)` by
    metis_tac[scfg_fix_phis_partition_instructions, APPEND_ASSOC] >>
  `!j i. LENGTH rs <= j /\ j < LENGTH rs + LENGTH cs /\
    get_instruction (fix_phis_in_block actual_preds bb) j = SOME i ==>
    i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE` by
    (rpt gen_tac >> strip_tac >>
     gvs[get_instruction_def, EL_APPEND, EVERY_EL]) >>
  qpat_x_assum `rs = _` kall_tac >> qpat_x_assum `cs = _` kall_tac >>
  drule scfg_iprefix_silent_replay >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qspecl_then [`n`, `owner`] strip_assume_tac) >>
  `exec_block n C (fix_phis_in_block actual_preds bb)
     (u with vs_inst_idx := LENGTH ps) =
   exec_block n C bb (u with vs_inst_idx := LENGTH ps)` by
    (irule scfg_fix_phis_exec_tail >> qexistsl_tac [`ps`, `tail`] >> simp[]) >>
  `gas_events_block n C owner (fix_phis_in_block actual_preds bb)
     (u with vs_inst_idx := LENGTH ps) =
   gas_events_block n C owner bb (u with vs_inst_idx := LENGTH ps)` by
    (irule scfg_fix_phis_gas_events_tail >> qexistsl_tac [`ps`, `tail`] >> simp[]) >>
  simp[Excl "APPEND_ASSOC", run_block_def, scfg_eval_phis_append,
       scfg_phi_prefix_append]
QED

Theorem scfg_rooted_fix_phis_observation:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  (!b. MEM b fn.fn_blocks ==> fn_reachable fn b.bb_label) /\
  fn_entry_state fn s0 /\ scfg_bprefix C fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  run_block n C (fix_phis_in_block (pred_labels fn bb.bb_label) bb) s =
    run_block n C bb s /\
  (case eval_phis s (fix_phis_in_block (pred_labels fn bb.bb_label) bb).bb_instructions of
     OK z => gas_events_block n C owner (fix_phis_in_block (pred_labels fn bb.bb_label) bb)
       (z with vs_inst_idx := phi_prefix_length
         (fix_phis_in_block (pred_labels fn bb.bb_label) bb).bb_instructions)
   | _ => []) =
  (case eval_phis s bb.bb_instructions of
     OK z => gas_events_block n C owner bb
       (z with vs_inst_idx := phi_prefix_length bb.bb_instructions)
   | _ => [])
Proof
  strip_tac >> drule_all scfg_bprefix_incoming >> strip_tac
  >- (gvs[] >> drule_all scfg_entry_block_no_phi >> strip_tac >>
      simp[scfg_fix_phis_no_phi]) >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  qabbrev_tac `ps = TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions` >>
  qabbrev_tac `tail = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions` >>
  `bb.bb_instructions = ps ++ tail` by simp[Abbr `ps`, Abbr `tail`] >>
  `EVERY (\i. i.inst_opcode = PHI) ps` by metis_tac[phi_prefix_all_phi] >>
  `EVERY (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode <> NOP) ps /\
   EVERY (\i. i.inst_opcode <> PHI) tail` by
    (irule scfg_fn_fix_phis_parts >> simp[Abbr `ps`, Abbr `tail`] >> metis_tac[]) >>
  qabbrev_tac `rs = FILTER (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode = PHI) ps` >>
  qabbrev_tac `cs = FILTER (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode <> PHI) ps` >>
  `EVERY (\i. i.inst_opcode = ASSIGN) (MAP (fix_phi_inst (pred_labels fn bb.bb_label)) cs)` by
    (irule scfg_converted_assigns >> simp[Abbr `cs`] >> metis_tac[]) >>
  `ps = TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\
   rs = FILTER (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode = PHI) ps /\
   cs = FILTER (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode <> PHI) ps` by
    simp[Abbr `ps`, Abbr `rs`, Abbr `cs`] >>
  `fn_reachable fn bb.bb_label /\
   (!qb. MEM qb fn.fn_blocks /\ MEM bb.bb_label (bb_succs qb) ==> fn_reachable fn qb.bb_label)` by
    metis_tac[] >>
  drule_all scfg_fn_fix_phis_block >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  irule scfg_fix_phis_snapshot_observation >>
  qexistsl_tac [`cs`, `ps`, `rs`, `tail`] >> metis_tac[]
QED
