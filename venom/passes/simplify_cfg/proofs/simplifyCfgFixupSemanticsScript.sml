(* Operational boundaries for the unchanged tail of PHI fixup. *)
Theory simplifyCfgFixupSemantics
Ancestors
  simplifyCfgFixupStatic simplifyCfgPhiConsumer venomExecSemantics
  venomExecProofs venomInst list rich_list simplifyCfgAvailability
  simplifyCfgPhiBlockSemantics simplifyCfgFragments simplifyCfgDefs venomWf
  analysisSimProofsBase cfgTransform o1PassLift passSimulationProofs

Theorem scfg_exec_block_suffix:
  !b s b' n C.
  LENGTH b.bb_instructions = LENGTH b'.bb_instructions /\
  DROP s.vs_inst_idx b.bb_instructions = DROP s.vs_inst_idx b'.bb_instructions ==>
  exec_block n C b s = exec_block n C b' s
Proof
  rpt gen_tac >>
  measureInduct_on `LENGTH b.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  Cases_on `s.vs_inst_idx < LENGTH b.bb_instructions`
  >- (`EL s.vs_inst_idx b.bb_instructions = EL s.vs_inst_idx b'.bb_instructions` by
        metis_tac[HD_DROP] >>
      once_rewrite_tac[exec_block_def] >> simp[get_instruction_def] >>
      Cases_on `step_inst n C (EL s.vs_inst_idx b'.bb_instructions) s` >> simp[] >>
      IF_CASES_TAC >> simp[] >> first_x_assum irule >> simp[] >>
      metis_tac[DROP_SUC]) >>
  once_rewrite_tac[exec_block_def] >> simp[get_instruction_def]
QED

Theorem scfg_fix_phis_exec_tail:
  bb.bb_instructions = ps ++ tail /\
  EVERY (\i. i.inst_opcode <> PHI) tail /\
  LENGTH ps <= s.vs_inst_idx ==>
  exec_block n C (fix_phis_in_block actual_preds bb) s = exec_block n C bb s
Proof
  strip_tac >>
  `LENGTH (fix_phis_in_block actual_preds bb).bb_instructions =
   LENGTH bb.bb_instructions` by metis_tac[scfg_fix_phis_length] >>
  irule scfg_exec_block_suffix >> simp[] >>
  irule LIST_EQ >> simp[EL_DROP] >> rpt strip_tac >>
  `s.vs_inst_idx + x = LENGTH ps + (s.vs_inst_idx + x - LENGTH ps)` by decide_tac >>
  `s.vs_inst_idx + x - LENGTH ps < LENGTH tail` by gvs[] >>
  drule_all scfg_fix_phis_tail_el >>
  simp[EL_APPEND]
QED

Theorem scfg_phi_prefix_append:
  !ps tail. EVERY (\i. i.inst_opcode = PHI) ps /\
    EVERY (\i. i.inst_opcode <> PHI) tail ==>
    phi_prefix_length (ps ++ tail) = LENGTH ps
Proof
  Induct >> simp[phi_prefix_length_def, no_phis_phi_prefix_length_zero]
QED

Theorem scfg_eval_phis_append:
  EVERY (\i. i.inst_opcode = PHI) ps /\
  EVERY (\i. i.inst_opcode <> PHI) tail ==>
  eval_phis s (ps ++ tail) = eval_phis s ps
Proof
  strip_tac >> irule eval_phis_same_phi_prefix >>
  simp[scfg_phi_prefix_append, scfg_phi_prefix_length, EL_APPEND]
QED

Theorem scfg_fix_phis_prefix_shape:
  rs = FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) ps /\
  cs = FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode <> PHI) ps /\
  EVERY (\i. i.inst_opcode <> PHI) tail ==>
  EVERY (\i. i.inst_opcode = PHI) (MAP (fix_phi_inst actual_preds) rs) /\
  EVERY (\i. i.inst_opcode <> PHI) (MAP (fix_phi_inst actual_preds) cs ++ tail) /\
  LENGTH rs + LENGTH cs = LENGTH ps
Proof
  strip_tac >> simp[EVERY_MAP, EVERY_FILTER, EVERY_MEM] >>
  conj_tac >- simp[MEM_FILTER] >> conj_tac >- fs[EVERY_MEM, MEM_FILTER] >>
  qpat_x_assum `EVERY _ tail` kall_tac >> gvs[] >>
  qid_spec_tac `ps` >> Induct >> simp[] >>
  Cases_on `(fix_phi_inst actual_preds h).inst_opcode = PHI` >> simp[]
QED

Theorem scfg_fix_phis_run_snapshot_same_fuel[local]:
  bb.bb_instructions = ps ++ tail /\
  EVERY (\i. i.inst_opcode = PHI) ps /\
  EVERY (\i. i.inst_opcode <> PHI) tail /\
  rs = FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) ps /\
  cs = FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode <> PHI) ps /\
  eval_phis s ps = OK u /\
  eval_phis s (MAP (fix_phi_inst actual_preds) rs) = OK v /\
  scfg_iprefix C (fix_phis_in_block actual_preds bb)
    (v with vs_inst_idx := LENGTH rs)
    (u with vs_inst_idx := LENGTH rs + LENGTH cs) /\
  run_block n C bb s = r /\ (!e. r <> Error e) ==>
  run_block n C (fix_phis_in_block actual_preds bb) s = r
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
  `exec_block n C bb (u with vs_inst_idx := LENGTH ps) = r` by
    (qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
     simp[run_block_def, scfg_eval_phis_append, scfg_phi_prefix_append]) >>
  `exec_block n C (fix_phis_in_block actual_preds bb)
     (u with vs_inst_idx := LENGTH rs + LENGTH cs) = r` by
    (simp[] >> dep_rewrite.DEP_REWRITE_TAC[scfg_fix_phis_exec_tail] >>
     simp[] >> metis_tac[]) >>
  `exec_block n C (fix_phis_in_block actual_preds bb)
     (v with vs_inst_idx := LENGTH rs) = r` by
    (drule scfg_iprefix_continue_same_fuel >> disch_then irule >>
     simp[] >> metis_tac[scfg_fix_phis_interval_non_invoke]) >>
  qpat_x_assum `rs = _` kall_tac >> qpat_x_assum `cs = _` kall_tac >>
  simp[Excl "APPEND_ASSOC", run_block_def, scfg_eval_phis_append, scfg_phi_prefix_append]
QED

Theorem scfg_fn_fix_phis_run_block_same_fuel[local]:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  ps = TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\
  bb.bb_instructions = ps ++ tail /\ EVERY (\i. i.inst_opcode <> PHI) tail /\
  rs = FILTER (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode = PHI) ps /\
  cs = FILTER (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode <> PHI) ps /\
  MEM pb fn.fn_blocks /\ fn_cfg_edge fn pb.bb_label bb.bb_label /\
  s.vs_prev_bb = SOME pb.bb_label /\
  scfg_path_defined fn path pb (LENGTH pb.bb_instructions) s /\
  (!qb. MEM qb fn.fn_blocks /\ MEM bb.bb_label (bb_succs qb) ==>
    fn_reachable fn qb.bb_label) /\
  run_block n C bb s = r /\ (!e. r <> Error e) ==>
  run_block n C (fix_phis_in_block (pred_labels fn bb.bb_label) bb) s = r
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode = PHI) ps` by metis_tac[phi_prefix_all_phi] >>
  drule_all scfg_fn_fix_phis_block >> strip_tac >>
  irule scfg_fix_phis_run_snapshot_same_fuel >> metis_tac[]
QED

Theorem scfg_fix_phis_run_no_phi:
  EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions ==>
  run_block n C (fix_phis_in_block actual_preds bb) s = run_block n C bb s
Proof
  simp[scfg_fix_phis_no_phi]
QED

Theorem scfg_fix_phis_run_snapshot_back[local]:
  bb.bb_instructions = ps ++ tail /\
  EVERY (\i. i.inst_opcode = PHI) ps /\
  EVERY (\i. i.inst_opcode <> PHI) tail /\
  rs = FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) ps /\
  cs = FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode <> PHI) ps /\
  eval_phis s ps = OK u /\
  eval_phis s (MAP (fix_phi_inst actual_preds) rs) = OK v /\
  scfg_iprefix C (fix_phis_in_block actual_preds bb)
    (v with vs_inst_idx := LENGTH rs)
    (u with vs_inst_idx := LENGTH rs + LENGTH cs) /\
  run_block n C (fix_phis_in_block actual_preds bb) s = r /\
  (!e. r <> Error e) ==> ?m. run_block m C bb s = r
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
  `exec_block n C (fix_phis_in_block actual_preds bb)
     (v with vs_inst_idx := LENGTH rs) = r` by
    (qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
     qpat_x_assum `rs = _` kall_tac >> qpat_x_assum `cs = _` kall_tac >>
     simp[Excl "APPEND_ASSOC", run_block_def, scfg_eval_phis_append,
          scfg_phi_prefix_append]) >>
  drule_all scfg_iprefix_cancel >> strip_tac >>
  `exec_block m C bb (u with vs_inst_idx := LENGTH ps) = r` by
    (qpat_x_assum `exec_block m _ _ _ = _` mp_tac >>
     dep_rewrite.DEP_REWRITE_TAC[scfg_fix_phis_exec_tail] >>
     simp[] >> metis_tac[]) >>
  qexists_tac `m` >>
  simp[run_block_def, scfg_eval_phis_append, scfg_phi_prefix_append]
QED

Theorem scfg_fn_fix_phis_run_block_back:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  ps = TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\
  bb.bb_instructions = ps ++ tail /\ EVERY (\i. i.inst_opcode <> PHI) tail /\
  rs = FILTER (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode = PHI) ps /\
  cs = FILTER (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode <> PHI) ps /\
  MEM pb fn.fn_blocks /\ fn_cfg_edge fn pb.bb_label bb.bb_label /\
  s.vs_prev_bb = SOME pb.bb_label /\
  scfg_path_defined fn path pb (LENGTH pb.bb_instructions) s /\
  (!qb. MEM qb fn.fn_blocks /\ MEM bb.bb_label (bb_succs qb) ==>
    fn_reachable fn qb.bb_label) /\
  run_block n C (fix_phis_in_block (pred_labels fn bb.bb_label) bb) s = r /\
  (!e. r <> Error e) ==> ?m. run_block m C bb s = r
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode = PHI) ps` by metis_tac[phi_prefix_all_phi] >>
  drule_all scfg_fn_fix_phis_block >> strip_tac >>
  irule scfg_fix_phis_run_snapshot_back >> metis_tac[]
QED

Theorem scfg_entry_block_no_phi:
  simplify_cfg_fn_ok fn /\ fn_entry_state fn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions
Proof
  Cases_on `fn.fn_blocks` >>
  simp[fn_entry_state_def, fn_entry_label_def, entry_block_def,
       lookup_block_def, FIND_thm, simplify_cfg_fn_ok_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem scfg_rooted_fix_phis_run_block_same_fuel:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  (!b. MEM b fn.fn_blocks ==> fn_reachable fn b.bb_label) /\
  fn_entry_state fn s0 /\ scfg_bprefix C fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!e. r <> Error e) /\ run_block n C bb s = r ==>
  run_block n C (fix_phis_in_block (pred_labels fn bb.bb_label) bb) s = r
Proof
  rpt strip_tac >> drule_all scfg_bprefix_incoming >> strip_tac
  >- (gvs[] >> drule_all scfg_entry_block_no_phi >> strip_tac >>
      simp[scfg_fix_phis_run_no_phi]) >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  qabbrev_tac `ps = TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions` >>
  qabbrev_tac `tail = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions` >>
  `bb.bb_instructions = ps ++ tail` by simp[Abbr `ps`, Abbr `tail`] >>
  `EVERY (\i. i.inst_opcode <> PHI) tail` by
    (irule (cj 2 scfg_fn_fix_phis_parts) >>
     simp[Abbr `ps`, Abbr `tail`] >> metis_tac[]) >>
  irule scfg_fn_fix_phis_run_block_same_fuel >>
  simp[] >> metis_tac[]
QED

Theorem scfg_rooted_fix_phis_run_block_back:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  (!b. MEM b fn.fn_blocks ==> fn_reachable fn b.bb_label) /\
  fn_entry_state fn s0 /\ scfg_bprefix C fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!e. r <> Error e) /\
  run_block n C (fix_phis_in_block (pred_labels fn bb.bb_label) bb) s = r ==>
  ?m. run_block m C bb s = r
Proof
  rpt strip_tac >> drule_all scfg_bprefix_incoming >> strip_tac
  >- (gvs[] >> drule_all scfg_entry_block_no_phi >> strip_tac >>
      qexists_tac `n` >> gvs[scfg_fix_phis_run_no_phi]) >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  qabbrev_tac `ps = TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions` >>
  qabbrev_tac `tail = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions` >>
  `bb.bb_instructions = ps ++ tail` by simp[Abbr `ps`, Abbr `tail`] >>
  `EVERY (\i. i.inst_opcode <> PHI) tail` by
    (irule (cj 2 scfg_fn_fix_phis_parts) >>
     simp[Abbr `ps`, Abbr `tail`] >> metis_tac[]) >>
  irule scfg_fn_fix_phis_run_block_back >> simp[] >> metis_tac[]
QED

Theorem scfg_fix_all_phis_lookup:
  lookup_block l (fix_all_phis fn).fn_blocks =
    OPTION_MAP (\bb. fix_phis_in_block (pred_labels fn bb.bb_label) bb)
      (lookup_block l fn.fn_blocks)
Proof
  simp[fix_all_phis_def] >> irule lookup_block_map_proof >>
  simp[fix_phis_in_block_def]
QED
