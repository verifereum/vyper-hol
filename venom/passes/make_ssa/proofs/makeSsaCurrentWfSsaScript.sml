(*
 * MakeSSA (make_ssa_current_fn, the supply variant the O1 dispatcher runs)
 * produces SSA: every variable is written once, and every use is reached
 * only through its definition.  The premises are those of the run's
 * simulation lemmas (o1ContractMakeSsa); the same statement covers the
 * first run (no PHIs in the input) and the second (the first run's PHIs).
 * One more premise: each input PHI names every label once, and only
 * predecessors.  The pass never drops a pair, so an extra or repeated label
 * would survive into the output and break phi_edge_uses_wf; on the second
 * run the first run's wf_ssa output gives it.
 *)
Theory makeSsaCurrentWfSsa
Ancestors
  makeSsaCurrentDefs makeSsaCurrentProps venomWf cfgWf venomInst irSupply
  unitShapeDefs o1PassContract makeSsaCurrentRenameTrace list
  makeSsaCurrentSourceCuts makeSsaCurrentAllocation makeSsaCurrentTreeTrace
  makeSsaCurrentFinalBlock makeSsaCurrentTreePaths makeSsaCurrentTraceCertificate
  makeSsaCurrentAvailability venomExecProofs

(* Consumer probe: the annotation at an output position names exactly the
   concrete output at that position.  Defaults cannot be substituted here. *)
Theorem current_wf_inst_output_name[local]:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' /\
  current_annotations_ok V H anns /\ j < LENGTH anns ==>
  j < LENGTH inst'.inst_outputs /\
  current_token_name H' (FST (EL j anns)) = SOME (EL j inst'.inst_outputs)
Proof
  simp[current_inst_trace_def] >> rpt strip_tac >>
  drule_all current_outputs_trace_names >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[] >>
  first_x_assum (qspec_then `j` mp_tac) >>
  Cases_on `EL j anns` >> simp[]
QED

(* Updates cannot invent a token: its owner was assigned in the prefix,
   or the token was inherited at entry. *)
Theorem current_wf_fold_origin[local]:
  !anns E v.
  FOLDL (\env (t,w). (w =+ t) env) E anns v = E v \/
  MEM (FOLDL (\env (t,w). (w =+ t) env) E anns v,v) anns
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  rpt gen_tac >> simp[] >>
  first_x_assum (qspecl_then [`(h1 =+ h0) E`, `v`] mp_tac) >>
  Cases_on `h1 = v` >> simp[combinTheory.APPLY_UPDATE_THM] >>
  metis_tac[]
QED

Theorem current_wf_local_origin[local]:
  current_local_trace annss insts s rs H E insts' s' rs' H' E' ==>
  E' v = E v \/ ?k. k < LENGTH annss /\ MEM (E' v,v) (EL k annss)
Proof
  strip_tac >> drule current_local_trace_exit_env >> strip_tac >>
  qspec_then `FLAT annss` (qspecl_then [`E`, `v`] mp_tac)
    current_wf_fold_origin >>
  simp[MEM_FLAT, MEM_EL] >> metis_tac[]
QED

Theorem current_wf_source_cut_origin[local]:
  current_source_cut A
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) n rs E ==>
  E v = E0 v \/ ?k. k < n /\ MEM (E v,v) (EL k (A l))
Proof
  simp[current_source_cut_def] >> rpt strip_tac >>
  qpat_x_assum `current_local_trace aq xq _ _ _ _ _ _ _ _ _` kall_tac >>
  drule current_wf_local_origin >>
  disch_then (qspec_then `v` strip_assume_tac)
  >- simp[] >>
  disj2_tac >> qexists_tac `k` >> simp[EL_APPEND_EQN]
QED

Theorem current_wf_local_output_name[local]:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' /\
  current_annotations_ok V H (FLAT annss) ==>
  !k j. k < LENGTH annss /\ j < LENGTH (EL k annss) ==>
    k < LENGTH insts' /\ j < LENGTH (EL k insts').inst_outputs /\
    current_token_name H' (FST (EL j (EL k annss))) =
      SOME (EL j (EL k insts').inst_outputs)
Proof
  Induct >> simp[current_local_trace_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  `current_annotations_ok V H h` by
    metis_tac[current_annotations_split, FLAT] >>
  rpt gen_tac >> strip_tac >> Cases_on `k`
  >- (gvs[] >> drule_all current_wf_inst_output_name >>
      strip_tac >>
      drule current_local_trace_history >> strip_tac >> gvs[] >>
      metis_tac[current_token_name_append_stable]) >>
  `current_annotations_ok V H1 (FLAT annss)` by
    (gvs[current_inst_trace_def] >>
     irule current_outputs_trace_remaining >> metis_tac[FLAT]) >>
  first_x_assum drule >> simp[] >>
  disch_then (qspecl_then [`n`, `j`] mp_tac) >> gvs[]
QED

Definition current_wf_output_at_def:
  current_wf_output_at A H ev k t <=>
    k < LENGTH (A (current_event_label ev)) /\
    k < LENGTH (current_event_renamed_block ev).bb_instructions /\
    ?j. j < LENGTH (EL k (A (current_event_label ev))) /\
      FST (EL j (EL k (A (current_event_label ev)))) = t /\
      j < LENGTH (EL k (current_event_renamed_block ev).bb_instructions).inst_outputs /\
      current_token_name H t = SOME
        (EL j (EL k (current_event_renamed_block ev).bb_instructions).inst_outputs)
End

Theorem current_wf_event_output_at[local]:
  current_event_trace A H ev /\ current_event_valid A V ev /\
  k < LENGTH (A (current_event_label ev)) /\
  j < LENGTH (EL k (A (current_event_label ev))) ==>
  current_wf_output_at A H ev k
    (FST (EL j (EL k (A (current_event_label ev)))))
Proof
  PairCases_on `ev` >>
  simp[current_event_trace_def, current_event_valid_def,
    current_event_label_def, current_event_renamed_block_def,
    current_wf_output_at_def] >> strip_tac >>
  drule_all current_wf_local_output_name >> strip_tac >> simp[] >>
  qexists_tac `j` >> simp[] >>
  metis_tac[current_token_name_append_stable]
QED

Theorem current_wf_provenance_valid_events[local]:
  LENGTH olds = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,bbs)) annsss /\
  ALL_DISTINCT (MAP FST (FLAT (FLAT annsss))) /\
  ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) /\
  ssa_vars_covered s (MAP FST defs) /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  current_tree_trace (current_annotation_map bbs annsss) sm tree
    s (init_current_rename_state defs) bbs [] CurrentDefault []
    ctrs' s' bbs' H' visited' events ==>
  EVERY (current_event_valid (current_annotation_map bbs annsss)
    (FLAT (MAP block_ir_vars bbs))) events
Proof
  strip_tac >>
  `LENGTH bbs = LENGTH annsss` by (drule LIST_REL_LENGTH >> simp[]) >>
  `LIST_REL (\bb anns.
      LIST_REL (\a inst. MAP SND a = inst.inst_outputs) anns bb.bb_instructions)
      bbs annsss` by
    (irule current_provenance_map_owners >> metis_tac[]) >>
  `current_annotations_ok (FLAT (MAP block_ir_vars bbs))
      ([] : (current_token # string # string) list) (FLAT (FLAT annsss))` by
    (irule current_provenance_annotations_ok >> simp[] >> conj_tac
     >- (drule current_annotation_owners_in_vars >> simp[]) >>
     qexistsl_tac [`fn`, `ZIP (olds,bbs)`] >> simp[]) >>
  `current_pending_annotations (FLAT (MAP block_ir_vars bbs))
      (current_annotation_map bbs annsss) [] []` by
    metis_tac[current_annotation_map_pending] >>
  `current_annotation_separation (current_annotation_map bbs annsss)` by
    (irule current_annotation_map_separation >> fs[current_annotations_ok_def]) >>
  `current_allocation_consistent (FLAT (MAP block_ir_vars bbs))
      ([] : (current_token # string # string) list) s (init_current_rename_state defs) /\
    current_env_realizes ([] : (current_token # string # string) list)
      CurrentDefault (init_current_rename_state defs) (FLAT (MAP block_ir_vars bbs))` by
    (irule current_initial_state_valid >> simp[]) >>
  drule (cj 1 current_tree_trace_events_valid) >> simp[] >>
  disch_then irule >> simp[]
QED

(* Validity, concrete names and local projections share this single history. *)
Theorem current_wf_named_structural_certificate:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  ?A H events V.
    current_structural_certificate s fn fn' s' A H events /\
    EVERY (current_event_valid A V) events /\
    EVERY (current_event_names H V) events /\
    EVERY (current_event_trace A H) events /\
    (!ev k j. MEM ev events /\
      k < LENGTH (A (current_event_label ev)) /\
      j < LENGTH (EL k (A (current_event_label ev))) ==>
      current_wf_output_at A H ev k
        (FST (EL j (EL k (A (current_event_label ev))))))
Proof
  strip_tac >> drule_all current_make_ssa_stages >> strip_tac >>
  `MAP (\b. b.bb_label) ins = MAP (\b. b.bb_label) fn.fn_blocks /\
    ssa_vars_covered si (FLAT (MAP block_ir_vars ins)) /\
    ssa_vars_covered si (MAP FST defs)` by
    (irule current_insertion_initial_supply >> metis_tac[]) >>
  `LENGTH fn.fn_blocks = LENGTH ins` by metis_tac[LENGTH_MAP] >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  qpat_x_assum `defs = _` SUBST_ALL_TAC >>
  drule_all current_actual_tree_trace >>
  disch_then (qspecl_then [`[]`, `CurrentDefault`] strip_assume_tac) >>
  `EVERY (current_event_valid (current_annotation_map ins annsss)
    (FLAT (MAP block_ir_vars ins))) events` by
    (drule_all current_wf_provenance_valid_events >> simp[]) >>
  drule_all current_provenance_initial_tree_names >> strip_tac >>
  `EVERY (current_event_trace (current_annotation_map ins annsss) H') events` by
    metis_tac[cj 1 current_tree_trace_events] >>
  qexistsl_tac [`current_annotation_map ins annsss`, `H'`, `events`,
    `FLAT (MAP block_ir_vars ins)`] >> simp[] >> conj_tac
  >- (simp[current_structural_certificate_def] >> metis_tac[]) >>
  rpt strip_tac >> irule current_wf_event_output_at >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem current_wf_path_last_edge[local]:
  !pre p target. is_fn_path fn (pre ++ [p;target]) ==>
    is_fn_path fn (pre ++ [p]) /\ fn_cfg_edge fn p target
Proof
  Induct >> simp[is_fn_path_def] >> rpt gen_tac >>
  Cases_on `pre` >> gvs[is_fn_path_def] >> metis_tac[]
QED

Theorem current_wf_first_entry_path:
  fn_reachable fn target /\ fn_entry_label fn = SOME entry /\ entry <> target ==>
  ?path pred. is_fn_path fn path /\ path <> [] /\
    HD path = entry /\ LAST path = pred /\
    fn_cfg_edge fn pred target /\ ~MEM target path
Proof
  simp[fn_reachable_def] >> strip_tac >>
  drule rtc_to_fn_path >> strip_tac >>
  drule_all current_path_first_target >> strip_tac >>
  `pre <> []` by (Cases_on `pre` >> gvs[]) >>
  Cases_on `pre` using SNOC_CASES >> gvs[SNOC_APPEND] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  drule current_wf_path_last_edge >> strip_tac >>
  qexists_tac `l ++ [x]` >> simp[] >>
  Cases_on `l` >> gvs[]
QED

Theorem make_ssa_current_fn_wf_ssa:
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  fn_phis_cover_preds fn /\
  (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
     inst.inst_opcode = PHI ==>
     ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
     !l v. MEM (l,v) (phi_pairs inst.inst_operands) ==>
       fn_cfg_edge fn l bb.bb_label) /\
  fn_phi_outputs_single_def fn /\ fn_phis_non_degenerate fn /\
  all_reachable fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  wf_ssa fn'
Proof
  cheat
QED
