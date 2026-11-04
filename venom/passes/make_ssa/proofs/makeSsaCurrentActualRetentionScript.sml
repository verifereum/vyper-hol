Theory makeSsaCurrentActualRetention
Ancestors
  makeSsaCurrentOutputNames makeSsaCurrentExitTokens makeSsaCurrentRetention
  makeSsaCurrentCleanupBoundary
  makeSsaCurrentFinalSlots makeSsaCurrentAllocation makeSsaCurrentRenameTrace
  makeSsaCurrentTreeTrace makeSsaCurrentTreePaths makeSsaCurrentInduct
  makeSsaCurrentEdgeTrace makeSsaCurrentTraceCertificate makeSsaCurrentCertificate
  makeSsaCurrentSourceCuts makeSsaCurrentFinalBlock irSupply
  venomWf venomInst list pair alist arithmetic

(* Extra predecessor labels are permitted by the frozen input contract.
   This probes the retention proof's proposed witness-to-event step, not
   the semantic correctness of the pass. *)
Definition current_extra_slot_phi_def:
  current_extra_slot_phi = mk_inst 2 PHI
    [Label "E"; Var "a"; Label "Ghost"; Var "b"; Label "Phantom"; Var "c"] ["v"]
End

Definition current_extra_slot_fn_def:
  current_extra_slot_fn = mk_raw_function "extra_slots"
    [<| bb_label := "E"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit 1w] ["a"]; mk_inst 1 JMP [Label "D"] []] |>;
     <| bb_label := "D"; bb_instructions :=
        [current_extra_slot_phi; mk_inst 3 STOP [] []] |>]
End

Theorem current_extra_slot_witness_probe:
  inst_wf current_extra_slot_phi /\
  phi_pairs current_extra_slot_phi.inst_operands =
    [("E","a"); ("Ghost","b"); ("Phantom","c")] /\
  fn_cfg_edge current_extra_slot_fn "E" "D" /\
  ~fn_cfg_edge current_extra_slot_fn "Ghost" "D" /\
  ~fn_cfg_edge current_extra_slot_fn "Phantom" "D"
Proof
  EVAL_TAC >>
  pure_rewrite_tac[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  simp[] >> qexists_tac `EL 0 current_extra_slot_fn.fn_blocks` >> EVAL_TAC
QED

Theorem current_extra_slot_input_probe:
  fn_inst_wf current_extra_slot_fn /\
  fn_phis_non_degenerate current_extra_slot_fn
Proof
  conj_tac >- EVAL_TAC >>
  simp[fn_phis_non_degenerate_def, fn_insts_def, fn_insts_blocks_def,
    current_extra_slot_fn_def, current_extra_slot_phi_def, mk_raw_function_def,
    mk_inst_def] >> rpt strip_tac >> gvs[] >>
  qexistsl_tac [`"E"`, `"a"`, `"Ghost"`, `"b"`] >> EVAL_TAC
QED

(* A source owner's unchanged spelling and allocated spellings form one
   name class. Different source owners have disjoint classes. *)
Definition current_owner_name_def:
  current_owner_name H (v : string) n <=>
    n = v \/ ?t : current_token. MEM (t,v,n) H
End

Theorem current_owner_name_separate:
  current_history_valid V H /\ MEM v V /\ MEM w V /\ v <> w /\
  current_owner_name H v n /\ current_owner_name H w m ==> n <> m
Proof
  rpt strip_tac >>
  gvs[current_owner_name_def, current_history_valid_def, EVERY_MEM,
    FORALL_PROD]
  >- metis_tac[]
  >- metis_tac[] >>
  qpat_x_assum `!a b c. _` kall_tac >>
  qpat_x_assum `MEM v V` kall_tac >>
  qpat_x_assum `MEM w V` kall_tac >>
  fs[MEM_EL] >>
  `EL n H = EL n' H` suffices_by metis_tac[PAIR_EQ] >>
  `n = n'` suffices_by simp[] >>
  `EL n (MAP (SND o SND) H) = EL n' (MAP (SND o SND) H)` by
    (simp[EL_MAP] >> metis_tac[SND]) >>
  metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP]
QED

Theorem current_event_fold_pair_inactive:
  !events slot.
  (!ev. MEM ev events /\ FST slot = current_event_label ev ==>
    ~MEM h (case ALOOKUP sm (current_event_label ev) of NONE => [] | SOME ss => ss)) ==>
  FOLDL (\slot ev. current_event_pair_action sm h ev slot) slot events = slot
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  `current_event_pair_action sm h h' slot = slot` by
    (Cases_on `slot` >> gvs[current_event_pair_action_def] >>
     IF_CASES_TAC >> gvs[] >> metis_tac[]) >>
  simp[] >> first_x_assum irule >> metis_tac[]
QED

Theorem current_event_fold_pair_cases:
  ALL_DISTINCT (MAP current_event_label events) ==>
  FOLDL (\slot ev. current_event_pair_action sm h ev slot) (p,v) events = (p,v) \/
  ?ev. MEM ev events /\ current_event_label ev = p /\
    MEM h (case ALOOKUP sm p of NONE => [] | SOME ss => ss) /\
    FOLDL (\slot ev. current_event_pair_action sm h ev slot) (p,v) events =
      (p,latest_current_name (current_event_exit_rs ev) v)
Proof
  strip_tac >>
  Cases_on `?ev. MEM ev events /\ current_event_label ev = p /\
    MEM h (case ALOOKUP sm p of NONE => [] | SOME ss => ss)`
  >- (gvs[] >> disj2_tac >> qexists_tac `ev` >> simp[] >>
      qspec_then `events`
        (qspecl_then [`(current_event_label ev,v)`, `ev`] mp_tac)
        current_event_fold_pair_unique >> simp[]) >>
  disj1_tac >> irule current_event_fold_pair_inactive >> simp[] >> metis_tac[]
QED

Definition current_env_history_owners_def:
  current_env_history_owners (H : (current_token # string # string) list) E <=>
    !v. E v = CurrentDefault v \/ ?n. MEM (E v,v,n) H
End

Theorem current_env_history_owners_default[simp]:
  current_env_history_owners H CurrentDefault
Proof
  simp[current_env_history_owners_def]
QED

Theorem current_env_history_owners_append:
  current_env_history_owners H E ==>
  current_env_history_owners (H ++ tail) E
Proof
  simp[current_env_history_owners_def, MEM_APPEND] >> metis_tac[]
QED

Theorem current_env_history_owners_push:
  current_env_history_owners H E ==>
  current_env_history_owners (H ++ [(t,v,n)]) ((v =+ t) E)
Proof
  simp[current_env_history_owners_def, combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >> Cases_on `v' = v` >> simp[] >> metis_tac[MEM_APPEND]
QED

Theorem current_outputs_trace_history_owners:
  !anns s rs H E names s' rs' H' E'.
  current_outputs_trace anns s rs H E names s' rs' H' E' /\
  current_env_history_owners H E ==> current_env_history_owners H' E'
Proof
  Induct >> simp[current_outputs_trace_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_outputs_trace_def] >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >>
  impl_tac >- (irule current_env_history_owners_push >> simp[]) >> simp[]
QED

Theorem current_inst_trace_history_owners:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' /\
  current_env_history_owners H E ==> current_env_history_owners H' E'
Proof
  simp[current_inst_trace_def] >> metis_tac[current_outputs_trace_history_owners]
QED

Theorem current_local_trace_history_owners:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' /\
  current_env_history_owners H E ==> current_env_history_owners H' E'
Proof
  Induct >> simp[current_local_trace_def] >> rpt gen_tac >> strip_tac >>
  drule_all current_inst_trace_history_owners >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem current_env_history_owner_name:
  current_history_valid V H /\ current_env_history_owners H E /\
  current_token_name H (E v) = SOME n ==> current_owner_name H v n
Proof
  strip_tac >>
  `E v = CurrentDefault v \/ ?m. MEM (E v,v,m) H` by
    fs[current_env_history_owners_def]
  >- gvs[current_owner_name_def] >>
  `ALOOKUP H (E v) = SOME (v,m)` by
    (irule ALOOKUP_ALL_DISTINCT_MEM >> fs[current_history_valid_def]) >>
  `!w. E v <> CurrentDefault w` by
    (fs[current_history_valid_def, EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
  Cases_on `E v` >> gvs[current_token_name_def, current_owner_name_def] >> metis_tac[]
QED

Theorem current_event_history_owners_append:
  EVERY (\ev. current_env_history_owners H (current_event_exit_env ev)) events ==>
  EVERY (\ev. current_env_history_owners (H ++ tail) (current_event_exit_env ev)) events
Proof
  simp[EVERY_MEM] >> metis_tac[current_env_history_owners_append]
QED

Theorem current_tree_trace_history_owners:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events /\ current_env_history_owners H E ==>
    EVERY (\ev. current_env_history_owners H' (current_event_exit_env ev)) events) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events /\ current_env_history_owners H E ==>
    EVERY (\ev. current_env_history_owners H' (current_event_exit_env ev)) events)
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      drule_all current_local_trace_history_owners >> strip_tac >>
      drule (cj 2 current_tree_trace_history) >> strip_tac >>
      first_x_assum drule >> simp[] >> strip_tac >>
      simp[current_event_exit_env_def] >>
      metis_tac[current_env_history_owners_append])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  `?tail. H1 = H ++ tail` by metis_tac[cj 1 current_tree_trace_history] >>
  `?tail. H' = H1 ++ tail` by metis_tac[cj 2 current_tree_trace_history] >>
  `current_env_history_owners H1 E` by metis_tac[current_env_history_owners_append] >>
  last_x_assum drule_all >> strip_tac >>
  last_x_assum drule_all >> strip_tac >>
  simp[EVERY_APPEND] >> metis_tac[current_event_history_owners_append]
QED

Theorem current_event_names_exit:
  current_event_names H V ev /\ MEM v V ==>
  current_token_name H (current_event_exit_env ev v) =
    SOME (latest_current_name (current_event_exit_rs ev) v)
Proof
  PairCases_on `ev` >>
  simp[current_event_names_def, current_event_exit_env_def, current_event_exit_rs_def]
QED

Theorem current_event_exit_owner_names:
  EVERY (\ev. current_env_history_owners H (current_event_exit_env ev)) events /\
  EVERY (current_event_names H V) events /\ current_history_valid V H ==>
  !ev v. MEM ev events /\ MEM v V ==>
    current_owner_name H v (latest_current_name (current_event_exit_rs ev) v)
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  irule current_env_history_owner_name >> conj_tac
  >- (qexists_tac `current_event_exit_env ev` >>
      metis_tac[current_event_names_exit]) >> metis_tac[]
QED

Theorem current_event_fold_pair_owner_name:
  ALL_DISTINCT (MAP current_event_label events) /\
  (!ev v. MEM ev events /\ MEM v V ==>
    current_owner_name H v (latest_current_name (current_event_exit_rs ev) v)) /\
  MEM v V ==>
  current_owner_name H v
    (SND (FOLDL (\slot ev. current_event_pair_action sm h ev slot) (p,v) events))
Proof
  strip_tac >> drule current_event_fold_pair_cases >>
  disch_then (qspecl_then [`v`, `sm`, `p`, `h`] mp_tac) >>
  strip_tac >> gvs[current_owner_name_def] >> metis_tac[current_owner_name_def]
QED

Theorem current_annotated_tree_history_valid:
  LENGTH bbs = LENGTH annsss /\
  current_annotations_ok V ([] : (current_token # string # string) list)
    (FLAT (FLAT annsss)) /\
  current_allocation_consistent V [] s rs /\
  current_env_realizes ([] : (current_token # string # string) list) E rs V /\
  current_env_history_owners [] E /\ ALL_DISTINCT (dom_tree_labels tree) /\
  current_tree_trace (current_annotation_map bbs annsss) sm tree
    s rs bbs [] E [] ctrs' s' bbs' H' visited' events ==>
  current_history_valid V H'
Proof
  strip_tac >>
  `current_pending_annotations V (current_annotation_map bbs annsss) [] []` by
    metis_tac[current_annotation_map_pending] >>
  `current_annotation_separation (current_annotation_map bbs annsss)` by
    (irule current_annotation_map_separation >> fs[current_annotations_ok_def]) >>
  drule (cj 1 current_tree_trace_preserves) >> simp[] >>
  disch_then (qspec_then `V` mp_tac) >> simp[current_allocation_consistent_def]
QED

Theorem current_annotated_tree_owner_names:
  LENGTH bbs = LENGTH annsss /\
  current_annotations_ok V ([] : (current_token # string # string) list)
    (FLAT (FLAT annsss)) /\
  current_allocation_consistent V [] s rs /\ current_env_realizes ([] : (current_token # string # string) list) E rs V /\
  current_env_history_owners [] E /\ ALL_DISTINCT (dom_tree_labels tree) /\
  current_tree_trace (current_annotation_map bbs annsss) sm tree
    s rs bbs [] E [] ctrs' s' bbs' H' visited' events ==>
  !ev v. MEM ev events /\ MEM v V ==>
    current_owner_name H' v (latest_current_name (current_event_exit_rs ev) v)
Proof
  strip_tac >>
  `current_history_valid V H'` by metis_tac[current_annotated_tree_history_valid] >>
  drule_all current_annotated_tree_events_valid >> strip_tac >>
  drule (cj 1 current_tree_trace_events) >> strip_tac >>
  drule_all current_events_names_valid >> strip_tac >>
  drule_all (cj 1 current_tree_trace_history_owners) >> strip_tac >>
  metis_tac[current_event_exit_owner_names]
QED

Theorem current_event_fold_slots_owner_name:
  ALL_DISTINCT (MAP current_event_label events) /\
  (!ev v. MEM ev events /\ MEM v V ==>
    current_owner_name H v (latest_current_name (current_event_exit_rs ev) v)) /\
  i < LENGTH slots /\ EL i slots = (p,v) /\ MEM v V ==>
  ?n. EL (2*i) (FOLDL (\ops ev. current_event_operand_action sm h ev ops)
      (current_phi_slots slots) events) = Label p /\
    EL (2*i+1) (FOLDL (\ops ev. current_event_operand_action sm h ev ops)
      (current_phi_slots slots) events) = Var n /\ current_owner_name H v n
Proof
  strip_tac >> rewrite_tac[current_event_fold_slots] >>
  qspec_then `MAP (\slot. FOLDL (\slot ev. current_event_pair_action sm h ev slot)
    slot events) slots` (qspec_then `i` mp_tac) current_phi_slots_index >>
  simp[EL_MAP] >> strip_tac >>
  irule current_event_fold_pair_owner_name >> simp[] >> metis_tac[]
QED

Theorem current_annotated_tree_phi_slot_owner:
  LENGTH bbs = LENGTH annsss /\
  current_annotations_ok V ([] : (current_token # string # string) list)
    (FLAT (FLAT annsss)) /\
  current_allocation_consistent V [] s rs /\ current_env_realizes ([] : (current_token # string # string) list) E rs V /\
  current_env_history_owners [] E /\ ALL_DISTINCT (dom_tree_labels tree) /\
  current_tree_trace (current_annotation_map bbs annsss) sm tree
    s rs bbs [] E [] ctrs' s' bbs' H' visited' events /\
  (!p ss. ALOOKUP sm p = SOME ss ==> ALL_DISTINCT ss) /\
  (!l. MEM l (dom_tree_labels tree) ==> IS_SOME (lookup_block l bbs)) /\
  lookup_block h bbs = SOME old /\ k < LENGTH old.bb_instructions /\
  (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_operands = current_phi_slots slots /\
  i < LENGTH slots /\ EL i slots = (p,v) /\ MEM v V ==>
  ?new n. lookup_block h bbs' = SOME new /\
    LENGTH new.bb_instructions = LENGTH old.bb_instructions /\
    k < LENGTH new.bb_instructions /\ (EL k new.bb_instructions).inst_opcode = PHI /\
    EL (2*i) (EL k new.bb_instructions).inst_operands = Label p /\
    EL (2*i+1) (EL k new.bb_instructions).inst_operands = Var n /\
    current_owner_name H' v n
Proof
  strip_tac >>
  `!ev v. MEM ev events /\ MEM v V ==>
    current_owner_name H' v (latest_current_name (current_event_exit_rs ev) v)` by
    metis_tac[current_annotated_tree_owner_names] >>
  `ALL_DISTINCT (MAP current_event_label events)` by
    (irule current_tree_trace_event_labels_distinct >> metis_tac[]) >>
  drule_all current_tree_trace_phi_lookup >> strip_tac >>
  drule_all current_phi_view_fold_instruction >> strip_tac >>
  `?n. EL (2*i) (FOLDL (\ops ev. current_event_operand_action sm h ev ops)
        (current_phi_slots slots) events) = Label p /\
      EL (2*i+1) (FOLDL (\ops ev. current_event_operand_action sm h ev ops)
        (current_phi_slots slots) events) = Var n /\ current_owner_name H' v n` by
    (irule current_event_fold_slots_owner_name >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`new`, `n`] >> simp[]
QED

Theorem current_provenance_tree_original_phi_slot_owner:
  LENGTH olds = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,bbs)) annsss /\
  ALL_DISTINCT (MAP FST (FLAT (FLAT annsss))) /\
  ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) /\ ssa_vars_covered s (MAP FST defs) /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  (!l. MEM l (dom_tree_labels tree) ==> IS_SOME (lookup_block l bbs)) /\
  (!p ss. ALOOKUP sm p = SOME ss ==> ALL_DISTINCT ss) /\
  current_tree_trace (current_annotation_map bbs annsss) sm tree
    s (init_current_rename_state defs) bbs [] CurrentDefault []
    ctrs' s' bbs' H' visited' events /\
  lookup_block h olds = SOME old /\ k < LENGTH old.bb_instructions /\
  (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_operands = current_phi_slots slots /\
  i < LENGTH slots /\ EL i slots = (p,v) ==>
  ?pre inserted final n.
    lookup_block h bbs = SOME inserted /\
    inserted = old with bb_instructions := pre ++ old.bb_instructions /\
    lookup_block h bbs' = SOME final /\
    LENGTH final.bb_instructions = LENGTH inserted.bb_instructions /\
    LENGTH pre+k < LENGTH final.bb_instructions /\
    (EL (LENGTH pre+k) final.bb_instructions).inst_opcode = PHI /\
    EL (2*i) (EL (LENGTH pre+k) final.bb_instructions).inst_operands = Label p /\
    EL (2*i+1) (EL (LENGTH pre+k) final.bb_instructions).inst_operands = Var n /\
    current_owner_name H' v n
Proof
  strip_tac >>
  `LENGTH bbs = LENGTH annsss` by (drule LIST_REL_LENGTH >> simp[]) >>
  drule_all current_provenance_tree_annotations_ok >> strip_tac >>
  `current_allocation_consistent (FLAT (MAP block_ir_vars bbs))
      ([] : (current_token # string # string) list) s (init_current_rename_state defs) /\
    current_env_realizes ([] : (current_token # string # string) list)
      CurrentDefault (init_current_rename_state defs) (FLAT (MAP block_ir_vars bbs))` by
    (irule current_initial_state_valid >> simp[]) >>
  drule_all current_provenance_annotation_lookup >> strip_tac >>
  `LENGTH pre+k < LENGTH inserted.bb_instructions /\
    (EL (LENGTH pre+k) inserted.bb_instructions).inst_opcode = PHI /\
    (EL (LENGTH pre+k) inserted.bb_instructions).inst_operands = current_phi_slots slots` by
    simp[EL_APPEND_EQN] >>
  `MEM v (FLAT (MAP block_ir_vars bbs))` by
    metis_tac[current_initial_slot_var_covered] >>
  `current_env_history_owners [] CurrentDefault` by simp[] >>
  drule_all current_annotated_tree_phi_slot_owner >> strip_tac >>
  qexistsl_tac [`pre`, `inserted`, `new`, `n`] >> simp[]
QED

Theorem current_outputs_trace_owned_names:
  !anns s rs H E names s' rs' H' E'.
  current_outputs_trace anns s rs H E names s' rs' H' E' ==>
  LIST_REL (\(t,v) n. MEM (t,v,n) H') anns names
Proof
  Induct >> simp[current_outputs_trace_def] >> rpt gen_tac >> strip_tac >>
  PairCases_on `h` >> gvs[current_outputs_trace_def] >>
  drule current_outputs_trace_history >> strip_tac >>
  first_x_assum drule >> simp[MEM_APPEND]
QED

Theorem current_local_trace_owned_names:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' ==>
  LIST_REL (\anns inst. LIST_REL (\(t,v) n. MEM (t,v,n) H')
    anns inst.inst_outputs) annss insts'
Proof
  Induct >> simp[current_local_trace_def] >> rpt gen_tac >> strip_tac >>
  `LIST_REL (\(t,v) n. MEM (t,v,n) H1) h inst1.inst_outputs` by
    (fs[current_inst_trace_def] >>
     Cases_on `inst.inst_opcode = PHI` >> gvs[] >>
     metis_tac[current_outputs_trace_owned_names]) >>
  `?tail. H' = H1 ++ tail` by metis_tac[current_local_trace_history] >>
  simp[] >> conj_tac
  >- (irule LIST_REL_mono >> goal_assum $ drule_at Any >>
      simp[FORALL_PROD, MEM_APPEND]) >>
  qpat_x_assum `!insts s rs H E insts' s' rs' H' E'. _` drule >> simp[]
QED

Theorem current_local_original_output_owner:
  current_local_trace (current_block_annotations old pre) insts s rs H E
    renamed s' rs' H' E' /\
  i < LENGTH old.bb_instructions /\ j < LENGTH (EL i old.bb_instructions).inst_outputs ==>
  MEM (CurrentOriginal old.bb_label i j, EL j (EL i old.bb_instructions).inst_outputs,
    EL j (EL (LENGTH pre+i) renamed).inst_outputs) H'
Proof
  strip_tac >> drule current_local_trace_owned_names >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  `LENGTH (current_block_annotations old pre) = LENGTH pre + LENGTH old.bb_instructions` by
    simp[NoAsms, current_block_annotations_def, current_inserted_annotations_def] >>
  qpat_x_assum `!n. _` (qspec_then `LENGTH pre+i` mp_tac) >> simp[] >> strip_tac >>
  `j < LENGTH (EL (LENGTH pre+i) (current_block_annotations old pre))` by
    simp[current_block_annotations_def, current_inserted_annotations_def, EL_APPEND_EQN,
      current_original_annotations_index] >>
  first_x_assum (qspec_then `j` mp_tac) >>
  gvs[current_block_annotations_def, current_inserted_annotations_def, EL_APPEND_EQN,
    current_original_annotations_index, current_original_outputs_index, ADD_COMM]
QED

Theorem current_tree_original_output_owner:
  ALL_DISTINCT (dom_tree_labels tree) /\
  LENGTH olds = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,bbs)) annsss /\
  current_tree_trace (current_annotation_map bbs annsss) sm tree
    s rs bbs [] E [] ctrs' s' bbs' H' visited' events /\
  events = before ++ (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)::after /\
  lookup_block l olds = SOME old /\
  i < LENGTH old.bb_instructions /\ j < LENGTH (EL i old.bb_instructions).inst_outputs ==>
  ?pre inserted final.
    lookup_block l bbs = SOME inserted /\
    inserted = old with bb_instructions := pre ++ old.bb_instructions /\
    lookup_block l bbs' = SOME final /\
    MEM (CurrentOriginal old.bb_label i j, EL j (EL i old.bb_instructions).inst_outputs,
      EL j (EL (LENGTH pre+i) final.bb_instructions).inst_outputs) H'
Proof
  strip_tac >> drule_all current_provenance_annotation_lookup >> strip_tac >>
  drule (cj 1 current_tree_trace_events) >> simp[EVERY_APPEND] >> strip_tac >>
  `MEM (CurrentOriginal old.bb_label i j, EL j (EL i old.bb_instructions).inst_outputs,
      EL j (EL (LENGTH pre+i) ren).inst_outputs) H'` by
    (fs[current_event_trace_def] >> gvs[] >>
     drule_all current_local_original_output_owner >> simp[MEM_APPEND]) >>
  `LENGTH pre+i < LENGTH ren` by
    (fs[current_event_trace_def] >> gvs[] >>
     drule current_local_trace_lengths >>
     simp[current_block_annotations_def, current_inserted_annotations_def]) >>
  drule_all current_trace_final_event >>
  simp[current_event_label_def, current_event_renamed_block_def] >> strip_tac >>
  qexists_tac `pre` >> simp[] >>
  qmatch_goalsub_abbrev_tac `current_replay_edges sm evs start` >>
  `LENGTH pre+i < LENGTH start.bb_instructions` by simp[Abbr `start`] >>
  `(EL (LENGTH pre+i) (current_replay_edges sm evs start).bb_instructions).inst_outputs =
      (EL (LENGTH pre+i) start.bb_instructions).inst_outputs` by
    metis_tac[current_replay_edges_output_index] >>
  gvs[Abbr `start`, ADD_COMM]
QED

Theorem current_owner_phi_retained:
  current_history_valid V H /\ MEM out V /\ current_owner_name H out name /\
  (!p v. MEM (p,v) slots ==> MEM v V) /\
  (!ev v. MEM ev events /\ MEM v V ==>
    current_owner_name H v (latest_current_name (current_event_exit_rs ev) v)) /\
  ALL_DISTINCT (MAP current_event_label events) /\
  MEM (p,a) slots /\ MEM (q,b) slots /\ a <> b /\ a <> out /\ b <> out /\
  inst.inst_opcode = PHI /\ inst.inst_outputs = [name] /\
  inst.inst_operands = FOLDL (\ops ev. current_event_operand_action sm h ev ops)
    (current_phi_slots slots) events ==>
  simplify_current_phi inst = inst
Proof
  strip_tac >>
  `current_owner_name H a (SND (FOLDL (\slot ev. current_event_pair_action sm h ev slot)
      (p,a) events))` by
    (irule current_event_fold_pair_owner_name >> simp[] >> metis_tac[]) >>
  `current_owner_name H b (SND (FOLDL (\slot ev. current_event_pair_action sm h ev slot)
      (q,b) events))` by
    (irule current_event_fold_pair_owner_name >> simp[] >> metis_tac[]) >>
  `SND (FOLDL (\slot ev. current_event_pair_action sm h ev slot) (p,a) events) <>
     SND (FOLDL (\slot ev. current_event_pair_action sm h ev slot) (q,b) events) /\
   SND (FOLDL (\slot ev. current_event_pair_action sm h ev slot) (p,a) events) <> name /\
   SND (FOLDL (\slot ev. current_event_pair_action sm h ev slot) (q,b) events) <> name` by
    metis_tac[current_owner_name_separate] >>
  irule current_phi_slots_retained >> conj_tac >- simp[] >>
  qexistsl_tac [`SND (FOLDL (\slot ev. current_event_pair_action sm h ev slot) (p,a) events)`,
    `SND (FOLDL (\slot ev. current_event_pair_action sm h ev slot) (q,b) events)`,
    `name`, `p`, `q`,
    `MAP (\slot. FOLDL (\slot ev. current_event_pair_action sm h ev slot) slot events) slots`] >>
  simp[current_event_fold_slots] >> rpt conj_tac
  >- (simp[MEM_MAP] >> qexists_tac `(p,a)` >> simp[] >>
      GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM PAIR] >> simp[])
  >- (simp[MEM_MAP] >> qexists_tac `(q,b)` >> simp[] >>
      GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM PAIR] >> simp[])
  >> metis_tac[current_owner_name_separate]
QED

Theorem current_phi_slots_pairs[simp]:
  !slots. phi_pairs (current_phi_slots slots) = slots
Proof
  Induct >> simp[current_phi_slots_def, phi_pairs_def] >> gen_tac >> PairCases_on `h` >>
  fs[current_phi_slots_def, phi_pairs_def]
QED

Theorem current_provenance_tree_ownership:
  LENGTH olds = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,bbs)) annsss /\
  ALL_DISTINCT (MAP FST (FLAT (FLAT annsss))) /\
  ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) /\ ssa_vars_covered s (MAP FST defs) /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  current_tree_trace (current_annotation_map bbs annsss) sm tree
    s (init_current_rename_state defs) bbs [] CurrentDefault []
    ctrs' s' bbs' H' visited' events ==>
  current_history_valid (FLAT (MAP block_ir_vars bbs)) H' /\
  (!ev v. MEM ev events /\ MEM v (FLAT (MAP block_ir_vars bbs)) ==>
    current_owner_name H' v (latest_current_name (current_event_exit_rs ev) v))
Proof
  strip_tac >>
  `LENGTH bbs = LENGTH annsss` by (drule LIST_REL_LENGTH >> simp[]) >>
  drule_all current_provenance_tree_annotations_ok >> strip_tac >>
  `current_allocation_consistent (FLAT (MAP block_ir_vars bbs))
      ([] : (current_token # string # string) list) s (init_current_rename_state defs) /\
    current_env_realizes ([] : (current_token # string # string) list)
      CurrentDefault (init_current_rename_state defs) (FLAT (MAP block_ir_vars bbs))` by
    (irule current_initial_state_valid >> simp[]) >>
  conj_tac >- metis_tac[current_annotated_tree_history_valid, current_env_history_owners_default] >>
  metis_tac[current_annotated_tree_owner_names, current_env_history_owners_default]
QED

Theorem current_history_owner_covered:
  current_history_valid V H /\ MEM (t,v,n) H ==> MEM v V
Proof
  simp[current_history_valid_def, EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED

Theorem current_initial_slots_vars_covered:
  lookup_block h bbs = SOME bb /\ k < LENGTH bb.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode = PHI /\
  (EL k bb.bb_instructions).inst_operands = current_phi_slots slots ==>
  !p v. MEM (p,v) slots ==> MEM v (FLAT (MAP block_ir_vars bbs))
Proof
  rpt strip_tac >> qpat_x_assum `MEM (p,v) slots`
    (strip_assume_tac o REWRITE_RULE[MEM_EL]) >>
  metis_tac[current_initial_slot_var_covered]
QED

Theorem current_owner_phi_retained_apply:
  inst.inst_operands = FOLDL (\ops ev. current_event_operand_action sm h ev ops)
    (current_phi_slots slots) events ==>
  inst.inst_outputs = [name] ==>
  current_history_valid V H ==>
  MEM out V /\ current_owner_name H out name /\
  (!p v. MEM (p,v) slots ==> MEM v V) /\
  (!ev v. MEM ev events /\ MEM v V ==>
    current_owner_name H v (latest_current_name (current_event_exit_rs ev) v)) /\
  ALL_DISTINCT (MAP current_event_label events) /\
  MEM (p,a) slots /\ MEM (q,b) slots /\ a <> b /\ a <> out /\ b <> out /\
  inst.inst_opcode = PHI ==>
  simplify_current_phi inst = inst
Proof
  metis_tac[current_owner_phi_retained]
QED

Theorem current_provenance_tree_original_phi_retained:
  LENGTH olds = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,bbs)) annsss /\
  ALL_DISTINCT (MAP FST (FLAT (FLAT annsss))) /\
  ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) /\ ssa_vars_covered s (MAP FST defs) /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  (!l. MEM l (dom_tree_labels tree) ==> IS_SOME (lookup_block l bbs)) /\
  (!p ss. ALOOKUP sm p = SOME ss ==> ALL_DISTINCT ss) /\
  current_tree_trace (current_annotation_map bbs annsss) sm tree
    s (init_current_rename_state defs) bbs [] CurrentDefault []
    ctrs' s' bbs' H' visited' events /\
  events = before ++ (h,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)::after /\
  lookup_block h olds = SOME old /\ k < LENGTH old.bb_instructions /\
  MEM (EL k old.bb_instructions) (fn_insts fn) /\ fn_phis_non_degenerate fn /\
  (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_outputs = [out] /\
  (EL k old.bb_instructions).inst_operands = current_phi_slots slots ==>
  ?pre inserted final.
    lookup_block h bbs = SOME inserted /\
    inserted = old with bb_instructions := pre ++ old.bb_instructions /\
    lookup_block h bbs' = SOME final /\
    LENGTH pre+k < LENGTH final.bb_instructions /\
    simplify_current_phi (EL (LENGTH pre+k) final.bb_instructions) =
      EL (LENGTH pre+k) final.bb_instructions
Proof
  strip_tac >>
  drule_all current_provenance_tree_original_phi_output >> strip_tac >>
  `0 < LENGTH (EL k old.bb_instructions).inst_outputs` by simp[] >>
  drule_all current_tree_original_output_owner >> strip_tac >>
  `pre' = pre` by
    (gvs[basic_block_component_equality] >> metis_tac[APPEND_11]) >>
  gvs[] >>
  `current_owner_name H' out name` by
    (simp[current_owner_name_def] >> metis_tac[]) >>
  drule_all current_provenance_tree_ownership >> strip_tac >>
  `MEM out (FLAT (MAP block_ir_vars bbs))` by
    metis_tac[current_history_owner_covered] >>
  `ALL_DISTINCT (MAP current_event_label
      (before ++ (h,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)::after))` by
    (irule current_tree_trace_event_labels_distinct >> metis_tac[]) >>
  `LENGTH pre+k < LENGTH (old with bb_instructions := pre ++ old.bb_instructions).bb_instructions /\
    (EL (LENGTH pre+k) (old with bb_instructions := pre ++ old.bb_instructions).bb_instructions).inst_opcode = PHI` by
    simp[EL_APPEND_EQN] >>
  drule_all current_tree_trace_phi_lookup >> strip_tac >>
  drule_all current_phi_view_fold_instruction >> strip_tac >>
  `!p v. MEM (p,v) slots ==> MEM v (FLAT (MAP block_ir_vars bbs))` by
    (match_mp_tac (GEN_ALL current_initial_slots_vars_covered) >>
     qexistsl_tac [`LENGTH pre+k`, `h`,
       `old with bb_instructions := pre ++ old.bb_instructions`] >>
     simp[EL_APPEND_EQN]) >>
  `?p a q b. MEM (p,a) slots /\ MEM (q,b) slots /\
    a <> out /\ b <> out /\ a <> b` by
    (fs[fn_phis_non_degenerate_def] >>
     first_x_assum drule >> simp[current_phi_slots_pairs]) >>
  gvs[EL_APPEND_EQN, ADD_COMM] >>
  qexists_tac `pre` >> simp[] >>
  qpat_x_assum `_.inst_operands = FOLDL _ _ _`
    (assume_tac o PURE_REWRITE_RULE[GSYM APPEND_ASSOC, APPEND]) >>
  drule current_owner_phi_retained_apply >>
  disch_then drule >> disch_then drule >>
  disch_then irule >> simp[] >> metis_tac[]
QED
