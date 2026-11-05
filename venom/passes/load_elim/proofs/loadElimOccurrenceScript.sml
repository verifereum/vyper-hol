Theory loadElimOccurrence
Ancestors
  loadElimExecutionAvailability loadElimOperationalHistory o1PassLift
  contextCodegenRel venomExecProps venomExecProofs venomWf venomInst list

Datatype:
  le_occurrence =
    StepOcc basic_block num num venom_state venom_state
  | PhiOcc basic_block venom_state venom_state
End

Definition le_occ_pre_def:
  le_occ_pre (StepOcc bb n k s t) = s /\
  le_occ_pre (PhiOcc bb s t) = s
End

Definition le_occ_post_def:
  le_occ_post (StepOcc bb n k s t) = t /\
  le_occ_post (PhiOcc bb s t) = t
End

Definition le_occ_writes_def:
  le_occ_writes (StepOcc bb n k s t) = set (EL n bb.bb_instructions).inst_outputs /\
  le_occ_writes (PhiOcc bb s t) = le_phi_outputs bb.bb_instructions
End

Definition le_occ_valid_def:
  (le_occ_valid C fn (StepOcc bb n k s t) <=>
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    n = s.vs_inst_idx /\ n < LENGTH bb.bb_instructions /\
    step_inst k C (EL n bb.bb_instructions) s = OK t) /\
  (le_occ_valid C fn (PhiOcc bb s t) <=>
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK t)
End

(* The state at the next call site, including the semantic index update. *)
Definition le_occ_after_def:
  le_occ_after (StepOcc bb n k s t) =
    (if is_terminator (EL n bb.bb_instructions).inst_opcode then t
     else t with vs_inst_idx := SUC n) /\
  le_occ_after (PhiOcc bb s t) =
    t with vs_inst_idx := phi_prefix_length bb.bb_instructions
End

Inductive le_occ_prefix:
[~start:]
  (!C fn s0 bb p i.
    lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s0 bb.bb_instructions = OK p /\
    active_inst fn i (p with vs_inst_idx := phi_prefix_length bb.bb_instructions) ==>
    le_occ_prefix C fn s0 [PhiOcc bb s0 p] i
      (p with vs_inst_idx := phi_prefix_length bb.bb_instructions))
[~next:]
  (!C fn s0 es i s bb k u j.
    le_occ_prefix C fn s0 es i s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL s.vs_inst_idx bb.bb_instructions = i /\
    ~is_terminator i.inst_opcode /\ step_inst k C i s = OK u /\
    active_inst fn j (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
    le_occ_prefix C fn s0 (es ++ [StepOcc bb s.vs_inst_idx k s u]) j
      (u with vs_inst_idx := SUC s.vs_inst_idx))
[~block:]
  (!C fn s0 es i s bb k u next p j.
    le_occ_prefix C fn s0 es i s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL s.vs_inst_idx bb.bb_instructions = i /\
    is_terminator i.inst_opcode /\ step_inst k C i s = OK u /\ ~u.vs_halted /\
    lookup_block u.vs_current_bb fn.fn_blocks = SOME next /\
    eval_phis u next.bb_instructions = OK p /\
    active_inst fn j (p with vs_inst_idx := phi_prefix_length next.bb_instructions) ==>
    le_occ_prefix C fn s0
      (es ++ [StepOcc bb s.vs_inst_idx k s u; PhiOcc next u p]) j
      (p with vs_inst_idx := phi_prefix_length next.bb_instructions))
End

Theorem le_occ_prefix_forget:
  !C fn s0 es i s. le_occ_prefix C fn s0 es i s ==>
    frame_reach C fn s0 i s
Proof
  ho_match_mp_tac le_occ_prefix_ind >> rpt strip_tac
  >- (irule (cj 1 frame_reach_rules) >>
      simp[enters_block_def] >> metis_tac[])
  >- (irule (cj 2 frame_reach_rules) >> metis_tac[]) >>
  irule (cj 3 frame_reach_rules) >>
  simp[enters_block_def] >> metis_tac[]
QED

Theorem le_active_inst_lookup:
  wf_function fn /\ active_inst fn i s ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL s.vs_inst_idx bb.bb_instructions = i
Proof
  rw[active_inst_def] >> qexists_tac `bb` >> simp[] >>
  irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]
QED

Theorem le_occ_prefix_annotate:
  !C fn s0 i s. frame_reach C fn s0 i s ==>
    wf_function fn ==> ?es. le_occ_prefix C fn s0 es i s
Proof
  ho_match_mp_tac frame_reach_strongind >> rpt conj_tac
  >- (rw[enters_block_def] >> metis_tac[cj 1 le_occ_prefix_rules])
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac >>
      drule frame_reach_active >> strip_tac >>
      drule_all le_active_inst_lookup >> strip_tac >>
      metis_tac[cj 2 le_occ_prefix_rules]) >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  drule frame_reach_active >> strip_tac >>
  drule_all le_active_inst_lookup >> strip_tac >>
  gvs[enters_block_def] >>
  metis_tac[cj 3 le_occ_prefix_rules]
QED

Definition le_occ_chain_def:
  (le_occ_chain s [] t <=> s = t) /\
  (le_occ_chain s (e::es) t <=>
    le_occ_pre e = s /\ le_occ_chain (le_occ_after e) es t)
End

Theorem le_occ_chain_append:
  !es s t fs. le_occ_chain s (es ++ fs) t <=>
    ?u. le_occ_chain s es u /\ le_occ_chain u fs t
Proof
  Induct >> simp[le_occ_chain_def] >> metis_tac[]
QED

Theorem le_occ_prefix_valid:
  !C fn s0 es i s. le_occ_prefix C fn s0 es i s ==>
    EVERY (le_occ_valid C fn) es
Proof
  ho_match_mp_tac le_occ_prefix_ind >>
  simp[le_occ_valid_def] >> metis_tac[]
QED

Theorem le_occ_prefix_chain:
  !C fn s0 es i s. le_occ_prefix C fn s0 es i s ==>
    le_occ_chain s0 es s
Proof
  ho_match_mp_tac le_occ_prefix_ind >>
  simp[le_occ_chain_append, le_occ_chain_def, le_occ_pre_def, le_occ_after_def]
QED

Definition le_occ_events_def:
  le_occ_events e =
    [(le_occ_writes e, le_occ_post e); ({}, le_occ_after e)]
End

Definition le_occ_history_def:
  le_occ_history es = FLAT (MAP le_occ_events es)
End

Theorem le_occ_history_append:
  le_occ_history (es ++ fs) = le_occ_history es ++ le_occ_history fs
Proof
  simp[le_occ_history_def, MAP_APPEND, FLAT_APPEND]
QED

Theorem le_occ_events_end:
  le_history_end s (le_occ_events e) = le_occ_after e
Proof
  simp[le_occ_events_def, loadElimHistoryHelpersTheory.le_history_end_def]
QED

Theorem le_occ_events_oper:
  le_occ_valid C fn e ==>
    le_oper_history (le_occ_pre e) (le_occ_events e)
Proof
  Cases_on `e` >>
  simp[le_occ_valid_def, le_occ_events_def, le_occ_pre_def,
       le_occ_writes_def, le_occ_post_def, le_occ_after_def,
       le_oper_history_def] >> strip_tac
  >- (conj_tac >- metis_tac[le_oper_step_event] >>
      irule le_oper_neutral_event >> rpt gen_tac >>
      IF_CASES_TAC >> simp[venomStateTheory.lookup_var_def]) >>
  conj_tac >- metis_tac[le_oper_phi_event] >>
  simp[le_oper_index_event]
QED

Theorem le_occ_chain_history:
  !es s t. le_occ_chain s es t /\ EVERY (le_occ_valid C fn) es ==>
    le_oper_history s (le_occ_history es) /\
    le_history_end s (le_occ_history es) = t
Proof
  Induct >> simp[le_occ_chain_def, le_occ_history_def, le_oper_history_def,
                loadElimHistoryHelpersTheory.le_history_end_def]
  >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule le_occ_events_oper >>
  simp[GSYM le_occ_history_def, le_oper_history_append,
       loadElimHistoryHelpersTheory.le_history_end_append, le_occ_events_end]
QED

Theorem le_occ_prefix_history:
  le_occ_prefix C fn s0 es i s ==>
  le_oper_history s0 (le_occ_history es) /\
  le_history_end s0 (le_occ_history es) = s
Proof
  strip_tac >> irule le_occ_chain_history >>
  metis_tac[le_occ_prefix_valid, le_occ_prefix_chain]
QED

Theorem le_occ_history_no_writes:
  !es. EVERY (\e. v NOTIN le_occ_writes e) es ==>
    le_epoch (le_occ_history es) v = 0
Proof
  simp[loadElimHistoryHelpersTheory.le_epoch_zero,
       le_occ_history_def, EVERY_FLAT, EVERY_MAP, le_occ_events_def]
QED

Theorem le_occ_chain_lookup:
  le_occ_chain s es t /\ EVERY (le_occ_valid C fn) es /\
  EVERY (\e. v NOTIN le_occ_writes e) es ==>
  lookup_var v t = lookup_var v s
Proof
  strip_tac >> drule_all le_occ_chain_history >> strip_tac >>
  drule le_oper_history_frame >> strip_tac >>
  drule_all le_occ_history_no_writes >> strip_tac >>
  drule_all loadElimHistoryHelpersTheory.le_history_lookup_persistence >> simp[]
QED

Theorem le_occ_after_lookup:
  lookup_var v (le_occ_after e) = lookup_var v (le_occ_post e)
Proof
  Cases_on `e` >>
  simp[le_occ_after_def, le_occ_post_def, venomStateTheory.lookup_var_def,
       COND_RAND]
QED

Theorem le_occ_prefix_suffix_lookup:
  le_occ_prefix C fn s0 (pre ++ e::suffix) i s /\
  EVERY (\q. v NOTIN le_occ_writes q) suffix ==>
  lookup_var v s = lookup_var v (le_occ_post e)
Proof
  strip_tac >> drule le_occ_prefix_chain >>
  simp[le_occ_chain_append, le_occ_chain_def] >> strip_tac >>
  drule le_occ_prefix_valid >> simp[] >> strip_tac >>
  drule_all le_occ_chain_lookup >> simp[le_occ_after_lookup]
QED

Theorem le_occ_prefix_member:
  le_occ_prefix C fn s0 es i s /\ MEM e es ==> le_occ_valid C fn e
Proof
  metis_tac[le_occ_prefix_valid, EVERY_MEM]
QED

Theorem le_occ_prefix_active:
  le_occ_prefix C fn s0 es i s ==> active_inst fn i s
Proof
  metis_tac[le_occ_prefix_forget, frame_reach_active]
QED
