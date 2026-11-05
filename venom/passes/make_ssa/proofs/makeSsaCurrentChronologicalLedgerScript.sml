Theory makeSsaCurrentChronologicalLedger
Ancestors makeSsaCurrentExecutionHistory makeSsaCurrentSemanticHistory
  venomExecSemantics venomState finite_map list rich_list pair

Inductive current_chronological:
  (!loc st. current_chronological fn ctx (loc,st) [] (loc,st)) /\
  (!start log loc before phases next after writes.
    current_chronological fn ctx start log (loc,before) /\
    current_execution_edge fn ctx loc before phases (SOME next) (OK after) after /\
    current_semantic_history 0 ctx phases before writes (OK after) after ==>
    current_chronological fn ctx start (log ++ [(phases,writes)]) (next,after))
End

Definition current_ledger_writes_def:
  current_ledger_writes log = FLAT (MAP SND log)
End

Definition current_ledger_phases_def:
  current_ledger_phases log = FLAT (MAP FST log)
End

Definition current_ledger_last_def:
  current_ledger_last log v n x <=>
    n < LENGTH (current_ledger_writes log) /\
    EL n (current_ledger_writes log) = (v,x) /\
    !j. n < j /\ j < LENGTH (current_ledger_writes log) ==>
      FST (EL j (current_ledger_writes log)) <> v
End

Theorem current_chronological_empty:
  current_chronological fn ctx (loc,st) [] (loc,st)
Proof
  simp[current_chronological_rules]
QED

Theorem current_chronological_extend:
  current_chronological fn ctx start log (loc,before) /\
  current_execution_edge fn ctx loc before phases (SOME next) (OK after) after ==>
  ?writes. current_chronological fn ctx start (log ++ [(phases,writes)]) (next,after)
Proof
  strip_tac >> drule current_execution_edge_history >>
  disch_then (qspec_then `0` strip_assume_tac) >>
  fs[current_history_result_def] >>
  qexists `writes` >> irule (cj 2 current_chronological_rules) >> metis_tac[]
QED

Theorem current_chronological_prefix:
  !start log finish. current_chronological fn ctx start log finish ==>
  current_actual_prefix fn ctx (FST start) (SND start) (current_ledger_phases log)
    (SOME (FST finish)) (OK (SND finish)) (SND finish)
Proof
  ho_match_mp_tac current_chronological_ind >>
  simp[current_ledger_phases_def, MAP_APPEND, FLAT_APPEND] >> rpt strip_tac
  >- simp[current_actual_prefix_rules] >>
  irule current_actual_prefix_append >>
  goal_assum $ drule_at Any >> simp[] >>
  metis_tac[current_actual_prefix_rules]
QED

Theorem current_chronological_store:
  !start log finish. current_chronological fn ctx start log finish ==>
  (SND finish).vs_vars = FOLDL (\m dv. m |+ dv) (SND start).vs_vars
    (current_ledger_writes log)
Proof
  ho_match_mp_tac current_chronological_ind >>
  simp[current_ledger_writes_def, MAP_APPEND, FLAT_APPEND, FOLDL_APPEND] >>
  rpt strip_tac >> drule current_semantic_history_fold >> simp[]
QED

Theorem current_fold_updates_absent[local]:
  !writes m. ~MEM v (MAP FST writes) ==>
    FLOOKUP (FOLDL (\m dv. m |+ dv) m writes) v = FLOOKUP m v
Proof
  Induct >> simp[] >> Cases_on `h` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[FLOOKUP_UPDATE]
QED

Theorem current_fold_updates_last[local]:
  !writes n m. n < LENGTH writes /\ EL n writes = (v,x) /\
    (!j. n < j /\ j < LENGTH writes ==> FST (EL j writes) <> v) ==>
    FLOOKUP (FOLDL (\m dv. m |+ dv) m writes) v = SOME x
Proof
  Induct >- simp[] >> Cases_on `n` >> simp[] >> rpt strip_tac
  >- (`~MEM v (MAP FST writes)` by
        (simp[MEM_MAP, MEM_EL] >> rpt strip_tac >>
         first_x_assum (qspec_then `SUC n` mp_tac) >> simp[] >> metis_tac[]) >>
      drule current_fold_updates_absent >>
      disch_then (qspec_then `m |+ (v,x)` mp_tac) >> simp[FLOOKUP_UPDATE]) >>
  first_x_assum irule >> qexists `n'` >> simp[] >> gen_tac >> strip_tac >>
  first_x_assum (qspec_then `SUC j` mp_tac) >> simp[]
QED

Theorem current_chronological_last_lookup:
  current_chronological fn ctx (loc0,initial) log (loc,st) /\
  current_ledger_last log v n x ==> FLOOKUP st.vs_vars v = SOME x
Proof
  strip_tac >> drule current_chronological_store >> simp[] >>
  disch_then SUBST1_TAC >> irule current_fold_updates_last >>
  fs[current_ledger_last_def] >> metis_tac[]
QED

Theorem current_chronological_unwritten_lookup:
  current_chronological fn ctx (loc0,initial) log (loc,st) /\
  ~MEM v (MAP FST (current_ledger_writes log)) ==>
  FLOOKUP st.vs_vars v = FLOOKUP initial.vs_vars v
Proof
  strip_tac >> drule current_chronological_store >> simp[] >>
  disch_then SUBST1_TAC >> irule current_fold_updates_absent >> simp[]
QED

Theorem current_chronological_enter:
  current_chronological fn ctx start log (CurrentEntry (SUC fuel),before) /\
  lookup_block before.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis before bb.bb_instructions = OK post ==>
  ?writes. current_chronological fn ctx start
    (log ++ [([CurrentBatch before.vs_current_bb
       (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions);
       CurrentControl],writes)])
    (CurrentBody fuel bb, post with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  strip_tac >> irule current_chronological_extend >>
  goal_assum $ drule_at Any >> simp[] >>
  irule (cj 1 current_execution_edge_rules) >> simp[]
QED

Theorem current_chronological_ordinary:
  current_chronological fn ctx start log (CurrentBody fuel bb,before) /\
  lookup_block before.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb before.vs_inst_idx = SOME inst /\ inst_wf inst /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx inst before = OK post /\ ~is_terminator inst.inst_opcode ==>
  ?writes. current_chronological fn ctx start
    (log ++ [([CurrentOrdinary before.vs_current_bb before.vs_inst_idx inst;
       CurrentControl],writes)])
    (CurrentBody fuel bb, post with vs_inst_idx := SUC before.vs_inst_idx)
Proof
  strip_tac >> irule current_chronological_extend >>
  goal_assum $ drule_at Any >> simp[] >>
  irule (cj 2 current_execution_edge_rules) >> simp[]
QED
