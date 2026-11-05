Theory makeSsaCurrentRuntimeTransport
Ancestors makeSsaCurrentJointRuntime makeSsaCurrentSemanticHistory
  venomState finite_map alist list pair

(* A demanded origin must be explicitly defined; joint equality alone also
   permits both origin maps to be absent. *)
Theorem current_joint_defined_seed:
  current_joint_rel Val Ms Mt rs D st st' /\ MEM v D /\
  ALOOKUP Ms v = SOME origin /\ Val origin = SOME value ==>
  ALOOKUP Mt (latest_current_name rs v) = SOME origin /\
  lookup_var v st = SOME value /\
  lookup_var (latest_current_name rs v) st' = SOME value
Proof
  pure_rewrite_tac[current_joint_rel_def] >> strip_tac >>
  `ALOOKUP Mt (latest_current_name rs v) = SOME origin` by metis_tac[] >>
  simp[] >> conj_tac >> irule current_origin_snapshot_read >> metis_tac[]
QED

Theorem current_value_writes_no_write:
  !writes m. EVERY (\dv. FST dv <> selected) writes ==>
    FLOOKUP (FOLDL (\m dv. m |+ dv) m writes) selected = FLOOKUP m selected
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
  simp[FLOOKUP_UPDATE]
QED

Theorem current_semantic_history_no_write:
  current_semantic_history fuel ctx phases before writes result after /\
  EVERY (\dv. FST dv <> selected) writes ==>
  lookup_var selected after = lookup_var selected before
Proof
  strip_tac >> drule current_semantic_history_fold >> strip_tac >>
  simp[lookup_var_def] >> irule current_value_writes_no_write >> simp[]
QED

Theorem current_semantic_history_write_outputs:
  !phases before writes result after.
  current_semantic_history fuel ctx phases before writes result after ==>
  EVERY (\dv. ?phase. MEM phase phases /\
    MEM (FST dv) (current_phase_outputs phase)) writes
Proof
  ho_match_mp_tac current_semantic_history_ind >> rpt strip_tac >>
  simp[] >> drule current_semantic_phase_outputs >>
  gvs[EVERY_APPEND, EVERY_MEM] >> metis_tac[]
QED

Theorem current_semantic_history_output_exclusion:
  current_semantic_history fuel ctx phases before writes result after /\
  (!phase. MEM phase phases ==> ~MEM selected (current_phase_outputs phase)) ==>
  EVERY (\dv. FST dv <> selected) writes
Proof
  strip_tac >> drule current_semantic_history_write_outputs >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem current_semantic_history_output_no_write:
  current_semantic_history fuel ctx phases before writes result after /\
  (!phase. MEM phase phases ==> ~MEM selected (current_phase_outputs phase)) ==>
  lookup_var selected after = lookup_var selected before
Proof
  strip_tac >> irule current_semantic_history_no_write >>
  drule_all current_semantic_history_output_exclusion >> metis_tac[]
QED
