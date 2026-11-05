Theory makeSsaCurrentRuntimeTransport
Ancestors makeSsaCurrentJointRuntime makeSsaCurrentSemanticHistory
  makeSsaCurrentTemporalWrites
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

(* Fresh origins are chosen beyond a finite first-coordinate bound. *)
Theorem current_origin_finite_bound[local]:
  !origins : (num # string # num # num) list.
  ?bound. !origin. MEM origin origins ==> FST origin < bound
Proof
  Induct >- (qexists_tac `0` >> simp[]) >>
  pop_assum strip_assume_tac >> gen_tac >>
  qexists_tac `bound + FST h + 1` >> simp[] >> rpt strip_tac >>
  gvs[] >> res_tac >> decide_tac
QED

Theorem current_origin_fresh:
  !origins : (num # string # num # num) list.
  ?origin. ~MEM origin origins
Proof
  gen_tac >> qspec_then `origins` strip_assume_tac current_origin_finite_bound >>
  qexists_tac `(bound,"",0,0)` >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem current_fresh_write_decoration:
  !writes : (string # bytes32) list.
  !protected : (num # string # num # num) list. !Val.
  ?originWrites Val'.
    ALL_DISTINCT (MAP SND originWrites) /\
    EVERY (\origin. ~MEM origin protected) (MAP SND originWrites) /\
    LIST_REL (\dv no. FST dv = FST no /\ Val' (SND no) = SOME (SND dv))
      writes originWrites /\
    (!origin. MEM origin protected ==> Val' origin = Val origin)
Proof
  Induct >- (rpt gen_tac >> qexistsl_tac [`[]`, `Val`] >> simp[]) >>
  rpt gen_tac >> PairCases_on `h` >>
  qspec_then `protected` (qx_choose_then `fresh` assume_tac) current_origin_fresh >>
  first_x_assum (qspecl_then [`fresh::protected`, `(fresh =+ SOME h1) Val`]
    strip_assume_tac) >>
  qexistsl_tac [`(h0,fresh)::originWrites`, `Val'`] >>
  gvs[EVERY_MEM, combinTheory.APPLY_UPDATE_THM] >>
  metis_tac[]
QED

Theorem current_write_decoration_names:
  !writes originWrites.
  LIST_REL (\dv no. FST dv = FST no /\ Val (SND no) = SOME (SND dv))
    writes originWrites ==>
  MAP FST originWrites = MAP FST writes
Proof
  Induct >> Cases_on `originWrites` >> simp[] >> rpt strip_tac >> simp[]
QED

Theorem current_write_decoration_realizes:
  !writes originWrites Mt before after.
  LIST_REL (\dv no. FST dv = FST no /\ Val (SND no) = SOME (SND dv))
    writes originWrites /\
  current_origin_realizes Val Mt before /\
  after.vs_vars = FOLDL (\m dv. m |+ dv) before.vs_vars writes ==>
  current_origin_realizes Val (current_chronological_writes originWrites Mt) after
Proof
  Induct >> Cases_on `originWrites` >>
  simp[current_chronological_writes_def] >> rpt gen_tac >> strip_tac
  >- gvs[current_origin_realizes_def, lookup_var_def] >>
  Cases_on `h` >> Cases_on `h'` >> gvs[] >>
  rename1 `Val origin = SOME value` >>
  rename1 `after.vs_vars = FOLDL _ (before.vs_vars |+ (dst,value)) writes` >>
  first_x_assum irule >> simp[] >>
  qexists_tac `update_var dst value before` >>
  `current_origin_realizes Val ((dst,origin)::Mt) (update_var dst value before)` by
    (irule current_origin_realizes_write >> simp[]) >>
  simp[update_var_def]
QED

Theorem current_compatible_origin_realizes:
  current_origin_realizes Val M st /\
  (!origin. MEM origin (MAP SND M) ==> Val' origin = Val origin) ==>
  current_origin_realizes Val' M st
Proof
  strip_tac >> irule current_origin_realizes_extensional >>
  qexists_tac `Val` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >>
  drule ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[pairTheory.SND]
QED

Theorem current_write_decoration_selected:
  LIST_REL (\dv no. FST dv = FST no /\ Val (SND no) = SOME (SND dv))
    writes originWrites /\ EVERY (\dv. FST dv <> selected) writes ==>
  ALOOKUP (current_chronological_writes originWrites Mt) selected = ALOOKUP Mt selected
Proof
  strip_tac >> irule current_chronological_no_write >>
  drule current_write_decoration_names >> disch_tac >>
  `EVERY (\n. n <> selected) (MAP FST originWrites)` suffices_by
    simp[EVERY_MAP] >>
  asm_rewrite_tac[] >> simp[EVERY_MAP]
QED

Theorem current_fresh_decoration_total_realization:
  current_origin_realizes Val Ms source /\
  current_origin_realizes Val Mt before /\
  after.vs_vars = FOLDL (\m dv. m |+ dv) before.vs_vars writes ==>
  ?originWrites Val'.
    MAP FST originWrites = MAP FST writes /\
    ALL_DISTINCT (MAP SND originWrites) /\
    EVERY (\origin. ~MEM origin (MAP SND Ms ++ MAP SND Mt ++ protected))
      (MAP SND originWrites) /\
    LIST_REL (\dv no. FST dv = FST no /\ Val' (SND no) = SOME (SND dv))
      writes originWrites /\
    (!origin. MEM origin (MAP SND Ms ++ MAP SND Mt ++ protected) ==>
      Val' origin = Val origin) /\
    current_origin_realizes Val' Ms source /\
    current_origin_realizes Val' (current_chronological_writes originWrites Mt) after /\
    (!selected. EVERY (\dv. FST dv <> selected) writes ==>
      ALOOKUP (current_chronological_writes originWrites Mt) selected = ALOOKUP Mt selected)
Proof
  strip_tac >>
  qspecl_then [`writes`, `MAP SND Ms ++ MAP SND Mt ++ protected`, `Val`]
    strip_assume_tac current_fresh_write_decoration >>
  qexistsl_tac [`originWrites`, `Val'`] >> simp[] >>
  conj_tac >- (irule current_write_decoration_names >> metis_tac[]) >>
  conj_tac >- (irule current_compatible_origin_realizes >>
    qexists_tac `Val` >> simp[]) >>
  conj_tac >- (irule current_write_decoration_realizes >> simp[] >>
    qexists_tac `before` >> simp[] >> qexists_tac `writes` >> simp[] >>
    irule current_compatible_origin_realizes >> qexists_tac `Val` >> simp[]) >>
  rpt strip_tac >> drule_all current_write_decoration_selected >> simp[]
QED
