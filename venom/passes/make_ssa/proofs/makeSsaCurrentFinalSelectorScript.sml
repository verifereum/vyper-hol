Theory makeSsaCurrentFinalSelector
Ancestors makeSsaCurrentLastEvent makeSsaCurrentRenameTrace
  makeSsaCurrentActualRetention makeSsaCurrentAllocation makeSsaCurrentDefs
  makeSsaCurrentProps irSupply list alist

(* Allocation coverage and name realization alone do not imply ownership
   of the incoming selected name. This is a boundary-interface probe only. *)
Definition current_selector_probe_supply_def:
  current_selector_probe_supply = <| irs_next_inst := 0; irs_next_var := 0;
    irs_next_label := 0; irs_used_inst_ids := []; irs_used_vars := ["x";"y"];
    irs_used_labels := [] |>
End

Theorem current_selector_missing_owner_probe:
  current_outputs_trace [(CurrentOriginal "E" 0 0,"y")]
    current_selector_probe_supply ([],[("x",["y"])]) [] (\v. CurrentDefault "y")
    ["y"] current_selector_probe_supply
    ([("y",1)],[("y",["y"]);("x",["y"])])
    [(CurrentOriginal "E" 0 0,"y","y")]
    (("y" =+ CurrentOriginal "E" 0 0) (\v. CurrentDefault "y")) /\
  current_annotations_ok ["x";"y"] [] [(CurrentOriginal "E" 0 0,"y")] /\
  current_allocation_consistent ["x";"y"] [] current_selector_probe_supply
    ([],[("x",["y"])]) /\
  current_env_realizes [] (\v. CurrentDefault "y") ([],[("x",["y"])]) ["x";"y"] /\
  current_last_event_hit ["y"] [(0,3n)] "x" = NONE /\
  current_last_event_hit ["y"] [(0,3n)]
    (latest_current_name ([("y",1)],[("y",["y"]);("x",["y"])]) "x") = SOME 0
Proof
  EVAL_TAC >> simp[] >> rpt strip_tac >> gvs[]
QED

Theorem current_outputs_trace_absent_latest:
  !anns s rs H E names s' rt H' E'.
  current_outputs_trace anns s rs H E names s' rt H' E' /\
  ~MEM v (MAP SND anns) ==>
  latest_current_name rt v = latest_current_name rs v
Proof
  Induct >> simp[current_outputs_trace_def] >> gen_tac >> PairCases_on `h` >>
  simp[current_outputs_trace_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule current_push_latest >> simp[]
QED

Definition current_last_name_hit_def:
  (current_last_name_hit [] v = NONE : num option) /\
  (current_last_name_hit (h::xs) v =
    case current_last_name_hit xs v of
      SOME j => SOME (SUC j)
    | NONE => if h = v then SOME 0 else NONE)
End

Theorem current_last_name_hit_none:
  !xs. current_last_name_hit xs v = NONE <=> ~MEM v xs
Proof
  Induct >> simp[current_last_name_hit_def] >>
  Cases_on `current_last_name_hit xs v` >> gvs[] >> metis_tac[]
QED

Theorem current_last_name_hit_cons:
  ~MEM v xs ==> current_last_name_hit (h::xs) v = if h = v then SOME 0 else NONE
Proof
  simp[GSYM current_last_name_hit_none, current_last_name_hit_def]
QED

Theorem current_trace_absent_name:
  current_outputs_trace anns s rs H E names s' rt H' E' /\
  current_annotations_ok V H anns /\
  current_allocation_consistent V H s rs /\ current_env_realizes H E rs V /\
  current_env_history_owners H E /\ MEM v V /\ ~MEM v (MAP SND anns) ==>
  ~MEM (latest_current_name rt v) names
Proof
  strip_tac >>
  `current_allocation_consistent V H' s' rt /\ current_env_realizes H' E' rt V` by
    (irule current_outputs_trace_preserves >> metis_tac[]) >>
  `current_env_history_owners H' E'` by
    metis_tac[current_outputs_trace_history_owners] >>
  `current_owner_name H' v (latest_current_name rt v)` by
    (irule current_env_history_owner_name >>
     gvs[current_allocation_consistent_def, current_env_realizes_def] >> metis_tac[]) >>
  drule current_outputs_trace_owned_names >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  strip_tac >>
  qpat_x_assum `MEM _ names` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  qpat_x_assum `!n. n < LENGTH anns ==> _` (qspec_then `n` mp_tac) >>
  simp[] >> Cases_on `EL n anns` >> simp[] >> strip_tac >>
  `MEM (q,r) anns` by metis_tac[EL_MEM] >>
  `MEM r V` by
    (fs[current_annotations_ok_def, EVERY_MEM] >>
     first_x_assum (qspec_then `(q,r)` mp_tac) >> simp[]) >>
  `r <> v` by (strip_tac >> fs[MEM_MAP] >> metis_tac[pairTheory.SND]) >>
  metis_tac[current_owner_name_separate, current_owner_name_def,
    current_allocation_consistent_def]
QED

Theorem current_outputs_trace_last_name_hit:
  !anns s rs H E names s' rt H' E' V v.
  current_outputs_trace anns s rs H E names s' rt H' E' /\
  current_annotations_ok V H anns /\
  current_allocation_consistent V H s rs /\ current_env_realizes H E rs V /\
  current_env_history_owners H E /\ MEM v V ==>
  current_last_name_hit (MAP SND anns) v =
    current_last_name_hit names (latest_current_name rt v)
Proof
  Induct >- simp[current_outputs_trace_def, current_last_name_hit_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  gvs[current_outputs_trace_def] >>
  `current_outputs_trace ((h0,h1)::anns) s rs H E (n::ns) s' rt H' E'` by
    (simp[current_outputs_trace_def] >> metis_tac[]) >>
  `current_annotations_ok V (H ++ [(h0,h1,n)]) anns` by
    metis_tac[current_annotations_tail] >>
  `(!w. h0 <> CurrentDefault w) /\ ~MEM h0 (MAP FST H) /\ MEM h1 V` by
    fs[current_annotations_ok_def] >>
  `current_allocation_consistent V (H ++ [(h0,h1,n)]) s1 rs1` by
    (irule current_push_consistent >> metis_tac[]) >>
  `current_env_realizes (H ++ [(h0,h1,n)]) ((h1 =+ h0) E) rs1 V` by
    (irule current_push_env_realizes >> metis_tac[]) >>
  `current_env_history_owners (H ++ [(h0,h1,n)]) ((h1 =+ h0) E)` by
    metis_tac[current_env_history_owners_push] >>
  `current_last_name_hit (MAP SND anns) v =
     current_last_name_hit ns (latest_current_name rt v)` by
    (first_x_assum irule >> goal_assum $ drule_at Any >> metis_tac[]) >>
  Cases_on `MEM v (MAP SND anns)`
  >- (Cases_on `current_last_name_hit ns (latest_current_name rt v)`
      >- metis_tac[current_last_name_hit_none] >>
      simp[current_last_name_hit_def]) >>
  `~MEM (latest_current_name rt v) ns` by
    (irule current_trace_absent_name >> metis_tac[]) >>
  Cases_on `h1 = v`
  >- (`latest_current_name rt v = n` by
        (drule_all current_outputs_trace_absent_latest >> strip_tac >>
         drule current_push_latest >> disch_then (qspec_then `v` mp_tac) >> simp[]) >>
      simp[current_last_name_hit_cons]) >>
  `~MEM v (MAP SND ((h0,h1)::anns))` by simp[] >>
  `~MEM (latest_current_name rt v) (n::ns)` by
    (irule current_trace_absent_name >> goal_assum $ drule_at Any >> metis_tac[]) >>
  metis_tac[current_last_name_hit_none, MEM]
QED

Theorem current_last_event_hit_names:
  !events. current_last_event_hit outs events v =
    current_last_name_hit (MAP (\ev. EL (FST ev) outs) events) v
Proof
  Induct >- simp[current_last_event_hit_def, current_last_name_hit_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[current_last_event_hit_def, current_last_name_hit_def]
QED

Theorem current_full_event_names:
  MAP FST events = GENLIST I (LENGTH outs) ==>
  MAP (\ev. EL (FST ev) outs) events = outs
Proof
  strip_tac >>
  `MAP (\ev. EL (FST ev) outs) events =
    MAP (\k. EL k outs) (MAP FST events)` by simp[MAP_MAP_o, combinTheory.o_DEF] >>
  simp[] >> irule LIST_EQ >> simp[EL_MAP, EL_GENLIST]
QED

Theorem current_last_event_hit_full:
  MAP FST events = GENLIST I (LENGTH outs) ==>
  current_last_event_hit outs events v = current_last_name_hit outs v
Proof
  strip_tac >> simp[current_last_event_hit_names] >>
  drule current_full_event_names >> simp[]
QED

Theorem current_outputs_trace_last_event_hit:
  current_outputs_trace anns s rs H E names s' rt H' E' /\
  current_annotations_ok V H anns /\
  current_allocation_consistent V H s rs /\ current_env_realizes H E rs V /\
  current_env_history_owners H E /\ MEM v V /\
  MAP FST events = GENLIST I (LENGTH anns) ==>
  current_last_event_hit (MAP SND anns) events v =
    current_last_event_hit names events (latest_current_name rt v)
Proof
  strip_tac >>
  `LENGTH names = LENGTH anns` by
    (drule current_outputs_trace_owned_names >> disch_then (mp_tac o MATCH_MP LIST_REL_LENGTH) >> simp[]) >>
  `current_last_event_hit (MAP SND anns) events v = current_last_name_hit (MAP SND anns) v` by
    (irule current_last_event_hit_full >> simp[]) >>
  `current_last_event_hit names events (latest_current_name rt v) =
     current_last_name_hit names (latest_current_name rt v)` by
    (irule current_last_event_hit_full >> simp[]) >>
  simp[] >> irule current_outputs_trace_last_name_hit >> metis_tac[]
QED

Theorem current_last_event_hit_full_none:
  MAP FST events = GENLIST I (LENGTH outs) ==>
  (current_last_event_hit outs events v = NONE <=> ~MEM v outs)
Proof
  strip_tac >> drule current_last_event_hit_full >>
  simp[current_last_name_hit_none]
QED

Theorem current_outputs_trace_absent_hits:
  current_outputs_trace anns s rs H E names s' rt H' E' /\
  current_annotations_ok V H anns /\
  current_allocation_consistent V H s rs /\ current_env_realizes H E rs V /\
  current_env_history_owners H E /\ MEM v V /\
  MAP FST events = GENLIST I (LENGTH anns) /\ ~MEM v (MAP SND anns) ==>
  latest_current_name rt v = latest_current_name rs v /\
  current_last_event_hit (MAP SND anns) events v = NONE /\
  current_last_event_hit names events (latest_current_name rt v) = NONE
Proof
  strip_tac >>
  `latest_current_name rt v = latest_current_name rs v` by
    metis_tac[current_outputs_trace_absent_latest] >>
  `current_last_event_hit (MAP SND anns) events v = NONE` by
    (`MAP FST events = GENLIST I (LENGTH (MAP SND anns))` by simp[] >>
     drule current_last_event_hit_full_none >> simp[]) >>
  drule_all current_outputs_trace_last_event_hit >> simp[]
QED

Theorem current_inst_trace_last_event_hit:
  current_inst_trace anns inst s rs H E inst' s' rt H' E' /\
  current_annotations_ok V H anns /\
  current_allocation_consistent V H s rs /\ current_env_realizes H E rs V /\
  current_env_history_owners H E /\ MEM v V /\
  MAP FST events = GENLIST I (LENGTH inst.inst_outputs) ==>
  current_last_event_hit inst.inst_outputs events v =
    current_last_event_hit inst'.inst_outputs events (latest_current_name rt v)
Proof
  simp[current_inst_trace_def] >> rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[] >>
  qpat_assum `MAP SND anns = _` (fn th => rewrite_tac[GSYM th]) >>
  irule current_outputs_trace_last_event_hit >> metis_tac[LENGTH_MAP]
QED

Theorem current_inst_trace_absent_latest:
  current_inst_trace anns inst s rs H E inst' s' rt H' E' /\
  ~MEM v inst.inst_outputs ==>
  latest_current_name rt v = latest_current_name rs v
Proof
  simp[current_inst_trace_def] >> metis_tac[current_outputs_trace_absent_latest]
QED
