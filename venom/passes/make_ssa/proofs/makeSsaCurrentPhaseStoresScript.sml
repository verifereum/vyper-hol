Theory makeSsaCurrentPhaseStores
Ancestors makeSsaCurrentNameStoreReplay makeSsaCurrentDynamicStores
  makeSsaCurrentAllocation makeSsaCurrentSymbolicInterface
  venomState finite_map list combin

(* Fixed final allocation history; projection is bookkeeping, not readiness.
   In particular a default is a read of the current concrete spelling. *)
Definition phase_project_def:
  phase_project H N t =
    case current_token_name H t of NONE => NONE | SOME x => N x
End

Definition phase_token_initial_def:
  phase_token_initial H = phase_project H current_origin_initial
End

Theorem phase_project_lookup:
  current_token_name H t = SOME x ==> phase_project H N t = N x
Proof
  simp[phase_project_def]
QED

Theorem phase_token_initial_lookup:
  current_token_name H t = SOME x ==>
  phase_token_initial H t = current_origin_initial x
Proof
  simp[phase_token_initial_def, phase_project_def]
QED

Theorem phase_project_update:
  current_token_name H t = SOME x ==>
  phase_project H (((a =+ z) N)) t = if x = a then z else N x
Proof
  simp[phase_project_def, APPLY_UPDATE_THM] >> metis_tac[]
QED

Theorem phase_token_initial_bounded:
  current_origin_bounded 0 (phase_token_initial H)
Proof
  simp[phase_token_initial_def, phase_project_def, current_origin_bounded_def,
       current_origin_initial_def, AllCaseEqs()]
QED

Theorem phase_project_default:
  phase_project H N (CurrentDefault x) = N x
Proof
  simp[phase_project_def, current_token_name_def]
QED

(* General alias boundary, including allocated names equal to source spellings.
   Both cells observe a name write. A default is not a stable token cell. *)
Theorem phase_project_alias_update:
  current_token_name H t = SOME x ==>
  phase_project H N t = phase_project H N (CurrentDefault x) /\
  phase_project H (((x =+ z) N)) t = z /\
  phase_project H (((x =+ z) N)) (CurrentDefault x) = z
Proof
  strip_tac >> simp[phase_project_def, current_token_name_def, APPLY_UPDATE_THM]
QED

Theorem phase_project_alias_probe:
  phase_token_initial [(CurrentOriginal "E" 0 0,"v","v")]
    (CurrentOriginal "E" 0 0) = SOME (CurrentInitial "v") /\
  phase_project [(CurrentOriginal "E" 0 0,"v","v")]
    (("v" =+ SOME (CurrentOccurrence 0 0)) current_origin_initial)
    (CurrentOriginal "E" 0 0) = SOME (CurrentOccurrence 0 0) /\
  phase_project [(CurrentOriginal "E" 0 0,"v","v")]
    (("v" =+ SOME (CurrentOccurrence 0 0)) current_origin_initial)
    (CurrentDefault "v") = SOME (CurrentOccurrence 0 0)
Proof
  simp[phase_token_initial_def, phase_project_def, current_token_name_def,
       current_origin_initial_def, APPLY_UPDATE_THM]
QED

(* An initial atom may denote absence. This concrete interpretation uses an
   empty initial variable map: even SOME initial-symbol is not a SOME value. *)
Theorem phase_initial_atom_not_readiness:
  st.vs_vars = FEMPTY ==>
  current_origin_initial x = SOME (CurrentInitial x) /\ lookup_var x st = NONE
Proof
  simp[current_origin_initial_def, lookup_var_def]
QED

(* Accepted sequential last-write replay instantiated at the new initial store.
   It projects only allocated history tokens, never source agreement or reads. *)
Theorem phase_initial_name_replay:
  LIST_REL (\anns i. LIST_REL (\(t,v) x.
    MEM t (MAP FST H) /\ current_token_name H t = SOME x)
      anns i.inst_outputs) annss insts /\ current_history_valid V H ==>
  !n j t x. MEM t (MAP FST H) /\ current_token_name H t = SOME x ==>
    current_token_replay n (TAKE j annss) (phase_token_initial H) t =
    current_source_replay n (TAKE j insts) current_origin_initial x
Proof
  rpt strip_tac >> irule current_replay_names >>
  qexistsl_tac [`H`, `V`] >> simp[phase_token_initial_lookup]
QED
