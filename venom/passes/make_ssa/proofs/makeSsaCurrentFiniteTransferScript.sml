(* Producer compatibility is independent of backward read/read closure. *)
Theory makeSsaCurrentFiniteTransfer
Ancestors makeSsaCurrentFiniteTables makeSsaCurrentStaticDemandProbe
  makeSsaCurrentFiniteDemandProbe makeSsaCurrentFiniteHistory
  makeSsaCurrentHistoryProbe makeSsaCurrentPlacementCut
  makeSsaCurrentSimDefs makeSsaCurrentAllocation
  venomInst venomExecSemantics list rich_list

Definition current_table_pull_safe_def:
  current_table_pull_safe result =
    case result of
      SOME (CurrentStaticRead u,CurrentStaticRead v) => T
    | SOME (CurrentStaticProduced i,CurrentStaticProduced j) => (i = j)
    | _ => F
End

Definition current_table_safe_row_def:
  current_table_safe_row fn fn' table c d k =
    EVERY (\(e,x,y). current_table_pull_safe (current_table_pull fn fn' c k x y))
      (FILTER (\(e,x,y). e = d) table)
End

Theorem current_table_safe_row_sound:
  current_table_safe_row fn fn' table c d k /\ MEM (d,x,y) table ==>
  ?a b. current_static_back fn fn' c k x y a b /\
    ((?u v. a = CurrentStaticRead u /\ b = CurrentStaticRead v) \/
     (?i. a = CurrentStaticProduced i /\ b = CurrentStaticProduced i))
Proof
  simp[current_table_safe_row_def, EVERY_MEM, MEM_FILTER] >> strip_tac >>
  first_x_assum (qspec_then `(d,x,y)` mp_tac) >> simp[] >>
  Cases_on `current_table_pull fn fn' c k x y` >> simp[current_table_pull_safe_def] >>
  PairCases_on `x'` >> Cases_on `x'0` >> Cases_on `x'1` >>
  simp[current_table_pull_safe_def] >>
  metis_tac[current_table_pull_back]
QED

Theorem current_table_entry_sound:
  EVERY (\(e,x,y). x = y) (FILTER (\(e,x,y). e = c) table) ==>
  !x y. MEM (c,x,y) table ==> x = y
Proof
  simp[EVERY_MEM, MEM_FILTER] >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then `(c,x,y)` mp_tac) >> simp[]
QED

Theorem current_loop_table_entry:
  MEM (CurrentStaticCut "" "E" 0 0,x,y) current_loop_demand_table ==> x = y
Proof
  match_mp_tac current_table_entry_sound >> CONV_TAC (RAND_CONV EVAL) >> EVAL_TAC
QED

Theorem current_backedges_table_entry:
  MEM (CurrentStaticCut "" "E" 0 0,x,y) current_backedges_demand_table ==> x = y
Proof
  match_mp_tac current_table_entry_sound >> CONV_TAC (RAND_CONV EVAL) >> EVAL_TAC
QED

Theorem current_loop_demand_entry:
  current_finite_demand current_probe_loop (current_finite_target current_probe_loop)
    (current_finite_history current_probe_loop) (CurrentStaticCut "" "E" 0 0) x y ==>
  x = y
Proof
  metis_tac[current_loop_demand_contained, current_loop_table_entry]
QED

Theorem current_backedges_demand_entry:
  current_finite_demand history_probe_backedges (current_finite_target history_probe_backedges)
    (current_finite_history history_probe_backedges) (CurrentStaticCut "" "E" 0 0) x y ==>
  x = y
Proof
  metis_tac[current_backedges_demand_contained, current_backedges_table_entry]
QED

