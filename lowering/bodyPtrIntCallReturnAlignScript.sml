Theory bodyPtrIntCallReturnAlign
Ancestors
  bodyPtrIntCallGhostTaint ptrSafeRun

Theorem intcall_completed_runs_taint_eq:
  (!e. frame_run n ctx fn s <> Error e) /\
  (!e. frame_run m ctx fn s <> Error e) ==>
  SND (ghost_run n ctx fn PG G tn s) =
  SND (ghost_run m ctx fn PGaux Gaux tn s)
Proof
  strip_tac >>
  `ghost_run (MAX n m) ctx fn PG G tn s = ghost_run n ctx fn PG G tn s` by
    (irule ghost_run_fuel_mono_up >> simp[]) >>
  `ghost_run (MAX n m) ctx fn PGaux Gaux tn s =
   ghost_run m ctx fn PGaux Gaux tn s` by
    (irule ghost_run_fuel_mono_up >> simp[]) >>
  metis_tac[intcall_ghost_run_taint_prov_independent]
QED

Theorem intcall_completed_runs_taint_outputs:
  (!e. frame_run n ctx fn s <> Error e) /\
  (!e. frame_run m ctx fn s <> Error e) /\
  ghost_run n ctx fn PG G tn s = (Gr,tnr) /\
  ghost_run m ctx fn PGaux Gaux tn s = (Ga,tna) ==>
  tnr = tna
Proof
  strip_tac >>
  `SND (ghost_run n ctx fn PG G tn s) =
   SND (ghost_run m ctx fn PGaux Gaux tn s)` by
    (irule intcall_completed_runs_taint_eq >> asm_rewrite_tac[]) >>
  gvs[]
QED
