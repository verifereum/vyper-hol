(* Join independently obtained block and continuation fuel witnesses. *)
Theory functionInlinerFuel
Ancestors
  venomExecSemantics venomExecProps crossBlockSimProps arithmetic

Theorem inline_run_blocks_continue:
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block fuel ctx bb t = OK u /\ ~u.vs_halted ==>
  run_blocks (SUC fuel) ctx fn t = run_blocks fuel ctx fn u
Proof
  simp[run_blocks_unfold]
QED

Theorem inline_run_blocks_join:
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block f ctx bb t = OK u /\ ~u.vs_halted /\
  run_blocks g ctx fn u = res /\ terminates res ==>
  ?h. run_blocks h ctx fn t = res
Proof
  strip_tac >>
  `run_block (g + f) ctx bb t = OK u` by
    (irule run_block_fuel_mono_OK >> qexists_tac `f` >> simp[]) >>
  qexists_tac `SUC (g + f)` >>
  drule_all inline_run_blocks_continue >> simp[] >>
  `terminates (run_blocks g ctx fn u)` by simp[] >>
  drule crossBlockSimPropsTheory.run_blocks_fuel_mono >>
  disch_then (qspec_then `f` mp_tac) >> simp[]
QED

Theorem inline_run_blocks_terminal:
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block fuel ctx bb t = res /\
  (!u. res <> OK u) ==>
  run_blocks (SUC fuel) ctx fn t = res
Proof
  strip_tac >> simp[run_blocks_unfold] >> Cases_on `res` >> gvs[]
QED
