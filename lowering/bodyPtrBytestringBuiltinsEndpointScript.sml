(* A STOP observation identifies normal counted endpoints without
   asserting equality of their unobserved halt/return-data fields. *)
Theory bodyPtrBytestringBuiltinsEndpoint
Ancestors
  fragGasPath abiEncoderObserver

Theorem run_from_nonerror_unique:
  run_from n ctx fn s = r /\ run_from m ctx fn s = q /\
  (!e. r <> Error e) /\ (!e. q <> Error e) ==> r = q
Proof
  strip_tac >>
  `run_from (n + m) ctx fn s = r` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `n` >> simp[]) >>
  `run_from (n + m) ctx fn s = q` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `m` >> simp[]) >>
  metis_tac[]
QED

Theorem gas_path_stop_observation:
  gas_path ctx fn s n (OK t) /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME (mk_inst id STOP [] []) /\
  run_from fuel ctx fn s = Halt (stop_view u) ==>
  stop_view t = stop_view u
Proof
  strip_tac >>
  drule_all run_from_stop_view >> strip_tac >>
  drule gas_path_normal >> strip_tac >>
  first_x_assum (qspecl_then [`0`, `Halt (stop_view t)`] mp_tac) >>
  simp[] >> strip_tac >>
  `Halt (stop_view t) = Halt (stop_view u)` suffices_by simp[] >>
  irule run_from_nonerror_unique >> simp[] >>
  metis_tac[]
QED
