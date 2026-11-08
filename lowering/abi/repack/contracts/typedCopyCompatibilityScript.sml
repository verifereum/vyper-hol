(* TOP-LEVEL: basic compatibility facts shared by recursive copy and Log
   proofs, independently of any particular lowering entry point. *)
Theory typedCopyCompatibility
Ancestors
  vyperEventArgCompat
  vyperTypeSystem list

Theorem event_arg_compatible_reflexive:
  (!fty aty. fty = aty ==> event_arg_compatible fty aty) /\
  (!fts ats. fts = ats ==> event_arg_compatible_list fts ats)
Proof
  ho_match_mp_tac event_arg_compatible_ind >> rw[event_arg_compatible_def] >> gvs[]
QED
