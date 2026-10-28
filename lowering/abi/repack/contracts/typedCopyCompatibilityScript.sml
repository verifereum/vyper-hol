(* TOP-LEVEL: basic compatibility facts shared by recursive copy and Log
   proofs, independently of any particular lowering entry point. *)
Theory typedCopyCompatibility
Ancestors
  vyperTypeSystem list

Theorem event_arg_compatible_reflexive:
  (!fty aty. fty = aty ==> event_arg_compatible fty aty) /\
  (!fts ats. fts = ats ==> event_arg_compatible_list fts ats)
Proof
  ho_match_mp_tac event_arg_compatible_ind >> rw[event_arg_compatible_def] >> gvs[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed shared typed-copy compatibility facts: " ^ name)
  end) (DB.thms "typedCopyCompatibility")
