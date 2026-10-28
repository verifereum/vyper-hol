(* TOP-LEVEL: compatible types with static ABI encoding are identical.
   Capacity widening occurs only in types with dynamic ABI encoding. *)
Theory typedStaticCompatibility
Ancestors
  vyperTypeSystem compileEnv list

Theorem event_arg_compatible_static_type:
  (!fty aty. event_arg_compatible fty aty ==>
    !(sfields:(string, (string # type # num) list) fmap).
      ~is_abi_dynamic sfields fty ==> fty = aty) /\
  (!fts ats. event_arg_compatible_list fts ats ==>
    !(sfields:(string, (string # type # num) list) fmap).
      ~EXISTS (is_abi_dynamic sfields) fts ==> fts = ats)
Proof
  ho_match_mp_tac event_arg_compatible_ind >>
  rw[event_arg_compatible_def, is_abi_dynamic_def] >>
  gvs[] >> res_tac >> gvs[] >>
  first_x_assum (qspec_then `sfields` mp_tac) >>
  gvs[combinTheory.o_DEF]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed static event compatibility: " ^ name)
  end) (DB.thms "typedStaticCompatibility")
