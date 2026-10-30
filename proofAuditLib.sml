(* Check each theory before serialization, while local axiom tags are available. *)
structure proofAuditLib = struct
open HolKernel

fun check_theory theory =
  List.app (fn (name, th) => let
    val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null (hyp th) andalso null axioms andalso
       List.all (fn tag => tag = "DISK_THM") oracles then ()
    else raise Fail (theory ^ "." ^ name ^ ": not kernel-closed/unadmitted")
  end) (DB.thms theory)
end
