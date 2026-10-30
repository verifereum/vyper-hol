(* Check proof tags while a theory is built: disk loading does not retain
   imported axiom dependencies, so downstream audits cannot check those. *)
structure proofAuditLib =
struct

(* Reject free hypotheses and all tags except ordinary disk dependencies. *)
fun check (name, th) =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn tag => tag = "DISK_THM") oracles
    then () else raise Fail ("Unchecked proof: " ^ name)
  end;

fun check_all named_theorems = List.app check named_theorems;
fun check_theory name = check_all (DB.thms name);

end
