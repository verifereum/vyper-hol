(* Exact equations for staging the original worklist transition. *)
Theory worklistStepCompute
Ancestors worklistDefs

Theorem wl_step_cons:
  wl_step changed process deps (lbl::rest,st) =
    let next = process lbl st in
    if changed lbl st next then (rest ++ deps lbl,next)
    else (rest,next)
Proof
  simp[wl_step_def]
QED

Theorem wl_step_nil:
  wl_step changed process deps ([],st) = ([],st)
Proof
  simp[wl_step_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("worklist step has oracle dependencies: " ^ name)
  end) (DB.thms "worklistStepCompute");
