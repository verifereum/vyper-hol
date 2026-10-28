(* Exact worklist composition with opaque analysis states. *)
Theory venomWorklistEval
Ancestors worklistDefs list pair

Theorem wl_step_cons_result:
  !changed process deps lbl rest state next changed_result.
    process lbl state = next /\
    changed lbl state next = changed_result ==>
    wl_step changed process deps (lbl::rest,state) =
      ((if changed_result then rest ++ deps lbl else rest),next)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `changed_result` >> simp[wl_step_def]
QED
