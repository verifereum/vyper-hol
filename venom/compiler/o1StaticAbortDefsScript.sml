(* The static companion keeps the context's layout bound on safe paths. *)
Theory o1StaticAbortDefs
Ancestors
  staticAbortMemDefs o1PassContract

Definition o1_lowered_inv_abort_def:
  o1_lowered_inv_abort C vs <=>
    ?eom. max_live_eom C = SOME eom /\
          mem_inv (static_mem_ok_abort eom) C vs
End
