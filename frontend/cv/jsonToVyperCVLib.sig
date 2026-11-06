signature jsonToVyperCVLib = sig
  (* Closed evaluation, including kernel proofs of defined-input conditions.
     Raises an exception rather than returning a conditional theorem. *)
  val eval : Term.term -> Thm.thm

  val register_first_order_induction :
    string -> Thm.thm -> Abbrev.tactic -> Thm.thm
end
