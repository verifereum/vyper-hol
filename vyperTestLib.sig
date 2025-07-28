signature vyperTestLib = sig

  val make_definitions_for_file : int -> unit
  val traces_ty : Type.hol_type
  val run_test_on_traces : Term.term -> unit
  val export_theory_no_docs : unit -> unit

end
