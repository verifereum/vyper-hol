signature vyperTestLib = sig

  val num_test_files : int
  val get_test_file : int -> string
  val make_definitions_for_file : int -> unit
  val traces_ty : Type.hol_type
  val run_test_on_traces : Term.term -> unit
  val export_theory_no_docs : unit -> unit

end
