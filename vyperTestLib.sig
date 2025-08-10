signature vyperTestLib = sig

  val test_files : string list
  val make_definitions_for_file : int * string -> unit
  val export_theory_no_docs : unit -> unit
  val generate_defn_scripts : unit -> unit

end
