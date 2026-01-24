signature vyperTestLib = sig

  val test_files : unit -> (string * string) list
  val tests_root_dir : string
  val make_definitions_for_file : string * string -> unit
  val generate_defn_scripts : unit -> unit
  val generate_test_scripts : unit -> unit

end
