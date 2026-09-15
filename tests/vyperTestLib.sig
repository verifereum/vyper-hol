signature vyperTestLib = sig

  val generate_tests : unit -> unit (* main generation function *)
  val write_coverage_report : string -> unit

  val test_files : unit -> (string * string) list
  val holbuild_extra_deps : string list -> unit
  val holbuild_extra_outputs : string list -> unit
  val make_definitions_for_file : string * string -> unit
  val generate_defn_scripts : unit -> unit
  val generate_test_scripts : unit -> unit

end
