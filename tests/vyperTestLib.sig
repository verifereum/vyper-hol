signature vyperTestLib = sig

  val generate_tests : unit -> unit (* main generation function *)
  val write_coverage_report : string -> unit
  val unsupported_source_reason_for : JSON.value list -> string option

  val test_files : unit -> (string * string) list
  val holbuild_extra_deps : string list -> unit
  val holbuild_extra_outputs : string list -> unit
  val make_definitions_for_file : string * string -> unit
  (* Global selection offsets; total guards against stale generated shards. *)
  val make_definitions_for_file_part : string * string ->
    {start : int, count : int, total : int} -> unit
  val test_parts : int -> (int * int) list
  val selected_test_names_for_file : string -> string list
  val generate_defn_scripts : unit -> unit
  val generate_test_scripts : unit -> unit

end
