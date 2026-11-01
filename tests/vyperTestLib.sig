signature vyperTestLib = sig

  val generate_tests : unit -> unit (* main generation function *)
  val write_coverage_report : string -> unit
  val unsupported_source_reason_for : JSON.value list -> string option

  val test_files : unit -> (string * string) list
  val holbuild_extra_deps : string list -> unit
  val holbuild_extra_outputs : string list -> unit
  val make_definitions_for_file : string * string -> unit
  (* Original suite ID; start/count index the full selected list, without truncation. *)
  val make_definitions_for_file_range : string * string * int * int -> unit
  type test_chunk = {id : string, start : int, count : int}
  (* Weights in selected-list order: binary payload hex-character counts.
     Max 100 cases / 262144 characters; oversized cases get singleton chunks. *)
  val test_chunks : string * int list -> test_chunk list
  val generate_defn_scripts : unit -> unit
  val generate_test_scripts : unit -> unit

end
