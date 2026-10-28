signature vyperTestLib = sig

  val generate_tests : unit -> unit (* main generation function *)
  val write_coverage_report : string -> unit
  val unsupported_source_reason_for : JSON.value list -> string option

  val test_files : unit -> (string * string) list
  val holbuild_extra_deps : string list -> unit
  val holbuild_extra_outputs : string list -> unit
  (* Raw selection expands fixtures, retaining the historical global index order.
     No HOL terms are decoded until a definition partition is built. *)
  val select_test_inputs :
    (string * JSON.value) list -> (string * JSON.value list) list
  val partition_indexed : int -> 'a list -> (int * 'a) list list
  val test_batch_size : int
  val valid_test_partition : int * int * int -> bool (* total, first, count *)
  (* Pure check of expected batch ids against directory basenames. *)
  val check_generated_script_inventory : string list -> string list -> unit
  val check_generated_scripts : unit -> unit (* raw exports vs generated/ *)
  val make_definitions_for_file : string * string -> unit
  val make_definitions_for_partition : string * string * int * int * int -> unit
  val generate_defn_scripts : unit -> unit
  val generate_test_scripts : unit -> unit

end
