signature vyperTestLib = sig

  type term = Term.term

  val read_test_json : string -> (string * term list) list

  val run_test : string * term list -> unit

end
