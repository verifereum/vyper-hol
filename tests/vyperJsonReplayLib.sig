signature vyperJsonReplayLib = sig
  (* Concrete logical trace lists, with same-file fixture dependencies applied. *)
  val prepare_file : string -> (string * Term.term) list
  (* The concrete CV argument used by the translated run_test invocation. *)
  val encode_traces : Term.term -> Term.term
  val replay_file : string -> (string * Thm.thm) list
end
