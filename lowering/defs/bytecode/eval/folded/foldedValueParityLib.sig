signature foldedValueParityLib = sig
  val setup : unit -> unit
  val refresh_compset : unit -> unit
  val eval : Abbrev.conv
  val restricted_eval : Term.term list -> Abbrev.conv
  val locate : (Term.term -> bool) -> Term.term -> string * Term.term
  val has_term : (Term.term -> bool) -> Term.term -> bool
  val at_conv : (Term.term -> bool) -> Abbrev.conv -> Abbrev.conv
  val call_conv : Term.term -> Abbrev.conv -> Abbrev.conv
  val input : string -> string -> Term.term
  val expected : string -> string -> Term.term
  val eval_call : Term.term -> Abbrev.tactic
  val PARITY_NORMALIZE_TAC : Abbrev.tactic
  val PARITY_PASS_TAC : Abbrev.tactic
  val PARITY_OPEN_PASS_TAC : Abbrev.tactic
  val audit : string -> unit
end
