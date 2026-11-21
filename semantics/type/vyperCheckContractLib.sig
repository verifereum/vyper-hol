signature vyperCheckContractLib = sig

  type check_input =
    {in_deploy : bool,
     layouts : Term.term,
     address : Term.term,
     modules : Term.term}

  val check_contract_compset : computeLib.compset
  val check_contract_conv : Conv.conv

  (* Decide `l = r` for string literals l and r, and `x IN s` for a string
     literal x and an INSERT chain of string literals s; UNCHANGED on any
     other term. check_contract_compset tries both before its generic
     rules. *)
  val string_literal_eq_conv : Conv.conv
  val string_literal_in_conv : Conv.conv

  val mk_check_contract : check_input -> Term.term
  val check_contract_with : Conv.conv -> check_input -> Thm.thm
  val check_contract : check_input -> Thm.thm

end
