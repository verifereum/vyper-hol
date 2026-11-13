(* stmt_state_rel is polymorphic in its horizon, so a lemma's !H' transport
   conjunct keeps a type variable that a drule/irule cannot later fix to the
   finite-storage horizon type valid_horizon uses.  at_horizon fixes it
   before the lemma is used; at_horizon_named does so for another name. *)
structure horizonTypeLib =
struct
open HolKernel boolLib

fun at_horizon_named name th =
  let
    val hs = find_terms (fn t => is_var t andalso fst (dest_var t) = name)
                        (concl th)
  in
    INST_TYPE (match_type (type_of (hd hs))
                 (Parse.Type `:(bool # bytes32 # type_value) list # num list`)) th
  end

val at_horizon = at_horizon_named "H'"

end
