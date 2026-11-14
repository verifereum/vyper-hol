(* stmt_state_rel is polymorphic in its horizon, so a lemma's !H' transport
   conjunct keeps a type variable that a drule/irule cannot later fix to the
   finite-storage horizon type valid_horizon uses.  at_horizon fixes it
   before the lemma is used; at_horizon_named does so for another name.
   Every variable of that name whose type matches is fixed, since a lemma
   can bind a finite H inside a conjunct about a polymorphic one. *)
structure horizonTypeLib =
struct
open HolKernel boolLib

fun at_horizon_named name th =
  let
    val horizon = Parse.Type `:(bool # bytes32 # type_value) list # num list`
    val tys = map type_of
      (find_terms (fn t => is_var t andalso fst (dest_var t) = name) (concl th))
    val matching = List.filter (fn ty => can (match_type ty) horizon) tys
  in
    if null matching then
      raise mk_HOL_ERR "horizonTypeLib" "at_horizon_named"
        ("no variable " ^ name ^ " has a type matching the horizon type; found: " ^
         String.concatWith ", " (map type_to_string tys))
    else
      INST_TYPE (foldl (fn (ty, s) => match_type_in_context ty horizon s)
                       [] matching) th
  end

val at_horizon = at_horizon_named "H'"

end
