(* Syntax helpers for giving existing normal-run sequents an extra observation.
   These only assemble statements; the producing proofs still choose the same
   states and ghost witnesses as the ordinary runs. *)
structure ctorCopyObservationLib =
struct
open HolKernel boolSyntax

fun named name vars =
  case List.find (fn v => fst (dest_var v) = name) vars of
    SOME v => v
  | NONE => raise Fail ("ctorCopyObservationLib: missing variable " ^ name)

fun observe start finish guard statement =
  let
    val (pre, post) = dest_imp statement
    val (witnesses, facts) = strip_exists post
    val src = named start (free_vars pre)
    val dst = named finish witnesses
    val observer = mk_var ("R", type_of src --> type_of dst --> bool)
    val observed = list_mk_comb (observer,[src,dst])
    val extra = case guard of NONE => observed | SOME g => mk_imp (g,observed)
  in
    mk_imp (pre, list_mk_exists (witnesses,mk_conj (extra,facts)))
  end

fun rename from into t =
  let val v = named from (free_vars t)
  in subst [v |-> mk_var (into,type_of v)] t end

fun close_except names t =
  list_mk_forall
    (List.filter (fn v => not (List.exists (fn n => fst (dest_var v) = n) names))
       (free_vars t),t)
end
