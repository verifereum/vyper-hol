(* Event-argument compatibility, field type first, as the event proofs state
   it.  The type checker's Log case uses arg_type_fits (argument type first);
   event_arg_compatible is that relation with its arguments swapped, and the
   clause equations and induction principle below are derived from
   arg_type_fits's, so the source semantics keeps a single widening rule. *)
Theory vyperEventArgCompat
Ancestors
  vyperTypeSystem vyperTypeArgFits list

Definition event_arg_compatible_alias_def:
  event_arg_compatible fty aty <=> arg_type_fits aty fty
End

Definition event_arg_compatible_list_alias_def:
  event_arg_compatible_list fts ats <=> arg_types_fit ats fts
End

Theorem event_arg_compatible_list_length[local]:
  !fts ats. event_arg_compatible_list fts ats <=>
            LENGTH fts = LENGTH ats /\ event_arg_compatible_list fts ats
Proof
  metis_tac[event_arg_compatible_list_alias_def, arg_types_fit_LENGTH]
QED

local
  val swap_rws = [GSYM event_arg_compatible_alias_def,
                  GSYM event_arg_compatible_list_alias_def]
  (* The tuple clause states the length agreement, as a recursive definition
     of event_arg_compatible would. *)
  fun with_length th =
    let val (l, r) = dest_eq (snd (strip_forall (concl th)))
    in if same_const (fst (strip_comb l)) ``event_arg_compatible`` andalso
          can (find_term (same_const ``event_arg_compatible_list``)) r
       then CONV_RULE (STRIP_QUANT_CONV (RAND_CONV
              (ONCE_REWRITE_CONV [event_arg_compatible_list_length]))) th
       else th
    end
in
  val clauses =
    LIST_CONJ (map with_length
      (CONJUNCTS (PURE_REWRITE_RULE swap_rws arg_type_fits_def)))
  val ind =
    let val P = mk_var ("P", ``:type -> type -> bool``)
        val Q = mk_var ("Q", ``:type list -> type list -> bool``)
        val a = mk_var ("a", ``:type``) and f = mk_var ("f", ``:type``)
        val as' = mk_var ("as", ``:type list``)
        val fs = mk_var ("fs", ``:type list``)
    in arg_type_fits_ind
       |> ISPECL [list_mk_abs ([a, f], list_mk_comb (P, [f, a])),
                  list_mk_abs ([as', fs], list_mk_comb (Q, [fs, as']))]
       |> BETA_RULE
       |> CONV_RULE (RAND_CONV (BINOP_CONV SWAP_FORALL_CONV))
       |> GENL [P, Q]
    end
end

Theorem event_arg_compatible_def = clauses;

Theorem event_arg_compatible_ind = ind;
