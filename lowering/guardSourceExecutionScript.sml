(* Whole evaluator fixed-horizon preservation under a selected-prefix rule. *)
Theory guardSourceExecution
Ancestors
  guardSourceOrdinarySchema guardSourceOrdinary guardSourceCalls
Libs
  guardSourceSchemaLib

val prefix_manifest = guardSourceSchemaLib.manifest finite_prefix_evaluate_ind;
val prefix_branches = CONJUNCTS finite_prefix_ordinary_branches @
                      CONJUNCTS finite_prefix_call_branches;
val _ = if length prefix_branches = length prefix_manifest andalso
           length (mk_set (map (guardSourceSchemaLib.label o concl) prefix_branches)) =
             length prefix_branches
        then () else raise Fail "Finite-prefix branch coverage differs from schema";
val ordered_prefix_branches = map (fn (name,tm) =>
  case List.find (fn th => guardSourceSchemaLib.label (concl th) = name) prefix_branches of
    SOME th => if aconv (concl th) tm then th
               else raise Fail ("Finite-prefix branch statement differs: " ^ name)
  | NONE => raise Fail ("Finite-prefix branch missing: " ^ name)) prefix_manifest;
val prefix_conclusion = #2 (dest_imp (concl finite_prefix_evaluate_ind));

Theorem eval_storage_finite_prefix_mutual:
  ^(list_mk_forall (free_vars prefix_conclusion, prefix_conclusion))
Proof
  MATCH_ACCEPT_TAC (GEN_ALL
    (MATCH_MP finite_prefix_evaluate_ind (LIST_CONJ ordered_prefix_branches)))
QED
