Theory jsonToVyperTypeCV
Ancestors
  jsonToVyperType jsonAST vyperAST vyperContext[ignore_grammar] list cv
Libs
  cv_transLib jsonToVyperCVLib

(* Reuse the interpreter's existing AST encoders before translating any
   frontend result. Independent encoders for the same datatype conflict when
   both frontend and execution CV theories are loaded in the test importer. *)

(* These helpers are abbreviations of the source traversal, not independent
   implementations.  Their nil/cons equations expose first-order recursion. *)
Definition translate_types_cv_def:
  translate_types_cv ctx tys = MAP (translate_type ctx) tys
End

Theorem translate_types_cv_compute:
  (translate_types_cv ctx [] = []) /\
  (translate_types_cv ctx (ty::tys) =
    translate_type ctx ty :: translate_types_cv ctx tys)
Proof
  simp[translate_types_cv_def]
QED

val translate_type_compute = save_thm ("translate_type_compute",
  CONJ (PURE_REWRITE_RULE [GSYM translate_types_cv_def] translate_type_def)
       translate_types_cv_compute);
val translate_type_compute_ind = save_thm ("translate_type_compute_ind",
  jsonToVyperCVLib.register_first_order_induction "translate_type_first_order"
    translate_type_compute
    (WF_REL_TAC `measure (λx. case x of
       INL (ctx,ty) => json_type_size ty
     | INR (ctx,tys) => list_size json_type_size tys)` >> simp[]));
val () = cv_auto_trans translate_type_compute;

(* LIST_REL can instead recurse through the original tuple constructors, so
   inferred-type checking needs no list helper at all. *)
Theorem inferred_tuple_consistent:
  (inferred_type_consistent ctx (TupleT []) (JT_Tuple []) = T) /\
  (inferred_type_consistent ctx (TupleT (ty::tys)) (JT_Tuple []) = F) /\
  (inferred_type_consistent ctx (TupleT []) (JT_Tuple (jt::jts)) = F) /\
  (inferred_type_consistent ctx (TupleT (ty::tys)) (JT_Tuple (jt::jts)) =
    (inferred_type_consistent ctx ty jt /\
     inferred_type_consistent ctx (TupleT tys) (JT_Tuple jts)))
Proof
  simp[inferred_type_consistent_def, LIST_REL_def]
QED

val (nested_type_eqs, other_type_eqs) = List.partition
  (fn th => can (find_term (same_const ``LIST_REL``)) (concl th))
  (CONJUNCTS (SPEC_ALL inferred_type_consistent_def));
val () = if length nested_type_eqs = 1 then ()
         else raise Fail "expected one nested inferred-type equation";
val inferred_type_compute = save_thm ("inferred_type_compute",
  LIST_CONJ (other_type_eqs @ CONJUNCTS (SPEC_ALL inferred_tuple_consistent)));
val inferred_type_compute_ind = save_thm ("inferred_type_compute_ind",
  jsonToVyperCVLib.register_first_order_induction "inferred_type_first_order"
    inferred_type_compute
    (WF_REL_TAC `measure (λ(_,_,jt). json_type_size jt)` >> simp[]));
val () = cv_auto_trans inferred_type_compute;
