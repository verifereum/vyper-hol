Theory jsonToVyperTypeCV
Ancestors
  jsonToVyperType jsonAST vyperAST list cv
Libs
  cv_transLib jsonToVyperCVLib

(* These helpers are abbreviations of the source traversal, not independent
   implementations.  Their nil/cons equations expose first-order recursion. *)
Definition translate_types_cv_def:
  translate_types_cv ctx tys = MAP (λty. translate_type ctx ty) tys
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

Definition translate_annotations_cv_def:
  translate_annotations_cv ctx anns = MAP (λann. translate_annotation ctx ann) anns
End

Theorem translate_annotations_cv_compute:
  (translate_annotations_cv ctx [] = []) /\
  (translate_annotations_cv ctx (ann::anns) =
    translate_annotation ctx ann :: translate_annotations_cv ctx anns)
Proof
  simp[translate_annotations_cv_def]
QED

val translate_annotation_compute = save_thm ("translate_annotation_compute",
  CONJ (PURE_REWRITE_RULE [GSYM translate_annotations_cv_def] translate_annotation_def)
       translate_annotations_cv_compute);
val translate_annotation_compute_ind = save_thm ("translate_annotation_compute_ind",
  jsonToVyperCVLib.register_first_order_induction "translate_annotation_first_order"
    translate_annotation_compute
    (WF_REL_TAC `measure (λx. case x of
       INL (ctx,ann) => json_type_annotation_size ann
     | INR (ctx,anns) => list_size json_type_annotation_size anns)` >> simp[]));
val () = cv_auto_trans translate_annotation_compute;

Definition annotations_resolved_cv_def:
  annotations_resolved_cv nominal_index all_import_maps ctx anns =
    EVERY (λann. annotation_resolved nominal_index all_import_maps ctx ann) anns
End

Theorem annotations_resolved_cv_compute:
  (annotations_resolved_cv nominal_index all_import_maps ctx [] = T) /\
  (annotations_resolved_cv nominal_index all_import_maps ctx (ann::anns) =
    (annotation_resolved nominal_index all_import_maps ctx ann /\
     annotations_resolved_cv nominal_index all_import_maps ctx anns))
Proof
  simp[annotations_resolved_cv_def]
QED

val annotation_resolved_compute = save_thm ("annotation_resolved_compute",
  CONJ (PURE_REWRITE_RULE [GSYM annotations_resolved_cv_def] annotation_resolved_def)
       annotations_resolved_cv_compute);
val annotation_resolved_compute_ind = save_thm ("annotation_resolved_compute_ind",
  jsonToVyperCVLib.register_first_order_induction "annotation_resolved_first_order"
    annotation_resolved_compute
    (WF_REL_TAC `measure (λx. case x of
       INL (ni,im,ctx,ann) => json_type_annotation_size ann
     | INR (ni,im,ctx,anns) => list_size json_type_annotation_size anns)` >> simp[]));
val () = cv_auto_trans annotation_resolved_compute;

Definition elaborate_annotations_cv_def:
  elaborate_annotations_cv nominal_index all_import_maps ctx anns =
    MAP (λann. elaborate_annotation nominal_index all_import_maps ctx ann) anns
End

Theorem elaborate_annotations_cv_compute:
  (elaborate_annotations_cv nominal_index all_import_maps ctx [] = []) /\
  (elaborate_annotations_cv nominal_index all_import_maps ctx (ann::anns) =
    elaborate_annotation nominal_index all_import_maps ctx ann ::
    elaborate_annotations_cv nominal_index all_import_maps ctx anns)
Proof
  simp[elaborate_annotations_cv_def]
QED

val elaborate_annotation_compute = save_thm ("elaborate_annotation_compute",
  CONJ (PURE_REWRITE_RULE [GSYM elaborate_annotations_cv_def] elaborate_annotation_def)
       elaborate_annotations_cv_compute);
val elaborate_annotation_compute_ind = save_thm ("elaborate_annotation_compute_ind",
  jsonToVyperCVLib.register_first_order_induction "elaborate_annotation_first_order"
    elaborate_annotation_compute
    (WF_REL_TAC `measure (λx. case x of
       INL (ni,im,ctx,ann) => json_type_annotation_size ann
     | INR (ni,im,ctx,anns) => list_size json_type_annotation_size anns)` >> simp[]));
val () = cv_auto_trans elaborate_annotation_compute;

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
