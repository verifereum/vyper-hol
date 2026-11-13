(* Simultaneous induction over types, struct fields and tuple members. *)
Theory typeValueInduction
Ancestors
  vyperValue list pair
Libs
  legacyInduction

Theorem type_value_mutual_induction:
  !value_pred fields_pred field_pred tuple_pred.
    (!bt. value_pred (BaseTV bt)) /\
    (!tvs. tuple_pred tvs ==> value_pred (TupleTV tvs)) /\
    (!tv. value_pred tv ==> !bd. value_pred (ArrayTV tv bd)) /\
    (!fields. fields_pred fields ==> value_pred (StructTV fields)) /\
    (!n. value_pred (FlagTV n)) /\ value_pred NoneTV /\
    fields_pred [] /\
    (!rest entry. field_pred entry /\ fields_pred rest ==> fields_pred (entry::rest)) /\
    (!name tv. value_pred tv ==> field_pred (name,tv)) /\
    tuple_pred [] /\
    (!rest tv. value_pred tv /\ tuple_pred rest ==> tuple_pred (tv::rest)) ==>
    (!tv. value_pred tv) /\ (!fields. fields_pred fields) /\
    (!entry:string # type_value. field_pred entry) /\ (!tvs. tuple_pred tvs)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`value_pred`, `tuple_pred`, `fields_pred`, `field_pred`]
    (legacyInduction.mutual_ind_from_ops
       (TypeBase.set_induction_of ``:type_value``))) >>
  asm_rewrite_tac [] >>
  simp_tac bool_ss [AC CONJ_COMM CONJ_ASSOC]
QED
