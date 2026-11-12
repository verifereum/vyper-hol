(* Type boundaries for bytestring comparisons and rejected membership. *)
Theory bodyMemBopHeldFacts
Ancestors
  compileEnv vyperTypeSystem

Theorem held_membership_word:
  well_typed_binop ann bop t1 t2 /\ (bop = In \/ bop = NotIn) ==>
  is_word_type t1
Proof
  strip_tac >>
  gvs[well_typed_binop_def, GSYM membership_element_word_boundary,
      is_prim_word_type_def]
QED

Theorem held_bytestring_eqne_types:
  well_typed_binop ann bop t1 t2 /\
  (bop = Eq \/ bop = NotEq) /\ is_bytestring_type t1 ==>
  ann = BaseT BoolT /\ t2 = t1 /\
  ((?n. t1 = BaseT (BytesT (Dynamic n))) \/
   (?n. t1 = BaseT (StringT n)))
Proof
  strip_tac >> gvs[well_typed_binop_def] >>
  Cases_on `t1` >> gvs[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[is_bytestring_type_def]
QED
