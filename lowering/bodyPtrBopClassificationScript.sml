Theory bodyPtrBopClassification
Ancestors
  exprSimOperators exprSimHypsDefs compileEnv vyperTypeSystem

Theorem bop_nonresidual_type_partition:
  well_typed_binop ann bop t1 t2 /\ bop <> In /\ bop <> NotIn /\
  ~((bop = Eq \/ bop = NotEq) /\ is_bytestring_type t1) ==>
  (word_value_type t1 /\ word_value_type t2) \/
  ((bop = Eq \/ bop = NotEq) /\
   (t1 = BaseT AddressT \/ ?m. t1 = BaseT (BytesT (Fixed m))))
Proof
  Cases_on `bop` >>
  simp[well_typed_binop_def, word_value_type_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `t1` >> gvs[word_value_type_def, is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[word_value_type_def, is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[is_bytestring_type_def]
QED
