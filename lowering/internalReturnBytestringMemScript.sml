(* Runtime bytestring source bounds are unchanged by capacity widening. *)
Theory internalReturnBytestringMem
Ancestors
  exprSimMemDefs stmtSimReturnWiden valueCopyBytes typedMemoryCopy
  vyperTypeSystem compileEnv

Theorem internal_return_bytestring_store_bound:
  type_widens_to (get_tenv cx) sty ty /\ is_bytestring_type ty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  expr_store_bound cx sty v op s ==>
  expr_store_bound cx ty v op s
Proof
  strip_tac >>
  `is_bytestring_type sty` by metis_tac[typed_copy_bytestring_source] >>
  `~is_word_type sty` by metis_tac[is_bytestring_word_type] >>
  `val_store_size stv v = val_store_size dtv v` by
    metis_tac[bytestring_val_store_size_eq] >>
  gvs[expr_store_bound_def]
QED
