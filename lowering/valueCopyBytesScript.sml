(*
 * Bytestrings under compile_store_memory: the copy ignores the source's
 * bound, and a value lies the same way at every bytestring type it has.
 *
 * TOP-LEVEL:
 *   compile_store_memory_bytestring_src — the copy at the destination type
 *   bytestring_val_in_memory_transfer, bytestring_val_footprint_eq — layout
 *     and footprint agree across bytestring types
 *   bytestring_type_value, is_bytestring_word_type — bytestring types
 *)
Theory valueCopyBytes
Ancestors
  exprSim context compileEnv valueTypingMemoryProps vyperTyping vyperValue valueEncoding

Theorem compile_store_memory_bytestring_src:
  !cenv src dst dty sty.
    is_bytestring_type dty ==>
    compile_store_memory cenv src dst dty sty =
    compile_store_memory cenv src dst dty dty
Proof
  simp[compile_store_memory_def]
QED

Theorem is_bytestring_word_type:
  !t. is_bytestring_type t ==> ~is_word_type t
Proof
  Cases >> simp[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
  simp[is_bytestring_type_def, is_word_type_def]
QED

Theorem bytestring_type_value:
  !tenv t tv.
    is_bytestring_type t /\ evaluate_type tenv t = SOME tv ==>
    (?n. tv = BaseTV (BytesT (Dynamic n))) \/ (?n. tv = BaseTV (StringT n))
Proof
  rpt gen_tac >> Cases_on `t` >> simp[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
  rw[is_bytestring_type_def, evaluate_type_def]
QED

Theorem bytestring_val_in_memory_transfer:
  !tenv t1 t2 tv1 tv2 v off mem.
    is_bytestring_type t1 /\ is_bytestring_type t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ evaluate_type tenv t2 = SOME tv2 /\
    value_has_type tv2 v /\ val_in_memory tv1 v off mem ==>
    val_in_memory tv2 v off mem
Proof
  rpt strip_tac >>
  qspecl_then [`tenv`, `t1`, `tv1`] mp_tac bytestring_type_value >>
  qspecl_then [`tenv`, `t2`, `tv2`] mp_tac bytestring_type_value >>
  simp[] >> rpt strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def, val_in_memory_def]
QED

Theorem bytestring_val_footprint_eq:
  !tenv t1 t2 tv1 tv2 v.
    is_bytestring_type t1 /\ is_bytestring_type t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ evaluate_type tenv t2 = SOME tv2 /\
    value_has_type tv1 v /\ value_has_type tv2 v ==>
    val_footprint tv1 v = val_footprint tv2 v
Proof
  rpt strip_tac >>
  qspecl_then [`tenv`, `t1`, `tv1`] mp_tac bytestring_type_value >>
  qspecl_then [`tenv`, `t2`, `tv2`] mp_tac bytestring_type_value >>
  simp[] >> rpt strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def, val_footprint_def]
QED
