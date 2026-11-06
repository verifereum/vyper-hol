(* Probe the static capacity interface separately from allocation ghost bounds. *)
Theory bodyPtrTypeBuiltinsLayoutProbe
Ancestors compileEnv exprLowering bodyPtrDefs words arithmetic

Theorem bytestring_nonzero_capacity:
  is_bytestring_type ty /\ ty <> BaseT (BytesT (Dynamic 0)) /\
  ty <> BaseT (StringT 0) ==> 64 <= type_memory_bytes cenv ty
Proof
  Cases_on `ty` >> simp[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
  simp[is_bytestring_type_def, type_memory_bytes_def]
  >- (strip_tac >> `1 <= (n+31) DIV 32` by
        (simp[arithmeticTheory.X_LE_DIV] >> decide_tac) >> decide_tac) >>
  Cases_on `b` >> simp[is_bytestring_type_def, type_memory_bytes_def] >>
  strip_tac >> `1 <= (n+31) DIV 32` by
    (simp[arithmeticTheory.X_LE_DIV] >> decide_tac) >> decide_tac
QED

Theorem ptr_covers_payload_nonwrap:
  ptr_covers G tn src s capacity /\ lookup_var src s = SOME a /\
  FLOOKUP G src = SOME (b,sz) /\ b+sz <= dimword(:256) /\ 64 <= capacity ==>
  w2n a+32 < dimword(:256)
Proof
  simp[ptr_covers_def] >> rpt strip_tac >> gvs[] >> decide_tac
QED
