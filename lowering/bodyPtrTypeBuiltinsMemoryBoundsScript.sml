Theory bodyPtrTypeBuiltinsMemoryBounds
Ancestors compileEnv allocLimits exprSimHyps valueTypingMemoryProps
  vyperTypeSystem words valueCopyBytes

Theorem bytestring_memory_header_bound:
  is_bytestring_type t ==> 32 <= type_memory_bytes cenv t
Proof
  Cases_on `t` >> simp[is_bytestring_type_def] >>
  rename1 `BaseT b` >> Cases_on `b` >> simp[is_bytestring_type_def, type_memory_bytes_def] >>
  rename1 `BytesT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def, type_memory_bytes_def]
QED

Theorem bytestring_alloc_word_bound:
  type_alloc_ok cenv t /\ is_bytestring_type t ==>
  type_memory_bytes cenv t < dimword(:256)
Proof
  strip_tac >> `~is_word_type t` by metis_tac[is_bytestring_word_type] >>
  fs[type_alloc_ok_def, wordsTheory.dimword_def]
QED

Theorem bytestring_alloc_capacity_bound:
  type_alloc_ok cenv t ==>
  !n. t = BaseT (BytesT (Dynamic n)) \/ t = BaseT (StringT n) ==>
    n < dimword(:256)
Proof
  rpt strip_tac >> gvs[type_alloc_ok_def, is_word_type_def, type_memory_bytes_def,
    wordsTheory.dimword_def] >>
  qspec_then `n` mp_tac word_size_capacity >>
  simp[vfmConstantsTheory.word_size_def] >> decide_tac
QED
