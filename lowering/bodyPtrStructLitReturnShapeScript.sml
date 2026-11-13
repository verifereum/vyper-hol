Theory bodyPtrStructLitReturnShape
Ancestors supportedTypes supportedDecls exprLowering compileEnv list

Theorem structlit_supported_scalar_shape:
  !ty. supported_scalar_type ty <=>
    supported_word_type ty \/ (?n. ty = BaseT (StringT n)) \/
    (?n. ty = BaseT (BytesT (Dynamic n)))
Proof
  Cases >> simp[supported_scalar_type_def, supported_string_type_def] >>
  Cases_on `b` >> simp[supported_string_type_def] >>
  Cases_on `b'` >> simp[supported_string_type_def]
QED

Theorem structlit_supported_value_shape:
  !tops ty. supported_value_type tops ty ==>
    supported_word_type ty \/
    (?n. ty = BaseT (StringT n)) \/
    (?n. ty = BaseT (BytesT (Dynamic n))) \/
    (?ts. ty = TupleT ts /\ ~NULL ts /\
      EVERY (\t. supported_word_type t \/ (?n. t = BaseT (StringT n)) \/
        (?n. t = BaseT (BytesT (Dynamic n)))) ts) \/
    (?elem n. ty = ArrayT elem (Fixed n) /\ supported_word_type elem /\ 0 < n) \/
    (?elem n. ty = ArrayT elem (Dynamic n) /\ supported_word_type elem) \/
    (?id fields. ty = StructT id /\
      supported_struct_fields tops id = SOME fields /\
      EVERY (supported_word_type o SND) fields)
Proof
  rpt gen_tac >> Cases_on `ty` >>
  simp[supported_value_type_def, structlit_supported_scalar_shape,
       supported_word_type_def] >>
  rpt strip_tac
  >- gvs[EVERY_MEM, structlit_supported_scalar_shape]
  >- (Cases_on `b` >> gvs[])
  >> Cases_on `supported_struct_fields tops p` >> gvs[]
QED

Theorem structlit_supported_internal_return_shape:
  !tops ty. supported_function_return tops Internal ty ==>
    ty = NoneT \/ supported_word_type ty \/
    (?n. ty = BaseT (StringT n)) \/
    (?n. ty = BaseT (BytesT (Dynamic n))) \/
    (?ts. ty = TupleT ts /\ ~NULL ts /\
      EVERY (\t. supported_word_type t \/ (?n. t = BaseT (StringT n)) \/
        (?n. t = BaseT (BytesT (Dynamic n)))) ts) \/
    (?elem n. ty = ArrayT elem (Fixed n) /\ supported_word_type elem /\ 0 < n) \/
    (?elem n. ty = ArrayT elem (Dynamic n) /\ supported_word_type elem) \/
    (?id fields. ty = StructT id /\
      supported_struct_fields tops id = SOME fields /\
      EVERY (supported_word_type o SND) fields)
Proof
  simp[supported_function_return_def, supported_return_type_def] >>
  rpt gen_tac >> strip_tac >- simp[] >>
  disj2_tac >> irule structlit_supported_value_shape >> simp[]
QED

Theorem structlit_supported_lowered_call_shape:
  !tops cenv fid ann args d ty.
    supported_function_return tops Internal
      (cenv.ce_func_return_type (nsid_to_string fid)) /\
    ty = lowered_value_type cenv (Call ann (IntCall fid) args d) ==>
    ty = NoneT \/ supported_word_type ty \/
    (?n. ty = BaseT (StringT n)) \/
    (?n. ty = BaseT (BytesT (Dynamic n))) \/
    (?ts. ty = TupleT ts /\ ~NULL ts /\
      EVERY (\t. supported_word_type t \/ (?n. t = BaseT (StringT n)) \/
        (?n. t = BaseT (BytesT (Dynamic n)))) ts) \/
    (?elem n. ty = ArrayT elem (Fixed n) /\ supported_word_type elem /\ 0 < n) \/
    (?elem n. ty = ArrayT elem (Dynamic n) /\ supported_word_type elem) \/
    (?id fields. ty = StructT id /\
      supported_struct_fields tops id = SOME fields /\
      EVERY (supported_word_type o SND) fields)
Proof
  rpt strip_tac >> gvs[lowered_value_type_def] >>
  irule structlit_supported_internal_return_shape >> simp[]
QED
