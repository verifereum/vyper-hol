(* Unequal compatible layouts select recursive typed-copy branches. *)
Theory bodyPtrWideningDispatch
Ancestors
  vyperTypeSystem context compileEnv

Theorem arg_type_fits_unequal_dispatch:
  !sty dty. arg_type_fits sty dty /\ sty <> dty ==>
    (is_bytestring_type sty /\ is_bytestring_type dty) \/
    (?s d n m. sty = ArrayT s (Dynamic n) /\ dty = ArrayT d (Dynamic m) /\
       n <= m /\ arg_type_fits s d) \/
    (?s d n. sty = ArrayT s (Fixed n) /\ dty = ArrayT d (Fixed n) /\
       arg_type_fits s d) \/
    (?ss ds. sty = TupleT ss /\ dty = TupleT ds /\ arg_types_fit ss ds)
Proof
  Cases_on `sty` >> Cases_on `dty` >>
  simp[arg_type_fits_def, is_bytestring_type_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `b` >> Cases_on `b'` >>
      gvs[arg_type_fits_def, is_bytestring_type_def] >>
      rename1 `BytesT bound` >> Cases_on `bound` >>
      gvs[arg_type_fits_def, is_bytestring_type_def] >>
      Cases_on `b` >> gvs[arg_type_fits_def, is_bytestring_type_def])
  >- (Cases_on `b` >> Cases_on `b'` >>
      gvs[arg_type_fits_def, is_bytestring_type_def] >>
      rename1 `BytesT bound` >> Cases_on `bound` >>
      gvs[arg_type_fits_def, is_bytestring_type_def] >>
      Cases_on `b` >> gvs[arg_type_fits_def, is_bytestring_type_def])
  >> Cases_on `b` >> Cases_on `b'` >> gvs[arg_type_fits_def]
QED
