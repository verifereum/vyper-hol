(* Composition of implicit aggregate widening. *)
Theory typeWideningComposition
Ancestors vyperTypeSystem

Theorem arg_type_fits_trans_joint[local]:
  (!s a. arg_type_fits s a ==> !d. arg_type_fits a d ==> arg_type_fits s d) /\
  (!ss aa. arg_types_fit ss aa ==> !dd. arg_types_fit aa dd ==> arg_types_fit ss dd)
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rw[arg_type_fits_def] >> gvs[arg_type_fits_def]
  >- (Cases_on `d` >> gvs[arg_type_fits_def] >>
      rename1 `BaseT b` >> Cases_on `b` >> gvs[arg_type_fits_def])
  >- (Cases_on `d` >> gvs[arg_type_fits_def] >>
      rename1 `BaseT b` >> Cases_on `b` >> gvs[arg_type_fits_def] >>
      qmatch_goalsub_rename_tac `arg_type_fits _ (BaseT (BytesT bound))` >> Cases_on `bound` >> gvs[arg_type_fits_def])
  >- (Cases_on `d` >> gvs[arg_type_fits_def] >>
      qmatch_goalsub_rename_tac `arg_type_fits _ (ArrayT _ bound)` >> Cases_on `bound` >> gvs[arg_type_fits_def])
  >- (Cases_on `d` >> gvs[arg_type_fits_def] >>
      qmatch_goalsub_rename_tac `arg_type_fits _ (ArrayT _ bound)` >> Cases_on `bound` >> gvs[arg_type_fits_def])
  >- (Cases_on `d` >> gvs[arg_type_fits_def]) >>
  Cases_on `dd` >> gvs[arg_type_fits_def]
QED

Theorem type_widens_to_trans:
  !tenv s a d. type_widens_to tenv s a /\ type_widens_to tenv a d ==>
    type_widens_to tenv s d
Proof
  rw[type_widens_to_def] >> metis_tac[arg_type_fits_trans_joint]
QED
