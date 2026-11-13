(* Widening composes across a physical return and its annotated result. *)
Theory typeWideningTrans
Ancestors vyperTypeArgFits vyperTypeSystem arithmetic

Theorem type_widens_to_trans:
  !tenv a b c.
    type_widens_to tenv a b /\ type_widens_to tenv b c ==>
    type_widens_to tenv a c
Proof
  `(!a b. arg_type_fits a b ==> !c.
      arg_type_fits b c ==> arg_type_fits a c) /\
   (!as_ bs. arg_types_fit as_ bs ==> !cs.
      arg_types_fit bs cs ==> arg_types_fit as_ cs)` by
    (ho_match_mp_tac arg_type_fits_ind >> rw[arg_type_fits_def]
     >- (Cases_on `c` >> gvs[arg_type_fits_def] >>
         rename1 `arg_type_fits _ (BaseT bt)` >>
         Cases_on `bt` >> gvs[arg_type_fits_def] >> decide_tac)
     >- (Cases_on `c` >> gvs[arg_type_fits_def] >>
         rename1 `arg_type_fits _ (BaseT bt)` >>
         Cases_on `bt` >> gvs[arg_type_fits_def] >>
         rename1 `arg_type_fits _ (BaseT (BytesT bd))` >>
         Cases_on `bd` >> gvs[arg_type_fits_def] >> decide_tac)
     >- (Cases_on `c` >> gvs[arg_type_fits_def] >>
         rename1 `arg_type_fits _ (ArrayT ct bd)` >>
         Cases_on `bd` >> gvs[arg_type_fits_def] >>
         metis_tac[LESS_EQ_TRANS])
     >- (Cases_on `c` >> gvs[arg_type_fits_def] >>
         rename1 `arg_type_fits _ (ArrayT ct bd)` >>
         Cases_on `bd` >> gvs[arg_type_fits_def] >> metis_tac[])
     >- (Cases_on `c` >> gvs[arg_type_fits_def] >> metis_tac[]) >>
     Cases_on `cs` >> gvs[arg_type_fits_def] >> metis_tac[]) >>
  rw[type_widens_to_def] >> metis_tac[]
QED
