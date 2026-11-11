(* TOP-LEVEL: basic compatibility facts shared by recursive copy and Log
   proofs, independently of any particular lowering entry point. *)
Theory typedCopyCompatibility
Ancestors
  vyperEventArgCompat
  vyperTypeSystem list

Theorem event_arg_compatible_reflexive:
  (!fty aty. fty = aty ==> event_arg_compatible fty aty) /\
  (!fts ats. fts = ats ==> event_arg_compatible_list fts ats)
Proof
  ho_match_mp_tac event_arg_compatible_ind >> rw[event_arg_compatible_def] >> gvs[]
QED

Theorem arg_type_fits_trans:
  (!a b. !c. arg_type_fits a b /\ arg_type_fits b c ==> arg_type_fits a c) /\
  (!as_ bs. !cs. arg_types_fit as_ bs /\ arg_types_fit bs cs ==>
    arg_types_fit as_ cs)
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rw[arg_type_fits_def]
  >- (Cases_on `c` >> gvs[arg_type_fits_def] >>
      rename1 `arg_type_fits _ (BaseT bt)` >> Cases_on `bt` >> gvs[arg_type_fits_def])
  >- (Cases_on `c` >> gvs[arg_type_fits_def] >>
      rename1 `arg_type_fits _ (BaseT bt)` >> Cases_on `bt` >> gvs[arg_type_fits_def] >>
      rename1 `arg_type_fits _ (BaseT (BytesT bd))` >> Cases_on `bd` >> gvs[arg_type_fits_def])
  >- (Cases_on `c` >> gvs[arg_type_fits_def] >>
      rename1 `arg_type_fits _ (ArrayT ct bd)` >> Cases_on `bd` >> gvs[arg_type_fits_def] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS])
  >- (Cases_on `c` >> gvs[arg_type_fits_def] >>
      rename1 `arg_type_fits _ (ArrayT ct bd)` >> Cases_on `bd` >> gvs[arg_type_fits_def] >>
      metis_tac[])
  >- (Cases_on `c` >> gvs[arg_type_fits_def] >> metis_tac[])
  >> Cases_on `cs` >> gvs[arg_type_fits_def] >> metis_tac[]
QED

Theorem type_widens_to_trans:
  type_widens_to tenv a b /\ type_widens_to tenv b c ==>
  type_widens_to tenv a c
Proof
  simp[type_widens_to_def] >> metis_tac[arg_type_fits_trans]
QED
