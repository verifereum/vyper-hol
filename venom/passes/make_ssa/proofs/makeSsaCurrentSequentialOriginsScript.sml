Theory makeSsaCurrentSequentialOrigins
Ancestors makeSsaCurrentDynamicStores venomExecSemantics venomState finite_map list combin arithmetic

Definition current_origin_sequential_def:
  current_origin_sequential X bs = FOLDL (\Y (v,a). (v =+ a) Y) X bs
End

Definition current_origin_write_last_def:
  current_origin_write_last X n outs =
    current_origin_sequential X (current_occurrence_bindings n 0 outs)
End

Theorem current_origin_sequential_absent:
  !bs X v. ~MEM v (MAP FST bs) ==> current_origin_sequential X bs v = X v
Proof
  Induct >- simp[current_origin_sequential_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[current_origin_sequential_def] >> strip_tac >>
  first_x_assum (qspecl_then [`(h0 =+ h1) X`, `v`] mp_tac) >>
  simp[current_origin_sequential_def, APPLY_UPDATE_THM]
QED

Theorem current_occurrence_bindings_keys:
  !outs k. MAP FST (current_occurrence_bindings n k outs) = outs
Proof
  Induct >> simp[current_occurrence_bindings_def]
QED

Theorem current_origin_write_last_absent:
  ~MEM v outs ==> current_origin_write_last X n outs v = X v
Proof
  simp[current_origin_write_last_def] >> strip_tac >>
  irule current_origin_sequential_absent >> simp[current_occurrence_bindings_keys]
QED

Theorem current_origin_write_last_duplicate:
  current_origin_write_last X n [v;v] v = SOME (CurrentOccurrence n 1)
Proof
  simp[current_origin_write_last_def, current_origin_sequential_def,
       current_occurrence_bindings_def, APPLY_UPDATE_THM]
QED

Theorem current_origin_sequential_bounded:
  !bs X. current_origin_bounded q X /\
    EVERY (\b. !m k. SND b = SOME (CurrentOccurrence m k) ==> m < q) bs ==>
    current_origin_bounded q (current_origin_sequential X bs)
Proof
  Induct >- simp[current_origin_sequential_def] >>
  gen_tac >> PairCases_on `h` >> gen_tac >> strip_tac >>
  rewrite_tac[current_origin_sequential_def, FOLDL] >>
  rewrite_tac[GSYM current_origin_sequential_def] >> first_x_assum irule >>
  gvs[current_origin_sequential_def, current_origin_bounded_def, APPLY_UPDATE_THM] >>
  metis_tac[]
QED

Theorem current_origin_write_last_bounded:
  current_origin_bounded n X ==>
  current_origin_bounded (SUC n) (current_origin_write_last X n outs)
Proof
  strip_tac >> simp[current_origin_write_last_def] >>
  irule current_origin_sequential_bounded >>
  simp[current_occurrence_bindings_bounded] >>
  irule current_origin_bounded_mono >> qexists `n` >> simp[]
QED

Theorem current_origin_sequential_pointwise:
  !bs X Y v. X v = Y v ==>
    current_origin_sequential X bs v = current_origin_sequential Y bs v
Proof
  Induct >- simp[current_origin_sequential_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  rewrite_tac[current_origin_sequential_def, FOLDL] >>
  rewrite_tac[GSYM current_origin_sequential_def] >> first_x_assum irule >>
  simp[APPLY_UPDATE_THM]
QED

Theorem current_origin_sequential_snapshot:
  !bs X. ALL_DISTINCT (MAP FST bs) ==>
    current_origin_sequential X bs = current_origin_snapshot X bs
Proof
  Induct >- simp[current_origin_sequential_def, current_origin_snapshot_def, FUN_EQ_THM] >>
  gen_tac >> PairCases_on `h` >> gen_tac >> strip_tac >>
  simp[current_origin_sequential_def, current_origin_snapshot_def, FUN_EQ_THM] >>
  qx_gen_tac `v` >> Cases_on `v = h0`
  >- (gvs[] >>
      `current_origin_sequential ((h0 =+ h1) X) bs h0 = h1` by
        (irule EQ_TRANS >> qexists `((h0 =+ h1) X) h0` >>
         simp[current_origin_sequential_absent, APPLY_UPDATE_THM]) >>
      gvs[current_origin_sequential_def]) >>
  `current_origin_sequential ((h0 =+ h1) X) bs v =
   current_origin_sequential X bs v` by
    (irule current_origin_sequential_pointwise >> simp[APPLY_UPDATE_THM]) >>
  gvs[current_origin_sequential_def]
QED

Theorem current_origin_write_last_distinct:
  ALL_DISTINCT outs ==>
    current_origin_write_last X n outs = current_origin_write X n outs
Proof
  simp[current_origin_write_last_def, current_origin_write_def] >> strip_tac >>
  irule current_origin_sequential_snapshot >> simp[current_occurrence_bindings_keys]
QED

Theorem current_sequential_bind_interpretation[local]:
  !outs vals k st X.
    LENGTH outs = LENGTH vals /\
    (!v. lookup_var v st = decode (X v)) /\
    (!j. j < LENGTH outs ==>
      decode (SOME (CurrentOccurrence n (k+j))) = SOME (EL j vals)) ==>
    !v. lookup_var v
      (FOLDL (\s (out,a). update_var out a s) st (ZIP (outs,vals))) =
      decode (current_origin_sequential X (current_occurrence_bindings n k outs) v)
Proof
  Induct >- simp[current_origin_sequential_def, current_occurrence_bindings_def] >>
  gen_tac >> Cases_on `vals` >- simp[] >>
  rpt gen_tac >> strip_tac >>
  rewrite_tac[ZIP, FOLDL, current_occurrence_bindings_def,
              current_origin_sequential_def] >>
  rewrite_tac[GSYM current_origin_sequential_def] >>
  first_x_assum irule >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE, APPLY_UPDATE_THM] >>
  conj_tac
  >- (gen_tac >> Cases_on `h = v` >> gvs[lookup_var_def] >>
      first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  conj_tac >- (rpt strip_tac >> first_x_assum (qspec_then `SUC j` mp_tac) >>
    gvs[ADD_CLAUSES, ADD_COMM]) >> gvs[]
QED

Theorem current_origin_write_last_bind_outputs:
  LENGTH outs = LENGTH vals /\ bind_outputs outs vals st = SOME st' /\
  (!v. lookup_var v st = decode (X v)) /\
  (!k. k < LENGTH outs ==>
    decode (SOME (CurrentOccurrence n k)) = SOME (EL k vals)) ==>
  !v. lookup_var v st' = decode (current_origin_write_last X n outs v)
Proof
  simp[bind_outputs_def] >> strip_tac >> gvs[] >>
  simp[current_origin_write_last_def] >>
  irule current_sequential_bind_interpretation >> simp[]
QED
