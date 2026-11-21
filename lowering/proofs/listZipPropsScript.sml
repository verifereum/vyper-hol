Theory listZipProps
Ancestors
  list

Theorem EVERY_FST_ZIP:
  !xs ys P. EVERY P xs ==> EVERY (P o FST) (ZIP (xs,ys))
Proof
  Induct >> Cases_on `ys` >> simp[ZIP_def]
QED
