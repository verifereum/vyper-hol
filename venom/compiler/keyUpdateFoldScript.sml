Theory keyUpdateFold
Ancestors
  list pair pred_set ptrDiscipline

Theorem key_update_fold_cases:
  !f m (ks:num list) X q b.
    (q,b) IN FOLDL (\Y j. key_update Y (f j) (m j)) X ks ==>
    ((q,b) IN X /\ (!j. MEM j ks ==> q <> f j)) \/
    (?j. MEM j ks /\ q = f j /\ b IN m j)
Proof
  rpt gen_tac >> qid_spec_tac `X` >> Induct_on `ks` >>
  simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >>
  simp[key_update_def, pairTheory.EXISTS_PROD] >> metis_tac[]
QED
