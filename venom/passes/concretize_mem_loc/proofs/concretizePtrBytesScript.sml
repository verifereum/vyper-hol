(* Protected byte agreement independent of allocation injectivity. *)
Theory concretizePtrBytes
Ancestors
  codegenRel pred_set

Definition ptr_bytes_agree_def:
  ptr_bytes_agree (live:num set) (rho:num -> num) m mt <=>
    !i. i IN live ==> read_byte i m = read_byte (rho i) mt
End

Theorem ptr_bytes_agree_restrict:
  !rho. ptr_bytes_agree live rho m mt /\ live' SUBSET live ==>
  ptr_bytes_agree live' rho m mt
Proof
  simp[ptr_bytes_agree_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ptr_bytes_agree_read:
  !rho. ptr_bytes_agree live rho m mt /\ i IN live ==>
  read_byte i m = read_byte (rho i) mt
Proof
  simp[ptr_bytes_agree_def]
QED

Theorem ptr_bytes_agree_write:
  !rho. ptr_bytes_agree live rho m mt /\
  (!i. i IN live ==> (i IN ws <=> rho i IN wt)) /\
  (!i. i IN live /\ i IN ws ==> read_byte i m' = read_byte (rho i) mt') /\
  (!i. ~(i IN ws) ==> read_byte i m' = read_byte i m) /\
  (!j. ~(j IN wt) ==> read_byte j mt' = read_byte j mt) ==>
  ptr_bytes_agree live rho m' mt'
Proof
  simp[ptr_bytes_agree_def] >> rpt strip_tac >>
  Cases_on `i IN ws` >> metis_tac[]
QED

Theorem ptr_bytes_agree_unwritten:
  !rho. ptr_bytes_agree live rho m mt /\
  DISJOINT live ws /\ DISJOINT (IMAGE rho live) wt /\
  (!i. ~(i IN ws) ==> read_byte i m' = read_byte i m) /\
  (!j. ~(j IN wt) ==> read_byte j mt' = read_byte j mt) ==>
  ptr_bytes_agree live rho m' mt'
Proof
  rpt strip_tac >> irule ptr_bytes_agree_write >>
  qexistsl_tac [`m`, `mt`, `ws`, `wt`] >>
  gvs[DISJOINT_DEF, EXTENSION, IN_IMAGE] >> metis_tac[]
QED
