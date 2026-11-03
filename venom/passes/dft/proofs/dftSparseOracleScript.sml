Theory dftSparseOracle
Ancestors
  list pred_set words

Definition dft_sparse_oracle_def:
  dft_sparse_oracle (a:num -> 256 word) xs <=>
    !n. a n = if n < LENGTH xs then EL n xs else 0w
End

Definition dft_read_allocation_def:
  dft_read_allocation (p:num -> num option) <=>
    !i j k. p i = SOME k /\ p j = SOME k ==> i = j
End

Definition dft_allocated_value_def:
  dft_allocated_value p (xs:256 word list) n =
    case p n of NONE => 0w
    | SOME k => if k < LENGTH xs then EL k xs else 0w
End

Theorem dft_sparse_oracle_finite_support:
  (?xs. dft_sparse_oracle a xs) <=> FINITE {n | a n <> 0w}
Proof
  eq_tac
  >- (rw[dft_sparse_oracle_def, num_FINITE] >>
      qexists_tac `LENGTH xs` >> rpt strip_tac >>
      first_x_assum (qspec_then `x` mp_tac) >>
      IF_CASES_TAC >> gvs[]) >>
  rw[num_FINITE] >> qexists_tac `GENLIST a (SUC a')` >>
  simp[dft_sparse_oracle_def, EL_GENLIST] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >> decide_tac
QED

Theorem dft_allocated_value_finite_support:
  dft_read_allocation p ==>
  FINITE {n | dft_allocated_value p xs n <> 0w}
Proof
  strip_tac >>
  irule (FINITE_INJ |> INST_TYPE [beta |-> ``:num option``]) >>
  qexistsl_tac [`p`, `IMAGE SOME (count (LENGTH xs))`] >>
  simp[INJ_DEF, dft_read_allocation_def] >>
  conj_tac
  >- (rw[dft_allocated_value_def] >>
      Cases_on `p x` >> gvs[] >>
      rename1 `p x = SOME k` >> Cases_on `k < LENGTH xs` >> gvs[]) >>
  rpt strip_tac >>
  Cases_on `p x` >> gvs[dft_allocated_value_def] >>
  metis_tac[dft_read_allocation_def]
QED

Theorem dft_allocated_oracle_exists:
  dft_read_allocation p ==>
  ?ys. dft_sparse_oracle (dft_allocated_value p xs) ys
Proof
  simp[dft_sparse_oracle_finite_support, dft_allocated_value_finite_support]
QED
