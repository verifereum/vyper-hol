(* Ordinary simulations retain execution; memory simulations also retain
   the checks made with the execution's own step fuel. *)
Theory fragGasMode
Ancestors
  fragGasPath fragGasPathMem gasCount fragExec venomState list arithmetic

Definition gas_marked_path_def:
  gas_marked_path memory ctx func s n r <=>
    if memory then gas_path_mem ctx func s n r
    else gas_path ctx func s n r
End

Theorem gas_marked_path_exec:
  gas_marked_path memory ctx func s n r ==> gas_path ctx func s n r
Proof
  Cases_on `memory` >> simp[gas_marked_path_def] >>
  metis_tac[gas_path_mem_exec]
QED

Theorem gas_marked_path_from_mem:
  gas_path_mem ctx func s n r ==> gas_marked_path memory ctx func s n r
Proof
  Cases_on `memory` >> simp[gas_marked_path_def] >>
  metis_tac[gas_path_mem_exec]
QED

Theorem gas_marked_path_ok_suffix:
  gas_marked_path memory ctx func s n (OK t) ==>
  t.vs_gas_readings = DROP n s.vs_gas_readings
Proof
  strip_tac >> drule gas_marked_path_exec >> strip_tac >>
  drule gas_path_suffix >> simp[gas_count_suffix_def]
QED

Theorem gas_marked_path_then:
  gas_marked_path memory ctx func s n (OK t) /\
  gas_marked_path memory ctx func t m r ==>
  gas_marked_path memory ctx func s (n + m) r
Proof
  Cases_on `memory` >>
  PURE_REWRITE_TAC[gas_marked_path_def, COND_CLAUSES]
  >- MATCH_ACCEPT_TAC gas_path_mem_then >>
  MATCH_ACCEPT_TAC gas_path_then
QED
