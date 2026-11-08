(* Right-end inversion of a counted pointer path.  Counts need not be
   positive on edges, and endpoints need not be visited for the first time. *)
Theory bodyPtrStructLitPathBoundary
Ancestors fragGasPathPtr fragExec arithmetic

Theorem gas_path_ptr_success_snoc_general[local]:
  !D lo ctx fn PG G tn s n G' tn' r.
    gas_path_ptr D lo ctx fn PG G tn s n G' tn' r ==>
    !t. r = OK t ==>
    (n = 0 /\ t = s /\ G' = G /\ tn' = tn) \/
    ?k m H u q.
      gas_path_ptr D lo ctx fn PG G tn s k H u (OK q) /\
      gas_path_ptr_edge D lo ctx fn PG H u q m G' tn' (OK t) /\
      n = k + m
Proof
  ho_match_mp_tac gas_path_ptr_ind >> rpt strip_tac >>
  gvs[exit_result_def]
  >- (disj2_tac >> qexistsl_tac [`0`, `n`, `G`, `tn`, `s`] >>
      simp[] >> irule (cj 1 gas_path_ptr_rules) >>
      gvs[gas_path_ptr_edge_def]) >>
  disj2_tac >> qexistsl_tac [`n+k`, `m`, `H`, `u`, `q`] >>
  simp[] >> once_rewrite_tac[ADD_COMM] >>
  irule (cj 2 gas_path_ptr_rules) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem gas_path_ptr_success_snoc:
  gas_path_ptr D lo ctx fn PG G tn s n G' tn' (OK t) ==>
  (n = 0 /\ t = s /\ G' = G /\ tn' = tn) \/
  ?k m H u q.
    gas_path_ptr D lo ctx fn PG G tn s k H u (OK q) /\
    gas_path_ptr_edge D lo ctx fn PG H u q m G' tn' (OK t) /\
    n = k + m
Proof
  metis_tac[gas_path_ptr_success_snoc_general]
QED
