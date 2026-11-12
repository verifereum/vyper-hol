Theory bodyPtrIfExpPathInversion
Ancestors fragGasPathPtr

(* Gas zero does not force the reflexive branch: edges may cost zero. *)
Theorem gas_path_ptr_first_edge:
  !D lo ctx fn PG G tn s n G' tn' r.
    gas_path_ptr D lo ctx fn PG G tn s n G' tn' r ==>
    (n = 0 /\ G' = G /\ tn' = tn /\ r = OK s /\ ~s.vs_halted) \/
    (?k H u t m.
      gas_path_ptr_edge D lo ctx fn PG G tn s k H u (OK t) /\
      gas_path_ptr D lo ctx fn PG H u t m G' tn' r /\ n = k + m) \/
    (gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' r /\ exit_result r)
Proof
  rpt gen_tac >> strip_tac >>
  dxrule (iffLR gas_path_ptr_cases) >> metis_tac[]
QED

Theorem gas_path_ptr_first_edge_ok:
  !D lo ctx fn PG G tn s n G' tn' t.
    gas_path_ptr D lo ctx fn PG G tn s n G' tn' (OK t) ==>
    (n = 0 /\ G' = G /\ tn' = tn /\ t = s /\ ~s.vs_halted) \/
    (?k H u mid m.
      gas_path_ptr_edge D lo ctx fn PG G tn s k H u (OK mid) /\
      gas_path_ptr D lo ctx fn PG H u mid m G' tn' (OK t) /\ n = k + m)
Proof
  rpt gen_tac >> disch_then (mp_tac o MATCH_MP gas_path_ptr_first_edge) >>
  simp[fragExecTheory.exit_result_def] >> metis_tac[]
QED
