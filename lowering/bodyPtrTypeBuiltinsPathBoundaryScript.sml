Theory bodyPtrTypeBuiltinsPathBoundary
Ancestors fragGasPathPtr fragExec arithmetic

(* The stopping relation records first arrival by edge count, not gas count:
   normal edges may cost zero, so the latter cannot express first arrival. *)
Inductive ptr_first_arrival:
  (!D lo ctx fn PG K G tn s.
    ~s.vs_halted /\ K s ==>
    ptr_first_arrival D lo ctx fn PG K G tn s 0 G tn s) /\
  (!D lo ctx fn PG K G tn s n H ts u m G' tn' t.
    ~K s /\
    gas_path_ptr_edge D lo ctx fn PG G tn s n H ts (OK u) /\
    ptr_first_arrival D lo ctx fn PG K H ts u m G' tn' t ==>
    ptr_first_arrival D lo ctx fn PG K G tn s (n + m) G' tn' t)
End

Theorem ptr_first_arrival_erase:
  !D lo ctx fn PG K G tn s n H ts t.
    ptr_first_arrival D lo ctx fn PG K G tn s n H ts t ==>
    gas_path_ptr D lo ctx fn PG G tn s n H ts (OK t)
Proof
  ho_match_mp_tac ptr_first_arrival_ind >> rpt strip_tac
  >- (irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  irule (cj 2 gas_path_ptr_rules) >> metis_tac[]
QED

Theorem ptr_first_arrival_endpoint:
  !D lo ctx fn PG K G tn s n H ts t.
    ptr_first_arrival D lo ctx fn PG K G tn s n H ts t ==> K t
Proof
  ho_match_mp_tac ptr_first_arrival_ind >> simp[]
QED

Theorem gas_path_ptr_first_arrival_cut:
  !D lo ctx fn PG G tn s n G' tn' r.
    gas_path_ptr D lo ctx fn PG G tn s n G' tn' r ==>
    !hit t. r = OK t /\ hit t ==>
    ?u H ts k m.
      n = k + m /\
      ptr_first_arrival D lo ctx fn PG hit G tn s k H ts u /\
      gas_path_ptr D lo ctx fn PG H ts u m G' tn' (OK t)
Proof
  ho_match_mp_tac gas_path_ptr_strongind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >>
      qexistsl_tac [`s`, `G`, `tn`] >> simp[] >>
      conj_tac >- (irule (cj 1 ptr_first_arrival_rules) >> simp[]) >>
      irule (cj 1 gas_path_ptr_rules) >> simp[]) 
  >- (rpt strip_tac >> gvs[] >> Cases_on `hit s`
      >- (qexistsl_tac [`s`, `G`, `tn`, `0`, `n + n'`] >> simp[] >>
          conj_tac
          >- (irule (cj 1 ptr_first_arrival_rules) >>
              gvs[gas_path_ptr_edge_def]) >>
          irule (cj 2 gas_path_ptr_rules) >> metis_tac[]) >>
      first_x_assum (qspec_then `hit` mp_tac) >> simp[] >>
      strip_tac >>
      qexistsl_tac [`u`, `H`, `ts`, `n + k`, `m`] >>
      conj_tac >- decide_tac >>
      conj_tac >- (irule (cj 2 ptr_first_arrival_rules) >> metis_tac[]) >>
      first_assum ACCEPT_TAC) >>
  rpt strip_tac >> gvs[exit_result_def]
QED

Theorem ptr_first_arrival_compose:
  ptr_first_arrival D lo ctx fn PG hit G tn s k H ts u /\
  gas_path_ptr D lo ctx fn PG H ts u m G' tn' r ==>
  gas_path_ptr D lo ctx fn PG G tn s (k + m) G' tn' r
Proof
  strip_tac >> drule ptr_first_arrival_erase >>
  metis_tac[gas_path_ptr_then]
QED

Theorem ptr_first_arrival_initial_hit:
  ptr_first_arrival D lo ctx fn PG hit G tn s n H ts t /\ hit s ==>
  n = 0 /\ H = G /\ ts = tn /\ t = s
Proof
  once_rewrite_tac[ptr_first_arrival_cases] >> simp[] >> metis_tac[]
QED

Theorem ptr_first_arrival_nonhalted:
  !D lo ctx fn PG hit G tn s n H ts t.
    ptr_first_arrival D lo ctx fn PG hit G tn s n H ts t ==>
    ~t.vs_halted
Proof
  ho_match_mp_tac ptr_first_arrival_ind >> simp[]
QED

Theorem ptr_first_arrival_zero_suffix:
  ptr_first_arrival D lo ctx fn PG hit G tn s n H ts t ==>
  n = n + 0 /\
  ptr_first_arrival D lo ctx fn PG hit G tn s n H ts t /\
  gas_path_ptr D lo ctx fn PG H ts t 0 H ts (OK t)
Proof
  strip_tac >> simp[] >> irule (cj 1 gas_path_ptr_rules) >>
  metis_tac[ptr_first_arrival_nonhalted]
QED
