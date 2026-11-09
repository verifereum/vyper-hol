(* Finite iteration with invariant and memory-safe reachability at one endpoint. *)
Theory finiteIterationMemory
Ancestors fragGasPathMem venomState arithmetic

Theorem gas_path_mem_finite_iteration:
  !N k Inv ctx func s.
  (!i u. i < N /\ Inv i u ==>
    ?v. gas_path_mem ctx func u 0 (OK v) /\ Inv (SUC i) v) /\
  (!i u. i <= N /\ Inv i u ==> ~u.vs_halted) /\
  k <= N /\ Inv k s ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\ Inv N t
Proof
  completeInduct_on `N-k` >> rpt strip_tac >>
  Cases_on `k = N`
  >- (gvs[] >> qexists_tac `s` >> simp[] >>
      irule (cj 1 gas_path_mem_rules) >>
      first_x_assum irule >> qexists_tac `N` >> simp[]) >>
  `k < N` by decide_tac >>
  `?v. gas_path_mem ctx func s 0 (OK v) /\ Inv (SUC k) v` by metis_tac[] >>
  rename1 `Inv (SUC k) next` >>
  `?t. gas_path_mem ctx func next 0 (OK t) /\ Inv N t` by
    (qpat_x_assum `!m. m < _ ==> _` (qspec_then `N - SUC k` mp_tac) >>
     (impl_tac >- decide_tac) >>
     disch_then (qspecl_then [`N`, `SUC k`] mp_tac) >>
     simp[] >> disch_then irule >> gvs[] >> first_assum ACCEPT_TAC) >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES]
QED

Theorem gas_path_mem_finite_iteration_exit:
  (!i u. i < N /\ Inv i u ==>
    ?v. gas_path_mem ctx func u 0 (OK v) /\ Inv (SUC i) v) /\
  (!i u. i <= N /\ Inv i u ==> ~u.vs_halted) /\
  (!u. Inv N u ==> ?v. gas_path_mem ctx func u 0 (OK v) /\ Q v) /\
  k <= N /\ Inv k s ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\ Q t
Proof
  strip_tac >> drule_all gas_path_mem_finite_iteration >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES]
QED
