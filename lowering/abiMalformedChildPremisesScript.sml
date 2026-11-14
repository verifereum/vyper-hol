(* Parent resource bounds descend only to children which are actually used. *)
Theory abiMalformedChildPremises
Ancestors
  abiMalformedConstructorInduction vyperTypeSystem valueEncoding list arithmetic words

Theorem abi_malformed_list_size_bounds:
  !tvs. type_memory_size_list tvs < limit ==>
    EVERY (\tv. type_memory_size tv < limit) tvs
Proof
  Induct >> simp[type_memory_size_def]
QED

Theorem abi_malformed_array_child_bound:
  assignable_type env (ArrayT ty bound) /\
  type_memory_size (ArrayTV tv bound) < limit /\
  0 < (case bound of Fixed n => n | Dynamic n => n) ==>
  assignable_type env ty /\ type_memory_size tv < limit
Proof
  strip_tac >> conj_tac >- fs[assignable_type_def] >>
  `type_memory_size tv <= (case bound of Fixed n => n | Dynamic n => n) * type_memory_size tv` by
    (Cases_on `(case bound of Fixed n => n | Dynamic n => n)` >> fs[MULT_CLAUSES]) >>
  `type_memory_size tv <= type_memory_size (ArrayTV tv bound)` by
    (irule LESS_EQ_TRANS >>
     qexists_tac `(case bound of Fixed n => n | Dynamic n => n) * type_memory_size tv` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     Cases_on `bound` >> simp[type_memory_size_def]) >>
  metis_tac[LESS_EQ_LESS_TRANS]
QED
