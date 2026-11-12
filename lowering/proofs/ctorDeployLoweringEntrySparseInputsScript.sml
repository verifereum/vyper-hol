Theory ctorDeployLoweringEntrySparseInputs
Ancestors
 vyperValue vyperTyping vyperTypeValues sorting alist list arithmetic combin

Theorem deploy_enumerate_dense_sparse:
 !n k (sparse : (num # 'a) list) d.
 SORTED $< (MAP FST sparse) /\
 (!j v. MEM (j,v) sparse ==> k <= j /\ j < k+n /\ v <> d) ==>
 enumerate_static_array d k
  (GENLIST (\i. case ALOOKUP sparse (k+i) of SOME v => v | NONE => d) n) = sparse
Proof
 Induct
 >- (rpt strip_tac >> Cases_on `sparse` >> simp[enumerate_static_array_def] >>
     PairCases_on `h` >>
     first_x_assum (qspecl_then [`h0`, `h1`] mp_tac) >>
     impl_tac >- simp[] >> strip_tac >> gvs[]) >>
 rpt strip_tac >> simp[GENLIST_CONS, enumerate_static_array_def] >>
 Cases_on `ALOOKUP sparse k`
 >- (simp[] >>
     `(\i. case ALOOKUP sparse (i+k) of NONE => d | SOME v => v) o SUC =
      (\i. case ALOOKUP sparse (SUC k+i) of NONE => d | SOME v => v)` by
       simp[FUN_EQ_THM, o_THM, ADD_CLAUSES] >>
     pop_assum SUBST1_TAC >> first_x_assum irule >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
     `j <> k` suffices_by simp[] >> CCONTR_TAC >> gvs[] >>
     qpat_x_assum `ALOOKUP _ _ = NONE` mp_tac >> simp[ALOOKUP_FAILS] >>
     qexists_tac `v` >> simp[]) >>
 rename1 `ALOOKUP sparse k = SOME v0` >>
 Cases_on `sparse` >> gvs[] >> PairCases_on `h` >> gvs[] >>
 `h0 = k` by
   (CCONTR_TAC >>
    `k <= h0` by (first_x_assum (qspecl_then [`h0`, `h1`] mp_tac) >> simp[]) >>
    `ALOOKUP t k = SOME v0` by gvs[] >>
    drule ALOOKUP_MEM >> strip_tac >> fs[less_sorted_eq] >>
    `MEM k (MAP FST t)` by (rw[MEM_MAP] >> qexists_tac `(k,v0)` >> simp[]) >>
    res_tac >> gvs[]) >>
 gvs[] >>
 `(\i. case if i = 0 then SOME h1 else ALOOKUP t (h0+i) of
         NONE => d | SOME v => v) o SUC =
  (\i. case ALOOKUP t (SUC h0+i) of NONE => d | SOME v => v)` by
    simp[FUN_EQ_THM, o_THM, ADD_CLAUSES] >>
 pop_assum SUBST1_TAC >>
 `enumerate_static_array d (SUC h0)
   (GENLIST (\i. case ALOOKUP t (i+SUC h0) of NONE => d | SOME v => v) n) = t`
   suffices_by simp[Once ADD_COMM] >>
 first_x_assum irule >> gvs[less_sorted_eq] >> rpt strip_tac >>
 first_x_assum (qspecl_then [`j`, `v`] mp_tac) >> simp[] >> strip_tac >>
 `MEM j (MAP FST t)` by (rw[MEM_MAP] >> qexists_tac `(j,v)` >> simp[]) >>
 res_tac >> simp[]
QED

Theorem deploy_sparse_has_type_members[local]:
 !sparse tv n. sparse_has_type tv n sparse ==>
 !j v. MEM (j,v) sparse ==> j < n /\ v <> default_value tv
Proof
 Induct >> simp[value_has_type_def] >> Cases_on `h` >>
 simp[value_has_type_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem deploy_typed_sparse_reconstruction:
 !tv n sparse.
 SORTED $< (MAP FST sparse) /\ sparse_has_type tv n sparse ==>
 enumerate_static_array (default_value tv) 0
  (GENLIST (\i. case ALOOKUP sparse i of
                  SOME v => v | NONE => default_value tv) n) = sparse
Proof
 rpt strip_tac >>
 drule deploy_sparse_has_type_members >> strip_tac >>
 qspecl_then [`n`, `0`, `sparse`, `default_value tv`] mp_tac
   deploy_enumerate_dense_sparse >> simp[] >> metis_tac[]
QED
