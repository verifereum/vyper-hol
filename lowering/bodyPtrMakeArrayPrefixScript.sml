(* A prefix may contain tainted dead bytes.  The source slot taint is
   fixed; only its one-way image in the copied prefix is constrained. *)
Theory bodyPtrMakeArrayPrefix
Ancestors ptrDiscipline words arithmetic pred_set

Theorem copied_prefix_taint_empty:
  !i j. i < 0 /\ j < 32 /\ b+32*i+j IN tainted ==>
    j IN key_taint keys (a+n2w i)
Proof
  simp[]
QED

Theorem copied_prefix_taint_transport:
  (!i j. i < k /\ j < 32 /\ b+32*i+j IN tainted ==>
    j IN key_taint keys (a+n2w i)) /\ tainted' = tainted ==>
  (!i j. i < k /\ j < 32 /\ b+32*i+j IN tainted' ==>
    j IN key_taint keys (a+n2w i))
Proof
  simp[]
QED

Theorem copied_prefix_taint_extend:
  (!i j. i < k /\ j < 32 /\ b+32*i+j IN tainted ==>
    j IN key_taint keys (a+n2w i)) /\
  loaded SUBSET key_taint keys (a+n2w k) /\
  tainted' =
    (tainted DIFF {x | b+32*k <= x /\ x < b+32*k+32}) UNION
    {b+32*k+j | j IN loaded} ==>
  (!i j. i < k+1 /\ j < 32 /\ b+32*i+j IN tainted' ==>
    j IN key_taint keys (a+n2w i))
Proof
  rpt strip_tac >>
  `!j. j IN loaded ==> j < 32` by
    (gvs[SUBSET_DEF, key_taint_def] >> metis_tac[]) >>
  Cases_on `i < k`
  >- (`b+32*i+j IN tainted` by
        (gvs[] >> gvs[IN_UNION, IN_DIFF] >>
         `k <= i` by decide_tac >> decide_tac) >>
      metis_tac[]) >>
  `i = k` by decide_tac >> gvs[] >>
  `j IN loaded` by
    (gvs[IN_UNION, IN_DIFF] >> metis_tac[ADD_ASSOC, EQ_ADD_LCANCEL]) >>
  gvs[SUBSET_DEF] >> metis_tac[]
QED
