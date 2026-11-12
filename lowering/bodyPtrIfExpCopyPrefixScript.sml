Theory bodyPtrIfExpCopyPrefix
Ancestors valueEncodingProps venomState pred_set arithmetic

Theorem ifexp_copy_word_prefix_store:
  (!i. i < k ==> mem_word_at (b+32*i) s.vs_memory = copied_word i) ==>
  !i. i < SUC k ==>
    mem_word_at (b+32*i) (mstore (b+32*k) (copied_word k) s).vs_memory = copied_word i
Proof
  rpt strip_tac >> Cases_on `i = k`
  >- gvs[mstore_mem_word_at_same] >>
  `i < k` by decide_tac >>
  `b+32*i+32 <= b+32*k` by decide_tac >>
  simp[mstore_mem_word_at_disjoint]
QED

Theorem ifexp_copy_taint_prefix_store:
  !T T' V X b k.
  (!i j. i < k /\ j < 32 /\ b+32*i+j IN T ==> (i,j) IN X) /\
  (!j. j IN V ==> (k,j) IN X) /\
  T' = (T DIFF {x | b+32*k <= x /\ x < b+32*k+32}) UNION
       {b+32*k+j | j IN V} ==>
  !i j. i < SUC k /\ j < 32 /\ b+32*i+j IN T' ==> (i,j) IN X
Proof
  simp[EXTENSION, IN_DIFF, IN_UNION, GSPECIFICATION] >>
  rpt strip_tac
  >- (`i < k` by decide_tac >> metis_tac[]) >>
  `i = k` by decide_tac >> gvs[]
QED
