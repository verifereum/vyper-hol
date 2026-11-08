Theory bodyPtrPopSupportTransfer
Ancestors pred_set arithmetic

Theorem pop_family_split_disjoint:
  i < n /\ supps i = left UNION right /\ DISJOINT left right /\
  (!j k. j < n /\ k < n /\ j <> k ==> DISJOINT (supps j) (supps k)) ==>
  (!j k. j < n /\ k < n /\ j <> k ==>
    DISJOINT (if j = i then left else supps j) (if k = i then left else supps k)) /\
  (!j. j < n ==> DISJOINT right (if j = i then left else supps j))
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >> Cases_on `j = i` >> Cases_on `k = i` >>
      gvs[] >> ASM_SET_TAC []) >>
  rpt strip_tac >> Cases_on `j = i` >> gvs[] >> ASM_SET_TAC []
QED

Theorem pop_family_transfer:
  0 < n /\ i < n /\ supps i = left UNION right /\ DISJOINT left right /\
  (!j k. j < n /\ k < n /\ j <> k ==> DISJOINT (supps j) (supps k)) ==>
  ?next.
    next 0 = (if i = 0 then left else supps 0) /\ next 1 = right /\
    (!j. 0 < j /\ j < n ==> next (SUC j) = (if j = i then left else supps j)) /\
    (!j k. j < n+1 /\ k < n+1 /\ j <> k ==> DISJOINT (next j) (next k))
Proof
  strip_tac >> drule_all pop_family_split_disjoint >> strip_tac >>
  qexists_tac `\j. if j = 1 then right else
    if (if j = 0 then 0 else PRE j) = i then left else supps (if j = 0 then 0 else PRE j)` >>
  simp[] >> rpt strip_tac >>
  Cases_on `j = 1`
  >- (gvs[] >> first_x_assum irule >> decide_tac) >>
  Cases_on `k = 1`
  >- (gvs[] >> once_rewrite_tac[DISJOINT_SYM] >> first_x_assum irule >> decide_tac) >>
  simp[] >> first_x_assum irule >> decide_tac
QED

Theorem pop_family_selected_exclusion:
  (!j k. j < n /\ k < n /\ j <> k ==> DISJOINT (supps j) (supps k)) /\
  i < n /\ j < n /\ j <> i /\ header SUBSET supps i ==>
  DISJOINT header (supps j)
Proof
  strip_tac >> `DISJOINT (supps i) (supps j)` by metis_tac[] >> ASM_SET_TAC []
QED
