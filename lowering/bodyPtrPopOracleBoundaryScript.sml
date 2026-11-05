Theory bodyPtrPopOracleBoundary
Ancestors
  extCallOracle vfmState

(* take_outcome_ordinary already supplies shared noncomputed outcomes.
   adopt_outcome_static/failed/computed and take_outcome_exhausted supply
   the retention branches. These projections expose only the new reset
   boundary; no old-store equality or global liveness is needed. *)
Theorem pop_adopt_accounts_reset:
  !rq outcome a t l.
    ~rq.cr_static /\ outcome.co_success ==>
    FST (adopt_outcome rq outcome (a,t,l)) = outcome.co_accounts
Proof
  simp[adopt_outcome_success]
QED

Theorem pop_adopt_transient_reset:
  !rq outcome a t l.
    ~rq.cr_static /\ outcome.co_success ==>
    FST (SND (adopt_outcome rq outcome (a,t,l))) = outcome.co_tStorage
Proof
  simp[adopt_outcome_success]
QED

Theorem pop_adopt_accounts_shared:
  !rq1 rq2 outcome a1 t1 l1 a2 t2 l2.
    ~rq1.cr_static /\ ~rq2.cr_static /\ outcome.co_success ==>
    FST (adopt_outcome rq1 outcome (a1,t1,l1)) =
    FST (adopt_outcome rq2 outcome (a2,t2,l2))
Proof
  simp[pop_adopt_accounts_reset]
QED

Theorem pop_adopt_transient_shared:
  !rq1 rq2 outcome a1 t1 l1 a2 t2 l2.
    ~rq1.cr_static /\ ~rq2.cr_static /\ outcome.co_success ==>
    FST (SND (adopt_outcome rq1 outcome (a1,t1,l1))) =
    FST (SND (adopt_outcome rq2 outcome (a2,t2,l2)))
Proof
  simp[pop_adopt_transient_reset]
QED

Theorem pop_adopt_storage_lookup_shared:
  !rq1 rq2 outcome a1 t1 l1 a2 t2 l2 addr k.
    ~rq1.cr_static /\ ~rq2.cr_static /\ outcome.co_success ==>
    lookup_storage k ((FST (adopt_outcome rq1 outcome (a1,t1,l1))) addr).storage =
    lookup_storage k ((FST (adopt_outcome rq2 outcome (a2,t2,l2))) addr).storage
Proof
  simp[pop_adopt_accounts_reset]
QED

Theorem pop_adopt_transient_lookup_shared:
  !rq1 rq2 outcome a1 t1 l1 a2 t2 l2 addr k.
    ~rq1.cr_static /\ ~rq2.cr_static /\ outcome.co_success ==>
    lookup_storage k ((FST (SND (adopt_outcome rq1 outcome (a1,t1,l1)))) addr) =
    lookup_storage k ((FST (SND (adopt_outcome rq2 outcome (a2,t2,l2)))) addr)
Proof
  simp[pop_adopt_transient_reset]
QED
