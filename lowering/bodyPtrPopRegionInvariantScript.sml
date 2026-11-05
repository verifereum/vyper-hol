Theory bodyPtrPopRegionInvariant
Ancestors
  bodyPtrDefs compileEnv pred_set

(* A fixed captured child needs an observer separate from global liveness:
   after ancestor shortening stor_taint_ok no longer constrains that child.
   Parameterizing the backend byte set avoids storage/transient duplication.
   This definition asserts no operational preservation by itself. *)
Definition pop_region_taint_ok_def:
  pop_region_taint_ok st base tv (X : (bytes32 # num) set) <=>
    !k b. (k,b) IN X /\ base <= w2n k /\
          w2n k < base + type_slot_size tv /\ b < 32 ==>
          dead_bytes st base tv (w2n k) b
End

Theorem pop_region_taint_entry:
  storage_read_live cx tr st w tv /\
  (!k b. (k,b) IN X ==> storage_dead cx tr st (w2n k) b) ==>
  pop_region_taint_ok st (w2n w) tv X
Proof
  simp[pop_region_taint_ok_def, storage_read_live_def] >> metis_tac[]
QED

Theorem pop_region_taint_storage_entry:
  stor_taint_ok cx tn s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
  storage_read_live cx F (s.vs_accounts cx.txn.target).storage w tv ==>
  pop_region_taint_ok (s.vs_accounts cx.txn.target).storage
    (w2n w) tv tn.t_stor
Proof
  strip_tac >> irule pop_region_taint_entry >>
  qexistsl [`cx`,`F`] >>
  gvs[stor_taint_ok_def, cx_dead_def, SUBSET_DEF] >> metis_tac[pairTheory.PAIR_EQ]
QED

Theorem pop_region_taint_transient_entry:
  stor_taint_ok cx tn s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
  storage_read_live cx T (s.vs_transient cx.txn.target) w tv ==>
  pop_region_taint_ok (s.vs_transient cx.txn.target)
    (w2n w) tv tn.t_trans
Proof
  strip_tac >> irule pop_region_taint_entry >>
  qexistsl [`cx`,`T`] >>
  gvs[stor_taint_ok_def, cx_dead_def, SUBSET_DEF] >> metis_tac[pairTheory.PAIR_EQ]
QED
