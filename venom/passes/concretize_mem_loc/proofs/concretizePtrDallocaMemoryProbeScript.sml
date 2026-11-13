Theory concretizePtrDallocaMemoryProbe
Ancestors
  concretizePtrDallocaGhostInterface concretizePtrChronologicalHistory
  concretizePtrPrefixLedger ptrDiscipline pred_set

(* Fresh source allocation masks arbitrary target taint, including stale
   taint at a reused static position.  The byte relation is the retained
   activation/birth ledger, not numerical interval inversion.  Freshness
   must be supplied for this birth, not for all historical owned bytes. *)
Theorem ptr_dalloca_fresh_owner_mask:
  ptr_chrono_step C a b /\ a.po_inst.inst_opcode = ALLOCA /\
  step_inst fuel C a.po_inst a.po_state = OK post /\
  (!k x y. ptr_ledger_owned_byte registry births token aid k x y ==>
    x IN new_site_bytes a.po_state post) ==>
  !k x y. ptr_ledger_owned_byte registry births token aid k x y /\
    y IN target_mem ==> x IN b.po_taint.t_mem
Proof
  metis_tac[ptr_chrono_step_alloca]
QED
