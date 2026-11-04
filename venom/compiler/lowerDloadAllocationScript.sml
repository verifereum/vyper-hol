(* Allocation-map accounting only; byte relations and reachability are separate. *)
Theory lowerDloadAllocation
Ancestors
  lowerDloadStackBound lowerDloadRelocation venomExecSemantics finite_map
  pred_set arithmetic

Definition ld_alloc_account_def:
  ld_alloc_account keys d0 A s t <=>
    FINITE keys /\ A SUBSET keys /\ DISJOINT (FDOM s.vs_allocas) keys /\
    FDOM t.vs_allocas = FDOM s.vs_allocas UNION A /\
    t.vs_alloca_next = s.vs_alloca_next + d0 + 32 * CARD A /\
    (!id bs sz. FLOOKUP s.vs_allocas id = SOME (bs,sz) ==>
      ?e. e <= d0 + 32 * CARD A /\
          FLOOKUP t.vs_allocas id = SOME (bs+e,sz)) /\
    (!id. id IN A ==> ?b. FLOOKUP t.vs_allocas id = SOME (b,32))
End

Theorem ld_alloc_account_init:
  s.vs_allocas = FEMPTY /\ t.vs_allocas = FEMPTY /\ FINITE keys /\
  t.vs_alloca_next = s.vs_alloca_next + d0 ==>
  ld_alloc_account keys d0 {} s t
Proof
  simp[ld_alloc_account_def]
QED

Theorem ld_alloc_account_finite:
  ld_alloc_account keys d0 A s t ==> FINITE A
Proof
  simp[ld_alloc_account_def] >> metis_tac[SUBSET_FINITE]
QED

Theorem ld_alloc_account_capacity:
  ld_alloc_account keys d0 A s t ==> FINITE keys /\ A SUBSET keys
Proof
  simp[ld_alloc_account_def]
QED

Theorem ld_alloc_account_disjoint:
  ld_alloc_account keys d0 A s t ==> DISJOINT (FDOM s.vs_allocas) keys
Proof
  simp[ld_alloc_account_def]
QED

Theorem ld_alloc_account_domain:
  ld_alloc_account keys d0 A s t ==>
  FDOM t.vs_allocas = FDOM s.vs_allocas UNION A
Proof
  simp[ld_alloc_account_def]
QED

Theorem ld_alloc_account_frontier:
  ld_alloc_account keys d0 A s t ==>
  t.vs_alloca_next = s.vs_alloca_next + d0 + 32 * CARD A
Proof
  simp[ld_alloc_account_def]
QED

Theorem ld_alloc_account_old_entry:
  ld_alloc_account keys d0 A s t /\
  FLOOKUP s.vs_allocas id = SOME (bs,sz) ==>
  ?e. e <= d0 + 32 * CARD A /\
      FLOOKUP t.vs_allocas id = SOME (bs+e,sz)
Proof
  simp[ld_alloc_account_def] >> metis_tac[]
QED

Theorem ld_alloc_account_scratch_entry:
  ld_alloc_account keys d0 A s t /\ id IN A ==>
  ?b. FLOOKUP t.vs_allocas id = SOME (b,32)
Proof
  simp[ld_alloc_account_def] >> metis_tac[]
QED

Theorem ld_alloc_account_old_absent:
  ld_alloc_account keys d0 A s t /\ id NOTIN keys ==>
  (FLOOKUP s.vs_allocas id = NONE <=> FLOOKUP t.vs_allocas id = NONE)
Proof
  simp[ld_alloc_account_def, FLOOKUP_DEF] >> SET_TAC[]
QED

Theorem ld_alloc_account_scratch_absent:
  ld_alloc_account keys d0 A s t /\ id IN keys ==>
  (FLOOKUP t.vs_allocas id = NONE <=> id NOTIN A)
Proof
  simp[ld_alloc_account_def, FLOOKUP_DEF] >> SET_TAC[]
QED
