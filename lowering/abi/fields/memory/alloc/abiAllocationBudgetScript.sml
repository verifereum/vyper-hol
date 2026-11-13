(* TOP-LEVEL: reserve space only for uncached allocation identities. The
   budget is conserved by allocation and reuse, including repeated loop
   iterations and duplicate identities in compiler request profiles.
   Helpers expose finite pending sets and their exact single-step change. *)
Theory abiAllocationBudget
Ancestors
  abiAllocationFrame memoryValueSnapshot venomState finite_map pred_set list arithmetic

Definition abi_alloca_pending_def:
  abi_alloca_pending ids ss = set ids DIFF FDOM ss.vs_allocas
End

Definition abi_alloca_budget_def:
  abi_alloca_budget byte_count ids ss =
    ss.vs_alloca_next + byte_count * CARD (abi_alloca_pending ids ss)
End

Theorem abi_alloca_pending_finite[simp]:
  !ids ss. FINITE (abi_alloca_pending ids ss)
Proof
  simp[abi_alloca_pending_def]
QED

Theorem abi_alloca_pending_member:
  !ids ss id. id IN abi_alloca_pending ids ss <=> MEM id ids /\ FLOOKUP ss.vs_allocas id = NONE
Proof
  simp[abi_alloca_pending_def, FLOOKUP_DEF]
QED

Theorem abi_alloca_frame_domain:
  !id byte_count ss.
    FDOM (memory_snapshot_alloc_frame id byte_count ss).vs_allocas = id INSERT FDOM ss.vs_allocas
Proof
  rpt gen_tac >> Cases_on `FLOOKUP ss.vs_allocas id = NONE`
  >- simp[memory_snapshot_alloc_frame_def] >>
  `id IN FDOM ss.vs_allocas` by fs[FLOOKUP_DEF] >>
  simp[memory_snapshot_alloc_frame_def] >> metis_tac[ABSORPTION]
QED

Theorem abi_alloca_pending_frame:
  !ids id byte_count ss.
    abi_alloca_pending ids (memory_snapshot_alloc_frame id byte_count ss) =
      abi_alloca_pending ids ss DELETE id
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_alloca_pending_def, abi_alloca_frame_domain] >> SET_TAC[]
QED

Theorem abi_alloca_pending_delete_card:
  !ids ss id.
    MEM id ids /\ FLOOKUP ss.vs_allocas id = NONE ==>
    CARD (abi_alloca_pending ids ss) = SUC (CARD (abi_alloca_pending ids ss DELETE id))
Proof
  rpt gen_tac >> strip_tac >>
  `id IN abi_alloca_pending ids ss` by simp[abi_alloca_pending_member] >>
  `abi_alloca_pending ids ss = id INSERT (abi_alloca_pending ids ss DELETE id)` by
    metis_tac[INSERT_DELETE] >>
  qpat_x_assum `abi_alloca_pending ids ss = _`
    (mp_tac o AP_TERM ``CARD:num set -> num``) >> simp[]
QED

Theorem abi_alloca_budget_frontier:
  !byte_count ids ss. ss.vs_alloca_next <= abi_alloca_budget byte_count ids ss
Proof
  simp[abi_alloca_budget_def]
QED

Theorem abi_alloca_budget_frame:
  !byte_count ids id ss.
    MEM id ids ==>
    abi_alloca_budget byte_count ids (memory_snapshot_alloc_frame id byte_count ss) =
      abi_alloca_budget byte_count ids ss
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `FLOOKUP ss.vs_allocas id = NONE`
  >- (drule_all abi_alloca_pending_delete_card >> DISCH_TAC >>
      simp_tac bool_ss [abi_alloca_budget_def, abi_alloca_pending_frame] >>
      asm_simp_tac bool_ss [memory_snapshot_alloc_frame_def, venom_state_accfupds,
        combinTheory.K_THM, MULT_CLAUSES, ADD_ASSOC]) >>
  simp[memory_snapshot_alloc_frame_def]
QED

Theorem abi_alloca_budget_nil[simp]:
  !byte_count ss. abi_alloca_budget byte_count [] ss = ss.vs_alloca_next
Proof
  simp[abi_alloca_budget_def, abi_alloca_pending_def]
QED

Theorem abi_alloca_budget_fields:
  !before after byte_count ids.
    after.vs_allocas = before.vs_allocas /\ after.vs_alloca_next = before.vs_alloca_next ==>
    abi_alloca_pending ids after = abi_alloca_pending ids before /\
    abi_alloca_budget byte_count ids after = abi_alloca_budget byte_count ids before
Proof
  simp[abi_alloca_pending_def, abi_alloca_budget_def]
QED

Theorem abi_alloca_budget_fresh:
  !byte_count ids id ss.
    MEM id ids /\ FLOOKUP ss.vs_allocas id = NONE ==>
    ss.vs_alloca_next + byte_count <= abi_alloca_budget byte_count ids ss
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`byte_count`, `ids`, `memory_snapshot_alloc_frame id byte_count ss`]
    mp_tac abi_alloca_budget_frontier >>
  `abi_alloca_budget byte_count ids (memory_snapshot_alloc_frame id byte_count ss) =
    abi_alloca_budget byte_count ids ss` by (irule abi_alloca_budget_frame >> simp[]) >>
  simp[memory_snapshot_alloc_frame_def]
QED
