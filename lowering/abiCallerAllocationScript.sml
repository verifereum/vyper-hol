(* Allocation-history consequences for live source and output buffers.
   TOP-LEVEL: abi_caller_allocation_scratch and abi_caller_allocation_frame
   establish precise scratch separation from the ordinary allocator invariant.
   Numeric allocation credit and ownership of instruction sites are separate. *)
Theory abiCallerAllocation
Ancestors
  abiDecoderFootprint abiDecoderFrame abiDecoderAllocation venomMemDefs
  venomState finite_map pred_set list arithmetic words

Theorem abi_caller_allocation_end:
  alloca_inv s /\ FLOOKUP s.vs_allocas live = SOME (loff,len) /\
  p + n <= loff + len ==>
  p + n <= s.vs_alloca_next
Proof
  simp_tac bool_ss [alloca_inv_def, alloca_next_valid_def] >>
  rpt strip_tac >>
  qpat_x_assum `!aid base sz. _` drule >> strip_tac >> decide_tac
QED

Theorem abi_caller_allocation_separate:
  alloca_inv s /\ FLOOKUP s.vs_allocas live = SOME (loff,len) /\
  FLOOKUP s.vs_allocas site = SOME (q,sz) /\ live <> site ==>
  loff + len <= q \/ q + sz <= loff
Proof
  metis_tac[alloca_inv_def, allocas_non_overlapping_def]
QED

Theorem abi_caller_allocation_scratch:
  alloca_inv s /\ FLOOKUP s.vs_allocas live = SOME (loff,len) /\
  loff <= p /\ p + n <= loff + len /\
  FINITE ids /\ ~(live IN ids) /\ s.vs_alloca_next <= b + cap ==>
  abi_footprint_disjoint p n (abi_decoder_child_scratch ids b cap s)
Proof
  strip_tac >> drule_all abi_caller_allocation_end >> strip_tac >>
  irule abi_decoder_child_scratch_disjoint >> asm_simp_tac (srw_ss()) [] >>
  rpt gen_tac >> strip_tac >>
  rename1 `FLOOKUP s.vs_allocas id = SOME (q,sz)` >>
  `live <> id` by metis_tac[] >>
  drule_all abi_caller_allocation_separate >> strip_tac >> decide_tac
QED

Theorem abi_caller_allocation_frame:
  alloca_inv s /\ FLOOKUP s.vs_allocas live = SOME (loff,len) /\
  loff <= p /\ p + n <= loff + len /\
  FINITE ids /\ ~(live IN ids) /\ s.vs_alloca_next <= b + cap /\
  abi_decode_footprint_frame (abi_decoder_child_scratch ids b cap s) s t ==>
  mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory
Proof
  strip_tac >> drule_all abi_caller_allocation_scratch >> strip_tac >>
  drule_all abi_decode_footprint_frame_slice >> simp[]
QED

(* Pairwise separation and the frontier bound follow from alloca_inv.
   Remaining premises describe scratch sizes, the envelope and fresh credit. *)
Theorem abi_caller_allocation_budget:
  alloca_inv s /\ b + cap < dimword (:256) /\ b <= s.vs_alloca_next /\
  s.vs_alloca_next + 32 * CARD (abi_decoder_missing first last s) <= b + cap /\
  (!id off sz. id IN abi_decoder_ids first last /\
    FLOOKUP s.vs_allocas id = SOME (off,sz) ==> sz = 32 /\ b <= off) ==>
  abi_decoder_budget first last b cap s
Proof
  simp_tac bool_ss [abi_decoder_budget_def, alloca_inv_def,
    alloca_next_valid_def, allocas_non_overlapping_def] >>
  rpt strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  metis_tac[]
QED

Theorem abi_caller_allocation_budget_zero:
  alloca_inv s /\
  s.vs_alloca_next + 32 * CARD (abi_decoder_missing first last s) < dimword (:256) /\
  (!id off sz. id IN abi_decoder_ids first last /\
    FLOOKUP s.vs_allocas id = SOME (off,sz) ==> sz = 32) ==>
  abi_decoder_budget first last 0
    (s.vs_alloca_next + 32 * CARD (abi_decoder_missing first last s)) s
Proof
  strip_tac >> irule abi_caller_allocation_budget >>
  asm_simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC
QED
