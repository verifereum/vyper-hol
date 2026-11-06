Theory fnLineageInvSpillReplay
Ancestors planSpillBounds doSwapSim

(* Resource transport only: reachability must separately supply the
   occupied-address inclusion and the replacement map's injectivity. *)
Theorem plan_slots_bounded_occupied_addresses:
  !base q m.
    plan_slots_bounded base q /\
    (!op off. FLOOKUP m op = SOME off ==>
       ?old. FLOOKUP q.ps_spilled old = SOME off) ==>
    plan_slots_bounded base (q with ps_spilled := m)
Proof
  rw[plan_slots_bounded_def] >> metis_tac[]
QED

Theorem spill_alloc_layout_wf_occupied_addresses:
  !al old m.
    spill_alloc_layout_wf al old /\
    (!op off. FLOOKUP m op = SOME off ==>
       ?old_op. FLOOKUP old old_op = SOME off) /\
    (!op1 op2 off. FLOOKUP m op1 = SOME off /\
       FLOOKUP m op2 = SOME off ==> op1 = op2) ==>
    spill_alloc_layout_wf al m
Proof
  rw[spill_alloc_layout_wf_def] >> metis_tac[]
QED
