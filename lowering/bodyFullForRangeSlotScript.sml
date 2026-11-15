(* The allocated Range loop slot survives a selected body's old-register
   and old-ghost frames; no memory-byte preservation is required. *)
Theory bodyFullForRangeSlot
Ancestors
  bodyPtrDefs loweringStateRelDefs

Theorem for_range_body_slot_preserved:
  !sb0 q G tn s G1 tn1 t sz.
    not_fresh_at sb0 q /\ ptr_covers G tn q s sz /\
    (!x w. not_fresh_at sb0 x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w) /\
    (!x. not_fresh_at sb0 x ==>
      FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x)) ==>
    ptr_covers G1 tn1 q t sz
Proof
  rw[ptr_covers_def] >> metis_tac[]
QED
