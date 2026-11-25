(* Publish the selected allocating copy's guarded walk. The cursor theory
   composes the allocation and the chosen linear or counted copy, and the
   existing unrestricted result is a projection of that same construction. *)
Theory bodyUnwrapSlotOriginPhysical
Ancestors
  bodyFullUnwrapSlotCursor

Theorem unwrap_ensure_slot_origin_execution_physical =
  bodyFullUnwrapSlotCursorTheory.unwrap_ensure_slot_origin_execution_walk;
