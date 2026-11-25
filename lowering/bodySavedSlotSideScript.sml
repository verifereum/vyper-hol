(* Joint storage/transient replay with a caller-supplied physical post. *)
Theory bodySavedSlotSide
Ancestors
  bodyFullExtCallSlotCopyReplay

Theorem unwrap_slot_copy_origin_ptr_no_dead_side =
  bodyFullUnwrapSlotTheory.unwrap_slot_copy_origin_ptr_no_dead_side

Theorem extcall_saved_slot_copy_replay_side =
  bodyFullExtCallSlotCopyReplayTheory.extcall_saved_slot_copy_replay_side
