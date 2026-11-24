(* The linked encoder-facing adapter for a delayed runtime-code read.  The
   runtime arrival theorem already packages the concrete copy endpoint, all-H
   linked posts, and the all-D path at one state. *)
Theory createCtorEncoderDelayedRuntimeLinkedMods
Ancestors
  createCtorUnwrapRuntimeCodeArrivalMods createCtorEncoderSavedAdvanceMods
  createCtorEncoderDelayedRuntimeMods

Theorem ctor_encoder_delayed_runtime_linked_mods =
  ctor_unwrap_runtime_code_arrival_mods
