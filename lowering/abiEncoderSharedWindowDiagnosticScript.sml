(* Resource-interface diagnostic for the shared-window adapter.
   Empty windows are zero-aware in the public contract, but the shared
   destination footprint requires ordinary interval separation. *)
Theory abiEncoderSharedWindowDiagnostic
Ancestors
  abiDecoderFrame venomMemDefs

Theorem shared_window_empty_destination_separation_gap:
  venomMemDefs$regions_disjoint (16,0) (0,32) /\
  ~abi_footprint_disjoint 16 0 [(0,32)]
Proof
  simp[regions_disjoint_def, abi_footprint_disjoint_def]
QED
