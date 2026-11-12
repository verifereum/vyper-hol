(*
 * Storage places a run observed, against a finite storage horizon H: a
 * storage place's slot lies on a path inside a root recorded in FST H.
 * The finite-horizon counterpart of storage_place_region, which asks for a
 * declared region instead.
 *)

Theory vyperStoragePlaceObserved
Ancestors
  vyperState vyperStoragePlaceRegion

Definition storage_place_observed_def:
  storage_place_observed (H : (bool # bytes32 # type_value) list # num list)
    (StoragePlace tr slot leaf) =
    (?root tv path delta.
      MEM (tr,root,tv) (FST H) /\
      storage_subregion tv path delta leaf /\ slot = root + n2w delta) /\
  storage_place_observed H (MemoryPlace id path) = T /\
  storage_place_observed H (ImmutablePlace mid id path) = T
End
