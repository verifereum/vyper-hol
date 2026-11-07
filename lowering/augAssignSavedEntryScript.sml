(* Entry is a frame for BOTH storage backends, on the actual entry
   state t.  internal_prologue_run supplies mat_frame for its very same
   execution witness, so no second existential run is needed here. *)
Theory augAssignSavedEntry
Ancestors
  augAssignEntryHistory vyperStorageBackend venomState

Theorem internal_entry_saved_word_history:
  setup_callee func args caller = SOME s0 /\
  mat_frame st s0 t /\
  (if tr then tload saved caller else sload saved caller) =
    lookup_storage saved (get_storage cx es tr) ==>
  (if tr then tload saved t else sload saved t) =
    lookup_storage saved (get_storage cx es tr)
Proof
  strip_tac >>
  drule setup_callee_storage_history >>
  disch_then (qspec_then `saved` strip_assume_tac) >>
  drule mat_frame_storage_history >>
  disch_then (qspec_then `saved` strip_assume_tac) >>
  Cases_on `tr` >> gvs[]
QED
