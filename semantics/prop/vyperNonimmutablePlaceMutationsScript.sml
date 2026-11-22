Theory vyperNonimmutablePlaceMutations
Ancestors
  vyperState vyperCallOutcomeFrame vyperMachineFrame vyperEvalFrame
  vyperPlaceFrames vyperScopePreservation

Theorem nonimmutable_place_mutations_frame:
  (!sid id path. pl <> ImmutablePlace sid id path) ==>
  (!v. state_rel_frame (\s t. t.immutables = s.immutables) (write_place cx pl v)) /\
  (!v. state_rel_frame (\s t. t.immutables = s.immutables) (append_place cx pl v)) /\
  state_rel_frame (\s t. t.immutables = s.immutables) (pop_place cx pl)
Proof
  Cases_on `pl` >> simp[]
  >- (simp[state_rel_frame_result] >>
      metis_tac[write_storage_place_immutables,
                append_storage_place_scopes_immutables,
                pop_storage_place_scopes_immutables]) >>
  rpt conj_tac >> rpt gen_tac >> irule state_rel_frame_machine >>
  simp[machine_frame_def, machine_frame_write_memory_place,
       machine_frame_append_memory_place, machine_frame_pop_memory_place]
QED
