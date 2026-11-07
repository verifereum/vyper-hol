Theory exprSimAbiEncodeSuffixOwnership
Ancestors
  abiEncoderRegisteredEffect abiEncoderWindowContract abiBuiltinEncodeSetup
  finite_map pred_set list arithmetic

(* Absorb explicit output writes only when each output lies in a final
   registered allocation.  This concerns the same pair of execution states. *)
Theorem abi_encode_registered_effect_absorb_outputs:
  abi_encoder_registered_effect ids outs s t /\
  EVERY (\(b,n). ?i p sz. i IN ids /\
    FLOOKUP t.vs_allocas i = SOME (p,sz) /\ p <= b /\ b+n <= p+sz) outs ==>
  abi_encoder_registered_effect ids [] s t
Proof
  simp_tac bool_ss [abi_encoder_registered_effect_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!a. EVERY _ outs /\ _ ==> _` irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  gvs[EVERY_MEM] >> Cases >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  qpat_x_assum `!i b sz. _` drule_all >> decide_tac
QED

(* A body_state and finish on the very same endpoint chain.  The containing output
   row is retained by the body_state's registered effect, including re-entry. *)
Theorem abi_encode_body_finish_registered:
  window_strong_result ctx func ready body_end len at av d prepared body_state /\
  abi_encoder_registered_effect {} [(p,32)] body_state actual /\
  body_ids = window_alloca_sites func (frag_ids ready body_end) /\
  body_ids SUBSET ids /\ site IN ids /\
  FLOOKUP prepared.vs_allocas site = SOME (p,outsz) /\
  p <= d /\ d+LENGTH (enc at av) <= p+outsz /\ 32 <= outsz ==>
  abi_encoder_registered_effect ids [] prepared actual
Proof
  strip_tac >>
  `abi_encoder_registered_effect body_ids [(d,LENGTH (enc at av))] prepared body_state` by
    gvs[window_strong_result_def] >>
  `FLOOKUP body_state.vs_allocas site = SOME (p,outsz)` by
    (irule abi_encoder_registered_effect_allocated >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `abi_encoder_registered_effect ids [(d,LENGTH (enc at av))] prepared body_state` by
    (irule abi_encoder_registered_effect_enlarge >>
     goal_assum (drule_at Any) >> simp[]) >>
  `abi_encoder_registered_effect ids [] prepared body_state` by
    (irule abi_encode_registered_effect_absorb_outputs >>
     goal_assum (drule_at Any) >>
     simp[] >> qexistsl [`site`, `p`, `outsz`] >> simp[]) >>
  `FLOOKUP actual.vs_allocas site = SOME (p,outsz)` by
    (irule abi_encoder_registered_effect_allocated >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  irule abi_encoder_registered_effect_trans >> qexists `body_state` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `abi_encoder_registered_effect ids [(p,32)] body_state actual` by
    (rev_drule abi_encoder_registered_effect_enlarge >>
     disch_then irule >> simp[]) >>
  irule abi_encode_registered_effect_absorb_outputs >>
  goal_assum (drule_at Any) >>
  simp[] >> qexistsl [`site`, `p`, `outsz`] >> simp[]
QED
