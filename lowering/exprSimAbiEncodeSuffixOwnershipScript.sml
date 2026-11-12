Theory exprSimAbiEncodeSuffixOwnership
Ancestors
  abiEncoderRegisteredEffect abiEncoderWindowContract abiBuiltinEncodeSetup
  abiDecoderContract abiDecodeStaticProps exprSimAbiEncodeFrameTransfer venomMemDefs
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

(* The setup ALLOCA changes metadata, not bytes.  Its only memory write is
   the optional full-width selector store, not the four-byte prefix. *)
Theorem abi_encode_setup_memory_effect:
  abi_builtin_encode_setup_frame next site outsz p write_size initial prepared /\
  (b+n <= p+32 \/ p+32+write_size <= b) ==>
  mem_bytes_at b n prepared.vs_memory = mem_bytes_at b n initial.vs_memory
Proof
  simp_tac bool_ss [abi_builtin_encode_setup_frame_def, abi_decode_frame_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_encode_registered_owned_interval:
  abi_encoder_registered_effect ids [] prepared actual /\
  alloca_inv actual /\ aid NOTIN ids /\
  FLOOKUP actual.vs_allocas aid = SOME (b,sz) /\
  b <= off /\ off+n <= b+sz ==>
  mem_bytes_at off n actual.vs_memory = mem_bytes_at off n prepared.vs_memory
Proof
  strip_tac >> irule mem_bytes_at_bytewise >> rpt strip_tac >>
  irule abi_encode_registered_protected_byte >>
  qexistsl [`ids`, `b`, `sz`, `[]`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `alloca_inv actual` mp_tac >>
  simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def] >>
  strip_tac >> metis_tac[]
QED

Theorem abi_encode_owned_interval_frame:
  abi_builtin_encode_setup_frame next site outsz p w initial prepared /\
  abi_encoder_registered_effect ids [] prepared actual /\
  alloca_inv actual /\ site IN ids /\ aid NOTIN ids /\
  FLOOKUP actual.vs_allocas site = SOME (p,outsz) /\
  FLOOKUP actual.vs_allocas aid = SOME (b,sz) /\
  32+w <= outsz /\ b <= off /\ off+n <= b+sz ==>
  mem_bytes_at off n actual.vs_memory = mem_bytes_at off n initial.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at off n actual.vs_memory = mem_bytes_at off n prepared.vs_memory` by
    (metis_tac[abi_encode_registered_owned_interval]) >>
  `b+sz <= p \/ p+outsz <= b` by
    (qpat_x_assum `alloca_inv actual` mp_tac >>
     simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def] >>
     strip_tac >> metis_tac[]) >>
  `mem_bytes_at off n prepared.vs_memory = mem_bytes_at off n initial.vs_memory` by
    (irule abi_encode_setup_memory_effect >> goal_assum (drule_at Any) >> decide_tac) >>
  simp[]
QED
