Theory exprSimAbiEncodeSuffixOwnership
Ancestors
  abiEncoderRegisteredEffect finite_map pred_set list arithmetic

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
