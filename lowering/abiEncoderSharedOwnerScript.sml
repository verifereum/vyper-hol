(* Compiler-independent runtime observations restored at their fixed owner. *)
Theory abiEncoderSharedOwner
Ancestors
  abiEncoderSharedInputEffect abiEncoderArrayCursor abiEncoderSharedContract
  abiEncoderMembersDefs compileEnv venomState

Theorem abi_encoder_shared_input_owner:
  abi_encoder_shared_input (ei,at,av) (owner_st,src,dst) sr dr arena s /\
  abi_encoder_shared_input (ei,at,av) (body_st,src,dst) sr dr arena t ==>
  abi_encoder_shared_input (ei,at,av) (owner_st,src,dst) sr dr arena t
Proof
  PairCases_on `sr` >> PairCases_on `dr` >> PairCases_on `arena` >>
  simp_tac bool_ss [abi_encoder_shared_input_def] >> strip_tac >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encoder_cursor_owner:
  abi_encoder_cursor active op site slot first lo owner_st old_off s /\
  abi_encoder_cursor active op site slot first lo body_st new_off t ==>
  abi_encoder_cursor active op site slot first lo owner_st new_off t
Proof
  Cases_on `active` >> simp_tac bool_ss [abi_encoder_cursor_def] >>
  strip_tac >> asm_simp_tac bool_ss []
QED
