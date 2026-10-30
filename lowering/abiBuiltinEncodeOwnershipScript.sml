(* TOP-LEVEL: preserve the actual output allocation through encoder execution.
   Fresh allocation and reuse both retain the same physical allocation row. *)
Theory abiBuiltinEncodeOwnership
Ancestors
  abiBuiltinAllocation abiBuiltinEncodeSetup abiDecoderEffect compileEnv venomState finite_map

Theorem abi_builtin_allocate_state_row:
  ((FLOOKUP s.vs_allocas site = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas site = SOME (p,outsz)) ==>
  FLOOKUP (abi_builtin_allocate_state site outsz s).vs_allocas site = SOME (p,outsz)
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  gvs[abi_builtin_allocate_state_def, FLOOKUP_UPDATE]
QED

Theorem abi_builtin_allocation_frame_row:
  abi_builtin_allocation_frame next site outsz s t /\
  ((FLOOKUP s.vs_allocas site = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas site = SOME (p,outsz)) ==>
  FLOOKUP t.vs_allocas site = SOME (p,outsz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_allocate_state_row >>
  fs[abi_builtin_allocation_frame_def]
QED

Theorem abi_builtin_encode_setup_frame_row:
  abi_builtin_encode_setup_frame next site outsz p write_size s t /\
  ((FLOOKUP s.vs_allocas site = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas site = SOME (p,outsz)) ==>
  FLOOKUP t.vs_allocas site = SOME (p,outsz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_allocate_state_row >>
  fs[abi_builtin_encode_setup_frame_def]
QED

Theorem abi_builtin_encode_body_allocation_row:
  abi_decoder_effect first last lo hi next limit_st d sz b cap s t /\
  (site < lo \/ hi <= site) /\ FLOOKUP s.vs_allocas site = SOME (p,outsz) ==>
  FLOOKUP t.vs_allocas site = SOME (p,outsz)
Proof
  simp_tac bool_ss [abi_decoder_effect_def, abi_decoder_scratch_frame_def] >>
  strip_tac >>
  qpat_x_assum `!id. id < lo \/ hi <= id ==> _` (qspec_then `site` mp_tac) >> simp[]
QED
