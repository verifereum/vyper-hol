(* TOP-LEVEL: retain the actual encoder output allocation on the precise
   scratch path. Both fresh allocation and reuse yield the same output row. *)
Theory abiScratchBuiltinOwnership
Ancestors
  abiBuiltinEncodeCorrect abiBuiltinEncodeSetup abiScratchEncoderContract abiDecoderAllocation
  compileEnv venomState finite_map pred_set arithmetic

Theorem abi_scratch_effect_allocation_row:
  abi_scratch_effect first last lo hi next limit_st d sz b cap s t /\
  (site < lo \/ hi <= site) /\ FLOOKUP s.vs_allocas site = SOME (p,outsz) ==>
  FLOOKUP t.vs_allocas site = SOME (p,outsz)
Proof
  simp_tac bool_ss [abi_scratch_effect_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `!id. id < lo \/ hi <= id ==> _` (qspec_then `site` mp_tac) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_scratch_builtin_allocation_frame:
  abi_builtin_encode_setup_frame next site outsz p write_size initial prepared /\
  abi_scratch_effect first last lo hi child_next limit_st d sz b cap prepared actual /\
  first <= lo /\ hi <= last ==>
  !id. ~(id IN abi_decoder_ids first last) ==>
    FLOOKUP actual.vs_allocas id =
      FLOOKUP (abi_builtin_allocate_state site outsz initial).vs_allocas id
Proof
  simp_tac bool_ss [abi_builtin_encode_setup_frame_def, abi_scratch_effect_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> qx_gen_tac `id` >> strip_tac >>
  SUBGOAL_THEN ``id < lo \/ hi <= id`` assume_tac
  >- (fs[abi_decoder_ids_def] >> decide_tac) >>
  qpat_x_assum `!id. id < lo \/ hi <= id ==> _` (qspec_then `id` mp_tac) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_scratch_builtin_allocation_row_frame:
  abi_builtin_encode_setup_frame next site outsz p write_size initial prepared /\
  abi_scratch_effect first last lo hi child_next limit_st d sz b cap prepared actual /\
  site < lo ==>
  FLOOKUP actual.vs_allocas site =
    FLOOKUP (abi_builtin_allocate_state site outsz initial).vs_allocas site
Proof
  simp_tac bool_ss [abi_builtin_encode_setup_frame_def, abi_scratch_effect_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `!id. id < lo \/ hi <= id ==> _` (qspec_then `site` mp_tac) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_scratch_builtin_output_row:
  abi_builtin_encode_setup_frame next site outsz p write_size initial prepared /\
  ((FLOOKUP initial.vs_allocas site = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas site = SOME (p,outsz)) /\
  abi_scratch_effect first last lo hi child_next limit_st d sz b cap prepared actual /\
  (site < lo \/ hi <= site) ==>
  FLOOKUP actual.vs_allocas site = SOME (p,outsz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_encode_setup_frame_row >> disch_then assume_tac >>
  drule_all abi_scratch_effect_allocation_row >> simp[]
QED
