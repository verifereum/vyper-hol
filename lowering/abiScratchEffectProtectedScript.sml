(* Complete sources and earlier cursor slots survive recursive child encoding.
   TOP-LEVEL: abi_scratch_effect_slot and abi_scratch_effect_source derive
   protection from physical footprints and the actual enclosing budget. *)
Theory abiScratchEffectProtected
Ancestors
  abiScratchEncoderContract abiScratchFootprint abiScratchSubset
  abiEncoderInputFrame abiEncoderInput abiDecoderAllocation abiDecoderFootprint
  abiDecoderFrame abiDecoderReentry compileEnv valueEncoding contractABI
  venomState finite_map pred_set words list arithmetic

Theorem abi_scratch_effect_operand:
  abi_scratch_effect first last lo hi next limit_st d sz b cap s t /\
  abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
  eval_operand op t = SOME w
Proof
  simp_tac bool_ss [abi_scratch_effect_def] >> strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_scratch_effect_slot:
  abi_scratch_effect first last lo hi next limit_st d sz b cap s t /\
  abi_decoder_budget first last b cap s /\ first <= lo /\ hi <= last /\
  site IN abi_decoder_ids first last /\ ~(site IN abi_decoder_ids lo hi) /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  abi_footprint_disjoint d sz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) ==>
  FLOOKUP t.vs_allocas site = SOME (slot,32) /\ mload slot t = mload slot s
Proof
  strip_tac >>
  `abi_decoder_ids lo hi SUBSET abi_decoder_ids first last` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `FINITE (abi_decoder_ids lo hi) /\ FINITE (abi_decoder_ids first last)` by simp[] >>
  drule_all abi_decoder_child_excludes_ancestor >> disch_then assume_tac >>
  `MEM (slot,32) (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_scratch_registered_member >> asm_simp_tac bool_ss [] >>
     qexists_tac `site` >> simp[]) >>
  `abi_footprint_disjoint slot 32
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s)` by
    (simp_tac bool_ss [abi_scratch_disjoint_cons] >> asm_rewrite_tac[] >>
     qpat_x_assum `abi_footprint_disjoint d sz _`
       (qspecl_then [`slot`, `32`] mp_tac o REWRITE_RULE [abi_footprint_disjoint_def]) >>
     simp[] >> decide_tac) >>
  qpat_x_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `site < lo \/ hi <= site` by fs[abi_decoder_ids_def] >>
  `FLOOKUP t.vs_allocas site = FLOOKUP s.vs_allocas site` by simp[] >>
  drule_all abi_decode_footprint_frame_mload >> simp[]
QED

Theorem abi_scratch_effect_source:
  abi_scratch_input ei at av st src dst sb source_cap d sz first last b cap s /\
  abi_scratch_effect first last lo hi next limit_st d sz b cap s t /\
  first <= lo /\ hi <= last ==>
  abi_encoder_input ei at av sb source_cap t.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  `abi_decoder_ids lo hi SUBSET abi_decoder_ids first last` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `FINITE (abi_decoder_ids first last)` by simp[] >>
  `abi_footprint_disjoint sb source_cap
    (abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s)` by
    (irule abi_scratch_disjoint_subset >> qexists_tac `abi_decoder_ids first last` >> simp[]) >>
  `abi_footprint_disjoint sb source_cap
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s)` by
    simp[abi_scratch_disjoint_cons] >>
  qpat_x_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  drule_all abi_encoder_input_frame >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_EFFECT_PROTECTED_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch protection not kernel closed: " ^ n)
  end) (DB.thms "abiScratchEffectProtected");
