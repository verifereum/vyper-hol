(* Bounded physical scratch and PHI interface diagnostics. *)
Theory abiEncoderEffectProbe
Ancestors
  abiEncoderLabelAliasProbe abiScratchEncoderContract abiScratchFootprint
  abiDecoderFootprint abiDecoderFrame abiEncoderProps compileEnv valueEncoding
  venomState venomInst venomMemDefs instIdxIndep finite_map pred_set list words arithmetic

Theorem alias_entry_phi_prefix_zero:
  phi_prefix_length alias_entry_block.bb_instructions = 0
Proof
  EVAL_TAC
QED

Theorem alias_function_end_phi_prefix_zero:
  !bb. lookup_block alias_end.cs_current_bb (alias_function fn).fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Definition effect_probe_start_def:
  effect_probe_start (s:venom_state) = s with
    <|vs_allocas := FEMPTY |+ (0,(32,32)); vs_alloca_next := 64;
      vs_memory := []|>
End

Definition effect_probe_end_def:
  effect_probe_end (s:venom_state) = write_memory_with_expansion 64 [1w] (effect_probe_start s)
End

Theorem effect_probe_evolution:
  abi_scratch_evolution {0} 0 96 (effect_probe_start s) (effect_probe_end s)
Proof
  simp[abi_scratch_evolution_def, effect_probe_start_def, effect_probe_end_def,
       FLOOKUP_UPDATE, write_memory_with_expansion_def] >> rpt strip_tac >> gvs[]
QED

Theorem effect_probe_registered_and_reserve:
  abi_decoder_child_scratch {0} 0 96 (effect_probe_start s) = [(64,32);(32,32)]
Proof
  simp[abi_decoder_child_scratch_def, effect_probe_start_def, SET_TO_LIST_SING,
       FLOOKUP_UPDATE]
QED

Theorem effect_probe_physical_frame:
  abi_decode_footprint_frame
    (abi_decoder_child_scratch {0} 0 96 (effect_probe_start s))
    (effect_probe_start s) (effect_probe_end s)
Proof
  simp_tac bool_ss [effect_probe_end_def] >>
  irule abi_decode_footprint_frame_write >>
  qexistsl_tac [`64`,`32`] >>
  simp[effect_probe_registered_and_reserve]
QED

Theorem effect_probe_reserve_unregistered:
  (!id p n. FLOOKUP (effect_probe_end s).vs_allocas id = SOME (p,n) ==>
    64 < p \/ p+n <= 64) /\
  mem_bytes_at 64 1 (effect_probe_end s).vs_memory = [1w] /\
  mem_bytes_at 64 1 (effect_probe_start s).vs_memory = [0w]
Proof
  simp[effect_probe_start_def, effect_probe_end_def, write_memory_with_expansion_def,
       FLOOKUP_UPDATE, mem_bytes_at_def] >>
  rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem effect_probe_no_public_frame:
  ~enc_frame alias_base (alias_base with cs_next_id := 1) 0 96 []
    (effect_probe_start s) (effect_probe_end s)
Proof
  strip_tac >>
  qpat_x_assum `enc_frame _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [enc_frame_def]) >>
  qpat_x_assum `!a. _ ==> mem_bytes_at _ _ _ = _` (qspec_then `64` mp_tac) >>
  mp_tac effect_probe_reserve_unregistered >> strip_tac >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem effect_probe_initial_scratch:
  enc_scratch {0} 0 96 (effect_probe_start s)
Proof
  simp[enc_scratch_def, effect_probe_start_def, alloca_inv_def,
       allocas_non_overlapping_def, alloca_next_valid_def, FLOOKUP_UPDATE,
       dimword_def] >>
  rpt strip_tac >> gvs[]
QED

(* Checked boundary outcome:
   - the aliased label has a non-PHI first instruction; its containing
     function satisfies the recursive encoder's end-block PHI premise.
     No STOP observation or cut-inequality premise is needed for this check.
   - the physical frame permits writing byte 64 in unregistered reserve,
     even with unchanged allocas/frontier, valid initial enc_scratch, and
     abi_scratch_evolution at the SAME endpoint. enc_frame forbids it.
   Missing for public-frame transport are a sharper memory-write footprint
   (registered final fragment slots, not arbitrary reserve), enc_scratch
   preservation, preservation of pre-existing allocation entries outside the
   owned interval, old-variable restoration, and accounts/transient/logs/
   requests preservation. The physical effect supplies budget/evolution,
   operand preservation, an outside-id frame, haltedness and call-context/
   data-section preservation, but does not by itself establish these exact
   public claims. This is not an execution counterexample: no compiler run
   is claimed for the artificial memory write above. *)
