(* Registered and protected loop cursors across precise recursive effects.
   TOP-LEVEL: cursor_registered records an owned update; cursor_protected
   preserves an ancestor using its physical slot and the enclosing budget. *)
Theory abiScratchCursor
Ancestors
  abiScratchEncoderContract abiScratchEffect abiEncoderMembersDefs abiDecoderAllocation
  abiDecoderFootprint abiDecoderReentry compileEnv venomState finite_map pred_set words
  arithmetic abiSiteEncoderContract abiSiteAllocation

Theorem abi_scratch_cursor_registered:
  abi_encoder_cursor active cursor_op site slot first lo st off initial /\
  abi_scratch_effect first last owned_lo owned_hi next limit_st d sz b cap initial actual /\
  st.cs_next_var <= next /\ FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
  mload slot actual = n2w next_off ==>
  abi_encoder_cursor active cursor_op site slot first lo st next_off actual
Proof
  Cases_on `active` >> simp_tac bool_ss [abi_encoder_cursor_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_operand_live next cursor_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand cursor_op actual = SOME (n2w slot)` by
    (drule_all abi_scratch_effect_operand >> simp[]) >>
  asm_simp_tac bool_ss []
QED


Theorem abi_site_cursor_registered:
  abi_encoder_cursor active cursor_op site slot first lo st off initial /\
  abi_site_encoder_effect A owned_lo owned_hi next limit_st d sz b cap initial actual /\
  st.cs_next_var <= next /\ FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
  mload slot actual = n2w next_off ==>
  abi_encoder_cursor active cursor_op site slot first lo st next_off actual
Proof
  Cases_on `active` >> simp_tac bool_ss [abi_encoder_cursor_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_operand_live next cursor_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand cursor_op actual = SOME (n2w slot)` by
    (drule_all abi_site_effect_operand >> simp[]) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_site_cursor_protected:
  abi_encoder_cursor active cursor_op site slot first lo st off initial /\
  abi_site_encoder_effect A owned_lo owned_hi next limit_st d sz b cap initial actual /\
  abi_site_budget A b cap initial /\ (active ==> site IN A) /\
  st.cs_next_var <= next /\ (site < owned_lo \/ owned_hi <= site) /\
  abi_footprint_disjoint d sz (abi_decoder_child_scratch A b cap initial) ==>
  abi_encoder_cursor active cursor_op site slot first lo st off actual
Proof
  Cases_on `active` >> simp_tac bool_ss [abi_encoder_cursor_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `~(site IN abi_decoder_ids owned_lo owned_hi)` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  drule_all abi_site_effect_slot >> strip_tac >>
  `abi_decoder_operand_live next cursor_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand cursor_op actual = SOME (n2w slot)` by
    (drule_all abi_site_effect_operand >> simp[]) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_scratch_cursor_protected:
  abi_encoder_cursor active cursor_op site slot first lo st off initial /\
  abi_scratch_effect first last owned_lo owned_hi next limit_st d sz b cap initial actual /\
  abi_decoder_budget first last b cap initial /\ first <= owned_lo /\ owned_hi <= last /\
  st.cs_next_var <= next /\ site < last /\ (site < owned_lo \/ owned_hi <= site) /\
  abi_footprint_disjoint d sz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) ==>
  abi_encoder_cursor active cursor_op site slot first lo st off actual
Proof
  strip_tac >>
  `(active ==> site IN abi_decoder_ids first last)` by
    (gvs[abi_encoder_cursor_def, abi_decoder_ids_def]) >>
  gvs[GSYM abi_site_encoder_effect_interval, GSYM abi_site_budget_interval] >>
  metis_tac[abi_site_cursor_protected]
QED

val _ = List.app (fn (name, th) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn tag => tag = "DISK_THM") oracles then ()
    else raise Fail ("non-clean cursor dependency: " ^ name)
  end) (DB.thms "abiScratchCursor");
