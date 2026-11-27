(* Discharge the phase contracts, retaining the selected loop result for replay. *)
Theory bodyAbiDecodeGuardedRuntimeLoopMods
Ancestors
  bodyAbiDecodeGuardedCounterLoadMods bodyAbiDecodeGuardedWordLoadMods
  bodyAbiDecodeGuardedTestBranchMods bodyAbiDecodeGuardedLoopHeaderMods
  bodyAbiDecodeGuardedLoopAccumulationMods bodyAbiDecodeGuardedLoopCutReplayMods
Libs
  bodyAbiDecodeGuardedEffectSyntaxLib bodyFullAbiDecodeCutArraySyntaxLib
  bodyFullAbiDecodeLoopObservedSyntaxLib bodyFullAbiDecodeRuntimeLoopLengthObservedLib

val loop_from_header = abi_decode_guarded_loop_split_entry_from_header_mods;
val loop_header_contract = fst (dest_imp (concl loop_from_header));

Theorem guarded_loop_header[local]:
  ^loop_header_contract
Proof
  mp_tac abi_decode_loop_header_observed_effect_from_phases_mods >>
  (impl_tac >- ACCEPT_TAC abi_decode_loop_counter_load_frame_mods) >>
  (impl_tac >- ACCEPT_TAC abi_decode_owned_relative_load_effect_mods) >>
  (impl_tac >- ACCEPT_TAC abi_decode_loop_owned_branch_frame_mods) >>
  disch_then ACCEPT_TAC
QED

Theorem abi_decode_guarded_loop_split_entry_mods:
  ^(guarded_effect_length_body_typed ()) ==> ^(guarded_effect_length_split_entry ())
Proof
  ACCEPT_TAC (MP loop_from_header guarded_loop_header)
QED

val loop_norm = REDEPTH_CONV BETA_CONV THENC simpLib.SIMP_CONV bool_ss [];

Theorem abi_decode_guarded_loop_length_mods:
  ^(guarded_effect_length_body_typed ()) ==> ^(guarded_effect_length_loop_clause ())
Proof
  CONV_TAC loop_norm >> disch_tac >>
  mp_tac (CONV_RULE loop_norm abi_decode_guarded_loop_split_entry_mods) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  rpt (ho_match_mp_tac InductiveDefinitionContextTheory.MONO_FORALL >> gen_tac) >>
  (match_mp_tac boolTheory.MONO_IMP >> conj_tac >- disch_then ACCEPT_TAC) >>
  rpt (ho_match_mp_tac InductiveDefinitionContextTheory.MONO_FORALL >> gen_tac) >>
  (match_mp_tac boolTheory.MONO_IMP >> conj_tac >- disch_then ACCEPT_TAC) >>
  disch_then (CHOOSE_THEN (mp_tac o List.last o CONJUNCTS)) >>
  rpt (ho_match_mp_tac InductiveDefinitionContextTheory.MONO_EXISTS >> gen_tac) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

val cut_loop_layout = ``^array_cut_layout /\
  cut = frag_observer_cut cut_finish /\
  EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code cut_start cut_finish)``;
val guarded_loop_cut_clause = specialize_array_cut (#loop
  (guarded_effect_compiler_cases (effect_ind [guarded_effect_motive_typed (),
    decorate_motive bounded_complex_plus_typed,
    decorate_array_motive (decorate_motive repaired_loop_length_plus_typed)])));

Theorem abi_decode_guarded_loop_cut_mods:
  ^(guarded_effect_length_body_typed ()) ==> ^cut_loop_layout ==> ^guarded_loop_cut_clause
Proof
  CONV_TAC loop_norm >> ntac 2 disch_tac >>
  mp_tac (CONV_RULE loop_norm abi_decode_guarded_loop_split_entry_mods) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  rpt (ho_match_mp_tac InductiveDefinitionContextTheory.MONO_FORALL >> gen_tac) >>
  (match_mp_tac boolTheory.MONO_IMP >> conj_tac >- disch_then ACCEPT_TAC) >>
  rpt (ho_match_mp_tac InductiveDefinitionContextTheory.MONO_FORALL >> gen_tac) >>
  disch_then (mk_asm "selected") >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "entry") strip_assume_tac) >>
  asm_x "selected" mp_tac >> (impl_tac >- asm "entry" ACCEPT_TAC) >>
  disch_then (qx_choose_then `hdr` (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?r Gf tnf. _` (qx_choose_then `r` (qx_choose_then `Gf`
    (qx_choose_then `tnf` (map_every assume_tac o CONJUNCTS)))) >>
  qexistsl [`r`,`Gf`,`tnf`] >>
  (conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  `(^array_shadow) start finish' s r` by
    (BETA_TAC >> match_mp_tac (BETA_RULE (Q.INST [`h` |-> `hdr`]
      abi_decode_guarded_loop_cut_replay_mods)) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     simp_tac bool_ss [BETA_THM] >>
     (conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `_ \/ (?t. r = Abort Revert_abort t)`
       (DISJ_CASES_THEN (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)))
     >- (disj1_tac >> qexists `t` >> simp[]) >>
     disj2_tac >> qexists `t` >> simp[]) >>
  qpat_assum `^cut_loop_layout` (assume_tac o CONJUNCT1 o CONJUNCT2) >>
  qpat_x_assum `(^array_shadow) start finish' s r` (mp_tac o BETA_RULE) >>
  asm_simp_tac bool_ss []
QED
