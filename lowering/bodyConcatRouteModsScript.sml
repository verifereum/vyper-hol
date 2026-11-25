(* Adapt the public Concat fold to the zero-entry route. *)
Theory bodyConcatRouteMods
Ancestors
  bodyConcatElementsMods bodyConcatCompactRouteMods bodyConcatCutsMods
  gasOutcomeFullPostMods valueEncodingDefs arithmetic list pair

val public_loop = concl concat_elements_mods
val (route_pre,route_post) =
  boolSyntax.dest_imp (concl (BETA_RULE concat_from_loop_entry_mods))
val (compact_loop,route_inputs) = boolSyntax.dest_conj route_pre

Theorem concat_public_zero_entry[local]:
  ^public_loop ==> ^compact_loop
Proof
  disch_tac >>
  qx_genl_tac [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`s0`,`G0`,`tn0`,`scratch`] >>
  PairCases_on `scratch` >>
  rename1 `concat_loop_entry_mods _ _ (dv,ov,ow,binst,oinst,B,bsz) _ _ _ _ _ _ ==> _` >>
  disch_then (map_every assume_tac o CONJUNCTS o
    SIMP_RULE bool_ss [concat_loop_entry_mods_def,concat_loop_code_mods_def,
      concat_live_mods_def,concat_horizon_mods_def,LET_THM,UNCURRY_DEF,LENGTH,ADD_CLAUSES]) >>
  qpat_x_assum `!args P k DF lo d. _`
    (mp_tac o Q.INST [`k` |-> `0`, `P` |-> `0`] o SPEC_ALL) >>
  (impl_tac >- asm_rewrite_tac [ADD_CLAUSES,ZERO_LESS_EQ,prim_recTheory.LESS_REFL,
                                wordsTheory.WORD_LITERAL_ADD]) >>
  disch_tac >>
  irule gas_outcome_full_mods_post_source >>
  qhdtm_x_assum `gas_outcome_full_mods` (irule_at Any) >>
  BETA_TAC >> simp_tac bool_ss [] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?vs. _`
    (strip_assume_tac o SIMP_RULE bool_ss [ADD_CLAUSES]) >>
  qexists_tac `vs` >>
  qpat_assum `mem_bytes_at _ 0 _ = []` (fn zero =>
    qpat_x_assum `mem_bytes_at _ _ _ = mem_bytes_at _ 0 _ ++ _`
      (assume_tac o REWRITE_RULE [zero,APPEND])) >>
  simp_tac bool_ss [concat_live_mods_def,concat_old_frame_mods_def,
    concat_horizon_mods_def,APPEND] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem concat_from_elements_mods:
  ^public_loop /\ ^route_inputs ==> ^route_post
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac concat_public_zero_entry >>
  mp_tac (BETA_RULE concat_from_loop_entry_mods) >>
  (impl_tac >- asm_rewrite_tac []) >>
  disch_then ACCEPT_TAC
QED
