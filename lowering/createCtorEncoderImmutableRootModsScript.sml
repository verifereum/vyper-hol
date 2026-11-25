Theory createCtorEncoderImmutableRootMods
Ancestors
  bodyFullPostsMods bodyInvSplit bodyFullShadowBodyInv loweringStateRelDefs
  compileEnv immutableEncoding valueEncodingDefs vyperState vfmState alist finite_map

Theorem linked_immutable_root_value_mods:
  contract_inv mods exps ctx ce cx /\ expr_sim_inv_mods mods ce cx env ee /\
  ce.ce_is_ctor /\ dead_lo_ok_mods H (DF H) lo ce cx /\
  immutable_frame_mods func ce cx ee u /\
  ALOOKUP ce.ce_modules src = SOME tops /\
  ALOOKUP ee.immutables cx.txn.target = SOME x /\
  FLOOKUP ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  FLOOKUP (get_source_immutables src x) id = SOME (rt,v) ==>
  immutable_value_admissible rt v /\ val_in_memory rt v off u.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `immutable_frame_mods _ _ _ _ _` mp_tac >>
  simp[immutable_frame_mods_def, immutables_rel_mods_def] >>
  disch_then (CONJUNCTS_THEN2 (qspecl_then [`src`,`tops`] mp_tac) kall_tac) >>
  simp[immutables_rel_def] >>
  disch_then (qspecl_then [`id`,`rt`,`v`,`off`] mp_tac) >>
  simp[]
QED
