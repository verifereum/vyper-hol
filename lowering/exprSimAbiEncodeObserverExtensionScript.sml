Theory exprSimAbiEncodeObserverExtension
Ancestors
  exprSimAbiEncodePhaseExtension exprSimAbiEncodeStagedObserver
  exprSimVVFrame abiDecoderReentry freshWrites varsExt exprSimProps
  loweringPosts compileEnv localPtrsProps finite_map pred_set arithmetic
  exprSimAbiEncodeSemantic venomState

Theorem abi_encode_observer_local_region_clean[local]:
  local_ptrs_reserved ce st ==>
  (local_region ce scopes (drop_fresh st s) n b sz <=>
   local_region ce scopes s n b sz)
Proof
  strip_tac >> simp[local_region_def] >>
  eq_tac >> rpt strip_tac >> goal_assum (drule_at Any) >>
  fs[local_ptrs_reserved_def] >> metis_tac[lookup_var_drop_fresh]
QED

Theorem abi_encode_staged_observation_clean_initial:
  local_ptrs_reserved ce st ==>
  (abi_encode_staged_observation ctx func ce cx vs st out mid outsz p at av
     (drop_fresh st initial) actual <=>
   abi_encode_staged_observation ctx func ce cx vs st out mid outsz p at av
     initial actual)
Proof
  strip_tac >>
  simp[abi_encode_staged_observation_def, abi_encode_observer_local_region_clean,
       abi_encode_semantic_obs_def, drop_fresh_def, lookup_var_def,
       FLOOKUP_DRESTRICT] >>
  metis_tac[not_fresh_at_def]
QED
