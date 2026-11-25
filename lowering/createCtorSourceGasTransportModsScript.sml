Theory createCtorSourceGasTransportMods
Ancestors
  bodyFullPostsMods loweringPosts vyperState

Theorem ctor_locals_kept_initial_gas[local]:
  locals_kept cenv (es with gas_obs := gs) ee s0 s <=>
  locals_kept cenv es ee s0 s
Proof
  simp[locals_kept_def, popped_kept_def]
QED

Theorem ctor_vv_post_initial_gas_mods:
  vv_post_mods H ctx func cenv cx e (es with gas_obs := gs) sa sb s0 ee tv vv s <=>
  vv_post_mods H ctx func cenv cx e es sa sb s0 ee tv vv s
Proof
  simp[vv_post_mods_def, ctor_locals_kept_initial_gas, pure_frame_gas_obs]
QED
