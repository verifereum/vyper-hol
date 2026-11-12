Theory exprSimAbiEncodeObservationExtension
Ancestors
  exprSimAbiEncodeStagedObserver exprSimAbiEncodeExecFrame
  exprSimAbiEncodeSemantic abiDecoderVarExtend varsExt exprSimProps
  execEquivParamDefs exprLoweringProps venomState finite_map

Theorem abi_encode_bounded_vars_ext:
  abi_decoder_vars_extend upper u v ==> vars_ext u v
Proof
  strip_tac >> drule abi_decoder_vars_extend_restore >> strip_tac >>
  simp[vars_ext_def] >> conj_tac
  >- gvs[abi_decoder_vars_extend_def, abi_decoder_var_map_def,
         Excl "vsr_complete_mask_equality"] >>
  qpat_x_assum `v with vs_vars := u.vs_vars = u` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem abi_encode_staged_observation_extend:
  abi_encode_staged_observation ctx func ce cx vs st out mid outsz p at av initial u /\
  abi_decoder_vars_extend upper u v ==>
  abi_encode_staged_observation ctx func ce cx vs st out mid outsz p at av initial v
Proof
  strip_tac >>
  `vars_ext u v` by (irule abi_encode_bounded_vars_ext >> goal_assum (drule_at Any)) >>
  `stmt_state_rel ctx func ce cx vs v` by
    (irule stmt_state_rel_vars_ext >> qexists_tac `u` >>
     gvs[abi_encode_staged_observation_def]) >>
  `eval_operand out v = SOME (n2w p)` by
    (irule abi_decoder_vars_extend_eval >> qexistsl_tac [`upper`, `u`] >>
     gvs[abi_encode_staged_observation_def]) >>
  fs[vars_ext_def] >>
  qpat_x_assum `v = u with vs_vars := _` SUBST_ALL_TAC >>
  gvs[abi_encode_staged_observation_def,
      Q.INST [`t` |-> `u with vs_vars := vv`, `s` |-> `u`]
        (SPEC_ALL loweringPostsTheory.pure_frame_state_cong),
      abi_encode_semantic_obs_def, mload_def] >>
  rpt strip_tac >>
  gvs[lookup_var_def] >> metis_tac[FLOOKUP_SUBMAP]
QED

Theorem abi_encode_exec_frame_extend:
  abi_encode_exec_frame obs initial u /\ abi_decoder_vars_extend upper u v ==>
  abi_encode_exec_frame obs initial v
Proof
  strip_tac >> drule abi_encode_bounded_vars_ext >>
  gvs[vars_ext_def, abi_encode_exec_frame_def, pending_alloca_size_def,
      abi_encode_semantic_obs_def] >>
  simp[venom_state_component_equality]
QED
