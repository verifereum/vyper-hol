(* Setup normalization preserves the caller relation by retaining old locals. *)
Theory abiDecodePtrEntryFrame
Ancestors
  abiDecodePtrReentryGhost abiDecoderReentry assignTuplePtrLoadStep
  stateFrame compileEnv venomState finite_map pred_set arithmetic

Theorem abi_decode_ptr_prune_stmt_state_rel:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
  stmt_state_rel ctx func cenv cx es
    (abi_decoder_prune_vars sa.cs_next_var s)
Proof
  strip_tac >> irule stmt_state_rel_old_vars_frame_ptr >>
  qexistsl [`s`, `sa`] >> simp[abi_decoder_prune_vars_def, state_frame_def] >>
  rpt strip_tac >>
  fs[lookup_var_def, FLOOKUP_DRESTRICT, not_fresh_at_def,
     abi_decoder_older_vars_def]
QED
