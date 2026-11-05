(* Compiler metadata and ID boundaries for external-return encoders. *)
Theory externalReturnEncoderSites
Ancestors
  externalReturnZeroLayout externalReturnWindowResources exprLoweringProps
  abiEncoderProps pred_set emitHelper compileEnv context

Theorem external_package_encoder_admissible:
  set_external_package_target tgt
    (package_external_fn tops ut0 nkm
      (mut, F, rr, fname, fargs, dflts, ret, fbody)) =
    (lbl, cenv0, pos_args, min_cds, is_payable, nr, nkey, ut, iv, fbody', rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv, sa) /\
  same_frame cenv cenv' /\ ret <> NoneT ==>
  abi_encoder_admissible cenv'.ce_ret_enc_info
Proof
  strip_tac >> drule_all external_package_return_encoder >>
  disch_then SUBST1_TAC >> simp[return_plan_encoder_admissible]
QED

Theorem encoder_fragment_prior_site_excluded:
  id < st.cs_next_id ==> id NOTIN frag_ids st en
Proof
  simp[frag_ids_def]
QED

Theorem allocated_encoder_site_excluded:
  compile_alloc_buffer n sa = (buf,st) ==>
  sa.cs_next_id NOTIN frag_ids st en
Proof
  simp[compile_alloc_buffer_def, emit_op_def, emit_inst_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def, frag_ids_def] >>
  rpt strip_tac >> gvs[]
QED
