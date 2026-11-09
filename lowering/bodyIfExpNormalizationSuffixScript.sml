Theory bodyIfExpNormalizationSuffix
Ancestors
  typedNormalizeEntryBoundary abiEncoderExitPhi emitHelperProps
  fragExec context venomInst venomExecSemantics

(* The conditional appends ASSIGN before its jump.  Even when normalization
   leaves an empty exit block, this supplies a nonempty non-PHI prefix. *)
Theorem ifexp_typed_normalization_assign_exit_phi:
  compile_store_memory_typed ce dst dt src st sa = ((),sb) /\
  emit_inst ASSIGN [op] [rv] sb = ((),sc) /\
  fn_has_code sb sc func /\
  emitted_blocks sa sb <> [] ==>
  ?bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
       phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  `phi_prefix_length sb.cs_current_insts = 0` by
    (drule_all normalize_typed_changed_prefix_zero >> simp[]) >>
  drule emit_inst_extends >> strip_tac >>
  `sc.cs_current_insts <> []` by simp[] >>
  `phi_prefix_length sc.cs_current_insts = 0` by
    (Cases_on `sb.cs_current_insts` >>
     gvs[phi_prefix_length_def, mk_inst_def] >>
     Cases_on `h.inst_opcode = PHI` >> gvs[]) >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  simp_tac bool_ss [fn_has_code_def] >> strip_tac >>
  qexists_tac `bb` >> metis_tac[abi_encoder_nonempty_prefix_phi]
QED
