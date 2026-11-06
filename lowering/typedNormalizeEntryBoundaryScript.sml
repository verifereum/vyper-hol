Theory typedNormalizeEntryBoundary
Ancestors
  typedNormalizeContinuation abiDecoderPhi fragExec exprLoweringProps
  stmtLoweringMono abiEncoderExitPhi compileEnv context venomExecSemantics
  venomInst emitHelper exprLowering stmtLowering

(* The second clause of abi_decoder_phi deliberately permits old PHIs. *)
Theorem normalize_changed_prefix_zero:
  cs_extends sa sb /\ abi_decoder_phi sa sb /\
  emitted_blocks sa sb <> [] ==>
  phi_prefix_length sb.cs_current_insts = 0
Proof
  simp_tac bool_ss [cs_extends_def, abi_decoder_phi_def] >>
  strip_tac >>
  `emitted_blocks sa sb = new` by metis_tac[emitted_blocks_append] >>
  gvs[]
QED

Theorem normalize_typed_changed_prefix_zero:
  compile_store_memory_typed ce dst dt src st sa = (x,sb) /\
  emitted_blocks sa sb <> [] ==>
  phi_prefix_length sb.cs_current_insts = 0
Proof
  strip_tac >> irule normalize_changed_prefix_zero >>
  qexists_tac `sa` >> simp[] >> reverse conj_tac
  >- metis_tac[cj 1 ci_mono_typed_memory_family, ci_mono_def, pairTheory.SND] >>
  mp_tac (cj 1 normalize_phi_typed_family) >>
  disch_then (qspecl_then [`ce`,`dst`,`dt`,`src`,`st`,`sa`] mp_tac) >> simp[]
QED

Theorem normalize_fields_changed_prefix_zero:
  compile_typed_copy_fields ce dst src dts sts doff soff sa = (x,sb) /\
  emitted_blocks sa sb <> [] ==>
  phi_prefix_length sb.cs_current_insts = 0
Proof
  strip_tac >> irule normalize_changed_prefix_zero >>
  qexists_tac `sa` >> simp[] >> reverse conj_tac
  >- metis_tac[cj 2 ci_mono_typed_memory_family, ci_mono_def, pairTheory.SND] >>
  mp_tac (cj 2 normalize_phi_typed_family) >>
  disch_then (qspecl_then [`ce`,`dst`,`src`,`dts`,`sts`,`doff`,`soff`,`sa`] mp_tac) >> simp[]
QED

Theorem normalize_offset_no_blocks:
  compile_with_byte_offset op off sa = (out,sb) ==>
  emitted_blocks sa sb = []
Proof
  simp[compile_with_byte_offset_def] >> IF_CASES_TAC >>
  simp[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[emitted_blocks_def]
QED

Theorem normalize_changed_blocks_trans:
  cs_extends sa sc /\ cs_extends sc sb /\
  emitted_blocks sa sc <> [] ==> emitted_blocks sa sb <> []
Proof
  simp_tac bool_ss [cs_extends_def] >> strip_tac >>
  `emitted_blocks sa sc = new` by metis_tac[emitted_blocks_append] >>
  `emitted_blocks sa sb = new' ++ new` by
    (irule emitted_blocks_append >> simp[]) >>
  gvs[listTheory.APPEND_eq_NIL]
QED

(* Only a block-changing child needs its endpoint as a fresh entry. *)
Theorem normalize_conditional_suffix_entry:
  cs_extends initial sa /\ cs_extends sa sb /\ abi_decoder_phi sa sb /\
  (emitted_blocks initial sa <> [] ==>
     phi_prefix_length sa.cs_current_insts = 0) /\
  fn_has_code sa sb fn /\
  (emitted_blocks initial sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) ==>
  (emitted_blocks initial sa <> [] ==>
    ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0)
Proof
  rpt strip_tac >>
  `emitted_blocks initial sb <> []` by
    metis_tac[normalize_changed_blocks_trans] >>
  irule normalize_phi_suffix_entry >> simp[] >> qexists_tac `sb` >> simp[]
QED

Theorem normalize_fields_conditional_suffix_entry:
  cs_extends initial sa /\
  (emitted_blocks initial sa <> [] ==>
    phi_prefix_length sa.cs_current_insts = 0) /\
  compile_typed_copy_fields ce dst src dts sts doff soff sa = (x,sb) /\
  fn_has_code sa sb fn /\
  (emitted_blocks initial sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) ==>
  (emitted_blocks initial sa <> [] ==>
    ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0)
Proof
  rpt strip_tac >> irule normalize_phi_suffix_entry >> simp[] >>
  qexists_tac `sb` >> simp[] >>
  `cs_extends sa sb` by
    metis_tac[cj 2 ci_mono_typed_memory_family, ci_mono_def, pairTheory.SND] >>
  `emitted_blocks initial sb <> []` by
    metis_tac[normalize_changed_blocks_trans] >> simp[] >>
  mp_tac (cj 2 normalize_phi_typed_family) >>
  disch_then (qspecl_then [`ce`,`dst`,`src`,`dts`,`sts`,`doff`,`soff`,`sa`] mp_tac) >> simp[]
QED

Theorem normalize_offset_conditional_suffix_entry:
  cs_extends initial sa /\
  (emitted_blocks initial sa <> [] ==>
    phi_prefix_length sa.cs_current_insts = 0) /\
  compile_with_byte_offset op off sa = (out,sb) /\
  fn_has_code sa sb fn /\
  (emitted_blocks initial sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) ==>
  (emitted_blocks initial sa <> [] ==>
    ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0)
Proof
  rpt strip_tac >>
  `emitted_blocks sa sb = []` by metis_tac[normalize_offset_no_blocks] >>
  `phi_prefix_length sa.cs_current_insts = 0` by simp[] >>
  irule normalize_field_offset_entry >> simp[] >>
  qexistsl_tac [`off`,`op`,`out`,`sb`] >> simp[] >>
  strip_tac >> gvs[compile_with_byte_offset_def, comp_return_def]
QED

Theorem normalize_typed_external_return_entry:
  compile_store_memory_typed ce dst dt src st initial = (y,sa) /\
  compile_external_return ret prim raw info msz nr nkey ut iv sa = (x,sb) /\
  (nr ==> iv) /\ fn_has_code sa sb fn ==>
  (emitted_blocks initial sa <> [] ==>
    ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0)
Proof
  rpt strip_tac >>
  `phi_prefix_length sa.cs_current_insts = 0` by
    metis_tac[normalize_typed_changed_prefix_zero] >>
  drule_all normalize_external_return_entry >> simp[]
QED
